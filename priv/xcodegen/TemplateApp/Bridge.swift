//
//  Bridge.swift
//  TemplateApp
//
//  Created by Dominic Letz on 25.09.21.
//

import Foundation
import Network
import ZIPFoundation
import SwiftUI

enum BridgeError: LocalizedError {
    case missingAppZip
    case missingBundleIdentifier

    var errorDescription: String? {
        switch self {
        case .missingAppZip:
            return "app.zip not found in application bundle"
        case .missingBundleIdentifier:
            return "Bundle identifier is missing"
        }
    }
}

class Bridge {
    var webview: WebViewController?
    var listener: NWListener?
    let home: URL
    var lastURL: URL?
    static public var instance: Bridge?
    var erlangStarted = false
    private var isReinitializing = false

    func setWebView(view: WebViewController) {
        self.webview = view
        loadURL()
    }

    func setURL(url: String) {
        lastURL = URL(string: url)
        loadURL()
    }

    func loadURL() {
        if let view = self.webview, let url = self.lastURL {
            print("Bridge: loading \(url)")
            view.loadURL(url: url)
        }
    }

    private var connectionsByID: [Int: ServerConnection] = [:]
    private let connectionsQueue = DispatchQueue(label: "bridge.connections")

    init() throws {
        guard let bundleID = Bundle.main.bundleIdentifier else {
            throw BridgeError.missingBundleIdentifier
        }
        home = FileManager.default.urls(for: .libraryDirectory, in: .userDomainMask)[0]
            .appendingPathComponent(bundleID)

        Bridge.instance = self
    }

    /// Extract app.zip and write inetrc. Safe to call from a background thread.
    func extractAppIfNeeded() throws {
        let zipURL = try zipFile()
        let infoAttr = try FileManager.default.attributesOfItem(atPath: zipURL.path)
        let infoDate = (infoAttr[FileAttributeKey.creationDate] as? Date) ?? Date.distantPast
        let build = UserDefaults.standard.string(forKey: "app_build_date")

        let appdir = home.appendingPathComponent("app")
        let info = appdir.appendingPathComponent("releases").appendingPathComponent("start_erl.data")

        if !FileManager.default.fileExists(atPath: info.path) {
            try unzipApp(dest: appdir)
        } else if infoDate.description != build {
            try FileManager.default.removeItem(atPath: appdir.path)
            try unzipApp(dest: appdir)
            UserDefaults.standard.set(infoDate.description, forKey: "app_build_date")
        }

        let inet_rc = appdir.appendingPathComponent("inetrc")
        setEnv(name: "ERL_INETRC", value: inet_rc.path)
        let rc = #"""
        %% enable EDNS, 0 means enable YES!
        {edns,0}.
        {alt_nameserver, {8,8,8,8}}.
        %% specify lookup method
        {lookup, [dns]}.
        """#
        try rc.write(to: inet_rc, atomically: true, encoding: .utf8)
    }

    func setupListener() {
        do {
            let l = try NWListener(using: .tcp, on: Bridge.port())
            l.stateUpdateHandler = self.stateDidChange(to:)
            l.newConnectionHandler = self.didAccept(nwConnection:)
            l.start(queue: .global())
            listener = l
        } catch {
            print("Bridge: failed to create TCP listener: \(error)")
        }
    }

    /// Disconnect LiveView WebSocket before going to background.
    /// This prevents the LiveView JS from attempting reconnections
    /// while iOS has suspended the app's network connections.
    func suspendWebSocket() {
        webview?.evaluateJavaScript("""
            if (window.__bridgeSuspended) return;
            window.__bridgeSuspended = true;
            if (window.liveSocket) {
                window.liveSocket.disconnect();
            }
        """)
    }

    /// Re-initialize the Bridge TCP listener after returning to foreground.
    /// After the TCP connection is re-established and the Elixir-side ranch
    /// listener has been resumed, triggers a LiveView reconnect via JS injection.
    func reinit() {
        guard !isReinitializing else { return }

        let needsRestart = connectionsQueue.sync {
            connectionsByID.isEmpty || connectionsByID.values.allSatisfy { conn in
                switch conn.connection.state {
                case .cancelled, .failed:
                    return true
                default:
                    return false
                }
            }
        }

        if needsRestart {
            isReinitializing = true
            stopListener()
            setupListener()

            // Wait for the Elixir-side ranch listener to finish suspend/resume,
            // then reconnect LiveView WebSocket.
            DispatchQueue.main.asyncAfter(deadline: .now() + 0.8) { [weak self] in
                self?.reconnectWebSocket()
                self?.isReinitializing = false
            }
        } else {
            reconnectWebSocket()
        }
    }

    /// Inject JavaScript to reconnect the LiveView WebSocket.
    /// Polls the Phoenix HTTP server until it's ready, then triggers
    /// the LiveSocket connect to avoid "reconnect" / "something went wrong" flashes.
    private func reconnectWebSocket() {
        guard let url = self.lastURL else { return }
        webview?.evaluateJavaScript("""
            window.__bridgeSuspended = false;
            (function reconnectLiveView() {
                fetch('\(url.absoluteString)', {method: 'HEAD', cache: 'no-store'})
                    .then(function() {
                        if (window.liveSocket) {
                            window.liveSocket.connect();
                        }
                    })
                    .catch(function() {
                        setTimeout(reconnectLiveView, 200);
                    });
            })();
        """)
    }

    /// Open a URL in the system default browser (Safari).
    func launchDefaultBrowser(urlString: String) {
        guard let url = URL(string: urlString) else { return }
        DispatchQueue.main.async {
            UIApplication.shared.open(url)
        }
    }

    /// Return the current device locale in the format "language_COUNTRY" (e.g. "en_US").
    func currentLocaleIdentifier() -> String {
        let locale = Locale.current
        let language = locale.language.languageCode?.identifier ?? "en"
        let country = locale.region?.identifier ?? "US"
        return "\(language)_\(country)"
    }

    static func port() -> NWEndpoint.Port {
        let port = UserDefaults.standard.string(forKey: "port")
            ?? {
                let p = String(20000 + Int.random(in: 1...20000))
                UserDefaults.standard.set(p, forKey: "port")
                return p
            }()
        guard let nwPort = NWEndpoint.Port(port) else {
            let fallback = String(20000 + Int.random(in: 1...20000))
            UserDefaults.standard.set(fallback, forKey: "port")
            return NWEndpoint.Port(fallback)!
        }
        return nwPort
    }

    func setEnv(name: String, value: String) {
        setenv(name, value, 1)
    }

    func zipFile() throws -> URL {
        guard let url = Bundle.main.url(forResource: "app", withExtension: "zip") else {
            throw BridgeError.missingAppZip
        }
        return url
    }

    func unzipApp(dest: URL) throws {
        try FileManager.default.createDirectory(at: dest, withIntermediateDirectories: true, attributes: nil)
        try FileManager.default.unzipItem(at: try zipFile(), to: dest)
    }

    func stateDidChange(to newState: NWListener.State) {
        switch newState {
        case .ready:
            if erlangStarted { break }
            erlangStarted = true
            print("Bridge: server ready, starting Erlang")

            guard let portValue = listener?.port?.rawValue else {
                print("Bridge: ERROR — listener port is nil, cannot start Erlang")
                return
            }

            setEnv(name: "ELIXIR_DESKTOP_OS", value: "ios")
            setEnv(name: "BRIDGE_PORT", value: String(portValue))
            setEnv(name: "HOME", value: home.path)
            let bindir = home.appendingPathComponent("bin")
            setEnv(name: "BINDIR", value: bindir.path)

            let urls = FileManager.default.urls(for: .documentDirectory, in: .userDomainMask)
            let logdir = urls[0].path
            let appdir = home.appendingPathComponent("app")
            let ret = start_erlang(appdir.path, logdir)
            let result = ret.map { String(cString: $0) } ?? "nil"
            print("Bridge: erlang start returned: " + result)

        case .failed(let error):
            print("Bridge: server failure: \(error.localizedDescription)")
        case .cancelled:
            print("Bridge: server cancelled")
        default:
            break
        }
    }

    private func didAccept(nwConnection: NWConnection) {
        let connection = ServerConnection(nwConnection: nwConnection, bridge: self)
        connectionsQueue.sync {
            self.connectionsByID[connection.id] = connection
        }
        connection.didStopCallback = { _ in
            self.connectionDidStop(connection)
        }
        connection.start()
        let payload = "\0\0\0\0\0\0\0\0\":reconnect\"".data(using: .utf8)!

        let size: UInt32 = CFSwapInt32(UInt32(payload.count))
        var message = withUnsafeBytes(of: size) { Data($0) }
        message.append(payload)
        connection.send(data: message)
    }

    private func connectionDidStop(_ connection: ServerConnection) {
        connectionsQueue.sync {
            self.connectionsByID.removeValue(forKey: connection.id)
        }
    }

    private func stopListener() {
        if let l = listener {
            l.stateUpdateHandler = nil
            l.newConnectionHandler = nil
            l.cancel()
            listener = nil
        }
    }

    private func stop() {
        stopListener()
        connectionsQueue.sync {
            for connection in self.connectionsByID.values {
                connection.didStopCallback = nil
                connection.stop()
            }
            self.connectionsByID.removeAll()
        }
    }
}

class ServerConnection {
    let MTU = 65536

    private static var nextID: Int = 0
    private static let idLock = NSLock()
    let connection: NWConnection
    let id: Int
    var bridge: Bridge

    init(nwConnection: NWConnection, bridge: Bridge) {
        self.bridge = bridge
        connection = nwConnection
        ServerConnection.idLock.lock()
        id = ServerConnection.nextID
        ServerConnection.nextID += 1
        ServerConnection.idLock.unlock()
    }

    var didStopCallback: ((Error?) -> Void)? = nil

    func start() {
        connection.stateUpdateHandler = self.stateDidChange(to:)
        setupReceive()
        connection.start(queue: .main)
    }

    private func stateDidChange(to state: NWConnection.State) {
        switch state {
        case .waiting(let error):
            connectionDidFail(error: error)
        case .failed(let error):
            connectionDidFail(error: error)
        case .ready:
            break
        default:
            break
        }
    }

    private func setupReceive() {
        connection.receive(minimumIncompleteLength: 4, maximumLength: 4) { (data, _, isComplete, error) in
            if isComplete {
                self.connectionDidEnd()
                return
            }

            if let error = error {
                self.connectionDidFail(error: error)
                return
            }

            guard let data = data else {
                self.connectionDidEnd()
                return
            }
            let length: Int = Int(CFSwapInt32(data.uint32))
            self.connection.receive(minimumIncompleteLength: length, maximumLength: length) { (datain, _, isComplete, error) in
                if isComplete {
                    self.connectionDidEnd()
                    return
                }

                if let error = error {
                    self.connectionDidFail(error: error)
                    return
                }

                guard let datain = datain, datain.count >= 8 else {
                    print("Bridge: received incomplete data")
                    self.setupReceive()
                    return
                }

                let ref = datain.prefix(8)
                let data = datain.dropFirst(8)

                guard let json = try? JSONSerialization.jsonObject(with: data, options: []),
                      let array = json as? [Any],
                      let method = array[1] as? String,
                      let args = array[2] as? [Any] else {
                    print("Bridge: failed to parse message")
                    self.setupReceive()
                    return
                }

                if method == ":loadURL" {
                    if let urlStr = args[safe: 1] as? String {
                        self.bridge.setURL(url: urlStr)
                    }
                }
                if method == ":launchDefaultBrowser" {
                    if let urlStr = args[0] as? String {
                        self.bridge.launchDefaultBrowser(urlString: urlStr)
                    }
                }

                var response = ref
                if method == ":getOsDescription" {
                    response.append(self.dataToList(string: "iOS \(UIDevice().model)"))
                } else if method == ":getCanonicalName" {
                    response.append(self.dataToList(string: self.bridge.currentLocaleIdentifier()))
                } else {
                    response.append("use_mock".data(using: .utf8)!)
                }

                let size: UInt32 = CFSwapInt32(UInt32(response.count))
                var message = withUnsafeBytes(of: size) { Data($0) }
                message.append(response)
                self.send(data: message)
                self.setupReceive()
            }
        }
    }

    func dataToList(string: String) -> Data {
        return dataToList(data: string.data(using: .utf8)!)
    }
    func dataToList(data: Data) -> Data {
        let numbers = data.map { "\($0)" }
        return "[\(numbers.joined(separator: ","))]".data(using: .utf8)!
    }

    func send(data: Data) {
        self.connection.send(content: data, completion: .contentProcessed({ error in
            if let error = error {
                self.connectionDidFail(error: error)
            }
        }))
    }

    func stop() {
        connection.stateUpdateHandler = nil
        connection.cancel()
    }

    private func connectionDidFail(error: Error) {
        print("Bridge: connection \(id) failed: \(error)")
        stop(error: error)
    }

    private func connectionDidEnd() {
        stop(error: nil)
    }

    private func stop(error: Error?) {
        connection.stateUpdateHandler = nil
        connection.cancel()
        if let didStopCallback = didStopCallback {
            self.didStopCallback = nil
            didStopCallback(error)
        }
    }
}

extension Data {
    var uint32: UInt32 {
        get {
            let i32array = self.withUnsafeBytes { $0.load(as: UInt32.self) }
            return i32array
        }
    }
}

extension Array {
    subscript(safe index: Int) -> Element? {
        return indices.contains(index) ? self[index] : nil
    }
}
