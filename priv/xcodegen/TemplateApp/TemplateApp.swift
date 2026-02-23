//
//  TemplateApp.swift
//  TemplateApp
//

import SwiftUI

@main
struct TemplateApp: App {
    @Environment(\.scenePhase) var scenePhase
    
    var content = ContentView()
    var body: some Scene {
        WindowGroup {
            self.content
        }
        .onChange(of: scenePhase) { _, phase in
            switch phase {
            case .background:
                print(".background")
                // Proactively disconnect LiveView WebSocket before iOS
                // freezes the network. This prevents the LiveView JS from
                // firing reconnection attempts while the app is suspended.
                if let bridge = Bridge.instance {
                    bridge.suspendWebSocket()
                }
            case .active:
                print(".active")
                // Re-establish Bridge TCP connection and then reconnect
                // LiveView WebSocket only after the server is ready.
                if let bridge = Bridge.instance {
                    bridge.reinit()
                }

            default: break
            }
        }

    }
}
