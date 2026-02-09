//
//  WebView.swift
//
//  Created by Dominic Letz on 19.09.22
//

import Foundation
import Combine

import SwiftUI
import UIKit
import WebKit

final class WebView: NSObject, WKNavigationDelegate, WKScriptMessageHandler {
    var webview: WKWebView
    var finish: (() -> ())?
    
    override init() {
        // Enable javascript in WKWebView to interact with the web app
        let preferences = WKPreferences()
        // preferences.javaScriptEnabled = true
        
        let page = WKWebpagePreferences()
        page.allowsContentJavaScript = true
        
        let configuration = WKWebViewConfiguration()
        configuration.limitsNavigationsToAppBoundDomains = true
        configuration.preferences = preferences
        configuration.defaultWebpagePreferences = page
        
        webview = WKWebView(frame: CGRect.zero, configuration: configuration)
        // webView.navigationDelegate = context.coordinator
        webview.allowsBackForwardNavigationGestures = true
        webview.scrollView.isScrollEnabled = true
        
        super.init()
        
        configuration.userContentController.add(self, name: "openSafari")

        // fixing the zoom level
        addScript(configuration, "var meta = document.createElement('meta');" +
            "meta.name = 'viewport';" +
            "meta.content = 'width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no';" +
            "var head = document.getElementsByTagName('head')[0];" +
            "head.appendChild(meta);")
        
        // adding debug output
        addScript(configuration, "window.onerror = (msg, url, line, column, error) => { " +
          "const message = {" +
          "  message: msg," +
          "  url: url," +
          "  line: line," +
          "  column: column," +
          "  error: JSON.stringify(error)" +
          "}" +
          "if (window.webkit) {" +
          "  window.webkit.messageHandlers.error.postMessage(message);" +
          "}" +
          "};")
        configuration.userContentController.add(self, name: "error")
        configuration.userContentController.add(self, name: "forceReconnect")
        configuration.userContentController.add(self, name: "consoleLog")

        // console.log/warn/error render native
        addScript(configuration, """
            (function() {
                var originalLog = console.log;
                var originalWarn = console.warn;
                var originalError = console.error;

                console.log = function() {
                    originalLog.apply(console, arguments);
                    if (window.webkit && window.webkit.messageHandlers.consoleLog) {
                        window.webkit.messageHandlers.consoleLog.postMessage('[LOG] ' + Array.from(arguments).join(' '));
                    }
                };
                console.warn = function() {
                    originalWarn.apply(console, arguments);
                    if (window.webkit && window.webkit.messageHandlers.consoleLog) {
                        window.webkit.messageHandlers.consoleLog.postMessage('[WARN] ' + Array.from(arguments).join(' '));
                    }
                };
                console.error = function() {
                    originalError.apply(console, arguments);
                    if (window.webkit && window.webkit.messageHandlers.consoleLog) {
                        window.webkit.messageHandlers.consoleLog.postMessage('[ERROR] ' + Array.from(arguments).join(' '));
                    }
                };
            })();
        """)

        // fixing the onlick event
        // https://stackoverflow.com/a/27525707
        addScript(configuration, """
            document.getElementsByTagName('a').forEach(node => {
                node.style.cursor = "pointer";
            })
        """)
        
        webview.navigationDelegate = self
    }
    
    func addScript(_ config: WKWebViewConfiguration, _ script: String) {
        let script: WKUserScript = WKUserScript(source: script, injectionTime: .atDocumentEnd, forMainFrameOnly: true)
        config.userContentController.addUserScript(script)
    }
    
    func onFinish(finish: @escaping () -> ()) {
        self.finish = finish
    }
    
    func webView(_ webView: WKWebView,
                          didFinish navigation: WKNavigation!) {
        if let fun = self.finish {
            fun()
        }
    }
    
    func userContentController(_ userContentController: WKUserContentController, didReceive message: WKScriptMessage) {
        switch message.name {
        case "openSafari":
            print(message.body)
            let url = URL(string:message.body as! String)
            if( UIApplication.shared.canOpenURL(url!) ) {
              UIApplication.shared.open(url!)
            }
        case "error":
            // You should actually handle the error :)
            let error = (message.body as? [String: Any])?["message"] as? String ?? "unknown"
            assertionFailure("JavaScript error: \(error)")
        case "forceReconnect":
            print("[WebView] forceReconnect called from JS")
            // Bridge経由で接続を強制リセットしてWebViewを再読み込み
            DispatchQueue.main.async {
                if let bridge = Bridge.instance {
                    bridge.forceReconnect()
                } else {
                    // Bridgeがない場合はフォールバックでリロード
                    self.webview.reload()
                }
            }
        case "consoleLog":
            if let logMessage = message.body as? String {
                print("[JS] \(logMessage)")
            }
        default:
            assertionFailure("Received invalid message: \(message.name)")
        }
    }

    // call Native -> JS 
    private func evalJavaScript(message: String) {
        let executeScript: String = "window.callFromNative(\"\(message)\");"
        webview.evaluateJavaScript(executeScript, completionHandler: { (object, error) -> Void in
            if let object = object {
                print(object)
            }
            if let error = error {
                print(error)
            }
        })
    }
}
