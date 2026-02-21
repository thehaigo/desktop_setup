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
        
        // Forward JS console messages to Xcode console
        addScript(configuration, """
            (function() {
                const levels = ['log', 'warn', 'error', 'info', 'debug'];
                levels.forEach(function(level) {
                    const original = console[level];
                    console[level] = function() {
                        const args = Array.prototype.slice.call(arguments).map(function(arg) {
                            try { return typeof arg === 'object' ? JSON.stringify(arg) : String(arg); }
                            catch(e) { return String(arg); }
                        });
                        if (window.webkit && window.webkit.messageHandlers.consoleLog) {
                            window.webkit.messageHandlers.consoleLog.postMessage(
                                { level: level, message: args.join(' ') }
                            );
                        }
                        original.apply(console, arguments);
                    };
                });
                window.onerror = function(msg, url, line, column, error) {
                    if (window.webkit && window.webkit.messageHandlers.consoleLog) {
                        window.webkit.messageHandlers.consoleLog.postMessage(
                            { level: 'error', message: msg + ' (' + url + ':' + line + ':' + column + ')' }
                        );
                    }
                };
            })();
        """)
        configuration.userContentController.add(self, name: "consoleLog")
        
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

    func evaluateJavaScript(_ script: String) {
        DispatchQueue.main.async { [weak self] in
            self?.webview.evaluateJavaScript(script) { _, error in
                if let error = error {
                    print("JS evaluation error: \(error.localizedDescription)")
                }
            }
        }
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
            if let urlString = message.body as? String, let url = URL(string: urlString) {
                if UIApplication.shared.canOpenURL(url) {
                    UIApplication.shared.open(url)
                }
            }
        case "consoleLog":
            if let body = message.body as? [String: Any],
               let level = body["level"] as? String,
               let msg = body["message"] as? String {
                print("JS [\(level)] \(msg)")
            }
        default:
            print("WebView: received unknown message: \(message.name)")
        }
    }
}
