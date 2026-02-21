//
//  ContentView.swift
//  TemplateApp
//

import SwiftUI
import UIKit
import WebKit

struct ContentView: View {
    @State var isActive: Bool = false
    @State var webview: WebViewController?
    @State var errorMessage: String?

    var body: some View {
        VStack {
            if let error = errorMessage {
                VStack(spacing: 12) {
                    Image(systemName: "exclamationmark.triangle")
                        .font(.largeTitle)
                        .foregroundColor(.red)
                    Text("Failed to start")
                        .font(.headline)
                    Text(error)
                        .font(.caption)
                        .foregroundColor(.secondary)
                        .multilineTextAlignment(.center)
                        .padding(.horizontal)
                }
                .frame(maxWidth: .infinity, maxHeight: .infinity)
                .background(Color("SplashBackground"))
                .ignoresSafeArea()
            } else if self.isActive {
                webview!.ignoresSafeArea()
            } else {
                Color("SplashBackground")
                    .ignoresSafeArea()
            }
        }
        .onAppear {
            DispatchQueue.main.async {
                do {
                    let bridge = try Bridge()
                    self.webview = WebViewController()
                    self.webview?.webview.onFinish {
                        self.isActive = true
                    }
                    bridge.setWebView(view: self.webview!)
                } catch {
                    print("Bridge init failed: \(error)")
                    self.errorMessage = error.localizedDescription
                }
            }
        }
    }
}

struct ContentView_Previews: PreviewProvider {
    static var previews: some View {
        ContentView()
    }
}
