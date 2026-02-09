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
            case .active:
                print(".active")
                DispatchQueue.main.asyncAfter(deadline: .now() + 0.3) {
                    if let bridge = Bridge.instance {
                        bridge.reinit()
                    }
                }

            default: break
            }
        }

    }
}
