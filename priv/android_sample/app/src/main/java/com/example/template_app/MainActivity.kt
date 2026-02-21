package com.example.template_app

import android.os.Bundle
import android.view.KeyEvent
import android.view.View
import android.webkit.WebView
import android.webkit.WebViewClient
import androidx.activity.result.contract.ActivityResultContracts
import androidx.appcompat.app.AppCompatActivity


class MainActivity : AppCompatActivity() {
    private lateinit var webView: WebView
    private lateinit var splash: View
    private lateinit var bridge: Bridge

    private val filePicker = registerForActivityResult(
        ActivityResultContracts.StartActivityForResult()
    ) { result ->
        bridge.onFilePickerResult(result.resultCode, result.data)
    }


    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        setContentView(R.layout.activity_main)
        webView = findViewById(R.id.browser)
        splash = findViewById(R.id.splash)

        if (::bridge.isInitialized) {
            bridge.setWebView(webView)
        } else {
            // ★ Activity と ランチャを渡す
            bridge = Bridge(
                activity = this,
                webview = webView,
                launchPicker = { intent -> filePicker.launch(intent) }
            )
        }

        webView.webViewClient = object : WebViewClient() {
            override fun onPageFinished(view: WebView, url: String) {
                if (webView.visibility != View.VISIBLE) {
                    webView.visibility = View.VISIBLE
                    splash.visibility = View.GONE
                    reportFullyDrawn()
                }
            }
        }
    }

    override fun onPause() {
        super.onPause()
        // Proactively disconnect LiveView WebSocket before Android
        // throttles the app's networking in the background.
        if (::bridge.isInitialized) {
            bridge.suspendWebSocket()
        }
    }

    override fun onResume() {
        super.onResume()
        // Reconnect LiveView WebSocket after returning to foreground.
        // The TCP Bridge connection stays alive on Android, so we only
        // need to re-establish the LiveView WebSocket.
        if (::bridge.isInitialized) {
            bridge.reconnectWebSocket()
        }
    }

    override fun onKeyDown(keyCode: Int, event: KeyEvent): Boolean {
        if (event.action == KeyEvent.ACTION_DOWN && keyCode == KeyEvent.KEYCODE_BACK) {
            if (webView.canGoBack()) {
                webView.goBack()
            } else {
                finish()
            }
            return true
        }
        return super.onKeyDown(keyCode, event)
    }
}
