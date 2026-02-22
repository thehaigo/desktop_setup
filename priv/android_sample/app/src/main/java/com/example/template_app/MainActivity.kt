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

    override fun onStop() {
        super.onStop()
        // Disconnect LiveView WebSocket when the activity is no longer visible.
        // Uses onStop instead of onPause to avoid unnecessary disconnections
        // during multi-window, notification shade, or picture-in-picture.
        if (::bridge.isInitialized) {
            bridge.suspendWebSocket()
        }
    }

    override fun onStart() {
        super.onStart()
        // Reconnect LiveView WebSocket when the activity becomes visible.
        // The TCP Bridge connection stays alive on Android, so we only
        // need to re-establish the LiveView WebSocket.
        if (::bridge.isInitialized) {
            bridge.reconnectWebSocket()
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        if (::bridge.isInitialized) {
            bridge.dispose()
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
