# DesktopSetup

Setup library for [ElixirDesktop](https://github.com/elixir-desktop/desktop) — build native iOS and Android apps from your Phoenix application.

## Requirements

- **Erlang/OTP 28** and **Elixir 1.19** (managed via [mise](https://mise.jdx.dev/))
- **macOS** for iOS builds; macOS or Linux for Android builds

### Common (macOS)

```bash
brew install wxwidgets@3.2 openssl@3
export KERL_CONFIGURE_OPTIONS="--without-javac --with-ssl=$(brew --prefix openssl@3) --with-wx-config=$(brew --prefix wxwidgets@3.2)/bin/wx-config-3.2"
mise install erlang@28.3.1
mise install elixir@1.19.5-otp-28
```

### iOS

```bash
brew install carthage xcodegen
```

- Xcode 16+ (iOS 17.4+ deployment target)

### Android

- Android Studio with SDK 36, NDK, and CMake 3.22.1
- Java 17

## Installation

Add `desktop_setup` to your list of dependencies in `mix.exs`:

```elixir
def deps do
  [
    {:desktop_setup, github: "thehaigo/desktop_setup", only: :dev}
  ]
end
```

## Usage

### 1. Install ElixirDesktop into your Phoenix app

```bash
mix desktop.install
```

This modifies your Phoenix app's config, endpoint, application module, and `mix.exs` for ElixirDesktop compatibility. The task is idempotent — safe to run multiple times.

### 2. iOS Setup

```bash
mix desktop.setup.ios
cd native/ios
open YourAppName.xcodeproj
```

Build and run from Xcode. If you encounter build errors, try running the build script manually:

```bash
cd native/ios
./run_mix
```

### 3. Android Setup

```bash
mix desktop.setup.android
```

Open `native/android` in Android Studio and build. If you encounter build errors:

```bash
cd native/android
./app/run_mix
```

### 4. SQLite Migrations (optional)

If your app uses SQLite (`ecto_sqlite3`), convert Ecto migration files for on-device execution:

```bash
mix desktop.migrations.convert
```

This converts `priv/repo/migrations/*.exs` into compiled modules under `lib/<app>/migrations/` that run at app startup.

## Architecture

```
Phoenix App  -->  mix release  -->  app.zip
                                      |
                               Native Shell (Swift / Kotlin)
                                      |
                               Erlang VM (liberlang)
                                      |
                               TCP Bridge Protocol
                                      |
                               Phoenix Endpoint  -->  WebView
```

Both iOS and Android use the same Bridge protocol: a TCP socket carrying length-prefixed JSON messages between the Erlang VM and the native shell. The native side manages app lifecycle (background/foreground), WebView display, and system integration (file upload, external browser, dialogs).

### Platform Details

| Feature | iOS | Android |
|---------|-----|---------|
| Native language | Swift (SwiftUI) | Kotlin |
| Bridge transport | NWListener (TCP) | ServerSocket (TCP) |
| WebView | WKWebView | android.webkit.WebView |
| File upload | Native WKWebView support (iOS 12+) | onShowFileChooser + ActivityResultLauncher |
| Background handling | scenePhase → suspend/reinit | onStop/onStart → suspend/reconnect |
| Erlang VM | liberlang.xcframework (static) | liberlang.so (shared, per ABI) |
| Build tool | XcodeGen + Carthage | Gradle + CMake |

## PostgreSQL on Mobile (Development)

If you use PostgreSQL, add the following to `config/prod.exs`:

```elixir
config :your_app, YourApp.Repo,
  username: "postgres",
  password: "postgres",
  database: "your_app_dev",
  stacktrace: true,
  show_sensitive_data_on_connection_error: true,
  pool_size: 10

if Mix.target() == :ios do
  config :your_app, YourApp.Repo, hostname: "127.0.0.1"
end

if Mix.target() == :android do
  config :your_app, YourApp.Repo, hostname: "10.0.2.2"
end
```

## Troubleshooting

### ZIPFoundation not found (iOS)

```
There is no XCFramework found at 'ios/Carthage/Build/ZIPFoundation.xcframework'.
```

```bash
cd native/ios
carthage update --platform iOS --use-xcframeworks
```

### Build script sandboxing error (iOS)

```
Sandbox: bash(39046) deny(1) file-read-data
```

In Xcode: Build Settings → Build Options → User Script Sandboxing → **No**

### KVM permission denied (Android on WSL2)

```
/dev/kvm device: permission denied
```

```bash
sudo chown $USER /dev/kvm
```

## Roadmap

- [x] Desktop app setup
- [x] iOS app setup
- [x] Android app setup
- [x] Erlang/OTP 25 → 26 → 27 → 28
- [x] JS dialog support (alert/confirm/prompt) on both platforms
- [x] JS console log forwarding to native debug console
- [x] File upload support on both platforms
- [x] Background/foreground lifecycle handling with LiveView reconnection
