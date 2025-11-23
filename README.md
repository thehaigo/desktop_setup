# DesktopSetup

Setup Library for Multiplatform Dev kit ElixirDesktop
https://github.com/elixir-desktop/desktop



## Requirements
Using Erlang version 27.3.4
Therefore, the build environment must be the same

```
asdf install erlang 27.3.4
asdf install elixir 1.19.3-otp-27
brew install carthage xcodegen
```


## Installation

If [available in Hex](https://hex.pm/docs/publish), the package can be installed
by adding `desktop_setup` to your list of dependencies in `mix.exs`:

```elixir
def deps do
  [
    {:desktop_setup, github: "thehaigo/desktop_setup", only: :dev}
  ]
end
```

## Usage
install to your phoenix app and run it 

```
mix desktop.install
```
 

## iOS Setup

```
mix desktop.setup.ios
```

```
cd native/ios
open [your app name].xcodeproj
```
build from Xcode 

if happen build error
try `./run_mix` at console


## Android Setup

```
mix desktop.setup.android
```
open from Android Studio
build from Android Studio

if happen build error
try `./app/run_mix` at console


## Roadmap

- [x] Dektop app setup
- [x] iOS App setup
- [x] Android App setup
- [x] update Android Erlang 25 -> 26
- [x] update Android Erlang 26 -> 27


## Use PostgreSQL at iOS and Android app in Develop
If you use postgresql, add the following to config/prod.exs

```
config :[your app name], [your app module name].Repo,
  username: "postgres",
  password: "postgres",
  database: "[your_app_name]_dev",
  stacktrace: true,
  show_sensitive_data_on_connection_error: true,
  pool_size: 10

if Mix.target() == :ios do
  config :[your app name], [your app module name].Repo, hostname: "127.0.0.1"
end

if Mix.target() == :android do
    config :[your app name], [your app module name].Repo, hostname: "10.0.2.2"
end
```

## Sqlite Migration at Native Device

After creating a new migration file, run the following command.

```
mix desktop.migrations.convert
```

# trouble shoot

## no ZIPFounfdation(iOS)

```
There is no XCFramework found at 'ios/Carthage/Build/ZIPFoundation.xcframework'.
```

```
cd native/ios
carthage update --platform iOS --use-xcframeworks
```

## can't run build script(iOS)

```
Sandbox: bash(39046) deny(1) file-read-data 
```

1. open xcode genereted ios project
2. select Build Settings
3. Build Options -> User Script Sandboxins -> Yes


## build script permisson denied(WSL2 Android)

```
Error running 'app'
/dev/kvm device: permission denied. Grant current user
access to /dev/kvm
```

```
sudo chown $USER /dev/kvm
```

Documentation can be generated with [ExDoc](https://github.com/elixir-lang/ex_doc)
and published on [HexDocs](https://hexdocs.pm). Once published, the docs can
be found at <https://hexdocs.pm/desktop_setup>.

