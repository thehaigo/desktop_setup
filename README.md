# DesktopSetup

Setup Library for Multiplatform Dev kit ElixirDesktop
https://github.com/elixir-desktop/desktop



## Requirements
Using Erlang version 26.2 for iOS and Android
Therefore, the build environment must be the same

```
asdf install erlang 26.2
asdf install elixir 1.16.0-otp-26
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
 

## iOS build
```
cd native/ios
open [your app name].xcodeproj
```
build from Xcode 

if happen build error
try `./run_mix` at console


## Roadmap

- [x] Dektop app setup
- [x] iOS App setup
- [ ] Android App setup


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



Documentation can be generated with [ExDoc](https://github.com/elixir-lang/ex_doc)
and published on [HexDocs](https://hexdocs.pm). Once published, the docs can
be found at <https://hexdocs.pm/desktop_setup>.

