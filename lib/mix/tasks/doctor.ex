defmodule Mix.Tasks.Desktop.Doctor do
  @moduledoc """
  Diagnoses your development environment for ElixirDesktop.

  Checks that all required tools are installed and reports missing
  dependencies with installation commands.

      mix desktop.doctor
      mix desktop.doctor --os ios
      mix desktop.doctor --os android

  ## Options

    * `--os` - Check only a specific platform: `ios` or `android`.
      When omitted, all applicable platforms are checked
      (iOS is skipped on Linux).
  """
  use Mix.Task

  @shortdoc "Check development environment for ElixirDesktop"

  @erlang_version "28.3.1"
  @elixir_version "1.19.5-otp-28"

  # ── Entry Point ──────────────────────────────────────────────────

  def run(args) do
    {parsed, _, _} = OptionParser.parse(args, strict: [os: :string])
    platform = detect_platform()
    os_filter = parsed[:os]

    print_banner()

    results =
      check_common()
      |> maybe_concat(fn -> check_macos() end, platform == :macos and os_filter != "android")
      |> maybe_concat(fn -> check_ios() end, should_check_ios?(platform, os_filter))
      |> maybe_concat(fn -> check_android() end, os_filter != "ios")

    print_summary(results)
  end

  # ── Platform Detection ───────────────────────────────────────────

  defp detect_platform do
    case :os.type() do
      {:unix, :darwin} -> :macos
      {:unix, _} -> :linux
      _ -> :unknown
    end
  end

  defp should_check_ios?(platform, os_filter) do
    cond do
      os_filter == "android" -> false
      platform != :macos -> false
      true -> true
    end
  end

  # ── Output Helpers ───────────────────────────────────────────────

  defp print_banner do
    Owl.IO.puts([
      Owl.Data.tag("\nElixirDesktop Doctor", :cyan),
      "\n====================\n"
    ])
  end

  defp print_section(title) do
    Owl.IO.puts(["\n", Owl.Data.tag(title, :cyan), ":"])
  end

  defp print_ok(label, detail) do
    Owl.IO.puts([Owl.Data.tag("  \u2713", :green), "  #{label} (#{detail})"])
  end

  defp print_warn(label, message, hint) do
    Owl.IO.puts([Owl.Data.tag("  !", :yellow), "  #{label} \u2014 #{message}"])
    Owl.IO.puts([Owl.Data.tag("    \u2192 ", :yellow), hint])
  end

  defp print_fail(label, message, hint) do
    Owl.IO.puts([Owl.Data.tag("  \u2717", :red), "  #{label} \u2014 #{message}"])
    Owl.IO.puts([Owl.Data.tag("    \u2192 ", :yellow), hint])
  end

  defp print_summary(results) do
    total = length(results)
    passed = Enum.count(results, &(&1 == :ok))

    color =
      cond do
        passed == total -> :green
        passed >= total - 2 -> :yellow
        true -> :red
      end

    Owl.IO.puts([
      "\n",
      Owl.Data.tag("Summary: #{passed} of #{total} checks passed", color),
      "\n"
    ])
  end

  # ── List Helpers ─────────────────────────────────────────────────

  defp maybe_concat(acc, fun, true), do: acc ++ fun.()
  defp maybe_concat(acc, _fun, false), do: acc

  # ── Common Checks ────────────────────────────────────────────────

  defp check_common do
    print_section("Common Tools")

    [
      check_mise(),
      check_erlang(),
      check_elixir(),
      check_node(),
      check_hex(),
      check_phoenix()
    ]
  end

  defp check_mise do
    case System.find_executable("mise") do
      nil ->
        print_fail("mise", "not installed", "curl https://mise.run | sh")
        :fail

      _path ->
        version = cmd_output("mise", ["--version"]) |> String.trim() |> String.split(" ") |> hd()
        print_ok("mise", version)
        :ok
    end
  end

  defp check_erlang do
    case cmd_output("erl", ["-noshell", "-eval", "io:format(erlang:system_info(otp_release)),halt()."]) do
      {:error, _} ->
        print_fail("Erlang", "not installed", "mise install erlang@#{@erlang_version}")
        :fail

      version ->
        version = String.trim(version)

        if version == String.split(@erlang_version, ".") |> hd() do
          full = cmd_output("erl", ["-noshell", "-eval", "io:format(erlang:system_info(system_version)),halt()."])
                 |> String.trim()
                 |> extract_erlang_full_version()
          print_ok("Erlang", full || version)
          :ok
        else
          print_warn("Erlang", "OTP #{version} installed, but #{@erlang_version} is required",
            "mise install erlang@#{@erlang_version}")
          :warn
        end
    end
  end

  defp extract_erlang_full_version(system_version) do
    case Regex.run(~r/Erlang\/OTP (\d+)[^\[]*\[erts-(\S+)\]/, system_version) do
      [_, otp, erts] -> "OTP #{otp} (erts #{erts})"
      _ -> nil
    end
  end

  defp check_elixir do
    case System.find_executable("elixir") do
      nil ->
        print_fail("Elixir", "not installed", "mise install elixir@#{@elixir_version}")
        :fail

      _path ->
        output = cmd_output("elixir", ["--version"]) |> String.trim()

        version =
          output
          |> String.split("\n")
          |> Enum.find(&String.starts_with?(&1, "Elixir"))
          |> case do
            nil -> nil
            line -> line |> String.replace("Elixir ", "") |> String.trim()
          end

        if version do
          print_ok("Elixir", version)
          :ok
        else
          print_fail("Elixir", "could not detect version", "mise install elixir@#{@elixir_version}")
          :fail
        end
    end
  end

  defp check_node do
    case System.find_executable("node") do
      nil ->
        print_fail("Node.js", "not installed", "mise install node@lts")
        :fail

      _path ->
        version = cmd_output("node", ["--version"]) |> String.trim()
        print_ok("Node.js", version)
        :ok
    end
  end

  defp check_hex do
    archives = cmd_output("mix", ["archive"]) |> String.trim()

    if String.contains?(archives, "hex-") do
      version =
        archives
        |> String.split("\n")
        |> Enum.find(&String.contains?(&1, "hex-"))
        |> case do
          nil -> nil
          line -> line |> String.trim() |> String.replace("* hex-", "")
        end

      print_ok("Hex", version)
      :ok
    else
      print_fail("Hex", "not installed", "mix local.hex --force")
      :fail
    end
  end

  defp check_phoenix do
    archives = cmd_output("mix", ["archive"]) |> String.trim()

    if String.contains?(archives, "phx_new-") do
      version =
        archives
        |> String.split("\n")
        |> Enum.find(&String.contains?(&1, "phx_new-"))
        |> case do
          nil -> nil
          line -> line |> String.trim() |> String.replace("* phx_new-", "")
        end

      print_ok("Phoenix (phx_new)", version)
      :ok
    else
      print_fail("Phoenix (phx_new)", "not installed", "mix archive.install hex phx_new")
      :fail
    end
  end

  # ── macOS Checks ─────────────────────────────────────────────────

  defp check_macos do
    print_section("macOS Tools")

    [
      check_homebrew(),
      check_wxwidgets(),
      check_openssl()
    ]
  end

  defp check_homebrew do
    case System.find_executable("brew") do
      nil ->
        print_fail("Homebrew", "not installed",
          ~s|/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"|)
        :fail

      _path ->
        version = cmd_output("brew", ["--version"]) |> String.trim() |> String.split("\n") |> hd()
        print_ok("Homebrew", version)
        :ok
    end
  end

  defp check_wxwidgets do
    brew_prefix = get_brew_prefix()

    cond do
      brew_prefix == nil ->
        print_fail("wxwidgets@3.2", "Homebrew not available", "brew install wxwidgets@3.2")
        :fail

      File.exists?(Path.join(brew_prefix, "opt/wxwidgets@3.2")) ->
        version = cmd_output("brew", ["list", "--versions", "wxwidgets@3.2"]) |> String.trim()
        v = version |> String.replace("wxwidgets@3.2 ", "")
        print_ok("wxwidgets@3.2", v)
        :ok

      true ->
        # Check if a different wxwidgets version is installed
        other = cmd_output("brew", ["list", "--versions", "wxwidgets"]) |> String.trim()

        if other != "" do
          print_warn("wxwidgets@3.2", "#{other} installed but @3.2 is required",
            "brew install wxwidgets@3.2")
          :warn
        else
          print_fail("wxwidgets@3.2", "not installed", "brew install wxwidgets@3.2")
          :fail
        end
    end
  end

  defp check_openssl do
    brew_prefix = get_brew_prefix()

    cond do
      brew_prefix == nil ->
        print_fail("openssl@3", "Homebrew not available", "brew install openssl@3")
        :fail

      File.exists?(Path.join(brew_prefix, "opt/openssl@3")) ->
        version = cmd_output("brew", ["list", "--versions", "openssl@3"]) |> String.trim()
        v = version |> String.replace("openssl@3 ", "")
        print_ok("openssl@3", v)
        :ok

      true ->
        print_fail("openssl@3", "not installed", "brew install openssl@3")
        :fail
    end
  end

  # ── iOS Checks ───────────────────────────────────────────────────

  defp check_ios do
    print_section("iOS Tools")

    [
      check_xcode(),
      check_xcodegen(),
      check_carthage()
    ]
  end

  defp check_xcode do
    case System.cmd("xcode-select", ["-p"], stderr_to_stdout: true) do
      {path, 0} ->
        # Try to get Xcode version
        case System.cmd("xcodebuild", ["-version"], stderr_to_stdout: true) do
          {output, 0} ->
            version = output |> String.trim() |> String.split("\n") |> hd()
            print_ok("Xcode", version)
            :ok

          _ ->
            print_ok("Xcode CLT", String.trim(path))
            :ok
        end

      _ ->
        print_fail("Xcode", "not installed",
          "Install Xcode from the App Store, then run: xcode-select --install")
        :fail
    end
  end

  defp check_xcodegen do
    case System.find_executable("xcodegen") do
      nil ->
        print_fail("XcodeGen", "not installed", "brew install xcodegen")
        :fail

      _path ->
        version = cmd_output("xcodegen", ["--version"]) |> String.trim()
        print_ok("XcodeGen", version)
        :ok
    end
  end

  defp check_carthage do
    case System.find_executable("carthage") do
      nil ->
        print_fail("Carthage", "not installed", "brew install carthage")
        :fail

      _path ->
        version = cmd_output("carthage", ["version"]) |> String.trim()
        print_ok("Carthage", version)
        :ok
    end
  end

  # ── Android Checks ───────────────────────────────────────────────

  defp check_android do
    print_section("Android Tools")

    [
      check_jdk(),
      check_android_sdk(),
      check_android_ndk(),
      check_android_cmake()
    ]
  end

  defp check_jdk do
    case System.find_executable("java") do
      nil ->
        hint = case detect_platform() do
          :macos -> "brew install openjdk@17"
          _ -> "sudo apt install openjdk-17-jdk  # or equivalent for your distro"
        end

        print_fail("JDK 17", "not installed", hint)
        :fail

      _path ->
        output = cmd_output("java", ["-version"]) |> String.trim()

        # java -version outputs to stderr, but cmd_output captures it via stderr_to_stdout
        major_version =
          case Regex.run(~r/version "(\d+)/, output) do
            [_, ver] -> String.to_integer(ver)
            _ -> nil
          end

        cond do
          major_version == nil ->
            print_warn("JDK", "installed but could not detect version", "Ensure JDK 17+ is installed")
            :warn

          major_version >= 17 ->
            version_line = output |> String.split("\n") |> hd() |> String.trim()
            print_ok("JDK", version_line)
            :ok

          true ->
            hint = case detect_platform() do
              :macos -> "brew install openjdk@17"
              _ -> "sudo apt install openjdk-17-jdk"
            end

            print_warn("JDK", "version #{major_version} found, but 17+ is required", hint)
            :warn
        end
    end
  end

  defp check_android_sdk do
    sdk_path = find_android_sdk()

    case sdk_path do
      nil ->
        print_fail("Android SDK", "not found",
          "Install Android Studio: https://developer.android.com/studio")
        :fail

      path ->
        print_ok("Android SDK", path)
        :ok
    end
  end

  defp check_android_ndk do
    sdk_path = find_android_sdk()

    case sdk_path do
      nil ->
        print_fail("Android NDK", "Android SDK not found",
          "Install Android Studio first, then: SDK Manager -> SDK Tools -> NDK")
        :fail

      path ->
        ndk_dir = Path.join(path, "ndk")

        if File.exists?(ndk_dir) and File.ls!(ndk_dir) != [] do
          versions = File.ls!(ndk_dir) |> Enum.sort() |> List.last()
          print_ok("Android NDK", versions)
          :ok
        else
          print_fail("Android NDK", "not installed",
            "Android Studio -> SDK Manager -> SDK Tools -> NDK (Side by side)")
          :fail
        end
    end
  end

  defp check_android_cmake do
    sdk_path = find_android_sdk()

    case sdk_path do
      nil ->
        print_fail("CMake", "Android SDK not found",
          "Install Android Studio first, then: SDK Manager -> SDK Tools -> CMake")
        :fail

      path ->
        cmake_dir = Path.join(path, "cmake")

        cond do
          File.exists?(cmake_dir) and File.ls!(cmake_dir) != [] ->
            versions = File.ls!(cmake_dir) |> Enum.sort() |> List.last()
            print_ok("CMake (Android SDK)", versions)
            :ok

          System.find_executable("cmake") != nil ->
            version = cmd_output("cmake", ["--version"]) |> String.trim() |> String.split("\n") |> hd()
            print_ok("CMake (system)", version)
            :ok

          true ->
            print_fail("CMake", "not installed",
              "Android Studio -> SDK Manager -> SDK Tools -> CMake")
            :fail
        end
    end
  end

  # ── Utility Functions ────────────────────────────────────────────

  defp find_android_sdk do
    candidates =
      [
        System.get_env("ANDROID_HOME"),
        System.get_env("ANDROID_SDK_ROOT"),
        Path.expand("~/Library/Android/sdk"),
        Path.expand("~/Android/Sdk")
      ]
      |> Enum.reject(&is_nil/1)

    Enum.find(candidates, &File.exists?/1)
  end

  defp get_brew_prefix do
    case System.find_executable("brew") do
      nil -> nil
      _path ->
        cmd_output("brew", ["--prefix"]) |> String.trim()
    end
  end

  defp cmd_output(cmd, args) do
    case System.find_executable(cmd) do
      nil ->
        {:error, :not_found}

      exe ->
        case System.cmd(exe, args, stderr_to_stdout: true) do
          {output, 0} -> output
          {output, _} -> output
        end
    end
  end
end
