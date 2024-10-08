defmodule Mix.Tasks.Desktop.Setup.Android do
  @moduledoc "Installer Mix task for ElixirDesktop: `mix desktop.setup.android`"
  use Mix.Task

  @requirements ["app.config"]

  @shortdoc "Setup ElixirDesktop for Android."
  def run(args) do
    {parsed_args, _, _} =
      OptionParser.parse(args, strict: [host_project_config: :string, task_settings: :string])

    host_project_config = Util.get_host_project_config(parsed_args)
    Owl.IO.puts([Owl.Data.tag("* generating ", :green), "Android project files"])

    if !File.exists?(host_project_config.native_path <> "/android") do
      make_native_project_dir(host_project_config)
      copy_android_files(host_project_config)
      prepare_source_files(host_project_config)
      rename_sources_directory(host_project_config)
    else
      IO.puts("Android Project already created, skipping...")
    end

    :ok
  end

  defp make_native_project_dir(%{native_path: native_path}) do
    native_path
    |> Path.join("android")
    |> File.mkdir_p()
  end

  defp copy_android_files(%{native_path: native_path}) do
    priv_dir = :code.priv_dir(:desktop_setup)
    native_project_dir = Path.join(native_path, "android")
    android_sample_path = Path.join(priv_dir, "android_sample")

    File.cp_r(android_sample_path, native_project_dir)
  end

  defp prepare_source_files(%{native_path: native_path} = host_project_config) do
    sources_path = Path.join(native_path, "android/")

    [
      "app/src/androidTest/java/com/example/template_app",
      "app/src/androidTest/java/com/example/template_app/ExampleInstrumentedTest.kt",
      "app/src/main/cpp/CMakeLists.txt",
      "app/src/main/cpp/native-lib.cpp",
      "app/src/main/java/com/example/template_app",
      "app/src/main/java/com/example/template_app/Bridge.kt",
      "app/src/main/java/com/example/template_app/MainActivity.kt",
      "app/src/main/res/values/strings.xml",
      "app/src/main/res/values/themes.xml",
      "app/src/main/res/values-night/themes.xml",
      "app/src/main/AndroidManifest.xml",
      "app/src/test/java/com/example/template_app",
      "app/src/test/java/com/example/template_app/ExampleUnitTest.kt",
      "app/build.gradle",
      "settings.gradle"
    ]
    |> Enum.map(&Path.join(sources_path, &1))
    |> Enum.filter(&(not File.dir?(&1)))
    |> Enum.concat([Path.join(sources_path, "app/run_mix")])
    |> Enum.map(&prepare_source_file(&1, host_project_config))
  end

  defp prepare_source_file(source_file, %{} = task_settings) do
    replace_name =
      if Path.basename(source_file) == "run_mix" do
        task_settings.app_name
      else
        String.replace(task_settings.app_name, "_", "")
      end

    body =
      source_file
      |> File.read!()
      |> String.replace("TemplateApp", task_settings.app_namespace)
      |> String.replace("template_app", replace_name)

    File.write!(source_file, body)
  end

  defp rename_sources_directory(%{app_name: app_name, native_path: native_path}) do
    source_path = Path.join(native_path, "android")

    [
      "app/src/androidTest/java/com/example/template_app",
      "app/src/main/java/com/example/template_app",
      "app/src/test/java/com/example/template_app"
    ]
    |> Enum.map(&Path.join(source_path, &1))
    |> Enum.map(&rename_sources_directory(&1, String.replace(app_name, "_", "")))
  end

  defp rename_sources_directory(source_path, namespace) do
    basename = Path.basename(source_path)
    dirname = Path.dirname(source_path)

    new_sources_path =
      Path.join(dirname, String.replace(basename, "template_app", namespace))

    File.rename(source_path, new_sources_path)
  end
end
