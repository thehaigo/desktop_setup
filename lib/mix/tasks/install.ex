defmodule Mix.Tasks.Desktop.Install do
  @moduledoc "Installer Mix task for Elixir Desktop: `mix desktop.install`"
  use Mix.Task

  @shortdoc "Setup ElixrDesktop app"
  def run(args) do
    {parsed_args, _, _} =
      OptionParser.parse(args, strict: [namespace: :string, os: :string, database: :string])

    # Get all Mix tasks for Elixir Desktop client project
    valid_mix_tasks = get_installer_mix_tasks()
    host_project_config = get_host_project_config(parsed_args)
    run_all_install_tasks(valid_mix_tasks, host_project_config)

    # IO.inspect(host_project_config)
    update_config_exs_if_needed(host_project_config)
    update_endpoint_ex_if_needed(host_project_config)
    update_application_ex_if_needed(host_project_config)
    update_mix_exs_application_if_needed(host_project_config)
    update_mix_exs_deps_if_needed(host_project_config)
    rename_runtime_exs_if_needed(host_project_config)
    clean_build_path(host_project_config)
    format_config_files()

    IO.puts("\nYour Phoenix app is ready to use ElixirDesktop!\n")
    IO.puts("\nStart your Desktop app with: \n \n $ iex -S mix\n")
    # IO.puts("Platform-specific project files have been placed in the \"native\" directory\n")
    :ok
  end

  defp run_all_install_tasks(mix_tasks, host_project_config) do
    mix_tasks
    |> Enum.map(&prompt_task_settings/1)
    |> Enum.map(&run_install_task(&1, host_project_config))
  end

  defp prompt_task_settings(%{client_name: client_name, prompts: [_ | _] = prompts} = task) do
    prompts
    |> Enum.reduce_while({:ok, task}, fn {prompt_key, prompt_settings}, {:ok, acc} ->
      case prompt_task_setting(prompt_settings, client_name) do
        {:error, message} ->
          Owl.IO.puts([Owl.Data.tag("#{client_name}: #{message}", :yellow)])

          {:halt, {:error, acc}}

        result ->
          settings = Map.get(acc, :settings, %{})
          updated_settings = Map.put(settings, prompt_key, result)

          {:cont, {:ok, Map.put(acc, :settings, updated_settings)}}
      end
    end)
  end

  defp prompt_task_setting(%{ignore: true}, _client_name), do: true

  defp prompt_task_setting(%{type: :confirm, label: label} = task, client_name) do
    if Owl.IO.confirm(message: "#{client_name}: #{label}", default: true) do
      if is_function(task[:on_yes]), do: apply(task[:on_yes], [])
    else
      if is_function(task[:on_no]), do: apply(task[:on_no], [])
    end
  end

  defp prompt_task_setting(
         %{type: :multiselect, label: label, options: options, default: default} = task,
         client_name
       ) do
    default_label = Map.get(task, :default_label, inspect(default))

    case Owl.IO.multiselect(options,
           label:
             "#{client_name}: #{label} (Space-delimited, leave blank for default: #{default_label})"
         ) do
      [] ->
        default || []

      result ->
        result
    end
  end

  defp prompt_task_setting(_task, _client_name), do: nil

  defp run_install_task(result, host_project_config) do
    case result do
      {:ok, %{client_name: client_name, mix_task: mix_task, settings: settings}} ->
        Owl.IO.puts([Owl.Data.tag("* generating ", :green), "#{client_name} project files"])

        mix_task.run(["--host-project-config", host_project_config, "--task-settings", settings])

      _ ->
        :skipped
    end
  end

  defp get_installer_mix_tasks do
    Mix.Task.load_all()
    |> Enum.filter(&function_exported?(&1, :desktop_install_config, 0))
    |> Enum.map(fn module ->
      module
      |> apply(:desktop_install_config, [])
      |> Map.put(:mix_task, module)
    end)
  end

  defp get_host_project_config(parsed_args) do
    # Define some paths for the host project
    current_path = File.cwd!()
    mix_config_path = Path.join(current_path, "mix.exs")
    build_path = Path.join(current_path, "_build")
    namespace = parsed_args[:namespace] || infer_app_namespace(mix_config_path)
    app_name = Macro.underscore(namespace)

    %{
      app_name: app_name,
      app_config_path: Path.join(current_path, "config/config.exs"),
      runtime_path: Path.join(current_path, "config/runtime.exs"),
      application_path: Path.join(current_path, "lib/#{app_name}.ex"),
      endpoint_path: Path.join(current_path, "lib/#{app_name}_web/endpoint.ex"),
      app_namespace: namespace,
      build_path: build_path,
      current_path: current_path,
      native_path: Path.join(current_path, "native"),
      libs_path: Path.join(build_path, "dev/lib"),
      mix_config_path: mix_config_path
    }
  end

  def infer_app_namespace(config_path) do
    with {:ok, config} <- File.read(config_path),
         {:ok, mix_project_ast} <- Code.string_to_quoted(config),
         {:ok, namespace} <- find_mix_project_namespace(mix_project_ast) do
      "#{namespace}"
    else
      _ ->
        raise "Could not infer Mix project namespace from mix.exs. Please provide it manually using the --namespace argument."
    end
  end

  defp find_mix_project_namespace(ast) do
    case ast do
      ast when is_list(ast) ->
        ast
        |> Enum.reduce_while({:error, :cannot_infer_app_name}, fn node, _acc ->
          {status, result} = find_mix_project_namespace(node)
          acc_op = if status == :ok, do: :halt, else: :cont

          {acc_op, {status, result}}
        end)

      {:defmodule, _, [{:__aliases__, _, [namespace, :MixProject]} | _rest]} ->
        {:ok, namespace}

      {:__block__, _, contents} ->
        find_mix_project_namespace(contents)

      _ ->
        {:error, :cannot_infer_app_name}
    end
  end

  defp update_config_exs_if_needed(%{app_config_path: path}) do
    # Update project's config.exs to modified for desktop if needed.
    replace_string = "http: [ip: {127, 0, 0, 1}, port: 10_000 + :rand.uniform(45_000)],"
    full_replace_string = Enum.join(
      [replace_string, "\n", " server: true,", "\n", "secret_key_base: :crypto.strong_rand_bytes(32),", "\n"])
    {:ok, app_config_body} = File.read(path)

    if String.contains?(app_config_body, replace_string) do
      IO.puts("config.exs already modified, skipping...")
    else
      Owl.IO.puts([Owl.Data.tag("* updating ", :yellow), "config/config.exs"])

      {:ok, app_config} = File.open(path, [:write])

      updated_app_config_body =
        String.replace(app_config_body, "url: [host: \"localhost\"],", full_replace_string)

      IO.binwrite(app_config, updated_app_config_body)
      File.close(app_config)
    end
  end

  defp update_endpoint_ex_if_needed(%{endpoint_path: path, app_name: app_name}) do
    replace_string = "store: :ets"

    full_replace_string =
      "@session_options [\n store: :ets,\n key: \"_#{app_name}_key\",\n table: :session\n ]"

    {:ok, config_body} = File.read(path)

    if String.contains?(config_body, replace_string) do
      IO.puts("endpoint.ex already modified, skipping...")
    else
      Owl.IO.puts([Owl.Data.tag("* updating ", :yellow), "endpoint.ex"])

      {:ok, app_config} = File.open(path, [:write])

      updated_config_body =
        config_body
        |> String.replace(~r/@session_options \[[\s\S]*?\]/, full_replace_string)

      IO.binwrite(app_config, updated_config_body)
      File.close(app_config)
    end
  end

  defp update_mix_exs_application_if_needed(%{mix_config_path: path, app_namespace: app_namespace}) do
    replace_string = "mod: {#{app_namespace}, []},"

    {:ok, config_body} = File.read(path)

    if String.contains?(config_body, replace_string) do
      IO.puts("mix.exs application already modified, skipping...")
    else
      Owl.IO.puts([Owl.Data.tag("* updating ", :yellow), "mix.exs"])

      {:ok, app_config} = File.open(path, [:write])

      updated_config_body =
        config_body
        |> String.replace(~r/#{app_namespace}.Application/, app_namespace)

      IO.binwrite(app_config, updated_config_body)
      File.close(app_config)
    end
  end

  defp update_mix_exs_deps_if_needed(%{mix_config_path: path}) do
    replace_string = "{:desktop, \"~> 1.5\"}"

    {:ok, config_body} = File.read(path)

    if String.contains?(config_body, replace_string) do
      IO.puts("mix.exs deps already modified, skipping...")
    else
      Owl.IO.puts([Owl.Data.tag("* updating ", :yellow), "mix.exs"])

      {:ok, app_config} = File.open(path, [:write])

      updated_config_body =
        config_body
        |> String.replace(
          ~r/defp deps do\n    \[\n/,
          "defp deps do\n    \[\n       {:desktop, \"~> 1.5\"}, \n{:wx, \"~> 1.1\", hex: :bridge, targets: [:android, :ios]},\n"
        )

      IO.binwrite(app_config, updated_config_body)
      File.close(app_config)
      System.cmd("mix", ["deps.get"])
    end
  end

  defp update_application_ex_if_needed(%{
         application_path: path,
         app_name: app_name,
         app_namespace: app_namespace,
         app_config_path: config_path
       }) do
    replace_string = "Desktop.OS.home()"

    {:ok, config_body} = File.read(path)

    if String.contains?(config_body, replace_string) do
      IO.puts("#{app_name}.ex already modified, skipping...")
    else
      Owl.IO.puts([Owl.Data.tag("* updating ", :yellow), "#{app_name}.ex"])

      {:ok, app_config} = File.open(path, [:write])

      updated_config_body = application_body(app_name, app_namespace, config_path)

      IO.binwrite(app_config, updated_config_body)
      File.close(app_config)
    end
  end

  defp application_body(app_name, app_namespace, config_path) do
    adapter = adapter_setting(app_namespace, config_path)
    repo = repo_setting(app_name, app_namespace)

    """
    defmodule #{app_namespace} do
      use Application

      def config_dir() do
        Path.join([Desktop.OS.home(), ".config", "#{app_name}"])
      end

      @app Mix.Project.config()[:app]
      def start(:normal, []) do
        File.mkdir_p!(config_dir())

        :session = :ets.new(:session, [:named_table, :public, read_concurrency: true])

        children = [
          #{repo}
          {Phoenix.PubSub, name: #{app_namespace}.PubSub},
          #{app_namespace}Web.Endpoint
        ]

        opts = [strategy: :one_for_one, name: #{app_namespace}.Supervisor]
        {:ok, sup} = Supervisor.start_link(children, opts)

        #{adapter}

        {:ok, _} =
          Supervisor.start_child(sup, {
            Desktop.Window,
            [
              app: @app,
              id: #{app_namespace}Window,
              title: "#{app_name}",
              size: {400, 800},
              url: "http://localhost:\#{port}"
            ]
          })
      end

      def config_change(changed, _new, removed) do
        #{app_namespace}Web.Endpoint.config_change(changed, removed)
        :ok
      end
    end
    """
  end

  defp repo_setting(app_name, app_namespace) do
    current_path = File.cwd!()

    if File.exists?(Path.join([current_path, "lib", app_name, "repo.ex"])) do
      "#{app_namespace}.Repo,"
    else
      ""
    end
  end

  defp adapter_setting(app_namespace, config_path) do
    {:ok, config_body} = File.read(config_path)

    if String.contains?(config_body, "Phoenix.Endpoint.Cowboy2Adapter") do
      "port = :ranch.get_port(#{app_namespace}Web.Endpoint.HTTP)"
    else
      "{:ok, {_ip, port}} = Bandit.PhoenixAdapter.server_info(#{app_namespace}Web.Endpoint, :http)"
    end
  end

  def rename_runtime_exs_if_needed(%{runtime_path: path}) do
    if File.exists?(path) do
      Owl.IO.puts([Owl.Data.tag("* renaming ", :yellow), "runtime.exs"])
      current_path = File.cwd!()
      File.rename(path, "#{current_path}/config/disabled_runtime.exs")
    else
      IO.puts("rumtime.exs already renamed, skipping...")
    end
  end

  defp format_config_files do
    System.cmd("mix", ["format"])
  end

  def clean_build_path(%{build_path: build_path}) do
    # Clear _build path to ensure it's rebuilt with new Config
    File.rm_rf(build_path)
  end
end
