defmodule Util do
  def get_host_project_config(parsed_args) do
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
end
