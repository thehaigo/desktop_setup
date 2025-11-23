defmodule Mix.Tasks.Desktop.Migrations.Convert do
  use Mix.Task

  @shortdoc "Convert priv/repo/migrations/*.exs to lib/<app>/migrations/*.ex (skip if exists)"

  @migrations_priv "priv/repo/migrations"

  def run(_args) do
    %{
      app_name: app_name
    } = Util.get_host_project_config([])

    migrations_lib = "lib/#{app_name}/migrations"

    Mix.shell().info("Converting migrations for #{app_name}...")

    File.mkdir_p!(migrations_lib)

    @migrations_priv
    |> Path.join("*.exs")
    |> Path.wildcard()
    |> Enum.each(&convert/1)

    System.cmd("mix", ["format", "lib/#{app_name}/migrations/*"])
    Mix.shell().info("Done!")
  end

  # -----------------------------
  # Convert a single migration file
  # -----------------------------
  defp convert(path) do
    %{
      app_name: app_name,
      app_namespace: app_namespace
    } = Util.get_host_project_config([])

    filename = Path.basename(path, ".exs")
    # Example: 20230729012345_create_books
    [version_str | name_parts] = String.split(filename, "_")
    module_suffix = name_parts |> Enum.map(&Macro.camelize/1) |> Enum.join()
    version = String.to_integer(version_str)
    migrations_lib = "lib/#{app_name}/migrations"
    base_name = Enum.join(name_parts, "_")
    out_path = Path.join(migrations_lib, "#{base_name}.ex")

    module_name = "#{app_namespace}.Migrations.#{module_suffix}"

    # ----------- SKIP if exists -----------
    case File.exists?(out_path) do
      true ->
        Mix.shell().info("  • Skip (already exists): #{out_path}")

      false ->
        Mix.shell().info("  • #{filename}.exs → #{module_name}")

        {:ok, original} = File.read(path)
        change_block = extract_change_block(original)

        output = migration_module_template(module_name, version, change_block)

        File.write!(out_path, output)
    end
  end

  # -----------------------------
  # Extract change block
  # -----------------------------
  defp extract_change_block(src) do
    case Regex.run(~r/def change do(.+?)end/s, src, capture: :all_but_first) do
      [block] -> String.trim(block)
      _ -> raise "Could not extract change block:\n\n#{src}"
    end
  end

  # -----------------------------
  # Generate module
  # -----------------------------
  defp migration_module_template(module_name, version, change_block) do
    """
    defmodule #{module_name} do
      use Ecto.Migration

      @version #{version}
      def version, do: @version

      def change do
    #{indent(change_block, 2)}
      end
    end
    end
    """
  end

  defp indent(text, depth) do
    padding = String.duplicate("  ", depth)

    text
    |> String.split("\n")
    |> Enum.map(&"#{padding}#{&1}")
    |> Enum.join("\n")
  end
end
