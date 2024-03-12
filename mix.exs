defmodule DesktopSetup.MixProject do
  use Mix.Project

  @version "0.2.0"
  @source_url "https://github.com/thehaigo/desktop_setup"

  def project do
    [
      app: :desktop_setup,
      version: @version,
      description: "Setup Library for Multiplatform Dev kit ElixirDesktop",
      elixir: "~> 1.15",
      package: package(),
      elixirc_paths: elixirc_paths(Mix.env()),
      compilers: Mix.compilers(),
      start_permanent: Mix.env() == :prod,
      deps: deps()
    ]
  end

  defp elixirc_paths(_), do: ["lib"]

  # Run "mix help compile.app" to learn about applications.
  def application do
    [
      extra_applications: [:logger]
    ]
  end

  # Run "mix help deps" to learn about dependencies.
  defp deps do
    [
      {:owl, "~> 0.8", runtime: false}
    ]
  end

  defp package do
    %{
      maintainers: ["thehaigo"],
      licenses: ["MIT"],
      links: %{
        "GitHub" => @source_url
      },
      source_url: @source_url
    }
  end
end
