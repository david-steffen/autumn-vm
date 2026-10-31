defmodule Mix.Tasks.Autumn.Compile do
  @shortdoc "Lower an Elixir subset file to Autumn IR JSON"
  @moduledoc """
  ## Usage

      mix autumn.compile path/to/file.ex [output.bc.json]
  """

  use Mix.Task

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("app.start")

    {path, out} =
      case args do
        [path] -> {path, Path.rootname(path) <> ".bc.json"}
        [path, out] -> {path, out}
        _ ->
          Mix.raise("usage: mix autumn.compile <file.ex> [output.bc.json]")
      end

    case AutumnCompiler.compile_file(path) do
      {:ok, module} ->
        json = Jason.encode!(module, pretty: true)
        File.write!(out, json <> "\n")
        Mix.shell().info("Wrote #{out}")

      {:error, msg} ->
        Mix.raise(msg)
    end
  end
end
