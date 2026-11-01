defmodule Mix.Tasks.Autumn.Compile do
  @shortdoc "Lower Elixir subset file(s) to Autumn IR JSON"
  @moduledoc """
  ## Usage

      mix autumn.compile path/to/file.ex [output.bc.json]
      mix autumn.compile a.ex b.ex [output.bc.json]

  Multiple `.ex` inputs are assembled into one image (`modules[]`
  when more than one `defmodule` is present).
  """

  use Mix.Task

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("app.start")

    {paths, out} = parse_args(args)

    result =
      case paths do
        [one] -> AutumnCompiler.compile_file(one)
        many -> AutumnCompiler.compile_files(many)
      end

    case result do
      {:ok, module} ->
        json = Jason.encode!(module, pretty: true)
        File.write!(out, json <> "\n")
        Mix.shell().info("Wrote #{out}")

      {:error, msg} ->
        Mix.raise(msg)
    end
  end

  defp parse_args(args) do
    case args do
      [] ->
        Mix.raise("usage: mix autumn.compile <file.ex>... [output.bc.json]")

      [path] ->
        {[path], Path.rootname(path) <> ".bc.json"}

      many ->
        {last, rest} = List.pop_at(many, -1)

        cond do
          String.ends_with?(last, ".json") ->
            if rest == [], do: Mix.raise("usage: mix autumn.compile <file.ex>... [output.bc.json]")
            {rest, last}

          true ->
            # All inputs are sources; default out from first path.
            {many, Path.rootname(hd(many)) <> ".bc.json"}
        end
    end
  end
end
