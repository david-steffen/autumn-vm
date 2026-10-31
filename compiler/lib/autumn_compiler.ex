defmodule AutumnCompiler do
  @moduledoc """
  Temporary Elixir-hosted lowerer: `.ex` subset → Autumn IR v1 JSON.
  """

  alias AutumnCompiler.Lower

  @doc """
  Compile an Elixir source file to Autumn bytecode JSON.

  Returns `{:ok, json_map}` or `{:error, message}`.
  """
  def compile_file(path) when is_binary(path) do
    with {:ok, source} <- File.read(path),
         {:ok, quoted} <- parse(source, path),
         {:ok, module} <- Lower.lower(quoted) do
      {:ok, module}
    end
  end

  @doc """
  Compile and write JSON to `out_path`.
  """
  def compile_file!(path, out_path) do
    case compile_file(path) do
      {:ok, module} ->
        json = Jason.encode!(module, pretty: true)
        File.write!(out_path, json <> "\n")
        :ok

      {:error, msg} ->
        raise ArgumentError, msg
    end
  end

  defp parse(source, path) do
    case Code.string_to_quoted(source, file: path, columns: true) do
      {:ok, quoted} -> {:ok, quoted}
      {:error, {meta, message, token}} ->
        line = meta[:line] || meta
        {:error, "parse error at line #{inspect(line)}: #{message}#{token}"}
    end
  end
end
