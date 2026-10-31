defmodule AutumnCompiler do
  @moduledoc """
  Temporary Elixir-hosted lowerer: `.ex` subset → Autumn IR JSON.
  """

  alias AutumnCompiler.Lower

  @doc """
  Compile an Elixir source file to Autumn bytecode JSON.

  The file may contain one `defmodule` or a block of several.

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
  Compile multiple Elixir source files into one IR image (IR v12 `modules[]`
  when more than one `defmodule` is present).
  """
  def compile_files(paths) when is_list(paths) and paths != [] do
    Enum.reduce_while(paths, {:ok, []}, fn path, {:ok, acc} ->
      with {:ok, source} <- File.read(path),
           {:ok, quoted} <- parse(source, path),
           {:ok, cms} <- Lower.lower_modules(quoted) do
        {:cont, {:ok, acc ++ cms}}
      else
        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, cms} -> Lower.assemble(cms)
      {:error, _} = err -> err
    end
  end

  @doc """
  Compile and write JSON to `out_path`.
  """
  def compile_file!(path, out_path) do
    case compile_file(path) do
      {:ok, module} ->
        write_json!(module, out_path)
        :ok

      {:error, msg} ->
        raise ArgumentError, msg
    end
  end

  @doc """
  Compile several files and write one IR JSON image.
  """
  def compile_files!(paths, out_path) when is_list(paths) do
    case compile_files(paths) do
      {:ok, module} ->
        write_json!(module, out_path)
        :ok

      {:error, msg} ->
        raise ArgumentError, msg
    end
  end

  defp write_json!(module, out_path) do
    json = Jason.encode!(module, pretty: true)
    File.write!(out_path, json <> "\n")
  end

  defp parse(source, path) do
    case Code.string_to_quoted(source, file: path, columns: true) do
      {:ok, quoted} ->
        {:ok, quoted}

      {:error, {meta, message, token}} ->
        line = meta[:line] || meta
        {:error, "parse error at line #{inspect(line)}: #{message}#{token}"}
    end
  end
end
