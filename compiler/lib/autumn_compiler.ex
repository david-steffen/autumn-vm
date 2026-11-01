defmodule AutumnCompiler do
  @moduledoc """
  Temporary Elixir-hosted lowerer: `.ex` subset → Autumn IR JSON.
  """

  alias AutumnCompiler.Lower

  @doc """
  Absolute path to the Lean `autumn` executable.

  Override with `AUTUMN_VM`, otherwise `<repo>/vm/.lake/build/bin/autumn`.
  """
  def vm_bin do
    case System.get_env("AUTUMN_VM") do
      bin when is_binary(bin) and bin != "" ->
        bin

      _ ->
        repo = Path.expand("../..", __DIR__)
        Path.join(repo, "vm/.lake/build/bin/autumn")
    end
  end

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
  Lower a single expression as `Repl.main/0` for the durable REPL.

  Uses module name `Repl` (not `Main`) so `.load` of a `Main` module is not
  clobbered on each eval.

  `bindings` is an ordered list of `{var_atom, rhs_ast}` replayed before `source`
  so prior `x = …` lines stay in scope (Lean still resets the process each EVAL).

  Returns `{:ok, json_map, expr_ast}` or `{:error, message}`.
  """
  def eval_expr(source, bindings \\ []) when is_binary(source) and is_list(bindings) do
    with {:ok, expr} <- parse(source, "eval"),
         {:ok, module} <- Lower.lower(wrap_repl(expr, bindings)) do
      {:ok, module, expr}
    end
  end

  @doc """
  Extend `bindings` when `expr` is a simple `var = rhs` assignment.
  """
  def binding_after(bindings, {:=, _, [{name, _, nil}, rhs]})
      when is_list(bindings) and is_atom(name) and name != :_ do
    bindings ++ [{name, rhs}]
  end

  def binding_after(bindings, _expr) when is_list(bindings), do: bindings

  defp wrap_repl(expr, bindings) do
    body =
      case bindings do
        [] ->
          expr

        _ ->
          stmts =
            Enum.map(bindings, fn {name, rhs} ->
              {:=, [], [{name, [], nil}, rhs]}
            end)

          {:__block__, [], stmts ++ [expr]}
      end

    {:defmodule, [],
     [
       {:__aliases__, [alias: false], [:Repl]},
       [do: {:def, [], [{:main, [], nil}, [do: body]]}]
     ]}
  end

  @doc """
  Compile multiple Elixir source files into one IR image (`modules[]`
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
