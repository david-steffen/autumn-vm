defmodule Mix.Tasks.Autumn.Smoke do
  @shortdoc "Compile fixtures fresh and run them on the Lean autumn VM"
  @moduledoc """
  ## Usage

      mix autumn.smoke

  Discovers `tests/fixtures/*.expect` next to a matching `.ex`, compiles each
  fixture to a tempfile (no committed `.bc.json`), runs
  `AUTUMN_VM` / `vm/.lake/build/bin/autumn`, and compares trimmed stdout.

  Optional `tests/fixtures/<stem>.smoke.json`:
  `{"extras": ["stdlib/genserver.ex", …]}` (paths relative to repo root).

  Before running, recompiles `hot_load/math_v{1,2}.ex` into gitignored
  `hot_load/math_v{1,2}.bc.json` so `hot_load.ex` `Code.load_file` paths work.

  Expects cwd `compiler/` so relative hot_load paths resolve.
  Override the VM binary with `AUTUMN_VM=/path/to/autumn`.
  """

  use Mix.Task

  # lib/mix/tasks → repo root
  @repo Path.expand("../../../../", __DIR__)
  @fixtures Path.join(@repo, "tests/fixtures")

  @impl Mix.Task
  def run(_args) do
    Mix.Task.run("app.start")

    bin = AutumnCompiler.vm_bin()

    unless File.exists?(bin) do
      Mix.raise("""
      autumn VM not found at #{bin}
      Build it with: (cd ../vm && lake build)
      Or set AUTUMN_VM to the autumn executable.
      """)
    end

    case prep_hot_load() do
      :ok -> :ok
      {:error, msg} -> Mix.raise("hot_load prep: #{msg}")
    end

    cases = discover_cases()

    if cases == [] do
      Mix.raise("autumn.smoke: no fixtures with .ex + .expect under #{@fixtures}")
    end

    failures =
      Enum.reduce(cases, [], fn {stem, expected, extras}, acc ->
        case smoke_one(bin, stem, expected, extras) do
          :ok ->
            Mix.shell().info("ok  #{stem} → #{expected}")
            acc

          {:error, msg} ->
            Mix.shell().error("FAIL #{stem}: #{msg}")
            [{stem, msg} | acc]
        end
      end)

    case failures do
      [] ->
        Mix.shell().info("autumn.smoke: #{length(cases)} ok")

      _ ->
        Mix.raise("autumn.smoke: #{length(failures)} failed")
    end
  end

  defp discover_cases do
    @fixtures
    |> Path.join("*.expect")
    |> Path.wildcard()
    |> Enum.sort()
    |> Enum.flat_map(fn expect_path ->
      stem = expect_path |> Path.basename() |> Path.rootname()
      ex = Path.join(@fixtures, stem <> ".ex")

      if File.exists?(ex) do
        expected = expect_path |> File.read!() |> String.trim()
        extras = read_extras(stem)
        [{stem, expected, extras}]
      else
        Mix.shell().error("skip #{stem}: missing #{stem}.ex")
        []
      end
    end)
  end

  defp read_extras(stem) do
    path = Path.join(@fixtures, stem <> ".smoke.json")

    if File.exists?(path) do
      path
      |> File.read!()
      |> Jason.decode!()
      |> Map.get("extras", [])
      |> Enum.map(&Path.join(@repo, &1))
    else
      []
    end
  end

  defp prep_hot_load do
    Enum.reduce_while(["math_v1", "math_v2"], :ok, fn stem, :ok ->
      ex = Path.join([@fixtures, "hot_load", stem <> ".ex"])
      bc = Path.join([@fixtures, "hot_load", stem <> ".bc.json"])

      case AutumnCompiler.compile_file(ex) do
        {:ok, module} ->
          File.write!(bc, Jason.encode!(module, pretty: true) <> "\n")
          {:cont, :ok}

        {:error, msg} ->
          {:halt, {:error, "#{stem}: #{msg}"}}
      end
    end)
  end

  defp smoke_one(bin, stem, expected, extras) do
    ex = Path.join(@fixtures, stem <> ".ex")
    sources = extras ++ [ex]
    bc = Path.join(System.tmp_dir!(), "autumn_smoke_#{stem}_#{System.unique_integer([:positive])}.bc.json")

    result =
      case sources do
        [one] -> AutumnCompiler.compile_file(one)
        many -> AutumnCompiler.compile_files(many)
      end

    try do
      with {:ok, module} <- result,
           :ok <- File.write(bc, Jason.encode!(module, pretty: true) <> "\n"),
           {out, 0} <- System.cmd(bin, [bc], stderr_to_stdout: true),
           actual = String.trim(out),
           true <- actual == expected do
        :ok
      else
        {:error, msg} when is_binary(msg) ->
          {:error, msg}

        {out, status} when is_binary(out) and is_integer(status) ->
          {:error, "exit #{status}, got #{inspect(String.trim(out))}"}

        false ->
          {:error, "expected #{inspect(expected)}, got mismatched stdout"}

        other ->
          {:error, "unexpected: #{inspect(other)}"}
      end
    after
      _ = File.rm(bc)
    end
  end
end
