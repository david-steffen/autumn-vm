defmodule Mix.Tasks.Autumn.Smoke do
  @shortdoc "Run allowlisted fixtures on the Lean autumn VM"
  @moduledoc """
  ## Usage

      mix autumn.smoke

  Compiles each allowlisted fixture (if needed) and runs
  `AUTUMN_VM` / `vm/.lake/build/bin/autumn` against the golden `.bc.json`.
  Expects to be run with cwd `compiler/` so `hot_load` relative paths resolve
  (`../tests/fixtures/hot_load/…`).

  Override the VM binary with `AUTUMN_VM=/path/to/autumn`.

  Fixtures that need the stdlib pass extra source paths (e.g. `stdlib/genserver.ex`)
  and are compiled with `AutumnCompiler.compile_files/1`.
  """

  use Mix.Task

  # lib/mix/tasks → repo root
  @repo Path.expand("../../../../", __DIR__)
  @fixtures Path.join(@repo, "tests/fixtures")
  @stdlib Path.join(@repo, "stdlib")

  # {fixture_stem, expected stdout (trimmed)} | {stem, expected, extra_source_paths}
  @allowlist [
    {"add_main", "3"},
    {"try_rescue", "3"},
    {"preempt_fair", "1"},
    {"hot_load", "11"},
    {"drain_siblings", "0"},
    {"monitor_exit", "1"},
    {"monitored_call", "7"},
    {"counter_server", "7"},
    {"fn_multi", "3"},
    {"list_helpers", "8"},
    {"genserver_counter", "7"},
    {"genserver_call_down", "1"},
    {"list_lit", "[1, 2, 3]"},
    {"genserver_stdlib", "7", [Path.join(@stdlib, "genserver.ex")]},
    {"genserver_stdlib_down", "0", [Path.join(@stdlib, "genserver.ex")]},
    {"genserver_behaviour", "8", [Path.join(@stdlib, "genserver.ex")]},
    {"supervisor_one_for_one", "3",
     [Path.join(@stdlib, "genserver.ex"), Path.join(@stdlib, "supervisor.ex")]}
  ]

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

    failures =
      Enum.reduce(@allowlist, [], fn entry, acc ->
        {stem, expected, extras} = normalize(entry)

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
        Mix.shell().info("autumn.smoke: #{length(@allowlist)} ok")

      _ ->
        Mix.raise("autumn.smoke: #{length(failures)} failed")
    end
  end

  defp normalize({stem, expected}), do: {stem, expected, []}
  defp normalize({stem, expected, extras}), do: {stem, expected, extras}

  defp smoke_one(bin, stem, expected, extras) do
    ex = Path.join(@fixtures, stem <> ".ex")
    bc = Path.join(@fixtures, stem <> ".bc.json")
    sources = extras ++ [ex]

    with :ok <- ensure_compiled(sources, bc),
         {out, 0} <- System.cmd(bin, [bc], stderr_to_stdout: true),
         actual = String.trim(out),
         true <- actual == expected do
      :ok
    else
      {:error, _} = e ->
        e

      {out, status} when is_binary(out) and is_integer(status) ->
        {:error, "exit #{status}, got #{inspect(String.trim(out))}"}

      false ->
        {out, _} = System.cmd(bin, [bc], stderr_to_stdout: true)
        {:error, "expected #{inspect(expected)}, got #{inspect(String.trim(out))}"}

      other ->
        {:error, "unexpected: #{inspect(other)}"}
    end
  end

  defp ensure_compiled(sources, bc) do
    result =
      case sources do
        [one] -> AutumnCompiler.compile_file(one)
        many -> AutumnCompiler.compile_files(many)
      end

    case result do
      {:ok, module} ->
        expected = bc |> File.read!() |> Jason.decode!()

        if module == expected do
          :ok
        else
          {:error, "compile diverged from golden #{Path.basename(bc)}"}
        end

      {:error, msg} ->
        {:error, msg}
    end
  end
end
