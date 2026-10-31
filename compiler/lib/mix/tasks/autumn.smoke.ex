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
  """

  use Mix.Task

  # lib/mix/tasks → repo root
  @fixtures Path.expand("../../../../tests/fixtures", __DIR__)

  # {fixture_stem, expected stdout (trimmed)}
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
    {"list_lit", "[1, 2, 3]"}
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
      Enum.reduce(@allowlist, [], fn {stem, expected}, acc ->
        case smoke_one(bin, stem, expected) do
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

  defp smoke_one(bin, stem, expected) do
    ex = Path.join(@fixtures, stem <> ".ex")
    bc = Path.join(@fixtures, stem <> ".bc.json")

    with :ok <- ensure_compiled(ex, bc),
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
        # re-run to get actual for message
        {out, _} = System.cmd(bin, [bc], stderr_to_stdout: true)
        {:error, "expected #{inspect(expected)}, got #{inspect(String.trim(out))}"}

      other ->
        {:error, "unexpected: #{inspect(other)}"}
    end
  end

  defp ensure_compiled(ex, bc) do
    case AutumnCompiler.compile_file(ex) do
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
