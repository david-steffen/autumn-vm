defmodule Mix.Tasks.Autumn.BenchCompare do
  @shortdoc "Time the same benches on Autumn VM vs BEAM (Elixir/OTP)"
  @moduledoc """
  ## Usage

      mix autumn.bench_compare
      mix autumn.bench_compare --runs 40

  Runs the `tests/bench` workloads on the Lean VM (`autumn --bench`) and the
  same algorithms on the host BEAM, then prints a side-by-side table.
  """

  use Mix.Task

  @repo Path.expand("../../../../", __DIR__)
  @bench Path.join(@repo, "tests/bench")

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("app.start")

    {opts, _, _} =
      OptionParser.parse(args,
        strict: [runs: :integer],
        aliases: [n: :runs]
      )

    runs = Keyword.get(opts, :runs, 40)
    bin = AutumnCompiler.vm_bin()

    unless File.exists?(bin) do
      Mix.raise("autumn VM not found at #{bin} — build with (cd ../vm && lake build)")
    end

    Mix.shell().info(
      "autumn.bench_compare: Elixir #{System.version()} / OTP #{:erlang.system_info(:otp_release)}, runs=#{runs}"
    )

    rows =
      [
        {"loop_sum", [], &beam_loop_sum/0, 2_001_000},
        {"list_map", [Path.join(@repo, "stdlib/enum.ex")], &beam_list_map/0, 20_300},
        {"genserver_ping", [Path.join(@repo, "stdlib/genserver.ex")], &beam_genserver_ping/0,
         5_050},
        {"ets_churn", [Path.join(@repo, "stdlib/ets.ex")], &beam_ets_churn/0, 20_100}
      ]
      |> Enum.map(fn {stem, extras, beam_fun, expect} ->
        autumn_ns = autumn_ns_per_run(bin, stem, extras, runs)
        beam_ns = beam_ns_per_run(beam_fun, runs, expect)
        {stem, autumn_ns, beam_ns}
      end)

    Mix.shell().info("")
    Mix.shell().info(pad("bench", 16) <> pad("autumn", 14) <> pad("beam", 14) <> "ratio")
    Mix.shell().info(String.duplicate("-", 56))

    Enum.each(rows, fn {stem, a, b} ->
      ratio =
        cond do
          is_nil(a) or is_nil(b) or b == 0 -> "n/a"
          true -> :erlang.float_to_binary(a / b, decimals: 1) <> "×"
        end

      Mix.shell().info(pad(stem, 16) <> pad(fmt_ns(a), 14) <> pad(fmt_ns(b), 14) <> ratio)
    end)
  end

  defp autumn_ns_per_run(bin, stem, extras, runs) do
    ex = Path.join(@bench, stem <> ".ex")
    sources = extras ++ [ex]

    bc =
      Path.join(
        System.tmp_dir!(),
        "autumn_cmp_#{stem}_#{System.unique_integer([:positive])}.bc.json"
      )

    result =
      case sources do
        [one] -> AutumnCompiler.compile_file(one)
        many -> AutumnCompiler.compile_files(many)
      end

    try do
      case result do
        {:ok, module} ->
          File.write!(bc, Jason.encode!(module) <> "\n")

          {out, 0} =
            System.cmd(bin, ["--bench", Integer.to_string(runs), bc], stderr_to_stdout: true)

          parse_ns_per_run(out)

        {:error, msg} ->
          Mix.shell().error("autumn #{stem}: compile #{msg}")
          nil
      end
    after
      _ = File.rm(bc)
    end
  end

  defp parse_ns_per_run(out) do
    case Regex.run(~r/ns_per_run=(\d+)/, out) do
      [_, n] ->
        String.to_integer(n)

      _ ->
        Mix.shell().error("could not parse autumn output: #{inspect(String.trim(out))}")
        nil
    end
  end

  defp beam_ns_per_run(fun, runs, expect) do
    # warmup
    ^expect = fun.()
    t0 = System.monotonic_time(:nanosecond)

    for _ <- 1..runs do
      ^expect = fun.()
    end

    t1 = System.monotonic_time(:nanosecond)
    div(t1 - t0, runs)
  end

  defp beam_loop_sum do
    loop_sum(2000, 0)
  end

  defp loop_sum(0, acc), do: acc
  defp loop_sum(n, acc), do: loop_sum(n - 1, acc + n)

  defp beam_list_map do
    xs = range(200, [])
    ys = for x <- xs, do: x + 1
    Enum.reduce(ys, 0, fn x, a -> a + x end)
  end

  defp range(0, acc), do: acc
  defp range(n, acc), do: range(n - 1, [n | acc])

  defp beam_genserver_ping do
    {:ok, pid} = GenServer.start_link(Mix.Tasks.Autumn.BenchCompare.Counter, 0)
    v = ping(pid, 100, 0)
    GenServer.stop(pid)
    v
  end

  defp ping(_pid, 0, acc), do: acc

  defp ping(pid, n, acc) do
    v = GenServer.call(pid, :inc)
    ping(pid, n - 1, acc + v)
  end

  defp beam_ets_churn do
    tid = :ets.new(:autumn_bench_ets, [:set, :public])
    insert_n(tid, 200)
    v = sum_n(tid, 200, 0)
    :ets.delete(tid)
    v
  end

  defp insert_n(_tid, 0), do: :ok

  defp insert_n(tid, n) do
    true = :ets.insert(tid, {n, n})
    insert_n(tid, n - 1)
  end

  defp sum_n(_tid, 0, acc), do: acc

  defp sum_n(tid, n, acc) do
    case :ets.lookup(tid, n) do
      [{^n, v}] -> sum_n(tid, n - 1, acc + v)
      _ -> sum_n(tid, n - 1, acc)
    end
  end

  defp pad(s, n), do: String.pad_trailing(to_string(s), n)

  defp fmt_ns(nil), do: "FAIL"

  defp fmt_ns(ns) when ns >= 1_000_000_000,
    do: :erlang.float_to_binary(ns / 1.0e9, decimals: 2) <> "s"

  defp fmt_ns(ns) when ns >= 1_000_000,
    do: :erlang.float_to_binary(ns / 1.0e6, decimals: 2) <> "ms"

  defp fmt_ns(ns) when ns >= 1_000,
    do: :erlang.float_to_binary(ns / 1.0e3, decimals: 1) <> "µs"

  defp fmt_ns(ns), do: Integer.to_string(ns) <> "ns"
end

defmodule Mix.Tasks.Autumn.BenchCompare.Counter do
  use GenServer

  @impl true
  def init(n), do: {:ok, n}

  @impl true
  def handle_call(:inc, _from, state), do: {:reply, state + 1, state + 1}
end
