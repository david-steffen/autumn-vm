defmodule Mix.Tasks.Autumn.Bench do
  @shortdoc "Compile bench fixtures and time the Lean autumn VM"
  @moduledoc """
  ## Usage

      mix autumn.bench
      mix autumn.bench loop_sum
      mix autumn.bench --runs 100

  Discovers `tests/bench/*.ex`, compiles each to a tempfile (no committed
  `.bc.json`), runs `autumn --bench N` (decode once, warmup once, then N timed
  runs). Optional `tests/bench/<stem>.bench.json`:

      {"extras": ["stdlib/enum.ex"], "runs": 50}

  Override runs with `--runs N` (default 30). Override VM with `AUTUMN_VM`.
  """

  use Mix.Task

  @repo Path.expand("../../../../", __DIR__)
  @bench Path.join(@repo, "tests/bench")

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("app.start")

    {opts, stems, _} =
      OptionParser.parse(args,
        strict: [runs: :integer],
        aliases: [n: :runs]
      )

    default_runs = Keyword.get(opts, :runs, 30)
    bin = AutumnCompiler.vm_bin()

    unless File.exists?(bin) do
      Mix.raise("""
      autumn VM not found at #{bin}
      Build it with: (cd ../vm && lake build)
      Or set AUTUMN_VM to the autumn executable.
      """)
    end

    cases = discover_cases(stems)

    if cases == [] do
      Mix.raise("autumn.bench: no .ex under #{@bench}")
    end

    Mix.shell().info("autumn.bench: #{length(cases)} case(s), default runs=#{default_runs}")

    Enum.each(cases, fn {stem, extras, runs} ->
      n = if Keyword.has_key?(opts, :runs), do: default_runs, else: runs
      bench_one(bin, stem, extras, n)
    end)
  end

  defp discover_cases([]) do
    @bench
    |> Path.join("*.ex")
    |> Path.wildcard()
    |> Enum.sort()
    |> Enum.map(fn ex ->
      stem = ex |> Path.basename() |> Path.rootname()
      {extras, runs} = read_meta(stem)
      {stem, extras, runs}
    end)
  end

  defp discover_cases(stems) do
    Enum.map(stems, fn stem ->
      ex = Path.join(@bench, stem <> ".ex")

      unless File.exists?(ex) do
        Mix.raise("autumn.bench: missing #{ex}")
      end

      {extras, runs} = read_meta(stem)
      {stem, extras, runs}
    end)
  end

  defp read_meta(stem) do
    path = Path.join(@bench, stem <> ".bench.json")

    if File.exists?(path) do
      meta = path |> File.read!() |> Jason.decode!()

      extras =
        meta
        |> Map.get("extras", [])
        |> Enum.map(&Path.join(@repo, &1))

      runs = Map.get(meta, "runs", 30)
      {extras, runs}
    else
      {[], 30}
    end
  end

  defp bench_one(bin, stem, extras, runs) do
    ex = Path.join(@bench, stem <> ".ex")
    sources = extras ++ [ex]

    bc =
      Path.join(
        System.tmp_dir!(),
        "autumn_bench_#{stem}_#{System.unique_integer([:positive])}.bc.json"
      )

    result =
      case sources do
        [one] -> AutumnCompiler.compile_file(one)
        many -> AutumnCompiler.compile_files(many)
      end

    try do
      case result do
        {:ok, module} ->
          File.write!(bc, Jason.encode!(module, pretty: true) <> "\n")

          {out, status} =
            System.cmd(bin, ["--bench", Integer.to_string(runs), bc], stderr_to_stdout: true)

          if status != 0 do
            Mix.shell().error("FAIL #{stem}: exit #{status}\n#{String.trim(out)}")
          else
            Mix.shell().info("#{stem}: #{String.trim(out)}")
          end

        {:error, msg} ->
          Mix.shell().error("FAIL #{stem}: compile #{msg}")
      end
    after
      _ = File.rm(bc)
    end
  end
end
