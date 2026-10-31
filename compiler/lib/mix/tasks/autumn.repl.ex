defmodule Mix.Tasks.Autumn.Repl do
  @shortdoc "Interactive Autumn REPL (Mix lowerer + durable Lean VM)"
  @moduledoc """
  ## Usage

      mix autumn.repl

  Spawns `autumn --repl` and keeps one VM session alive. Each line is lowered
  as `Repl.main/0` and sent as `EVAL` (so a loaded `Main` is not replaced).
  Modules installed via `.load` persist; process tables reset on every eval.

  Simple `var = expr` bindings are replayed on the Mix side into later lines
  (IEx-like session vars). Side-effecting RHS forms are re-executed each line.

  ### Commands

      <expr>          lower + EVAL (`Repl.main/0`)
      .help           this help
      .bindings       list Mix-side session bindings
      .load <path>    compile file, LOAD (install only)
      .clear          drop Mix-side bindings
      .quit / .q      exit

  Override the VM binary with `AUTUMN_VM=/path/to/autumn`.
  """

  use Mix.Task

  @help """
  Commands:
    <expr>           lower + EVAL as Repl.main/0
    .help            show this help
    .bindings        list Mix-side var = … bindings
    .load <path>     compile + LOAD (modules persist)
    .clear           drop Mix-side bindings
    .quit / .q       exit

  Bindings: only simple `var = expr` (atom LHS). Mix replays prior assigns as
  AST before each new line (side-effecting RHS re-runs). Lean resets processes
  each EVAL; modules from .load stay installed.
  """

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

    port =
      Port.open(
        {:spawn_executable, bin},
        [
          :binary,
          :exit_status,
          :use_stdio,
          {:line, 1_048_576},
          {:args, ["--repl"]}
        ]
      )

    case await_ready(port) do
      :ok ->
        Mix.shell().info("Autumn REPL (.help for commands; Ctrl-C or .quit to exit)")
        loop(port, 1, [])

      {:error, reason} ->
        Port.close(port)
        Mix.raise("failed to start autumn --repl: #{reason}")
    end
  end

  defp await_ready(port) do
    receive do
      {^port, {:data, {:eol, line}}} ->
        case String.trim(line) do
          "# ready" -> :ok
          other -> {:error, "unexpected banner: #{inspect(other)}"}
        end

      {^port, {:exit_status, status}} ->
        {:error, "exited with status #{status}"}
    after
      10_000 ->
        {:error, "timed out waiting for # ready"}
    end
  end

  defp loop(port, n, bindings) do
    case IO.gets("autumn(#{n})> ") do
      :eof ->
        send_line(port, "QUIT")
        drain_exit(port)

      line when is_binary(line) ->
        line = String.trim(line)

        cond do
          line == "" ->
            loop(port, n, bindings)

          line in [".quit", ".q"] ->
            send_line(port, "QUIT")
            drain_exit(port)

          line == ".help" ->
            Mix.shell().info(String.trim_trailing(@help))
            loop(port, n + 1, bindings)

          line == ".bindings" ->
            print_bindings(bindings)
            loop(port, n + 1, bindings)

          line == ".clear" ->
            Mix.shell().info(":ok")
            loop(port, n + 1, [])

          String.starts_with?(line, ".load ") ->
            path = String.trim_leading(line, ".load ") |> String.trim()

            case AutumnCompiler.compile_file(path) do
              {:ok, module} ->
                json = Jason.encode!(module)
                send_line(port, "LOAD " <> json)
                _ = print_reply(port)
                loop(port, n + 1, bindings)

              {:error, msg} ->
                Mix.shell().error("** #{msg}")
                loop(port, n + 1, bindings)
            end

          String.starts_with?(line, ".") ->
            cmd = line |> String.split(~r/\s+/, parts: 2) |> hd()
            Mix.shell().error("** unknown command #{cmd} (try .help)")
            loop(port, n + 1, bindings)

          true ->
            case AutumnCompiler.eval_expr(line, bindings) do
              {:ok, module, expr} ->
                json = Jason.encode!(module)
                send_line(port, "EVAL " <> json)

                bindings =
                  case print_reply(port) do
                    :ok -> AutumnCompiler.binding_after(bindings, expr)
                    :error -> bindings
                  end

                loop(port, n + 1, bindings)

              {:error, msg} ->
                Mix.shell().error("** #{msg}")
                loop(port, n + 1, bindings)
            end
        end
    end
  end

  defp print_bindings([]) do
    Mix.shell().info("(no bindings)")
  end

  defp print_bindings(bindings) do
    Enum.each(bindings, fn {var, rhs} ->
      Mix.shell().info("#{var} = #{Macro.to_string(rhs)}")
    end)
  end

  defp send_line(port, line) do
    true = Port.command(port, line <> "\n")
  end

  defp print_reply(port) do
    receive do
      {^port, {:data, {:eol, line}}} ->
        case line do
          <<"=> ", rest::binary>> ->
            Mix.shell().info(rest)
            :ok

          <<"! ", rest::binary>> ->
            Mix.shell().error("** #{rest}")
            :error

          other ->
            Mix.shell().error("** unexpected VM reply: #{inspect(other)}")
            :error
        end

      {^port, {:exit_status, status}} ->
        Mix.raise("autumn --repl exited with status #{status}")
    after
      60_000 ->
        Mix.raise("timed out waiting for VM reply")
    end
  end

  defp drain_exit(port) do
    receive do
      {^port, {:exit_status, _}} -> :ok
      {^port, {:data, _}} -> drain_exit(port)
    after
      2_000 ->
        Port.close(port)
        :ok
    end
  end
end
