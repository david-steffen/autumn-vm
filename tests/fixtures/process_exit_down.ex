defmodule Main do
  def sleeper do
    receive do
      _ -> 0
    after
      100 -> 0
    end
  end

  def main do
    pid = spawn(:sleeper, [])
    _ref = monitor(pid)
    Process.exit(pid, :shutdown)

    receive do
      {:DOWN, _r, :process, _pid, reason} ->
        case reason do
          :shutdown -> 1
          _ -> 0
        end
    after
      50 -> 0
    end
  end
end
