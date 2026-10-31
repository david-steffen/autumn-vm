defmodule Main do
  # GenServer.call against a crashing server → pinned monitor DOWN → 0.

  def boom_loop(_state) do
    receive do
      {:call, _from, _ref, :die} ->
        raise :boom
    end
  end

  def main do
    pid = spawn(:boom_loop, 0)
    GenServer.call(pid, :die)
  end
end
