defmodule Main do
  # Uses stdlib GenServer.call/cast/reply (compile with stdlib/genserver.ex).

  def loop(state) do
    receive do
      {:call, from, ref, :get} ->
        _ = GenServer.reply(from, ref, state)
        loop(state)

      {:call, from, ref, {:add, x}} ->
        n = state + x
        _ = GenServer.reply(from, ref, n)
        loop(n)

      {:cast, :stop} ->
        :ok
    end
  end

  def main do
    pid = spawn(:loop, 0)
    a = GenServer.call(pid, {:add, 1})
    b = GenServer.call(pid, {:add, 2})
    c = GenServer.call(pid, :get)
    _ = GenServer.cast(pid, :stop)
    # 1 + 3 + 3
    a + b + c
  end
end
