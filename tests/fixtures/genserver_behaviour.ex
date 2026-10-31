defmodule Counter do
  def init(n) do
    {:ok, n}
  end

  def handle_call(:get, _from, state) do
    {:reply, state, state}
  end

  def handle_call({:add, x}, _from, state) do
    n = state + x
    {:reply, n, n}
  end

  def handle_cast(:bump, state) do
    {:noreply, state + 1}
  end

  def handle_cast(:stop, state) do
    {:stop, :normal, state}
  end
end

defmodule Main do
  def main do
    pid = GenServer.start(Counter, 0)
    a = GenServer.call(pid, {:add, 1})
    b = GenServer.call(pid, {:add, 2})
    _ = GenServer.cast(pid, :bump)
    c = GenServer.call(pid, :get)
    _ = GenServer.cast(pid, :stop)
    # 1 + 3 + 4 = 8
    a + b + c
  end
end
