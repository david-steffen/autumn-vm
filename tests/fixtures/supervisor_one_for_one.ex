defmodule CrashOnce do
  def init({parent, n}) do
    _ = send(parent, {:child, self()})
    {:ok, n}
  end

  def handle_call(:boom, _from, state) do
    _ = raise(:crash)
    {:reply, state, state}
  end

  def handle_call(:get, _from, state) do
    {:reply, state, state}
  end

  def handle_call({:add, x}, _from, state) do
    n = state + x
    {:reply, n, n}
  end

  def handle_cast(_msg, state) do
    {:noreply, state}
  end
end

defmodule Main do
  def main do
    me = self()
    _sup = Supervisor.start_link([{CrashOnce, {me, 0}}])

    pid =
      receive do
        {:child, p} -> p
      after
        200 -> 0
      end

    _ = GenServer.call(pid, :boom)

    pid2 =
      receive do
        {:child, p} -> p
      after
        200 -> 0
      end

    a = GenServer.call(pid2, {:add, 3})
    b = GenServer.call(pid2, :get)
    # 3 + 3 — exercises restart + two calls after DOWN
    a + b
  end
end
