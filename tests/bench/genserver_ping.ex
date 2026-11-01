defmodule Counter do
  @behaviour GenServer
  use GenServer

  @impl true
  def init(n) do
    {:ok, n}
  end

  @impl true
  def handle_call(:inc, _from, state) do
    {:reply, state + 1, state + 1}
  end

  @impl true
  def handle_cast(_msg, state) do
    {:noreply, state}
  end

  @impl true
  def handle_continue(_cont, state) do
    {:noreply, state}
  end
end

defmodule Main do
  def ping(pid, 0, acc) do
    _ = pid
    acc
  end

  def ping(pid, n, acc) do
    v = GenServer.call(pid, :inc)
    ping(pid, n - 1, acc + v)
  end

  def main do
    pid = GenServer.start_link(Counter, 0)
    ping(pid, 100, 0)
  end
end
