defmodule Counter do
  @behaviour GenServer
  use GenServer

  @impl true
  def init(n) do
    {:ok, n, {:continue, :bump}}
  end

  @impl true
  def handle_continue(:bump, state) do
    {:noreply, state + 2}
  end

  @impl true
  def handle_call(:get, _from, state) do
    {:reply, state, state}
  end

  @impl true
  def handle_cast(_msg, state) do
    {:noreply, state}
  end
end

defmodule Main do
  def main do
    pid = GenServer.start(Counter, 0)
    GenServer.call(pid, :get)
  end
end
