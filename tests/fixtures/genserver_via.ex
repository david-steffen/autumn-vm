defmodule Counter do
  @behaviour GenServer
  use GenServer

  @impl true
  def init(n) do
    {:ok, n}
  end

  @impl true
  def handle_call(:get, _from, state) do
    {:reply, state, state}
  end

  def handle_call({:add, x}, _from, state) do
    n = state + x
    {:reply, n, n}
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
  def main do
    reg = Registry.start_link(:unique)
    via = Registry.via(reg, :counter)
    _pid = GenServer.start(Counter, 7, via)
    a = GenServer.call(via, :get)
    b = GenServer.call(via, {:add, 3})
    a + b
  end
end
