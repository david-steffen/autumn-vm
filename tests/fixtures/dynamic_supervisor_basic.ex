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
    sup = DynamicSupervisor.start_link()
    pid = DynamicSupervisor.start_child(sup, {Counter, 11})
    GenServer.call(pid, :get)
  end
end
