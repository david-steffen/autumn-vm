defmodule Leaf do
  def init(parent) do
    _ = send(parent, {:leaf, self()})
    {:ok, 0}
  end

  def handle_call(:get, _from, s) do
    {:reply, 42, s}
  end

  def handle_cast(_msg, s) do
    {:noreply, s}
  end

  def handle_continue(_c, s) do
    {:noreply, s}
  end
end

defmodule Main do
  def main do
    me = self()
    leaf = {Leaf, me}
    inner = map_put(%{}, :id, :inner)
    inner = map_put(inner, :start, {Supervisor, :child_main, [[leaf]]})
    inner = map_put(inner, :type, :supervisor)
    _ = Supervisor.start_link([inner])

    receive do
      {:leaf, p} -> GenServer.call(p, :get)
    after
      500 -> 7
    end
  end
end
