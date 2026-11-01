defmodule Worker do
  def start_link({parent, n}) do
    GenServer.start(Worker, {parent, n})
  end

  def init({parent, n}) do
    _ = send(parent, {:child, self()})
    {:ok, n}
  end

  def handle_call(:get, _from, state) do
    {:reply, state, state}
  end

  def handle_cast(_msg, state) do
    {:noreply, state}
  end

  def handle_continue(_c, state) do
    {:noreply, state}
  end
end

defmodule Main do
  def main do
    me = self()
    spec = map_put(%{}, :id, Worker)
    spec = map_put(spec, :start, {Worker, :start_link, [{me, 9}]})
    _sup = Supervisor.start_link([spec])

    pid =
      receive do
        {:child, p} -> p
      after
        200 -> 0
      end

    GenServer.call(pid, :get)
  end
end
