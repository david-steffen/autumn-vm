defmodule BoomChild do
  def init(parent) do
    _ = send(parent, {:child, self()})
    {:ok, 0}
  end

  def handle_call(:boom, _from, state) do
    _ = raise(:crash)
    {:reply, state, state}
  end

  def handle_call(:get, _from, state) do
    {:reply, state, state}
  end

  def handle_cast(_msg, state) do
    {:noreply, state}
  end
end

defmodule Main do
  def main do
    Process.flag(:trap_exit, true)
    me = self()
    # max_restarts = 1 → one restart allowed; second crash shuts the supervisor down
    _sup = Supervisor.start_link([{BoomChild, me}], 1)

    pid1 =
      receive do
        {:child, p} -> p
      after
        200 -> 0
      end

    _ = GenServer.call(pid1, :boom)

    pid2 =
      receive do
        {:child, p} -> p
      after
        200 -> 0
      end

    _ = GenServer.call(pid2, :boom)

    receive do
      {:EXIT, _pid, _reason} ->
        1
    after
      500 ->
        0
    end
  end
end
