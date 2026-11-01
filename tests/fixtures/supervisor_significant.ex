defmodule SigChild do
  use GenServer, restart: :temporary, significant: true

  def init({parent, n}) do
    _ = send(parent, {:child, self()})
    {:ok, n}
  end

  def handle_call(:boom, _from, state) do
    _ = raise(:crash)
    {:reply, state, state}
  end

  def handle_call(:ping, _from, state) do
    {:reply, state, state}
  end

  def handle_cast(_msg, state) do
    {:noreply, state}
  end

  def handle_continue(_cont, state) do
    {:noreply, state}
  end
end

defmodule Main do
  def main do
    Process.flag(:trap_exit, true)
    me = self()
    sup = Supervisor.start_link([SigChild.child_spec({me, 9})])
    mref = monitor(sup)

    pid =
      receive do
        {:child, p} -> p
      after
        200 -> 0
      end

    _ = GenServer.call(pid, :boom)

    # Significant temporary exit → supervisor shuts down → DOWN.
    receive do
      {:DOWN, ^mref, :process, _p, _reason} ->
        1
    after
      500 ->
        0
    end
  end
end
