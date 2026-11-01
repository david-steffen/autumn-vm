defmodule TempChild do
  use GenServer, restart: :temporary

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

  def handle_cast(_msg, state) do
    {:noreply, state}
  end

  def handle_continue(_cont, state) do
    {:noreply, state}
  end
end

defmodule Main do
  def main do
    me = self()
    _sup = Supervisor.start_link([TempChild.child_spec({me, 7})])

    pid =
      receive do
        {:child, p} -> p
      after
        200 -> 0
      end

    _ = GenServer.call(pid, :boom)

    # Temporary: no restart → no second {:child, _}; timeout path yields 1.
    second =
      receive do
        {:child, _p} -> 0
      after
        200 -> 1
      end

    second
  end
end
