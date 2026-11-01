defmodule Boom do
  @behaviour GenServer
  use GenServer

  @impl true
  def init(parent) do
    _ = send(parent, :booted)
    {:ok, parent}
  end

  @impl true
  def handle_call(:die, _from, parent) do
    {:stop, :crash, :ok, parent}
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
    # start_link; trap so stop(:normal) does not kill Main (Autumn links kill on any reason).
    _ = Process.flag(:trap_exit, true)
    me = self()
    sup = DynamicSupervisor.start_link(:permanent)
    pid = DynamicSupervisor.start_child(sup, {Boom, me})

    a =
      receive do
        :booted -> 1
      after
        100 -> 0
      end

    _ = GenServer.call(pid, :die)

    b =
      receive do
        :booted -> 1
      after
        100 -> 0
      end

    _ = DynamicSupervisor.stop(sup)
    a + b
  end
end
