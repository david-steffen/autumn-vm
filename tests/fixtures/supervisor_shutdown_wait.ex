defmodule SlowChild do
  use GenServer, shutdown: 5

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

  def handle_continue(_c, state) do
    {:noreply, state}
  end
end

defmodule Marker do
  use GenServer

  def init(parent) do
    _ = send(parent, {:marker, self()})
    {:ok, 0}
  end

  def handle_call(:get, _from, state) do
    {:reply, 4, state}
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
    # rest_for_one: crash SlowChild → shutdown SlowChild (wait 50) then Marker, restart both
    _sup =
      Supervisor.start_link(
        [SlowChild.child_spec(me), Marker.child_spec(me)],
        :rest_for_one,
        5
      )

    child =
      receive do
        {:child, p} -> p
      after
        200 -> 0
      end

    _m1 =
      receive do
        {:marker, p} -> p
      after
        200 -> 0
      end

    _ = GenServer.call(child, :boom)

    _c2 =
      receive do
        {:child, p} -> p
      after
        200 -> 0
      end

    m2 =
      receive do
        {:marker, p} -> p
      after
        200 -> 0
      end

    GenServer.call(m2, :get)
  end
end
