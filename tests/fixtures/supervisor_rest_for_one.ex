defmodule ChildA do
  def init(parent) do
    _ = send(parent, {:a, self()})
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

defmodule ChildB do
  def init(parent) do
    _ = send(parent, {:b, self()})
    {:ok, 0}
  end

  def handle_call(:get, _from, state) do
    {:reply, 7, state}
  end

  def handle_cast(_msg, state) do
    {:noreply, state}
  end
end

defmodule Main do
  def main do
    me = self()
    _sup = Supervisor.start_link([{ChildA, me}, {ChildB, me}], :rest_for_one, 5)

    a1 =
      receive do
        {:a, p} -> p
      after
        200 -> 0
      end

    b1 =
      receive do
        {:b, p} -> p
      after
        200 -> 0
      end

    _ = GenServer.call(a1, :boom)

    _a2 =
      receive do
        {:a, p} -> p
      after
        200 -> 0
      end

    b2 =
      receive do
        {:b, p} -> p
      after
        200 -> 0
      end

    # B was restarted (new pid) and answers 7
    same =
      if b1 == b2 do
        0
      else
        1
      end

    GenServer.call(b2, :get) + same
  end
end
