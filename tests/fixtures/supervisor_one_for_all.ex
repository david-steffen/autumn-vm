defmodule AllA do
  def init(parent) do
    _ = send(parent, {:a, self()})
    {:ok, 0}
  end

  def handle_call(:get, _from, state) do
    {:reply, 1, state}
  end

  def handle_cast(_msg, state) do
    {:noreply, state}
  end
end

defmodule AllB do
  def init(parent) do
    _ = send(parent, {:b, self()})
    {:ok, 0}
  end

  def handle_call(:boom, _from, state) do
    _ = raise(:crash)
    {:reply, state, state}
  end

  def handle_call(:get, _from, state) do
    {:reply, 2, state}
  end

  def handle_cast(_msg, state) do
    {:noreply, state}
  end
end

defmodule Main do
  def main do
    me = self()
    _sup = Supervisor.start_link([{AllA, me}, {AllB, me}], :one_for_all, 5)

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

    _ = GenServer.call(b1, :boom)

    a2 =
      receive do
        {:a, p} -> p
      after
        500 -> 0
      end

    b2 =
      receive do
        {:b, p} -> p
      after
        500 -> 0
      end

    a_new =
      if a1 == a2 do
        0
      else
        1
      end

    b_new =
      if b1 == b2 do
        0
      else
        1
      end

    ga = GenServer.call(a2, :get)
    gb = GenServer.call(b2, :get)
    # 1 + 2 + 1 + 1 = 5
    ga + gb + a_new + b_new
  end
end
