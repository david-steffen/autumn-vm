defmodule Main do
  # Teaching GenServer shape (no stdlib): init state via spawn arg,
  # handle_call via {:call, from, ref, req} / {:reply, ref, value},
  # handle_cast via {:cast, msg}, client call = make_ref + monitor + selective receive.

  def loop(state) do
    receive do
      {:call, from, ref, :get} ->
        _ = send(from, {:reply, ref, state})
        loop(state)

      {:call, from, ref, {:add, x}} ->
        n = state + x
        _ = send(from, {:reply, ref, n})
        loop(n)

      {:cast, :stop} ->
        :ok
    end
  end

  def call(pid, req) do
    me = self()
    ref = make_ref()
    mref = monitor(pid)
    _ = send(pid, {:call, me, ref, req})

    receive do
      {:reply, ^ref, reply} ->
        _ = demonitor(mref)
        reply

      {:DOWN, ^mref, :process, _pid, _reason} ->
        0
    after
      50 -> 0
    end
  end

  def cast(pid, msg) do
    _ = send(pid, {:cast, msg})
    :ok
  end

  def main do
    pid = spawn(:loop, 0)
    a = call(pid, {:add, 1})
    b = call(pid, {:add, 2})
    c = call(pid, :get)
    _ = cast(pid, :stop)
    # 1 + 3 + 3
    a + b + c
  end
end
