defmodule Main do
  # GenServer-shaped call against a crashing server → pinned monitor DOWN.

  def boom_loop(_state) do
    receive do
      {:call, _from, _ref, {:add, _x}} ->
        raise :boom
    end
  end

  def call(pid, req) do
    me = self()
    ref = make_ref()
    mref = monitor(pid)
    _ = send(pid, {:call, me, ref, req})

    receive do
      {:reply, ^ref, _reply} ->
        _ = demonitor(mref)
        0

      {:DOWN, ^mref, :process, _pid, reason} ->
        case reason do
          :boom -> 1
          _ -> 0
        end
    after
      50 -> 0
    end
  end

  def main do
    pid = spawn(:boom_loop, 0)
    call(pid, {:add, 1})
  end
end
