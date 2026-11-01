defmodule Main do
  def boom do
    # Abnormal exit so :permanent restarts.
    _ = Process.exit(self(), :crash)
    0
  end

  def main do
    # start_link; trap so stop(:normal) does not kill Main.
    _ = Process.flag(:trap_exit, true)
    me = self()
    sup = Task.Supervisor.start_link(:permanent)

    _t =
      Task.Supervisor.start_child(sup, fn ->
        _ = send(me, :booted)
        Main.boom()
      end)

    a =
      receive do
        :booted -> 1
      after
        100 -> 0
      end

    b =
      receive do
        :booted -> 1
      after
        100 -> 0
      end

    _ = Task.Supervisor.stop(sup)
    a + b
  end
end
