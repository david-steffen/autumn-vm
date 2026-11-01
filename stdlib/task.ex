defmodule Task do
  # Teaching Task: async/await via spawn MFA + monitor.
  # Uses spawn (not spawn_link): Autumn signals links on any exit, including
  # normal return, which would kill the caller after the first await.
  # No spawn(fn …) — trampoline through Task.runner/3 with a closure arg.
  #
  # API: async/1 → {pid, ref, mref}; await/1.
  # Skip: async_nolink, Task.Supervisor, yield/shutdown.

  def async(fun) do
    parent = self()
    ref = make_ref()
    pid = spawn(Task, :runner, [parent, ref, fun])
    mref = monitor(pid)
    {pid, ref, mref}
  end

  def runner(parent, ref, fun) do
    result = fun.()
    _ = send(parent, {ref, result})
    result
  end

  def await({_pid, ref, mref}) do
    receive do
      {^ref, result} ->
        _ = demonitor(mref)
        result

      {:DOWN, ^mref, :process, _pid, _reason} ->
        0
    after
      500 ->
        _ = demonitor(mref)
        0
    end
  end
end
