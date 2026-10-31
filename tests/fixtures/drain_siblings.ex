# Entry returns immediately after spawning a worker; durable drain must still
# run the worker to completion before the machine stops (CLI still prints 0).
defmodule Main do
  def worker do
    # burn a few reductions so preemption / scheduling matters
    _ = 1 + 1
    _ = 2 + 2
    1
  end

  def main do
    spawn(:worker, [])
    0
  end
end
