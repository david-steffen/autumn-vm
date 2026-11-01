defmodule Main do
  def main do
    pid = Agent.start(10)
    a = Agent.get(pid, fn s -> s end)
    _ = Agent.update(pid, fn s -> s + 2 end)
    b = Agent.get(pid, fn s -> s end)
    c = Agent.get_and_update(pid, fn s -> {s, s + 1} end)
    _ = Agent.cast(pid, fn s -> s + 3 end)
    d = Agent.get(pid, fn s -> s end)
    # 10 + 12 + 12 + 16
    a + b + c + d
  end
end
