defmodule Main do
  def main do
    t = Task.async(fn -> 21 end)
    Task.await(t) + Task.await(Task.async(fn -> 21 end))
  end
end
