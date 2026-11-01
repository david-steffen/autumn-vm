defmodule Main do
  def main do
    sup = Task.Supervisor.start_link()
    t = Task.Supervisor.start_child(sup, fn -> 34 end)
    Task.await(t)
  end
end
