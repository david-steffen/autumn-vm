defmodule Main do
  def main do
    sup = Task.Supervisor.start_link()
    t = Task.Supervisor.async(sup, fn -> 21 end)
    Task.await(t)
  end
end
