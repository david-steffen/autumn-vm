defmodule Main do
  def bad_server do
    receive do
      {_from, :add, _x} ->
        raise :boom
    end
  end

  def main do
    pid = spawn(:bad_server, [])
    me = self()
    ref = monitor(pid)
    _ = send(pid, {me, :add, 1})

    receive do
      {:ok, _} ->
        0

      {:DOWN, _r, :process, _pid, reason} ->
        case reason do
          :boom -> 1
          _ -> 0
        end
    after
      50 -> 0
    end
  end
end
