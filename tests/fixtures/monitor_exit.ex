defmodule Main do
  def worker do
    raise :boom
  end

  def main do
    pid = spawn(:worker, [])
    _ref = monitor(pid)

    receive do
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
