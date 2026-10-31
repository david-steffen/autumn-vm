defmodule Main do
  def worker do
    raise :boom
  end

  def main do
    spawn_link(:worker, [])

    receive do
      {:EXIT, _pid, reason} ->
        case reason do
          :boom -> 1
          _ -> 0
        end
    after
      50 -> 0
    end
  end
end
