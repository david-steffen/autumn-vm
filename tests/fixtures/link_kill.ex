# Default (no trap_exit): linked crash kills the parent; machine result is :boom.
defmodule Main do
  def worker do
    raise :boom
  end

  def main do
    spawn_link(:worker, [])

    receive do
      _ -> 0
    after
      50 -> 0
    end
  end
end
