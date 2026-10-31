defmodule Main do
  def main do
    receive do
      :never -> 0
    after
      0 -> 11
    end
  end
end
