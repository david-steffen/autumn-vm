defmodule Main do
  def sum([]), do: 0
  def sum([h | t]), do: h + sum(t)

  def main do
    sum([1, 2])
  end
end
