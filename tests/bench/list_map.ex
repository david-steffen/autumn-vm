defmodule Main do
  def range(0, acc) do
    acc
  end

  def range(n, acc) do
    range(n - 1, [n | acc])
  end

  def main do
    xs = range(200, [])
    ys = for x <- xs, do: x + 1
    Enum.reduce(ys, 0, fn x, a -> a + x end)
  end
end
