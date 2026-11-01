defmodule Main do
  def main do
    xs = [1, 2, 3, 4]
    ys = for x <- xs, do: x + 1
    # [2,3,4,5]
    s = Enum.reduce(ys, 0, fn x, a -> a + x end)

    zs = for x <- xs, x > 2, do: x
    # [3,4]
    s + list_size(zs)
  end
end
