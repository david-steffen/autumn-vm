defmodule Main do
  def main do
    xs = [1, 2, 3, 4]
    ys = Enum.map(xs, fn x -> x + 1 end)
    # [2,3,4,5] sum via reduce
    s = Enum.reduce(ys, 0, fn x, a -> a + x end)
    zs = Enum.filter(xs, fn x -> x > 2 end)
    # [3,4] → list_size 2
    _ = Enum.each(zs, fn _x -> :ok end)
    s + list_size(zs)
  end
end
