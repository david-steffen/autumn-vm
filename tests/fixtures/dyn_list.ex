defmodule Main do
  def prepend(h, t), do: [h | t]

  def main do
    xs = prepend(1, [2, 3])
    list_size(xs)
  end
end
