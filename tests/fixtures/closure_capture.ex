defmodule Main do
  def main do
    x = 10
    y = 3
    add = fn a -> x + a end
    f = add.(y)
    id = fn z -> z end
    g = id.(1)

    h =
      if is_function(add) do
        1
      else
        0
      end

    f + g + h
  end
end
