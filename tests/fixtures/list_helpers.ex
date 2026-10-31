defmodule Main do
  def main do
    xs = [1, 2, 3]
    # hd → 1, tl → [2,3], ++ → [1,2,3,4,5]; 1 + 2 + 3 + 4 + 5 = 15? 
    # Return {hd, length(tl), length(xs ++ [4, 5])} = {1, 2, 5} via arithmetic: 1 + 2 + 5 = 8
    h = hd(xs)
    t = tl(xs)
    ys = xs ++ [4, 5]
    h + list_size(t) + list_size(ys)
  end
end
