defmodule Main do
  def main do
    t = Ets.new(nil, :ordered_set)
    _ = Ets.insert(t, 3, :c)
    _ = Ets.insert(t, 1, :a)
    _ = Ets.insert(t, 2, :b)

    k1 = Ets.first(t)
    k2 = Ets.next(t, k1)
    k3 = Ets.next(t, k2)
    k1 + k2 + k3
  end
end
