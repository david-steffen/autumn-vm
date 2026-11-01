defmodule Main do
  def main do
    t = Ets.new(nil, :set)
    _ = Ets.insert(t, :a, 1)
    _ = Ets.insert(t, :b, 2)
    _ = Ets.insert(t, :c, 3)

    ms = [{{:_, :"$1"}, [{:"==", :"$1", 2}], [:"$1"]}]
    vals = Ets.select(t, ms)
    hd(vals)
  end
end
