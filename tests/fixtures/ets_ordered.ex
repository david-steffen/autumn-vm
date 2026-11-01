defmodule Main do
  def main do
    t = Ets.new(nil, :ordered_set)
    _ = Ets.insert(t, 3, :c)
    _ = Ets.insert(t, 1, :a)
    _ = Ets.insert(t, 2, :b)

    ms = [{{:"$1", :_}, [], [:"$1"]}]
    keys = Ets.select(t, ms)
    hd(keys)
  end
end
