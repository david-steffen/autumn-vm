defmodule Main do
  def main do
    t = Ets.new(nil, :bag)
    _ = Ets.insert(t, :a, 1)
    _ = Ets.insert(t, :b, 2)
    _ = Ets.insert(t, :a, 3)

    objs = Ets.match_object(t, {:a, :_})
    ms = [{{:a, :"$1"}, [], [:"$1"]}]
    vals = Ets.select(t, ms)

    list_size(objs) + list_size(vals) + hd(vals)
  end
end
