defmodule Main do
  def main do
    t = Ets.new(nil, :bag)
    _ = Ets.insert(t, :k, 1)
    _ = Ets.insert(t, :k, 2)
    _ = Ets.delete_object(t, {:k, 1})
    vs = Ets.lookup(t, :k)
    list_size(vs) + hd(vs)
  end
end
