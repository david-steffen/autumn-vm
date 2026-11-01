defmodule Main do
  def main do
    t = Ets.new()
    _ = Ets.insert(t, :k, 41)
    _ = Ets.insert(t, :k, 42)
    vs = Ets.lookup(t, :k)
    _ = Ets.delete(t, :k)
    missing = Ets.lookup(t, :k)

    if missing == [] do
      hd(vs)
    else
      0
    end
  end
end
