defmodule Main do
  def main do
    _ = Ets.new(:t, :set)
    _ = Ets.insert(:t, :k, 7)
    vs = Ets.lookup(:t, :k)
    hd(vs)
  end
end
