defmodule Main do
  def child(parent) do
    t = Ets.new(:tab, :set)
    _ = Ets.insert(t, :k, 42)
    _ = Ets.heir(t, {parent, :payload})
    :ok
  end

  def main do
    me = self()
    _ = spawn(:child, me)

    receive do
      {:"ETS-TRANSFER", tid, _from, :payload} ->
        vs = Ets.lookup(tid, :k)
        hd(vs)
    end
  end
end
