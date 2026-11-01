defmodule Main do
  def insert_n(_tid, 0) do
    :ok
  end

  def insert_n(tid, n) do
    _ = Ets.insert(tid, n, n)
    insert_n(tid, n - 1)
  end

  def sum_n(_tid, 0, acc) do
    acc
  end

  def sum_n(tid, n, acc) do
    case Ets.lookup(tid, n) do
      [v] ->
        sum_n(tid, n - 1, acc + v)

      _ ->
        sum_n(tid, n - 1, acc)
    end
  end

  def main do
    tid = Ets.new()
    _ = insert_n(tid, 200)
    sum_n(tid, 200, 0)
  end
end
