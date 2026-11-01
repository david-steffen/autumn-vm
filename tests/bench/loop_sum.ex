defmodule Main do
  # Hot arithmetic: sum 1..n via recursion.
  def loop(0, acc) do
    acc
  end

  def loop(n, acc) do
    loop(n - 1, acc + n)
  end

  def main do
    loop(2000, 0)
  end
end
