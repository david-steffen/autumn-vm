defmodule Main do
  def f(0), do: 0
  def f(n), do: n + 1

  def main do
    f(0) + f(2)
  end
end
