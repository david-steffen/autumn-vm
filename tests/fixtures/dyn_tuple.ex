defmodule Main do
  def pair(a, b), do: {a, b}

  def main do
    t = pair(2, 5)
    elem(t, 0) + elem(t, 1)
  end
end
