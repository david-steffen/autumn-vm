defmodule Math do
  def add(a, b), do: a + b
  def double(x), do: add(x, x)
end

defmodule Main do
  def main do
    a = Math.add(10, 5)
    b = Math.double(3)
    a + b
  end
end
