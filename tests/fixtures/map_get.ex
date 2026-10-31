defmodule Main do
  def main do
    m = map_put(%{}, :a, 3)
    map_get(m, :a)
  end
end
