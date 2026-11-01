defmodule Main do
  def main do
    case {:ok, 1, 2} do
      {:ok, _x} ->
        0

      {:ok, x, y} ->
        x + y
    end
  end
end
