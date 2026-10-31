defmodule Main do
  def classify(n) when is_integer(n) and n > 0, do: :pos
  def classify(n) when is_integer(n) and n < 0, do: :neg
  def classify(_), do: :other

  def main do
    case classify(3) do
      :pos -> 1
      _ -> 0
    end
  end
end
