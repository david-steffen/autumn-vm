defmodule Main do
  def get_a(m) do
    case m do
      %{a: x} -> x
      _ -> 0
    end
  end

  def main do
    get_a(%{a: 7, b: 1})
  end
end
