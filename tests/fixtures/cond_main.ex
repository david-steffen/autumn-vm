defmodule Main do
  def grade(n) do
    cond do
      n >= 90 -> 4
      n >= 80 -> 3
      n >= 70 -> 2
      true -> 1
    end
  end

  def main do
    a = grade(95)
    b = grade(85)
    c = grade(75)
    d = grade(50)
    a + b + c + d
  end
end
