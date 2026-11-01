defmodule Main do
  def main do
    n = 8
    <<x::size(n)>> = <<7>>
    m = 16
    <<y::size(m)>> = <<1, 2>>
    # 7 + (258 - 250) = 7 + 8 = 15
    x + (y - 250)
  end
end
