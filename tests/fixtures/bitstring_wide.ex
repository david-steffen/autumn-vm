defmodule Main do
  def main do
    # 16-bit match via lowerer chunking (8+8); <<1,2>> → 258
    <<x::16>> = <<1, 2>>
    # 24-bit → three 8-bit chunks; <<1,2,3>> → 66051
    <<y::24>> = <<1, 2, 3>>
    # 258 - 200 + (66051 - 66000) = 58 + 51 = 109
    x - 200 + (y - 66000)
  end
end
