defmodule Main do
  def main do
    # 3-bit + 5-bit partials → aligned byte 0b101_11000 = 0xB8
    a = <<0b101::3>>
    b = <<0b11000::5>>
    c = a <> b

    d =
      if c == <<0xB8>> do
        1
      else
        0
      end

    d
  end
end
