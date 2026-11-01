defmodule Main do
  def main do
    # 3 bits: value 3 → bits 011, pad → byte 96, trailing_bits 5
    p = <<3::3>>

    a =
      if is_bitstring(p) do
        1
      else
        0
      end

    b =
      if is_binary(p) do
        0
      else
        1
      end

    c =
      if p == <<3::size(3)>> do
        1
      else
        0
      end

    # Full bytes then trailing partial: <<1, 2::3>>
    q = <<1, 2::3>>

    d =
      if is_bitstring(q) do
        if is_binary(q) do
          0
        else
          1
        end
      else
        0
      end

    a + b + c + d
  end
end
