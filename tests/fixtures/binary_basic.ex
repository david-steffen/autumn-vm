defmodule Main do
  def main do
    a = <<1, 2>>
    b = <<3>>
    c = a <> b
    d =
      if is_binary(c) do
        1
      else
        0
      end

    e =
      if is_bitstring(c) do
        1
      else
        0
      end

    f =
      if is_binary("hi") do
        1
      else
        0
      end

    g =
      if c == <<1, 2, 3>> do
        1
      else
        0
      end

    d + e + f + g
  end
end
