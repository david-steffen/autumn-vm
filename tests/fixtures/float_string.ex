defmodule Main do
  def main do
    a = 1.5 + 2.5
    b = 3.0 * 2.0
    c = "hel" <> "lo"
    d =
      if is_float(a) do
        1
      else
        0
      end

    e =
      if is_binary(c) do
        1
      else
        0
      end

    f =
      case c do
        "hello" -> 1
        _ -> 0
      end

    g =
      if a > 3.0 do
        1
      else
        0
      end

    # Use int sum so machine result stays an int for easy checking.
    d + e + f + g +
      if b == 6.0 do
        1
      else
        0
      end
  end
end
