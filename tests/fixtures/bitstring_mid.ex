defmodule Main do
  def main do
    # Mid-construct partials that align: 001_00010 → 34
    p = <<1::3, 2::5>>

    a =
      if p == <<34>> do
        1
      else
        0
      end

    # Partial then more partials: 1111_0001 → 241
    q = <<15::4, 1::4>>

    b =
      if q == <<241>> do
        1
      else
        0
      end

    a + b
  end
end
