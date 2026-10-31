defmodule Main do
  def classify(n) do
    if n > 0 do
      1
    else
      if n < 0 do
        2
      else
        0
      end
    end
  end

  def pick(flag) do
    unless flag do
      4
    else
      8
    end
  end

  def main do
    a = classify(5)
    b = classify(0 - 2)
    c = classify(0)
    d = pick(false)
    e = pick(true)
    # if without else yields nil when falsy
    f =
      if false do
        9
      end

    case f do
      nil -> a + b + c + d + e
      _ -> 0
    end
  end
end
