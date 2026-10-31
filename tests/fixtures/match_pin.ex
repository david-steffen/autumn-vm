defmodule Main do
  def main do
    {:ok, x} = {:ok, 10}
    [h | t] = [1, 2, 3]
    [a, b] = t

    pinned =
      case {:ok, x} do
        {:ok, ^x} -> 1
        _ -> 0
      end

    miss =
      try do
        {1, 2} = {1, 3}
        0
      rescue
        :match_error -> 1
      end

    bad_pin =
      try do
        {:ok, ^x} = {:ok, 99}
        0
      rescue
        :match_error -> 1
      end

    # 10 + 1 + 2 + 3 + 1 + 1 + 1 = 19
    x + h + a + b + pinned + miss + bad_pin
  end
end
