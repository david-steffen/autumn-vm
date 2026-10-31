defmodule Main do
  def main do
    f = fn
      0 -> 0
      n -> n + 1
    end

    f.(0) + f.(2)
  end
end
