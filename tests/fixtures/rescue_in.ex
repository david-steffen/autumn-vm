defmodule Main do
  def boom do
    raise :bang
  end

  def main do
    try do
      boom()
    rescue
      e in [:boom, :bang] ->
        case e do
          :bang -> 2
          _ -> 0
        end
    end
  end
end
