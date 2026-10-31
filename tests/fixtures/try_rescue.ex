defmodule Main do
  def boom do
    raise :boom
  end

  def main do
    try do
      boom()
    rescue
      :boom -> 3
    end
  end
end
