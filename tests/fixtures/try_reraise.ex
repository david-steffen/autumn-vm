defmodule Main do
  def boom do
    raise :boom
  end

  def main do
    try do
      try do
        boom()
      rescue
        :other -> 1
      end
    rescue
      :boom -> 9
    end
  end
end
