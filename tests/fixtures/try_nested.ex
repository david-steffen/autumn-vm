defmodule Main do
  def boom do
    raise :inner
  end

  def main do
    try do
      try do
        boom()
      rescue
        :inner -> raise :outer
      end
    rescue
      :outer -> 7
    end
  end
end
