defmodule Main do
  def main do
    try do
      1 + :a
    rescue
      :badarg -> 1
    end
  end
end
