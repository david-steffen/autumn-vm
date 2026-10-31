defmodule Main do
  def main do
    try do
      case 1 do
        2 -> 0
      end
    rescue
      :match_error -> 5
    end
  end
end
