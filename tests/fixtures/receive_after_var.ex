defmodule Main do
  def main do
    t = 10

    receive do
    after
      t ->
        1
    end
  end
end
