defmodule Main do
  def main do
    <<x::8, rest::binary>> = <<40, 2>>
    <<y::8>> = rest
    x + y
  end
end
