defmodule Main do
  def main do
    <<a::utf8>> = <<65>>
    <<b::utf8, rest::binary>> = <<0xC3, 0xA9, 7>>
    <<c::utf8>> = rest

    d =
      case <<1, 2>> do
        <<_::utf8>> -> 0
        _ -> 1
      end

    a + b + c + d
  end
end
