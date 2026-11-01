defmodule Main do
  def main do
    # Codepoint construct → UTF-8 bytes (65 → "A")
    a = <<65::utf8>>

    b =
      if a == <<"A">> do
        1
      else
        0
      end

    # Multi-byte: U+00E9 (é) → 0xC3 0xA9
    c = <<0xE9::utf8>>

    d =
      if c == <<0xC3, 0xA9>> do
        1
      else
        0
      end

    b + d
  end
end
