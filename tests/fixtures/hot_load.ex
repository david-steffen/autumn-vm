defmodule Main do
  def main do
    miss =
      try do
        _ = Code.load_file("missing.bc.json")
        1
      rescue
        _ -> 0
      end

    _ = Code.load_file("../tests/fixtures/hot_load/math_v1.bc.json")
    a = Math.add(2, 3)
    _ = Code.load_file("../tests/fixtures/hot_load/math_v2.bc.json")
    b = Math.add(2, 3)
    # miss == 0, a == 5, b == 6 → 11
    miss + a + b
  end
end
