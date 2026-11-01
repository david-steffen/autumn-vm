defmodule Main do
  def ok(x) do
    {:ok, x}
  end

  def err(_x) do
    :error
  end

  def main do
    a =
      with {:ok, x} <- ok(10),
           {:ok, y} <- ok(20) do
        x + y
      end

    b =
      with {:ok, x} <- err(1) do
        x
      else
        :error -> 1
        _ -> 0
      end

    c =
      with {:ok, x} <- err(2) do
        x
      end

    d =
      case c do
        :error -> 1
        _ -> 0
      end

    a + b + d
  end
end
