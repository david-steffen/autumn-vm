defmodule Main do
  # Infinite busy loop — never parks. Without reduction preemption this
  # starves `helper` and `main` never receives `:pong`.
  def hog, do: hog()

  def helper do
    receive do
      {from, :ping} ->
        _ = send(from, :pong)
        :ok
    end
  end

  def main do
    h = spawn(:helper, [])
    _ = spawn(:hog, [])
    me = self()
    _ = send(h, {me, :ping})

    case recv() do
      :pong -> 1
      _ -> 0
    end
  end
end
