defmodule Main do
  def main do
    me = self()
    _ = send(me, :noise)
    _ = send(me, :ping)

    receive do
      :ping -> :ok
    end

    # leftover unmatched message
    recv()
  end
end
