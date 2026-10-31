defmodule Main do
  def pong(from) do
    msg = recv()
    _ = send(from, msg)
    msg
  end

  def main do
    me = self()
    child = spawn(:pong, me)
    _ = send(child, 42)
    recv()
  end
end
