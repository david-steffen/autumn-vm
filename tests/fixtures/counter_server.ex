defmodule Main do
  # Tagged request/reply messages (Phase 6).
  def server(n) do
    receive do
      {from, :add, x} ->
        _ = send(from, {:ok, n + x})
        server(n + x)

      {from, :get} ->
        _ = send(from, {:ok, n})
        server(n)

      :stop ->
        :ok
    end
  end

  def main do
    pid = spawn(:server, 0)
    me = self()
    _ = send(pid, {me, :add, 1})
    a = recv()
    _ = send(pid, {me, :add, 2})
    b = recv()
    _ = send(pid, {me, :get})
    c = recv()
    _ = send(pid, :stop)

    case a do
      {:ok, x} ->
        case b do
          {:ok, y} ->
            case c do
              {:ok, z} -> x + y + z
              _ -> 0
            end

          _ ->
            0
        end

      _ ->
        0
    end
  end
end
