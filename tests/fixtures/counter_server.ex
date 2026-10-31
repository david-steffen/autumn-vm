defmodule Main do
  # Messages are sequenced atoms/ints/pids (no dynamic tuples yet).
  def server(n) do
    receive do
      :add ->
        receive do
          x ->
            receive do
              from ->
                _ = send(from, n + x)
                server(n + x)
            end
        end

      :get ->
        receive do
          from ->
            _ = send(from, n)
            server(n)
        end

      :stop ->
        :ok
    end
  end

  def main do
    pid = spawn(:server, 0)
    me = self()
    _ = send(pid, :add)
    _ = send(pid, 1)
    _ = send(pid, me)
    a = recv()
    _ = send(pid, :add)
    _ = send(pid, 2)
    _ = send(pid, me)
    b = recv()
    _ = send(pid, :get)
    _ = send(pid, me)
    c = recv()
    _ = send(pid, :stop)
    a + b + c
  end
end
