defmodule Main do
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

  # Client call: monitor + selective receive for reply or DOWN (timeout via after).
  def call_add(pid, x) do
    me = self()
    ref = monitor(pid)
    _ = send(pid, {me, :add, x})

    receive do
      {:ok, reply} ->
        _ = demonitor(ref)
        reply

      {:DOWN, _r, :process, _pid, _reason} ->
        0
    after
      50 -> 0
    end
  end

  def main do
    pid = spawn(:server, 0)
    a = call_add(pid, 1)
    b = call_add(pid, 2)
    me = self()
    ref = monitor(pid)
    _ = send(pid, {me, :get})

    c =
      receive do
        {:ok, reply} ->
          _ = demonitor(ref)
          reply

        {:DOWN, _r, :process, _pid, _reason} ->
          0
      after
        50 -> 0
      end

    _ = send(pid, :stop)
    a + b + c
  end
end
