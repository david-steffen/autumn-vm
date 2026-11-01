defmodule InfoCounter do
  def init(n) do
    {:ok, n}
  end

  def handle_call(:get, _from, state) do
    {:reply, state, state}
  end

  def handle_cast(_msg, state) do
    {:noreply, state}
  end

  def handle_info(:bump, state) do
    {:noreply, state + 1}
  end

  def handle_info({:add, x}, state) do
    {:noreply, state + x}
  end
end

defmodule Main do
  def main do
    pid = GenServer.start(InfoCounter, 0)
    _ = send(pid, :bump)
    _ = send(pid, {:add, 2})
    # FIFO mailbox: info msgs then call → get sees 3
    GenServer.call(pid, :get)
  end
end
