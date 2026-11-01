defmodule Task.Supervisor do
  # Teaching Task.Supervisor: tracks Task children; temporary (DOWN drops pid).
  # API: start_link/0, async/2, start_child/2.
  # Both async and start_child run Task.async on the **caller** so await delivers
  # there; start_child also casts {:track, pid} for bookkeeping.
  # Skip: async_nolink, permanent/transient restart, shutdown.

  @behaviour GenServer
  use GenServer

  def start_link do
    GenServer.start_link(Task.Supervisor, [])
  end

  def async(_sup, fun) do
    Task.async(fun)
  end

  def start_child(sup, fun) do
    task = Task.async(fun)
    {pid, _ref, _mref} = task
    _ = GenServer.cast(sup, {:track, pid})
    task
  end

  @impl true
  def init(_) do
    {:ok, []}
  end

  @impl true
  def handle_call(_req, _from, kids) do
    {:reply, :ok, kids}
  end

  @impl true
  def handle_cast({:track, pid}, kids) do
    _mref = monitor(pid)
    {:noreply, [pid | kids]}
  end

  def handle_cast(_msg, kids) do
    {:noreply, kids}
  end

  @impl true
  def handle_continue(_cont, kids) do
    {:noreply, kids}
  end

  def handle_info({:DOWN, _mref, :process, pid, _reason}, kids) do
    {:noreply, drop_pid(kids, pid)}
  end

  def handle_info(_info, kids) do
    {:noreply, kids}
  end

  def drop_pid(kids, pid) do
    case kids do
      [] ->
        []

      [h | t] ->
        if h == pid do
          t
        else
          [h | drop_pid(t, pid)]
        end
    end
  end
end
