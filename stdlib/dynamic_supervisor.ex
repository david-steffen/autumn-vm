defmodule DynamicSupervisor do
  # Teaching DynamicSupervisor: GenServer that starts temporary children via MFA.
  # API: start_link/0, start_child/2 → pid | :error.
  # Children are temporary (no restart). Skip: strategies, intensity, shutdown.

  @behaviour GenServer
  use GenServer

  def start_link do
    GenServer.start_link(DynamicSupervisor, [])
  end

  def start_child(sup, {mod, arg}) do
    GenServer.call(sup, {:start_child, mod, arg})
  end

  @impl true
  def init(_) do
    {:ok, []}
  end

  @impl true
  def handle_call({:start_child, mod, arg}, _from, kids) do
    pid = spawn(GenServer, :server, [mod, arg])
    _mref = monitor(pid)
    {:reply, pid, [pid | kids]}
  end

  @impl true
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
