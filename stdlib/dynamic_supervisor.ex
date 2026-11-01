defmodule DynamicSupervisor do
  # Teaching DynamicSupervisor: start_child + restart + stop shutdown.
  # start_link/0 → temporary; start_link/1 → :temporary | :permanent | :transient.
  # Kids: [{pid, mod, arg}]; on DOWN restart per policy (Supervisor.should_restart).
  # stop/1 exits children with :shutdown then stops the supervisor.
  # Skip: intensity windows, nested strategies, significant.

  @behaviour GenServer
  use GenServer

  def start_link do
    start_link(:temporary)
  end

  def start_link(restart) do
    GenServer.start_link(DynamicSupervisor, restart)
  end

  def start_child(sup, {mod, arg}) do
    GenServer.call(sup, {:start_child, mod, arg})
  end

  def stop(sup) do
    GenServer.call(sup, :stop)
  end

  @impl true
  def init(restart) do
    {:ok, {restart, []}}
  end

  @impl true
  def handle_call({:start_child, mod, arg}, _from, {restart, kids}) do
    pid = spawn(GenServer, :server, [mod, arg])
    _mref = monitor(pid)
    {:reply, pid, {restart, [{pid, mod, arg} | kids]}}
  end

  def handle_call(:stop, _from, {_restart, kids}) do
    _ = shutdown_all(kids)
    {:stop, :normal, :ok, {:temporary, []}}
  end

  @impl true
  def handle_cast(_msg, state) do
    {:noreply, state}
  end

  @impl true
  def handle_continue(_cont, state) do
    {:noreply, state}
  end

  def handle_info({:DOWN, _mref, :process, pid, reason}, {restart, kids}) do
    case take_kid(kids, pid) do
      {:ok, {mod, arg}, rest} ->
        if Supervisor.should_restart(restart, reason) do
          new_pid = spawn(GenServer, :server, [mod, arg])
          _ = monitor(new_pid)
          {:noreply, {restart, [{new_pid, mod, arg} | rest]}}
        else
          {:noreply, {restart, rest}}
        end

      :none ->
        {:noreply, {restart, kids}}
    end
  end

  def handle_info(_info, state) do
    {:noreply, state}
  end

  def take_kid(kids, pid) do
    case kids do
      [] ->
        :none

      [{p, mod, arg} | t] ->
        if p == pid do
          {:ok, {mod, arg}, t}
        else
          case take_kid(t, pid) do
            {:ok, found, rest} ->
              {:ok, found, [{p, mod, arg} | rest]}

            :none ->
              :none
          end
        end
    end
  end

  def shutdown_all(kids) do
    case kids do
      [] ->
        :ok

      [{pid, _m, _a} | t] ->
        _ = Process.exit(pid, :shutdown)
        shutdown_all(t)
    end
  end
end
