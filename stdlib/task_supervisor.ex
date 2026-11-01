defmodule Task.Supervisor do
  # Teaching Task.Supervisor: async/start_child + optional restart + stop.
  # start_link/0 → temporary; start_link/1 → :temporary | :permanent | :transient.
  # async/2 and start_child/2 run Task.async on the **caller** (await delivers there);
  # start_child also tracks {pid, fun} for restart on abnormal DOWN.
  # stop/1 exits tracked children then stops.
  # Skip: async_nolink, intensity, significant.

  @behaviour GenServer
  use GenServer

  def start_link do
    start_link(:temporary)
  end

  def start_link(restart) do
    GenServer.start_link(Task.Supervisor, restart)
  end

  def async(_sup, fun) do
    Task.async(fun)
  end

  def start_child(sup, fun) do
    task = Task.async(fun)
    {pid, _ref, _mref} = task
    _ = GenServer.cast(sup, {:track, pid, fun})
    task
  end

  def stop(sup) do
    GenServer.call(sup, :stop)
  end

  @impl true
  def init(restart) do
    {:ok, {restart, []}}
  end

  @impl true
  def handle_call(:stop, _from, {_restart, kids}) do
    _ = shutdown_all(kids)
    {:stop, :normal, :ok, {:temporary, []}}
  end

  def handle_call(_req, _from, state) do
    {:reply, :ok, state}
  end

  @impl true
  def handle_cast({:track, pid, fun}, {restart, kids}) do
    _mref = monitor(pid)
    {:noreply, {restart, [{pid, fun} | kids]}}
  end

  def handle_cast(_msg, state) do
    {:noreply, state}
  end

  @impl true
  def handle_continue(_cont, state) do
    {:noreply, state}
  end

  def handle_info({:DOWN, _mref, :process, pid, reason}, {restart, kids}) do
    case take_kid(kids, pid) do
      {:ok, fun, rest} ->
        if Supervisor.should_restart(restart, reason) do
          {new_pid, _ref, _mref} = Task.async(fun)
          _ = monitor(new_pid)
          {:noreply, {restart, [{new_pid, fun} | rest]}}
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

      [{p, fun} | t] ->
        if p == pid do
          {:ok, fun, t}
        else
          case take_kid(t, pid) do
            {:ok, found, rest} ->
              {:ok, found, [{p, fun} | rest]}

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

      [{pid, _fun} | t] ->
        _ = Process.exit(pid, :shutdown)
        shutdown_all(t)
    end
  end
end
