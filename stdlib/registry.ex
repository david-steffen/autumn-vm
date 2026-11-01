defmodule Registry do
  # Teaching unique Registry on GenServer + ETS :set.
  # register/lookup/unregister; auto-drop on DOWN (pid from message).
  # Skip: :via, partitions, :duplicate, named tables.

  @behaviour GenServer
  use GenServer

  def start_link(keys) do
    GenServer.start_link(Registry, keys)
  end

  def register(reg, key, pid) do
    GenServer.call(reg, {:register, key, pid})
  end

  def lookup(reg, key) do
    GenServer.call(reg, {:lookup, key})
  end

  def unregister(reg, key) do
    GenServer.call(reg, {:unregister, key})
  end

  @impl true
  def init(:unique) do
    tab = Ets.new()
    {:ok, tab}
  end

  def init(_) do
    {:stop, :badarg}
  end

  @impl true
  def handle_call({:register, key, pid}, _from, tab) do
    case Ets.lookup(tab, key) do
      [] ->
        _mref = monitor(pid)
        _ = Ets.insert(tab, key, pid)
        {:reply, :ok, tab}

      _ ->
        {:reply, :error, tab}
    end
  end

  def handle_call({:lookup, key}, _from, tab) do
    {:reply, Ets.lookup(tab, key), tab}
  end

  def handle_call({:unregister, key}, _from, tab) do
    _ = Ets.delete(tab, key)
    {:reply, :ok, tab}
  end

  @impl true
  def handle_cast(_msg, tab) do
    {:noreply, tab}
  end

  def handle_info({:DOWN, _mref, :process, pid, _reason}, tab) do
    _ = drop_pid(tab, Ets.first(tab), pid)
    {:noreply, tab}
  end

  def handle_info(_info, tab) do
    {:noreply, tab}
  end

  @impl true
  def handle_continue(_cont, tab) do
    {:noreply, tab}
  end

  def drop_pid(_tab, :"$end_of_table", _pid) do
    :ok
  end

  def drop_pid(tab, key, pid) do
    next = Ets.next(tab, key)
    vs = Ets.lookup(tab, key)

    _ =
      case vs do
        [p] ->
          if p == pid do
            Ets.delete(tab, key)
          else
            :ok
          end

        _ ->
          :ok
      end

    drop_pid(tab, next, pid)
  end
end
