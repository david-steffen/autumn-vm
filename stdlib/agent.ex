defmodule Agent do
  # Teaching Agent on GenServer. State is an immediate or heap term;
  # client funs are applied with `f.(state)` (closures as messages).
  #
  # API: start/1, start_link/1, get/2, update/2, get_and_update/2, cast/2.
  # Skip: names, stop extras, :via.

  @behaviour GenServer
  use GenServer

  def start(initial) do
    GenServer.start(Agent, initial)
  end

  def start_link(initial) do
    GenServer.start_link(Agent, initial)
  end

  def get(pid, fun) do
    GenServer.call(pid, {:get, fun})
  end

  def update(pid, fun) do
    GenServer.call(pid, {:update, fun})
  end

  def get_and_update(pid, fun) do
    GenServer.call(pid, {:get_and_update, fun})
  end

  def cast(pid, fun) do
    GenServer.cast(pid, {:cast, fun})
  end

  @impl true
  def init(initial) do
    {:ok, initial}
  end

  @impl true
  def handle_call({:get, fun}, _from, state) do
    {:reply, fun.(state), state}
  end

  def handle_call({:update, fun}, _from, state) do
    {:reply, :ok, fun.(state)}
  end

  def handle_call({:get_and_update, fun}, _from, state) do
    {get, new_state} = fun.(state)
    {:reply, get, new_state}
  end

  @impl true
  def handle_cast({:cast, fun}, state) do
    {:noreply, fun.(state)}
  end

  @impl true
  def handle_continue(_cont, state) do
    {:noreply, state}
  end
end
