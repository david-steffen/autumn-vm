defmodule Task.Supervisor do
  # Teaching Task.Supervisor: GenServer holder + Task.async from the caller.
  # `async/2` runs `Task.async` on the client so `await` delivers to the caller
  # (OTP-shaped ownership). The supervisor pid is retained for API shape.
  # Skip: start_child/2, async_nolink, restart strategies, DynamicSupervisor.

  @behaviour GenServer
  use GenServer

  def start_link do
    GenServer.start_link(Task.Supervisor, :ok)
  end

  def async(_sup, fun) do
    Task.async(fun)
  end

  @impl true
  def init(:ok) do
    {:ok, :ok}
  end

  @impl true
  def handle_call(_req, _from, state) do
    {:reply, :ok, state}
  end

  @impl true
  def handle_cast(_msg, state) do
    {:noreply, state}
  end

  @impl true
  def handle_continue(_cont, state) do
    {:noreply, state}
  end
end
