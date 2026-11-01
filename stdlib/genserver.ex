defmodule GenServer do
  # Autumn stdlib GenServer (OTP-shaped, no `use GenServer` macro).
  #
  # Callback module `mod` is a runtime atom (bare alias `Counter` → `"Counter"`).
  # Required callbacks:
  #   init(arg) -> {:ok, state} | {:stop, reason}
  #   handle_call(req, {from, ref}, state) ->
  #     {:reply, reply, state} | {:noreply, state} |
  #     {:stop, reason, reply, state} | {:stop, reason, state}
  #   handle_cast(msg, state) ->
  #     {:noreply, state} | {:stop, reason, state}
  # Optional:
  #   handle_info(msg, state) -> {:noreply, state} | {:stop, reason, state}
  #   Missing handle_info/2 → catchable :undef rescued as {:noreply, state} (OTP-ish).
  #
  # Client: call/2, cast/2, reply/3. Dispatch uses IR v15 apply_mfa.
  # Non-{:call,:cast} mailbox messages are delivered to handle_info.

  def start(mod, init_arg) do
    spawn(GenServer, :server, [mod, init_arg])
  end

  def start_link(mod, init_arg) do
    spawn_link(GenServer, :server, [mod, init_arg])
  end

  def server(mod, init_arg) do
    case apply(mod, :init, [init_arg]) do
      {:ok, state} ->
        loop(mod, state)

      {:stop, _reason} ->
        :ok

      _ ->
        :ok
    end
  end

  def loop(mod, state) do
    receive do
      {:call, from, ref, req} ->
        case apply(mod, :handle_call, [req, {from, ref}, state]) do
          {:reply, reply, new_state} ->
            _ = reply(from, ref, reply)
            loop(mod, new_state)

          {:noreply, new_state} ->
            loop(mod, new_state)

          {:stop, _reason, reply, _new_state} ->
            _ = reply(from, ref, reply)
            :ok

          {:stop, _reason, _new_state} ->
            :ok
        end

      {:cast, msg} ->
        case apply(mod, :handle_cast, [msg, state]) do
          {:noreply, new_state} ->
            loop(mod, new_state)

          {:stop, _reason, _new_state} ->
            :ok
        end

      info ->
        case do_info(mod, info, state) do
          {:noreply, new_state} ->
            loop(mod, new_state)

          {:stop, _reason, _new_state} ->
            :ok
        end
    end
  end

  def do_info(mod, msg, state) do
    try do
      apply(mod, :handle_info, [msg, state])
    rescue
      :undef ->
        {:noreply, state}
    end
  end

  def call(pid, req) do
    me = self()
    ref = make_ref()
    mref = monitor(pid)
    _ = send(pid, {:call, me, ref, req})

    receive do
      {:reply, ^ref, reply} ->
        _ = demonitor(mref)
        reply

      {:DOWN, ^mref, :process, _pid, _reason} ->
        0
    after
      # Logical-clock budget must cover busy schedulers (e.g. supervisor restart).
      # Too small → client times out while the server still handles the call.
      500 ->
        _ = demonitor(mref)
        0
    end
  end

  def cast(pid, msg) do
    _ = send(pid, {:cast, msg})
    :ok
  end

  def reply(from, ref, value) do
    _ = send(from, {:reply, ref, value})
    :ok
  end
end
