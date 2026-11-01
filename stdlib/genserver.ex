defmodule GenServer do
  # Autumn stdlib GenServer (OTP-shaped teaching subset).
  #
  # Callback module `mod` is a runtime atom (bare alias `Counter` → `"Counter"`).
  # With `use GenServer` or `@behaviour GenServer`, Mix requires:
  #   init/1, handle_call/3, handle_cast/2, handle_continue/2
  # Optional: handle_info/2 (missing → :undef rescued as {:noreply, state}).
  #
  # Returns (teaching):
  #   init -> {:ok, state} | {:ok, state, {:continue, c}} | {:ok, state, :hibernate} |
  #           {:stop, reason}
  #   handle_call -> {:reply, reply, state} | {:noreply, state} |
  #                  … + {:continue, c} | :hibernate tails |
  #                  {:stop, reason, reply, state} | {:stop, reason, state}
  #   handle_cast / handle_info / handle_continue ->
  #                  {:noreply, state} | {:noreply, state, {:continue, c}} |
  #                  {:noreply, state, :hibernate} | {:stop, reason, state}
  # :hibernate → Process.hibernate/0 (GC) then loop (still ends in receive).
  #
  # Tuple return patterns rely on Mix arity checks (tuple_size before get_tuple_elem).
  #
  # `use GenServer` options: restart:, shutdown:, significant:, type: → child_spec keys.
 # Client: call/2, cast/2, reply/3. Dispatch uses apply_mfa.

  def child_spec({mod, arg}) do
    m = map_put(%{}, :id, mod)
    map_put(m, :start, {mod, arg})
  end

  def start(mod, init_arg) do
    spawn(GenServer, :server, [mod, init_arg])
  end

  def start_link(mod, init_arg) do
    spawn_link(GenServer, :server, [mod, init_arg])
  end

  def server(mod, init_arg) do
    case apply(mod, :init, [init_arg]) do
      {:ok, state, extra} ->
        after_ok(mod, state, extra)

      {:ok, state} ->
        loop(mod, state)

      {:stop, reason} ->
        reason

      _ ->
        :ok
    end
  end

  def after_ok(mod, state, {:continue, cont}) do
    continue(mod, cont, state)
  end

  def after_ok(mod, state, :hibernate) do
    _ = Process.hibernate()
    loop(mod, state)
  end

  def after_ok(mod, state, _) do
    loop(mod, state)
  end

  def continue(mod, cont, state) do
    case do_continue(mod, cont, state) do
      {:noreply, new_state, extra} ->
        after_noreply(mod, new_state, extra)

      {:noreply, new_state} ->
        loop(mod, new_state)

      {:stop, reason, _new_state} ->
        reason

      _ ->
        :undef
    end
  end

  def do_continue(mod, cont, state) do
    try do
      apply(mod, :handle_continue, [cont, state])
    rescue
      :undef ->
        {:stop, :undef, state}
    end
  end

  def loop(mod, state) do
    receive do
      {:call, from, ref, req} ->
        case apply(mod, :handle_call, [req, {from, ref}, state]) do
          {:reply, reply, new_state, extra} ->
            _ = reply(from, ref, reply)
            after_noreply(mod, new_state, extra)

          {:stop, reason, reply, _new_state} ->
            _ = reply(from, ref, reply)
            reason

          {:reply, reply, new_state} ->
            _ = reply(from, ref, reply)
            loop(mod, new_state)

          {:noreply, new_state, extra} ->
            after_noreply(mod, new_state, extra)

          {:stop, reason, _new_state} ->
            reason

          {:noreply, new_state} ->
            loop(mod, new_state)
        end

      {:cast, msg} ->
        case apply(mod, :handle_cast, [msg, state]) do
          {:noreply, new_state, extra} ->
            after_noreply(mod, new_state, extra)

          {:stop, reason, _new_state} ->
            reason

          {:noreply, new_state} ->
            loop(mod, new_state)
        end

      info ->
        case do_info(mod, info, state) do
          {:noreply, new_state, extra} ->
            after_noreply(mod, new_state, extra)

          {:stop, reason, _new_state} ->
            reason

          {:noreply, new_state} ->
            loop(mod, new_state)
        end
    end
  end

  def after_noreply(mod, state, {:continue, cont}) do
    continue(mod, cont, state)
  end

  def after_noreply(mod, state, :hibernate) do
    _ = Process.hibernate()
    loop(mod, state)
  end

  def after_noreply(mod, state, _) do
    loop(mod, state)
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
