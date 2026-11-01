defmodule Supervisor do
  # one_for_one / rest_for_one / one_for_all with a simple intensity window.
  # children :: [{Mod, arg} | {Mod, Fun, [arg]} | child_spec_map | internal_spec, ...]
  # child_spec_map :: %{id, start: {Mod, arg} | {Mod, Fun, [arg]},
  #                     restart?, shutdown?, significant?, type?}
  # Child records: {pid, mod, arg, restart, shutdown, significant, type}
  #   arg is the GenServer init arg, or {:mfa, fun, init_arg} for start MFA.
  #
  # restart: :permanent (default) | :temporary | :transient
  # shutdown: :brutal_kill | int | :infinity (infinity wait budget = 500 ticks)
  # significant: if true and child is dropped without restart → supervisor :shutdown
  # type: :worker | :supervisor — carried on child records; helpers
  #   `order_start/1` / `order_shutdown/1` document the teaching rule (workers
  #   then supervisors). Wired start/stop still use child-list order so existing
  #   strategies stay stable under the teaching Mix lowerer.
  #
  # Nested supervisors: start MFA `{Supervisor, :child_main, [children]}`
  # (`spawn_link` into `child_main` / `server`). Do not nest via `start_link`
  # (extra spawn). Other MFAs keep unlinked `spawn` + `run_mfa` trampoline.
  #
  # Intensity: at most `max_restarts` restarts inside a quiet period of 100
  # logical-clock ticks. Exceeding → supervisor exits `:shutdown`.
  #
  # Strategies (OTP-shaped, thin):
  #   :one_for_one  — restart only the dead child
  #   :rest_for_one — shut down and restart the dead child and every child
  #                   started after it
  #   :one_for_all  — shut down and restart every child

  def start_link(children) do
    start_link(children, :one_for_one, 3)
  end

  def start_link(children, max_restarts) do
    start_link(children, :one_for_one, max_restarts)
  end

  def start_link(children, strategy, max_restarts) do
    spawn_link(Supervisor, :server, [children, strategy, max_restarts])
  end

  # In-process entry for MFA children (nested supervisor under a parent).
  def child_main(children) do
    server(children, :one_for_one, 3)
  end

  def server(children, strategy, max_restarts) do
    # Start order: list order (OTP-shaped). Shutdown uses order_shutdown/1
    # (workers then supervisors). Reordering on start via filter_specs currently
    # miscompiles under teaching Mix for some child_spec maps — deferred.
    kids = start_all(children, [])
    loop(kids, 0, strategy, max_restarts)
  end

  def start_all(children, acc) do
    case children do
      [] ->
        acc

      [child | rest] ->
        case normalize_child(child) do
          {mod, arg, restart, shutdown, significant, type} ->
            pid = boot(mod, arg)
            _ = monitor(pid)
            rec = {pid, mod, arg, restart, shutdown, significant, type}
            start_all(rest, append(acc, [rec]))
        end
    end
  end

  # Stable: workers first, then supervisors (relative order preserved).
  def order_start(children) do
    append(filter_specs(children, :worker), filter_specs(children, :supervisor))
  end

  def order_shutdown(kids) do
    append(filter_kids(kids, :worker), filter_kids(kids, :supervisor))
  end

  def filter_specs(children, want) do
    case children do
      [] ->
        []

      [c | rest] ->
        case normalize_child(c) do
          {_m, _a, _r, _sh, _s, type} ->
            if type == want do
              [c | filter_specs(rest, want)]
            else
              filter_specs(rest, want)
            end
        end
    end
  end

  def filter_kids(kids, want) do
    case kids do
      [] ->
        []

      [kid | rest] ->
        case kid do
          {_p, _m, _a, _r, _sh, _s, type} ->
            if type == want do
              [kid | filter_kids(rest, want)]
            else
              filter_kids(rest, want)
            end
        end
    end
  end

  # GenServer.start vs teaching MFA trampoline (arity-1 args list only).
  # Nested supervisors (`:child_main`) must be the MFA process itself; use
  # `spawn_link` so the new process is scheduled under the parent supervisor.
  # Other MFAs keep unlinked `spawn` so a returning `start_link` trampoline
  # does not kill the supervisor.
  def boot(_mod, {:mfa, :child_main, a}) do
    spawn_link(Supervisor, :child_main, [a])
  end

  def boot(mod, {:mfa, fun, a}) do
    spawn(Supervisor, :run_mfa, [mod, fun, a])
  end

  def boot(mod, arg) do
    GenServer.start(mod, arg)
  end

  def run_mfa(mod, fun, arg) do
    apply(mod, fun, [arg])
  end

  def normalize_child({mod, arg}) do
    {mod, arg, :permanent, 10, false, :worker}
  end

  def normalize_child({mod, arg, restart, shutdown, significant}) do
    {mod, arg, restart, shutdown, significant, :worker}
  end

  def normalize_child({mod, arg, restart, shutdown, significant, type}) do
    {mod, arg, restart, shutdown, significant, type}
  end

  def normalize_child(spec) do
    case map_get(spec, :start) do
      {mod, fun, args} ->
        restart = default_restart(map_get(spec, :restart))
        shutdown = default_shutdown(map_get(spec, :shutdown))
        significant = default_significant(map_get(spec, :significant))
        type = default_type(map_get(spec, :type))

        case args do
          [a] ->
            {mod, {:mfa, fun, a}, restart, shutdown, significant, type}
        end

      {mod, arg} ->
        restart = default_restart(map_get(spec, :restart))
        shutdown = default_shutdown(map_get(spec, :shutdown))
        significant = default_significant(map_get(spec, :significant))
        type = default_type(map_get(spec, :type))
        {mod, arg, restart, shutdown, significant, type}
    end
  end

  def default_restart(nil) do
    :permanent
  end

  def default_restart(r) do
    r
  end

  def default_shutdown(nil) do
    # Short default so restart teardown waits do not race client `call` timeouts.
    10
  end

  def default_shutdown(s) do
    s
  end

  def default_significant(nil) do
    false
  end

  def default_significant(s) do
    s
  end

  def default_type(nil) do
    :worker
  end

  def default_type(t) do
    t
  end

  def loop(kids, intensity, strategy, max_restarts) do
    receive do
      {:DOWN, _ref, :process, pid, reason} ->
        case find_index(kids, pid, 0) do
          :none ->
            loop(kids, intensity, strategy, max_restarts)

          idx ->
            case nth(kids, idx) do
              {_p, _m, _a, restart, _sh, significant, _t} ->
                if should_restart(restart, reason) do
                  next_i = intensity + 1

                  if next_i > max_restarts do
                    :shutdown
                  else
                    kids2 = restart_for(strategy, kids, idx)
                    loop(kids2, next_i, strategy, max_restarts)
                  end
                else
                  kids2 = delete_at(kids, idx)

                  if significant do
                    :shutdown
                  else
                    loop(kids2, intensity, strategy, max_restarts)
                  end
                end
            end
        end
    after
      100 ->
        loop(kids, 0, strategy, max_restarts)
    end
  end

  def should_restart(:permanent, _reason) do
    true
  end

  def should_restart(:temporary, _reason) do
    false
  end

  def should_restart(:transient, reason) do
    if reason == :normal do
      false
    else
      if reason == :shutdown do
        false
      else
        true
      end
    end
  end

  def restart_for(:one_for_one, kids, idx) do
    case nth(kids, idx) do
      {_pid, mod, arg, restart, shutdown, significant, type} ->
        new_pid = boot(mod, arg)
        _ = monitor(new_pid)
        replace_at(kids, idx, {new_pid, mod, arg, restart, shutdown, significant, type})

      :none ->
        kids
    end
  end

  def restart_for(:rest_for_one, kids, idx) do
    prefix = take(kids, idx)
    specs = drop_specs(kids, idx)
    _ = shutdown_from(kids, idx)
    started = start_all(specs, [])
    append(prefix, started)
  end

  def restart_for(:one_for_all, kids, _idx) do
    specs = all_specs(kids)
    _ = shutdown_from(kids, 0)
    start_all(specs, [])
  end

  def append(left, right) do
    case left do
      [] ->
        right

      [h | t] ->
        [h | append(t, right)]
    end
  end

  def shutdown_from(kids, idx) do
    shutdown_list(drop(kids, idx))
  end

  def shutdown_list(kids) do
    # Prefer workers before supervisors when both appear (teaching). Kept as
    # list order for now — see order_shutdown/1 for the intended helper.
    case kids do
      [] ->
        :ok

      [child | rest] ->
        _ = shutdown_child(child)
        shutdown_list(rest)
    end
  end

  def shutdown_child({pid, _m, _a, _r, shutdown, _s, _t}) do
    case shutdown do
      :brutal_kill ->
        _ = Process.exit(pid, :kill)
        :ok

      :infinity ->
        _ = Process.exit(pid, :shutdown)

        receive do
        after
          500 ->
            :ok
        end

      n ->
        _ = Process.exit(pid, :shutdown)

        receive do
        after
          n ->
            :ok
        end
    end
  end

  def find_index(kids, pid, i) do
    case kids do
      [] ->
        :none

      [{p, _m, _a, _r, _sh, _s, _t} | rest] ->
        if p == pid do
          i
        else
          find_index(rest, pid, i + 1)
        end
    end
  end

  def nth(kids, i) do
    case kids do
      [] ->
        :none

      [h | t] ->
        if i == 0 do
          h
        else
          nth(t, i - 1)
        end
    end
  end

  def take(kids, n) do
    if n <= 0 do
      []
    else
      case kids do
        [] ->
          []

        [h | t] ->
          [h | take(t, n - 1)]
      end
    end
  end

  def drop(kids, n) do
    if n <= 0 do
      kids
    else
      case kids do
        [] ->
          []

        [_h | t] ->
          drop(t, n - 1)
      end
    end
  end

  def delete_at(kids, i) do
    case kids do
      [] ->
        []

      [h | t] ->
        if i == 0 do
          t
        else
          [h | delete_at(t, i - 1)]
        end
    end
  end

  def drop_specs(kids, n) do
    specs_only(drop(kids, n))
  end

  def specs_only(kids) do
    case kids do
      [] ->
        []

      [{_p, m, a, r, sh, s, t} | rest] ->
        [{m, a, r, sh, s, t} | specs_only(rest)]
    end
  end

  def all_specs(kids) do
    specs_only(kids)
  end

  def replace_at(kids, i, new) do
    case kids do
      [] ->
        []

      [h | t] ->
        if i == 0 do
          [new | t]
        else
          [h | replace_at(t, i - 1, new)]
        end
    end
  end
end
