defmodule Supervisor do
  # one_for_one / rest_for_one / one_for_all with a simple intensity window.
  # children :: [{Mod, arg}, ...] in start order (Mod = GenServer callback atom).
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

  def server(children, strategy, max_restarts) do
    kids = start_all(children, [])
    loop(kids, 0, strategy, max_restarts)
  end

  def start_all(children, acc) do
    case children do
      [] ->
        acc

      [{mod, arg} | rest] ->
        pid = GenServer.start(mod, arg)
        _ = monitor(pid)
        start_all(rest, append(acc, [{pid, mod, arg}]))
    end
  end

  def loop(kids, intensity, strategy, max_restarts) do
    receive do
      {:DOWN, _ref, :process, pid, _reason} ->
        case find_index(kids, pid, 0) do
          :none ->
            loop(kids, intensity, strategy, max_restarts)

          idx ->
            next_i = intensity + 1

            if next_i > max_restarts do
              :shutdown
            else
              kids2 = restart_for(strategy, kids, idx)
              loop(kids2, next_i, strategy, max_restarts)
            end
        end
    after
      100 ->
        loop(kids, 0, strategy, max_restarts)
    end
  end

  def restart_for(:one_for_one, kids, idx) do
    case nth(kids, idx) do
      {pid, mod, arg} ->
        new_pid = GenServer.start(mod, arg)
        _ = monitor(new_pid)
        replace_at(kids, idx, {new_pid, mod, arg})

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
    case drop(kids, idx) do
      [] ->
        :ok

      [{pid, _m, _a} | rest] ->
        _ = Process.exit(pid, :shutdown)
        shutdown_list(rest)
    end
  end

  def shutdown_list(kids) do
    case kids do
      [] ->
        :ok

      [{pid, _m, _a} | rest] ->
        _ = Process.exit(pid, :shutdown)
        shutdown_list(rest)
    end
  end

  def find_index(kids, pid, i) do
    case kids do
      [] ->
        :none

      [{p, _m, _a} | rest] ->
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

  def drop_specs(kids, n) do
    case drop(kids, n) do
      [] ->
        []

      [{_p, m, a} | rest] ->
        [{m, a} | specs_only(rest)]
    end
  end

  def specs_only(kids) do
    case kids do
      [] ->
        []

      [{_p, m, a} | rest] ->
        [{m, a} | specs_only(rest)]
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
