defmodule Supervisor do
  # Thin one_for_one supervisor (no intensity window / rest_for_one / one_for_all).
  # children :: [{Mod, arg}, ...] where Mod is a GenServer callback module atom.

  def start_link(children) do
    spawn_link(Supervisor, :server, [children])
  end

  def server(children) do
    kids = start_all(children, [])
    loop(kids)
  end

  def start_all(children, acc) do
    case children do
      [] ->
        acc

      [{mod, arg} | rest] ->
        pid = GenServer.start(mod, arg)
        _ = monitor(pid)
        start_all(rest, [{pid, mod, arg} | acc])
    end
  end

  def loop(kids) do
    receive do
      {:DOWN, _ref, :process, pid, _reason} ->
        case find_child(kids, pid) do
          {mod, arg} ->
            new_pid = GenServer.start(mod, arg)
            _ = monitor(new_pid)
            loop(replace_child(kids, pid, new_pid, mod, arg))

          :none ->
            loop(kids)
        end
    end
  end

  def find_child(kids, pid) do
    case kids do
      [] ->
        :none

      [{p, mod, arg} | rest] ->
        if p == pid do
          {mod, arg}
        else
          find_child(rest, pid)
        end
    end
  end

  def replace_child(kids, old_pid, new_pid, mod, arg) do
    case kids do
      [] ->
        []

      [{p, m, a} | rest] ->
        if p == old_pid do
          [{new_pid, mod, arg} | rest]
        else
          [{p, m, a} | replace_child(rest, old_pid, new_pid, mod, arg)]
        end
    end
  end
end
