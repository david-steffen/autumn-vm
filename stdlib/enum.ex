defmodule Enum do
  # Teaching Enum on proper lists only (patterns + recursion; no new builtins).
  # API: map/2, reduce/3, filter/2, each/2.
  # Skip: streams, ranges, maps, into, sort, zip, …

  def map(list, fun) do
    case list do
      [] ->
        []

      [h | t] ->
        [fun.(h) | map(t, fun)]
    end
  end

  def reduce(list, acc, fun) do
    case list do
      [] ->
        acc

      [h | t] ->
        reduce(t, fun.(h, acc), fun)
    end
  end

  def filter(list, fun) do
    case list do
      [] ->
        []

      [h | t] ->
        if fun.(h) do
          [h | filter(t, fun)]
        else
          filter(t, fun)
        end
    end
  end

  def each(list, fun) do
    case list do
      [] ->
        :ok

      [h | t] ->
        _ = fun.(h)
        each(t, fun)
    end
  end
end
