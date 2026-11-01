defmodule Ets do
  # Teaching ETS: set / bag / duplicate_bag / ordered_set, named tables,
  # list lookup, match_object + select (teaching guards), delete_object, heir,
  # first/next walk, give_away (IR v21).

  def new do
    ets_new()
  end

  def new(name, type) do
    ets_new(name, type)
  end

  def insert(tab, key, val) do
    ets_insert(tab, key, val)
  end

  def lookup(tab, key) do
    ets_lookup(tab, key)
  end

  def delete(tab, key) do
    ets_delete(tab, key)
  end

  def delete_object(tab, object) do
    ets_delete_object(tab, object)
  end

  def match_object(tab, pattern) do
    ets_match_object(tab, pattern)
  end

  def select(tab, match_spec) do
    ets_select(tab, match_spec)
  end

  def heir(tab, heir) do
    ets_heir(tab, heir)
  end

  def first(tab) do
    ets_first(tab)
  end

  def next(tab, key) do
    ets_next(tab, key)
  end

  def give_away(tab, pid, data) do
    ets_give_away(tab, pid, data)
  end
end
