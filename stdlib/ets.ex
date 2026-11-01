defmodule Ets do
  # Teaching ETS: set / bag / duplicate_bag, named tables, list lookup,
  # match_object + select (empty-guard match-specs).

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

  def match_object(tab, pattern) do
    ets_match_object(tab, pattern)
  end

  def select(tab, match_spec) do
    ets_select(tab, match_spec)
  end
end
