defmodule AutumnCompiler.Lower do
  @moduledoc false

  @builtins %{
    {:+, 2} => "+/2",
    {:-, 2} => "-/2",
    {:*, 2} => "*/2",
    {:==, 2} => "==/2",
    {:<, 2} => "</2",
    {:>, 2} => ">/2",
    {:<=, 2} => "<=/2",
    {:>=, 2} => ">=/2",
    {:tuple_size, 1} => "tuple_size/1",
    {:list_size, 1} => "list_size/1",
    {:elem, 2} => "elem/2",
    {:map_size, 1} => "map_size/1",
    {:map_get, 2} => "map_get/2",
    {:map_put, 3} => "map_put/3",
    {:self, 0} => "self/0",
    {:make_ref, 0} => "make_ref/0",
    {:<>, 2} => "<>/2",
    {:bit_size, 1} => "bit_size/1",
    {:bs_get_integer, 2} => "bs_get_integer/2",
    {:bs_drop, 2} => "bs_drop/2",
    {:cons, 2} => "cons/2",
    {:ets_new, 0} => "ets_new/0",
    {:ets_new, 2} => "ets_new/2",
    {:ets_insert, 3} => "ets_insert/3",
    {:ets_lookup, 2} => "ets_lookup/2",
    {:ets_delete, 2} => "ets_delete/2",
    {:ets_delete_object, 2} => "ets_delete_object/2",
    {:ets_match_object, 2} => "ets_match_object/2",
    {:ets_select, 2} => "ets_select/2",
    {:ets_heir, 2} => "ets_heir/2",
    {:ets_first, 1} => "ets_first/1",
    {:ets_next, 2} => "ets_next/2",
    {:ets_give_away, 3} => "ets_give_away/3"
  }

  @type_guards %{
    is_integer: "int",
    is_float: "float",
    is_atom: "atom",
    is_boolean: "bool",
    is_list: "list",
    is_tuple: "tuple",
    is_map: "map",
    is_pid: "pid",
    is_reference: "ref",
    is_binary: "binary",
    is_bitstring: "bitstring",
    is_nil: "nil",
    is_function: "fun"
  }

  @doc """
  Lower a single `defmodule` or a `__block__` of them into a loadable IR image.
  """
  def lower(ast) do
    with {:ok, code_modules} <- lower_modules(ast) do
      assemble(code_modules)
    end
  end

  @doc """
  Lower one or more `defmodule` forms into code-module maps
  (`%{"name" => …, "functions" => …}`), without requiring `main/0`.
  """
  def lower_modules({:__block__, _, forms}) when is_list(forms) do
    Enum.reduce_while(forms, {:ok, []}, fn
      {:defmodule, _, _} = mod, {:ok, acc} ->
        case lower_code_module(mod) do
          {:ok, cm} -> {:cont, {:ok, acc ++ [cm]}}
          {:error, _} = err -> {:halt, err}
        end

      other, _ ->
        {:halt, {:error, "expected defmodule, got: #{Macro.to_string(other)}"}}
    end)
  end

  def lower_modules({:defmodule, _, _} = mod) do
    with {:ok, cm} <- lower_code_module(mod), do: {:ok, [cm]}
  end

  def lower_modules(_) do
    {:error, "expected defmodule (or a block of defmodules) at the top level"}
  end

  @doc """
  Assemble code modules into an IR image (`format` is always `1`).
  Always emits `"modules"` (one or more named code modules).
  """
  def assemble(code_modules, entry \\ nil) do
    code_modules = List.wrap(code_modules)

    with :ok <- validate_code_modules(code_modules),
         {:ok, entry} <- resolve_entry(code_modules, entry) do
      {:ok,
       %{
         "format" => 1,
         "entry" => entry,
         "modules" => code_modules
       }}
    end
  end

  defp lower_code_module({:defmodule, _meta, [alias_ast, [do: body]]}) do
    mod_name = module_name(alias_ast)
    reset_lifted!(mod_name)

    with {:ok, defs} <- expand_module_body(flatten_block(body), mod_name),
         {:ok, groups} <- group_defs(defs),
         {:ok, funs} <- lower_groups(groups, mod_name) do
      lifted = take_lifted!()

      funs =
        (funs ++ lifted)
        |> Enum.map(&resolve_locals(&1, mod_name))

      {:ok, %{"name" => mod_name, "functions" => funs}}
    end
  end

  defp lower_code_module(_), do: {:error, "expected a defmodule"}

  # Teaching `use GenServer` / `@behaviour` / `@impl` (no general macro engine).
  defp expand_module_body(stmts, mod_name) do
    init = %{defs: [], used?: false, gs_behaviour?: false, use_opts: []}

    case Enum.reduce_while(stmts, {:ok, init}, fn stmt, {:ok, st} ->
           expand_module_stmt(stmt, st, mod_name)
         end) do
      {:ok, st} ->
        with :ok <- maybe_require_genserver_callbacks(st, mod_name) do
          finalize_expanded_defs(st, mod_name)
        end

      {:error, _} = err ->
        err
    end
  end

  defp expand_module_stmt({:use, _, [{:__aliases__, _, [:GenServer]}]}, st, mod_name) do
    if st.used? do
      {:halt, {:error, "duplicate use GenServer in module #{mod_name}"}}
    else
      {:cont, {:ok, %{st | used?: true}}}
    end
  end

  defp expand_module_stmt({:use, _, [{:__aliases__, _, [:GenServer]}, opts]}, st, mod_name) do
    if st.used? do
      {:halt, {:error, "duplicate use GenServer in module #{mod_name}"}}
    else
      case parse_use_genserver_opts(opts) do
        {:ok, use_opts} ->
          {:cont, {:ok, %{st | used?: true, use_opts: use_opts}}}

        {:error, _} = err ->
          {:halt, err}
      end
    end
  end

  defp expand_module_stmt({:use, _, _} = stmt, _st, _mod_name) do
    {:halt, {:error, "unsupported use: #{Macro.to_string(stmt)} (only use GenServer)"}}
  end

  defp expand_module_stmt(
         {:@, _, [{:behaviour, _, [{:__aliases__, _, parts}]}]},
         st,
         _mod_name
       )
       when is_list(parts) and parts != [] do
    gs? = parts == [:GenServer]
    {:cont, {:ok, %{st | gs_behaviour?: st.gs_behaviour? or gs?}}}
  end

  defp expand_module_stmt({:@, _, [{:behaviour, _, _}]} = stmt, _st, _mod_name) do
    {:halt, {:error, "unsupported @behaviour: #{Macro.to_string(stmt)}"}}
  end

  defp expand_module_stmt({:@, _, [{:impl, _, [flag]}]}, st, _mod_name)
       when flag in [true, false] do
    {:cont, {:ok, st}}
  end

  defp expand_module_stmt({:@, _, [{:impl, _, [{:__aliases__, _, [:GenServer]}]}]}, st, _mod_name) do
    {:cont, {:ok, st}}
  end

  defp expand_module_stmt({:@, _, [{:impl, _, _}]} = stmt, _st, _mod_name) do
    {:halt, {:error, "unsupported @impl: #{Macro.to_string(stmt)}"}}
  end

  defp expand_module_stmt({:@, _, _} = stmt, _st, _mod_name) do
    {:halt, {:error, "unsupported module attribute: #{Macro.to_string(stmt)}"}}
  end

  defp expand_module_stmt(other, st, _mod_name) do
    {:cont, {:ok, %{st | defs: st.defs ++ [other]}}}
  end

  defp parse_use_genserver_opts(opts) when is_list(opts) do
    Enum.reduce_while(opts, {:ok, []}, fn
      {:restart, v}, {:ok, acc} when v in [:permanent, :temporary, :transient] ->
        {:cont, {:ok, Keyword.put(acc, :restart, v)}}

      {:shutdown, :brutal_kill}, {:ok, acc} ->
        {:cont, {:ok, Keyword.put(acc, :shutdown, :brutal_kill)}}

      {:shutdown, :infinity}, {:ok, acc} ->
        {:cont, {:ok, Keyword.put(acc, :shutdown, :infinity)}}

      {:shutdown, n}, {:ok, acc} when is_integer(n) and n >= 0 ->
        {:cont, {:ok, Keyword.put(acc, :shutdown, n)}}

      {:significant, v}, {:ok, acc} when is_boolean(v) ->
        {:cont, {:ok, Keyword.put(acc, :significant, v)}}

      {:type, v}, {:ok, acc} when v in [:worker, :supervisor] ->
        {:cont, {:ok, Keyword.put(acc, :type, v)}}

      other, _ ->
        {:halt, {:error, "unsupported use GenServer option: #{Macro.to_string(other)}"}}
    end)
  end

  defp parse_use_genserver_opts(other) do
    {:error, "use GenServer options must be a keyword list, got: #{Macro.to_string(other)}"}
  end

  defp maybe_require_genserver_callbacks(%{used?: false, gs_behaviour?: false}, _mod_name),
    do: :ok

  defp maybe_require_genserver_callbacks(%{defs: defs}, mod_name) do
    required = [{:init, 1}, {:handle_call, 3}, {:handle_cast, 2}, {:handle_continue, 2}]

    case Enum.find(required, fn {name, arity} -> not has_def?(defs, name, arity) end) do
      nil ->
        :ok

      {name, arity} ->
        {:error, "module #{mod_name} missing #{name}/#{arity} (required by GenServer behaviour)"}
    end
  end

  defp finalize_expanded_defs(%{defs: defs, used?: false}, _mod_name), do: {:ok, defs}

  defp finalize_expanded_defs(%{defs: defs, used?: true, use_opts: opts}, mod_name) do
    if has_def?(defs, :child_spec, 1) do
      {:ok, defs}
    else
      {:ok, defs ++ [injected_child_spec_def(mod_name, opts)]}
    end
  end

  defp has_def?(defs, name, arity) do
    Enum.any?(defs, fn
      {:def, _, [{:when, _, [head, _]}, _]} -> def_head_match?(head, name, arity)
      {:def, _, [head, _]} -> def_head_match?(head, name, arity)
      _ -> false
    end)
  end

  defp def_head_match?({fun, _, params}, name, arity)
       when is_atom(fun) and is_list(params),
       do: fun == name and length(params) == arity

  defp def_head_match?({fun, _, nil}, name, 0) when is_atom(fun), do: fun == name
  defp def_head_match?(_, _, _), do: false

  # Build AST by hand: `quote do {unquote(:Atom), arg} end` becomes a keyword
  # list when passed as a sole call arg; use explicit `{:{}, …}` tuple.
  defp injected_child_spec_def(mod_name, opts) do
    mod_atom = String.to_atom(mod_name)
    arg = {:arg, [], nil}
    pair = {:{}, [], [mod_atom, arg]}
    m = {:m, [], nil}

    base =
      {:=, [],
       [
         m,
         {{:., [], [{:__aliases__, [alias: false], [:GenServer]}, :child_spec]}, [], [pair]}
       ]}

    puts =
      opts
      |> Enum.reduce([], fn {key, val}, acc ->
        acc ++
          [
            {:=, [],
             [
               m,
               {:map_put, [], [m, key, val]}
             ]}
          ]
      end)

    body =
      case puts do
        [] ->
          {{:., [], [{:__aliases__, [alias: false], [:GenServer]}, :child_spec]}, [], [pair]}

        _ ->
          {:__block__, [], [base | puts] ++ [m]}
      end

    {:def, [], [{:child_spec, [], [arg]}, [do: body]]}
  end

  defp validate_code_modules([]) do
    {:error, "no modules to assemble"}
  end

  defp validate_code_modules(cms) do
    names = Enum.map(cms, & &1["name"])

    cond do
      length(Enum.uniq(names)) != length(names) ->
        {:error, "duplicate module names: #{inspect(names)}"}

      true ->
        fun_names = Enum.flat_map(cms, fn cm -> Enum.map(cm["functions"], & &1["name"]) end)

        if length(Enum.uniq(fun_names)) != length(fun_names) do
          {:error, "duplicate function MFAs across modules"}
        else
          :ok
        end
    end
  end

  defp resolve_entry(_cms, entry) when is_binary(entry), do: {:ok, entry}

  defp resolve_entry(cms, nil) do
    mains =
      for cm <- cms,
          f <- cm["functions"],
          String.ends_with?(f["name"], ".main/0"),
          do: f["name"]

    case mains do
      [one] ->
        {:ok, one}

      [] ->
        # Library image (e.g. for Code.load_file): use the first MFA as a dummy entry.
        case Enum.flat_map(cms, & &1["functions"]) do
          [f | _] -> {:ok, f["name"]}
          [] -> {:error, "no main/0 entry found in assembled modules"}
        end

      many ->
        if "Main.main/0" in many do
          {:ok, "Main.main/0"}
        else
          {:error, "ambiguous entry (multiple main/0): #{inspect(many)}"}
        end
    end
  end

  defp reset_lifted!(mod_name) do
    Process.put({:autumn, :mod}, mod_name)
    Process.put({:autumn, :fn_id}, 0)
    Process.put({:autumn, :lifted}, [])
    Process.put({:autumn, :list_append}, false)
  end

  defp take_lifted! do
    lifted = Process.get({:autumn, :lifted}, [])
    Process.put({:autumn, :lifted}, [])
    lifted
  end

  defp push_lifted!(fun) do
    Process.put({:autumn, :lifted}, Process.get({:autumn, :lifted}, []) ++ [fun])
  end

  defp next_fn_id! do
    id = Process.get({:autumn, :fn_id}, 0)
    Process.put({:autumn, :fn_id}, id + 1)
    id
  end

  defp module_name({:__aliases__, _, parts}), do: Enum.map_join(parts, ".", &to_string/1)

  defp flatten_block({:__block__, _, stmts}), do: stmts
  defp flatten_block(other), do: [other]

  # Group defs by {name, arity}, preserving first-seen order.
  # Clause shape: {params, body, guard | nil}
  defp group_defs(defs) do
    Enum.reduce_while(defs, {:ok, [], %{}}, fn def_ast, {:ok, order, map} ->
      case take_def_clause(def_ast) do
        {:ok, name, params, body, guard} ->
          key = {name, length(params)}
          clause = {params, body, guard}

          {order, map} =
            if Map.has_key?(map, key) do
              {order, Map.update!(map, key, &(&1 ++ [clause]))}
            else
              {order ++ [key], Map.put(map, key, [clause])}
            end

          {:cont, {:ok, order, map}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, order, map} ->
        {:ok, Enum.map(order, fn key -> {key, Map.fetch!(map, key)} end)}

      {:error, _} = err ->
        err
    end
  end

  defp take_def_clause({:def, _meta, [{:when, _, [head, guard]}, [do: body]]}) do
    with {:ok, name, params} <- parse_head_patterns(head) do
      {:ok, name, params, body, guard}
    end
  end

  defp take_def_clause({:def, _meta, [head, [do: body]]}) do
    with {:ok, name, params} <- parse_head_patterns(head) do
      {:ok, name, params, body, nil}
    end
  end

  defp take_def_clause({:def, _, _}),
    do: {:error, "unsupported def form (defaults not allowed)"}

  defp take_def_clause(other),
    do: {:error, "unsupported module form: #{Macro.to_string(other)}"}

  defp lower_groups(groups, mod_name) do
    Enum.reduce_while(groups, {:ok, []}, fn {{name, arity}, clauses}, {:ok, acc} ->
      case lower_grouped_def(name, arity, clauses, mod_name) do
        {:ok, fun} -> {:cont, {:ok, acc ++ [fun]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp lower_grouped_def(name, arity, [{params, body, nil}], mod_name) do
    if all_var_params?(params) do
      names = Enum.map(params, fn {n, _, nil} -> n end)

      with {:ok, code, locals} <- lower_body(body, names) do
        {:ok,
         %{
           "name" => "#{mod_name}.#{name}/#{arity}",
           "arity" => arity,
           "locals" => locals,
           "code" => code
         }}
      end
    else
      lower_multi_clause(name, arity, [{params, body, nil}], mod_name)
    end
  end

  defp lower_grouped_def(name, arity, clauses, mod_name) do
    lower_multi_clause(name, arity, clauses, mod_name)
  end

  defp lower_multi_clause(_name, 0, _clauses, _mod_name),
    do: {:error, "multi-clause arity 0 not supported"}

  defp lower_multi_clause(name, arity, clauses, mod_name) when arity > 0 do
    params = Enum.map(0..(arity - 1), fn i -> String.to_atom("a#{i}") end)

    scrut =
      case arity do
        1 -> {hd(params), [], nil}
        _ -> {:{}, [], Enum.map(params, &{&1, [], nil})}
      end

    case_clauses =
      Enum.map(clauses, fn {pats, body, guard} ->
        pat =
          case arity do
            1 -> hd(pats)
            _ -> {:{}, [], pats}
          end

        lhs = if guard == nil, do: [pat], else: [{:when, [], [pat, guard]}]
        {:->, [], [lhs, body]}
      end)

    body = {:case, [], [scrut, [do: case_clauses]]}

    with {:ok, code, locals} <- lower_body(body, params) do
      {:ok,
       %{
         "name" => "#{mod_name}.#{name}/#{arity}",
         "arity" => arity,
         "locals" => locals,
         "code" => code
       }}
    end
  end

  defp all_var_params?(params) do
    Enum.all?(params, fn
      {name, _, nil} when is_atom(name) -> true
      _ -> false
    end)
  end

  defp parse_head_patterns({name, _meta, nil}) when is_atom(name), do: {:ok, name, []}

  defp parse_head_patterns({name, _meta, params}) when is_atom(name) and is_list(params) do
    {:ok, name, params}
  end

  defp parse_head_patterns(_), do: {:error, "unsupported function head"}

  defp lower_body(body, params) do
    env =
      params
      |> Enum.with_index()
      |> Map.new(fn {name, i} -> {name, i} end)

    next = length(params)

    with {:ok, code, _env, next, result_reg} <- expr(body, env, next, []) do
      {:ok, code ++ [%{"op" => "return", "reg" => result_reg}], next}
    end
  end

  # Discard: _ = expr — evaluate for effects, keep RHS value (Elixir-like).
  defp expr({:=, _, [{:_, _, nil}, rhs]}, env, next, code) do
    expr(rhs, env, next, code)
  end

  # Binding: a = expr (always rebinds; use ^a to match an existing value)
  defp expr({:=, _, [{name, _, nil}, rhs]}, env, next, code) when is_atom(name) do
    with {:ok, code, env, next, reg} <- expr(rhs, env, next, code) do
      {:ok, code, Map.put(env, name, reg), next, reg}
    end
  end

  # Match: pat = expr (miss → raise :match_error). Value of the match is the RHS.
  defp expr({:=, _, [pat, rhs]}, env, next, code) do
    with {:ok, code, env, next, scr} <- expr(rhs, env, next, code),
         {:ok, code, env, next, fail_idx} <- emit_pattern_test(pat, scr, env, next, code),
         {:ok, code, env, next} <- emit_pattern_binds(pat, scr, env, next, code) do
      err_reg = next
      next = next + 1
      jump_over = length(code)
      code = code ++ [%{"op" => "jump", "target" => 0}]
      raise_ip = length(code)

      code =
        List.update_at(code, fail_idx, fn %{"op" => "jump"} = j ->
          %{j | "target" => raise_ip}
        end)

      code =
        code ++
          [
            %{"op" => "load_lit", "reg" => err_reg, "lit" => %{"atom" => "match_error"}},
            %{"op" => "raise", "reg" => err_reg}
          ]

      end_ip = length(code)

      code =
        List.update_at(code, jump_over, fn %{"op" => "jump"} = j ->
          %{j | "target" => end_ip}
        end)

      {:ok, code, env, next, scr}
    end
  end

  # Blocks: evaluate in order, keep last
  defp expr({:__block__, _, stmts}, env, next, code) do
    Enum.reduce_while(stmts, {:ok, code, env, next, nil}, fn
      stmt, {:ok, code, env, next, _} ->
        case expr(stmt, env, next, code) do
          {:ok, code, env, next, reg} -> {:cont, {:ok, code, env, next, reg}}
          {:error, _} = err -> {:halt, err}
        end
    end)
    |> case do
      {:ok, _code, _env, _next, nil} -> {:error, "empty block"}
      other -> other
    end
  end

  defp expr(nil, env, next, code), do: emit_lit(nil, env, next, code)

  defp expr(b, env, next, code) when is_boolean(b),
    do: emit_lit(%{"bool" => b}, env, next, code)

  defp expr(n, env, next, code) when is_integer(n),
    do: emit_lit(%{"int" => n}, env, next, code)

  defp expr(f, env, next, code) when is_float(f),
    do: emit_lit(%{"float" => f}, env, next, code)

  defp expr(s, env, next, code) when is_binary(s),
    do: emit_lit(%{"string" => s}, env, next, code)

  # Binary / partial bitstring literal `<<…>>`. Integer segments size 1…8
  # (default 8) + UTF-8 string chunks; trailing partial sizes 1…7 → `bitstring` lit.
  defp expr({:<<>>, _, segs}, env, next, code) when is_list(segs) do
    case literal_bitstring_lit(segs) do
      {:ok, lit} -> emit_lit(lit, env, next, code)
      {:error, msg} -> {:error, msg}
    end
  end

  defp expr(a, env, next, code) when is_atom(a),
    do: emit_lit(%{"atom" => Atom.to_string(a)}, env, next, code)

  # Bare module alias `Counter` → atom `"Counter"` (OTP-shaped MFA prefix).
  defp expr({:__aliases__, _, parts}, env, next, code) when is_list(parts) do
    emit_lit(%{"atom" => Enum.map_join(parts, ".", &to_string/1)}, env, next, code)
  end

  defp expr({name, _, nil}, env, next, code) when is_atom(name) do
    case Map.fetch(env, name) do
      {:ok, reg} -> {:ok, code, env, next, reg}
      :error -> {:error, "unbound variable #{name}"}
    end
  end

  # list literal [a, b, c] or dynamic [x, y] / [h | t]
  defp expr(list, env, next, code) when is_list(list) do
    case literal_list(list) do
      {:ok, lit} -> emit_lit(lit, env, next, code)
      :error -> lower_dynamic_list(list, env, next, code)
    end
  end

  # map literal %{k => v, ...} (literal keys/values only)
  defp expr({:%{}, _, pairs}, env, next, code) when is_list(pairs) do
    case literal_map(pairs) do
      {:ok, lit} -> emit_lit(lit, env, next, code)
      :error -> {:error, "map keys and values must be literals"}
    end
  end

  defp expr({:{}, _, elems}, env, next, code) when is_list(elems) do
    case literal_tuple(elems) do
      {:ok, lit} -> emit_lit(lit, env, next, code)
      :error -> lower_dynamic_tuple(elems, env, next, code)
    end
  end

  defp expr({a, b}, env, next, code) do
    expr({:{}, [], [a, b]}, env, next, code)
  end

  # case expr do pat -> body; ... end
  defp expr({:case, _, [scrutinee, [do: clauses]]}, env, next, code) do
    lower_case(scrutinee, List.wrap(clauses), env, next, code)
  end

  # if cond do then [else else_body] end — falsy is false | nil (Elixir-like)
  defp expr({:if, _, [cond_ast, opts]}, env, next, code) when is_list(opts) do
    then_ast = Keyword.get(opts, :do)
    else_ast = Keyword.get(opts, :else, nil)
    lower_if(cond_ast, then_ast, else_ast, env, next, code)
  end

  # unless cond do then [else else_body] end — desugar to if not truthy
  defp expr({:unless, _, [cond_ast, opts]}, env, next, code) when is_list(opts) do
    then_ast = Keyword.get(opts, :do)
    else_ast = Keyword.get(opts, :else, nil)
    # unless c, do: t, else: e  ≡  if c, do: e, else: t
    lower_if(cond_ast, else_ast, then_ast, env, next, code)
  end

  # cond do c1 -> b1; … end
  defp expr({:cond, _, [[do: clauses]]}, env, next, code) do
    lower_cond(List.wrap(clauses), env, next, code)
  end

  # raise expr (language exception; not StepError)
  defp expr({:raise, _, [arg]}, env, next, code) do
    with {:ok, code, env, next, reg} <- expr(arg, env, next, code) do
      {:ok, code ++ [%{"op" => "raise", "reg" => reg}], env, next, reg}
    end
  end

  # Code.load_file(path) — loads a .bc.json image at runtime
  defp expr(
         {{:., _, [{:__aliases__, _, [:Code]}, :load_file]}, _, [path_ast]},
         env,
         next,
         code
       ) do
    with {:ok, code, env, next, path_reg} <- expr(path_ast, env, next, code) do
      dest = next
      instr = %{"op" => "load_file", "dest" => dest, "path" => path_reg}
      {:ok, code ++ [instr], env, next + 1, dest}
    end
  end

  # try do ... rescue ... after ... end
  defp expr({:try, _, [opts]}, env, next, code) when is_list(opts) do
    lower_try(opts, env, next, code)
  end

  # receive do ... after ... end
  defp expr({:receive, _, [opts]}, env, next, code) when is_list(opts) do
    lower_receive(opts, env, next, code)
  end

  # spawn(Mod, :fun, [args...]) — static MFA when Mod/fun are literals
  defp expr({:spawn, _, [{:__aliases__, _, parts}, fun, args_list]}, env, next, code)
       when is_atom(fun) and is_list(args_list) do
    mod = Enum.map_join(parts, ".", &to_string/1)
    arity = length(args_list)
    lower_spawn_mfa("#{mod}.#{fun}/#{arity}", args_list, env, next, code)
  end

  # spawn(Mod.fun/arity isn't Elixir) — spawn(Main, :worker, [arg]) style via Autumn.spawn
  # We accept spawn(fun_name_atom, arg) as local MFA spawn: spawn(:worker, x) -> Main.worker/1
  defp expr({:spawn, _, [fun_ast, args_ast]}, env, next, code) when is_list(args_ast) or true do
    lower_spawn(fun_ast, args_ast, env, next, code)
  end

  # spawn_link(Mod, :fun, [args...])
  defp expr({:spawn_link, _, [{:__aliases__, _, parts}, fun, args_list]}, env, next, code)
       when is_atom(fun) and is_list(args_list) do
    mod = Enum.map_join(parts, ".", &to_string/1)
    arity = length(args_list)

    with {:ok, code, env, next, pid_reg} <-
           lower_spawn_mfa("#{mod}.#{fun}/#{arity}", args_list, env, next, code) do
      code = code ++ [%{"op" => "link", "pid" => pid_reg}]
      {:ok, code, env, next, pid_reg}
    end
  end

  # spawn_link(fun, args) → spawn then link
  defp expr({:spawn_link, _, [fun_ast, args_ast]}, env, next, code) do
    with {:ok, code, env, next, pid_reg} <- lower_spawn(fun_ast, args_ast, env, next, code) do
      code = code ++ [%{"op" => "link", "pid" => pid_reg}]
      {:ok, code, env, next, pid_reg}
    end
  end

  # link(pid)
  defp expr({:link, _, [pid_ast]}, env, next, code) do
    with {:ok, code, env, next, pid_reg} <- expr(pid_ast, env, next, code) do
      {:ok, code ++ [%{"op" => "link", "pid" => pid_reg}], env, next, pid_reg}
    end
  end

  # monitor(pid) → dest ← ref
  defp expr({:monitor, _, [pid_ast]}, env, next, code) do
    with {:ok, code, env, next, pid_reg} <- expr(pid_ast, env, next, code) do
      dest = next
      instr = %{"op" => "monitor", "dest" => dest, "pid" => pid_reg}
      {:ok, code ++ [instr], env, next + 1, dest}
    end
  end

  # demonitor(ref)
  defp expr({:demonitor, _, [ref_ast]}, env, next, code) do
    with {:ok, code, env, next, ref_reg} <- expr(ref_ast, env, next, code) do
      {:ok, code ++ [%{"op" => "demonitor", "ref" => ref_reg}], env, next, ref_reg}
    end
  end

  defp expr({:send, _, [pid_ast, msg_ast]}, env, next, code) do
    with {:ok, code, env, next, pid_reg} <- expr(pid_ast, env, next, code),
         {:ok, code, env, next, msg_reg} <- expr(msg_ast, env, next, code) do
      # send returns the message (Elixir-like); keep msg_reg as result
      instr = %{"op" => "send", "pid" => pid_reg, "msg" => msg_reg}
      {:ok, code ++ [instr], env, next, msg_reg}
    end
  end

  defp expr({:recv, _, []}, env, next, code) do
    dest = next
    {:ok, code ++ [%{"op" => "recv", "dest" => dest}], env, next + 1, dest}
  end

  defp expr({{:., _, [{:__aliases__, _, parts}, fun]}, _, args}, env, next, code)
       when is_atom(fun) and is_list(args) do
    mod = Enum.map_join(parts, ".", &to_string/1)
    arity = length(args)
    lower_call_named("#{mod}.#{fun}/#{arity}", args, env, next, code)
  end

  # apply(mod, fun, [a, b, ...]) with a literal arg list → apply_mfa
  defp expr({:apply, _, [mod_ast, fun_ast, args_list]}, env, next, code)
       when is_list(args_list) do
    with {:ok, code, env, next, mod_reg} <- expr(mod_ast, env, next, code),
         {:ok, code, env, next, fun_reg} <- expr(fun_ast, env, next, code),
         {:ok, code, env, next, arg_regs} <- map_exprs(args_list, env, next, code) do
      dest = next

      instr = %{
        "op" => "apply_mfa",
        "dest" => dest,
        "mod" => mod_reg,
        "fun" => fun_reg,
        "args" => arg_regs
      }

      {:ok, code ++ [instr], env, next + 1, dest}
    end
  end

  # Closure apply: `f.(args)` — `.` with a single callee expression.
  defp expr({{:., _, [fun_ast]}, _, args}, env, next, code) when is_list(args) do
    with {:ok, code, env, next, fun_reg} <- expr(fun_ast, env, next, code),
         {:ok, code, env, next, arg_regs} <- map_exprs(args, env, next, code) do
      dest = next
      instr = %{"op" => "apply", "dest" => dest, "fun" => fun_reg, "args" => arg_regs}
      {:ok, code ++ [instr], env, next + 1, dest}
    end
  end

  # `fn` → lift + make_fun. Multi-clause / patterned heads → synthetic case.
  defp expr({:fn, _, clauses}, env, next, code) when is_list(clauses) and clauses != [] do
    case clauses do
      [{:->, _, [params, body]}] ->
        case fn_param_names(params) do
          {:ok, _} -> lower_fn(params, body, env, next, code)
          {:error, _} -> lower_multi_fn(clauses, env, next, code)
        end

      _ ->
        lower_multi_fn(clauses, env, next, code)
    end
  end

  defp expr({:fn, _, _}, _env, _next, _code) do
    {:error, "fn: expected one or more clauses (fn pat -> body; … end)"}
  end

  defp expr({:|>, _, [left, right]}, env, next, code) do
    case desugar_pipe(left, right) do
      {:ok, call} -> expr(call, env, next, code)
      {:error, _} = err -> err
    end
  end

  # `for` / `with` are not in the teaching subset (avoid "unbound var" via call fallback).
  defp expr({:for, _, _}, _env, _next, _code) do
    {:error, "list comprehensions (for) are not supported yet"}
  end

  defp expr({:with, _, _}, _env, _next, _code) do
    {:error, "with is not supported yet"}
  end

  defp expr({name, _meta, args}, env, next, code)
       when is_atom(name) and is_list(args) and
              name not in [
                :{},
                :%{},
                :__aliases__,
                :__block__,
                :case,
                :if,
                :unless,
                :cond,
                :try,
                :raise,
                :receive,
                :spawn,
                :spawn_link,
                :apply,
                :link,
                :monitor,
                :demonitor,
                :send,
                :recv,
                :fn,
                :for,
                :with
              ] do
    arity = length(args)

    cond do
      arity == 1 and is_map_key(@type_guards, name) ->
        # `is_float(x)` etc. as expressions → is_tag (same as guards).
        [arg] = args
        tag = Map.fetch!(@type_guards, name)

        with {:ok, code, env, next, reg} <- expr(arg, env, next, code) do
          dest = next
          instr = %{"op" => "is_tag", "dest" => dest, "reg" => reg, "tag" => tag}
          {:ok, code ++ [instr], env, next + 1, dest}
        end

      name == :hd and arity == 1 ->
        lower_hd_tl(:hd, hd(args), env, next, code)

      name == :tl and arity == 1 ->
        lower_hd_tl(:tl, hd(args), env, next, code)

      name == :++ and arity == 2 ->
        [left, right] = args
        lower_list_append(left, right, env, next, code)

      true ->
        fun =
          case Map.fetch(@builtins, {name, arity}) do
            {:ok, builtin} -> builtin
            :error -> "__local__:#{name}/#{arity}"
          end

        lower_call_named(fun, args, env, next, code)
    end
  end

  defp expr(other, _env, _next, _code) do
    {:error, "unsupported expression: #{Macro.to_string(other)}"}
  end

  defp lower_hd_tl(which, arg, env, next, code) do
    with {:ok, code, env, next, list_reg} <- expr(arg, env, next, code) do
      dest = next

      instr =
        case which do
          :hd ->
            %{"op" => "get_list_elem", "dest" => dest, "list" => list_reg, "index" => 0}

          :tl ->
            %{"op" => "get_list_rest", "dest" => dest, "list" => list_reg, "index" => 0}
        end

      {:ok, code ++ [instr], env, next + 1, dest}
    end
  end

  # `a ++ b` → call a per-module lifted `__list_append__/2` (case + cons).
  defp lower_list_append(left, right, env, next, code) do
    fun_name = ensure_list_append!()
    lower_call_named(fun_name, [left, right], env, next, code)
  end

  defp ensure_list_append! do
    mod = Process.get({:autumn, :mod})
    fun_name = "#{mod}.__list_append__/2"

    unless Process.get({:autumn, :list_append}) do
      # xs, ys. case xs do [] -> ys; [h|t] -> [h | append(t, ys)] end
      xs = {:xs, [], nil}
      ys = {:ys, [], nil}
      h = {:h, [], nil}
      t = {:t, [], nil}

      body =
        {:case, [],
         [
           xs,
           [
             do: [
               # Quote shapes: `[] -> ys` and `[h|t] -> …` (see Code.string_to_quoted)
               {:->, [], [[[]], ys]},
               {:->, [],
                [
                  [[{:|, [], [h, t]}]],
                  {:cons, [], [h, {String.to_atom("__list_append__"), [], [t, ys]}]}
                ]}
             ]
           ]
         ]}

      case lower_body(body, [:xs, :ys]) do
        {:ok, lifted_code, locals} ->
          lifted_code =
            Enum.map(lifted_code, fn
              %{"op" => "call", "fun" => "__local__:__list_append__/2"} = instr ->
                %{instr | "fun" => fun_name}

              instr ->
                instr
            end)

          push_lifted!(%{
            "name" => fun_name,
            "arity" => 2,
            "locals" => locals,
            "code" => lifted_code
          })

          Process.put({:autumn, :list_append}, true)

        {:error, msg} ->
          raise "internal: failed to lower __list_append__/2: #{msg}"
      end
    end

    fun_name
  end

  defp lower_if(cond_ast, then_ast, else_ast, env, next, code) do
    result_reg = next
    next = next + 1

    with {:ok, code, env, next, c_reg} <- expr(cond_ast, env, next, code) do
      # jump to else when cond is false or nil
      code =
        code ++
          [
            %{
              "op" => "jump_if_eq",
              "target" => 0,
              "reg" => c_reg,
              "lit" => %{"bool" => false}
            }
          ]

      jump_false = length(code) - 1

      code =
        code ++
          [
            %{
              "op" => "jump_if_eq",
              "target" => 0,
              "reg" => c_reg,
              "lit" => nil
            }
          ]

      jump_nil = length(code) - 1

      with {:ok, code, env, next, then_reg} <- expr(then_ast, env, next, code) do
        code =
          code ++
            [
              %{"op" => "move", "dest" => result_reg, "src" => then_reg},
              %{"op" => "jump", "target" => 0}
            ]

        jump_end = length(code) - 1
        else_ip = length(code)

        with {:ok, code, env, next, else_reg} <- expr(else_ast, env, next, code) do
          code =
            code ++
              [
                %{"op" => "move", "dest" => result_reg, "src" => else_reg}
              ]

          end_ip = length(code)

          code =
            code
            |> List.update_at(jump_false, fn j -> %{j | "target" => else_ip} end)
            |> List.update_at(jump_nil, fn j -> %{j | "target" => else_ip} end)
            |> List.update_at(jump_end, fn j -> %{j | "target" => end_ip} end)

          {:ok, code, env, next, result_reg}
        end
      end
    end
  end

  defp lower_cond(clauses, env, next, code) do
    result_reg = next
    next = next + 1

    with {:ok, code, env, next, end_jumps} <-
           Enum.reduce_while(clauses, {:ok, code, env, next, []}, fn clause,
                                                                     {:ok, code, env, next, jumps} ->
             case lower_cond_clause(clause, result_reg, env, next, code) do
               {:ok, code, env, next, jump_end} ->
                 {:cont, {:ok, code, env, next, [jump_end | jumps]}}

               {:error, _} = err ->
                 {:halt, err}
             end
           end) do
      # No clause matched → raise :cond_clause_error (like match_error).
      with {:ok, code, env, next, err_reg} <-
             emit_lit(%{"atom" => "cond_clause_error"}, env, next, code) do
        code = code ++ [%{"op" => "raise", "reg" => err_reg}]
        end_ip = length(code)

        code =
          Enum.reduce(end_jumps, code, fn idx, code ->
            List.update_at(code, idx, fn %{"op" => "jump"} = j ->
              %{j | "target" => end_ip}
            end)
          end)

        {:ok, code, env, next, result_reg}
      end
    end
  end

  defp lower_cond_clause({:->, _, [[cond_ast], body]}, result_reg, env, next, code) do
    with {:ok, code, env, next, c_reg} <- expr(cond_ast, env, next, code) do
      code =
        code ++
          [
            %{
              "op" => "jump_if_eq",
              "target" => 0,
              "reg" => c_reg,
              "lit" => %{"bool" => false}
            }
          ]

      jump_false = length(code) - 1

      code =
        code ++
          [
            %{
              "op" => "jump_if_eq",
              "target" => 0,
              "reg" => c_reg,
              "lit" => nil
            }
          ]

      jump_nil = length(code) - 1

      with {:ok, code, env, next, body_reg} <- expr(body, env, next, code) do
        code =
          code ++
            [
              %{"op" => "move", "dest" => result_reg, "src" => body_reg},
              %{"op" => "jump", "target" => 0}
            ]

        jump_end = length(code) - 1
        next_clause = length(code)

        code =
          code
          |> List.update_at(jump_false, fn j -> %{j | "target" => next_clause} end)
          |> List.update_at(jump_nil, fn j -> %{j | "target" => next_clause} end)

        {:ok, code, env, next, jump_end}
      end
    end
  end

  defp lower_cond_clause(other, _result_reg, _env, _next, _code) do
    {:error, "unsupported cond clause: #{Macro.to_string(other)}"}
  end

  defp lower_spawn(fun_ast, args_ast, env, next, code) do
    args_list =
      case args_ast do
        args when is_list(args) -> args
        other -> [other]
      end

    with {:ok, fun_name, arity} <- spawn_fun(fun_ast, length(args_list)),
         {:ok, code, env, next, arg_regs} <- map_exprs(args_list, env, next, code) do
      dest = next

      # local MFA filled in resolve — use __local__
      fun =
        case fun_name do
          {:local, n} -> "__local__:#{n}/#{arity}"
          s when is_binary(s) -> s
        end

      instr = %{"op" => "spawn", "dest" => dest, "fun" => fun, "args" => arg_regs}
      {:ok, code ++ [instr], env, next + 1, dest}
    end
  end

  defp lower_spawn_mfa(mfa, args_list, env, next, code) when is_binary(mfa) do
    with {:ok, code, env, next, arg_regs} <- map_exprs(args_list, env, next, code) do
      dest = next
      instr = %{"op" => "spawn", "dest" => dest, "fun" => mfa, "args" => arg_regs}
      {:ok, code ++ [instr], env, next + 1, dest}
    end
  end

  defp spawn_fun(name, arity) when is_atom(name), do: {:ok, {:local, name}, arity}

  defp spawn_fun({{:., _, [{:__aliases__, _, parts}, fun]}, _, []}, arity)
       when is_atom(fun) do
    mod = Enum.map_join(parts, ".", &to_string/1)
    {:ok, "#{mod}.#{fun}/#{arity}", arity}
  end

  defp spawn_fun(other, _),
    do: {:error, "unsupported spawn target: #{Macro.to_string(other)}"}

  defp desugar_pipe(left, {name, meta, args}) when is_atom(name) and is_list(args) do
    {:ok, {name, meta, [left | args]}}
  end

  defp desugar_pipe(left, {name, meta, ctx}) when is_atom(name) and is_atom(ctx) do
    # `x |> foo` (no parens) — Elixir encodes the call context atom as the third element.
    {:ok, {name, meta, [left]}}
  end

  defp desugar_pipe(left, {{:., _, _} = remote, meta, args}) when is_list(args) do
    {:ok, {remote, meta, [left | args]}}
  end

  defp desugar_pipe(_left, other),
    do: {:error, "unsupported pipe right-hand side: #{Macro.to_string(other)}"}

  # try/rescue/after — after is a join label, not a VM opcode.
  # Shape:
  #   enter_try Lrescue rexc
  #     body -> result
  #     leave_try
  #     jump Lafter
  #   Lrescue:
  #     rescue clauses on rexc; match -> result; jump Lafter
  #     no match -> raise rexc
  #   Lafter:
  #     optional after; keep result
  defp lower_try(opts, env, next, code) do
    body = Keyword.get(opts, :do)
    rescue_clauses = opts |> Keyword.get(:rescue, []) |> List.wrap()
    after_body = Keyword.get(opts, :after)

    if body == nil do
      {:error, "try requires a do body"}
    else
      if rescue_clauses == [] and after_body == nil do
        expr(body, env, next, code)
      else
        if rescue_clauses == [] do
          # try/after only — handler so `after` runs on uncaught raise, then re-raise
          lower_try_after(body, after_body, env, next, code)
        else
          lower_try_rescue(body, rescue_clauses, after_body, env, next, code)
        end
      end
    end
  end

  # try/after (no rescue): after runs on success and on raise; raise is re-raised after.
  #   enter_try Lrescue rexc
  #     body -> result; leave_try; raised := false; jump Lafter
  #   Lrescue:
  #     raised := true; jump Lafter
  #   Lafter:
  #     after; jump_if_eq Lraise raised true; jump Lend
  #   Lraise: raise rexc
  #   Lend:
  defp lower_try_after(body, after_body, env, next, code) do
    result_reg = next
    exc_reg = next + 1
    raised_reg = next + 2
    next = next + 3

    enter_idx = length(code)
    code = code ++ [%{"op" => "enter_try", "rescue" => 0, "exc" => exc_reg}]

    with {:ok, code, env, next, body_reg} <- expr(body, env, next, code) do
      code =
        code ++
          [
            %{"op" => "move", "dest" => result_reg, "src" => body_reg},
            %{"op" => "leave_try"},
            %{"op" => "load_lit", "reg" => raised_reg, "lit" => %{"bool" => false}},
            %{"op" => "jump", "target" => 0}
          ]

      jump_after_success = length(code) - 1
      rescue_ip = length(code)

      code =
        List.update_at(code, enter_idx, fn %{"op" => "enter_try"} = i ->
          %{i | "rescue" => rescue_ip}
        end)

      code =
        code ++
          [
            %{"op" => "load_lit", "reg" => raised_reg, "lit" => %{"bool" => true}},
            %{"op" => "jump", "target" => 0}
          ]

      jump_after_rescue = length(code) - 1
      after_ip = length(code)

      code =
        Enum.reduce([jump_after_success, jump_after_rescue], code, fn idx, code ->
          List.update_at(code, idx, fn %{"op" => "jump"} = j ->
            %{j | "target" => after_ip}
          end)
        end)

      with {:ok, code, env, next, _} <- expr(after_body, env, next, code) do
        raise_ip = length(code) + 2
        end_ip = length(code) + 3

        code =
          code ++
            [
              %{
                "op" => "jump_if_eq",
                "target" => raise_ip,
                "reg" => raised_reg,
                "lit" => %{"bool" => true}
              },
              %{"op" => "jump", "target" => end_ip},
              %{"op" => "raise", "reg" => exc_reg}
            ]

        {:ok, code, env, next, result_reg}
      end
    end
  end

  defp lower_try_rescue(body, rescue_clauses, after_body, env, next, code) do
    result_reg = next
    exc_reg = next + 1
    next = next + 2

    enter_idx = length(code)
    # Placeholder rescue target; patched after body.
    code = code ++ [%{"op" => "enter_try", "rescue" => 0, "exc" => exc_reg}]

    with {:ok, code, env, next, body_reg} <- expr(body, env, next, code) do
      code =
        code ++
          [
            %{"op" => "move", "dest" => result_reg, "src" => body_reg},
            %{"op" => "leave_try"},
            %{"op" => "jump", "target" => 0}
          ]

      jump_after_success = length(code) - 1
      rescue_ip = length(code)

      code =
        List.update_at(code, enter_idx, fn %{"op" => "enter_try"} = i ->
          %{i | "rescue" => rescue_ip}
        end)

      rescue_result =
        Enum.reduce_while(rescue_clauses, {:ok, code, env, next, []}, fn clause,
                                                                         {:ok, code, env, next,
                                                                          jumps} ->
          case lower_clause(clause, exc_reg, result_reg, env, next, code) do
            {:ok, code, env, next, after_body_jump_slot} ->
              {:cont, {:ok, code, env, next, jumps ++ [after_body_jump_slot]}}

            {:error, _} = err ->
              {:halt, err}
          end
        end)

      with {:ok, code, env, next, rescue_ends} <- rescue_result do
        # No rescue matched — re-raise the exception.
        code = code ++ [%{"op" => "raise", "reg" => exc_reg}]
        after_ip = length(code)

        code =
          Enum.reduce([jump_after_success | rescue_ends], code, fn idx, code ->
            List.update_at(code, idx, fn %{"op" => "jump"} = j ->
              %{j | "target" => after_ip}
            end)
          end)

        if after_body == nil do
          {:ok, code, env, next, result_reg}
        else
          with {:ok, code, env, next, _} <- expr(after_body, env, next, code) do
            {:ok, code, env, next, result_reg}
          end
        end
      end
    end
  end

  # receive do clauses after timeout -> body end
  # Empty `do` (after-only) allowed. Scan loop: recv_peek; clauses; else idx++; wait.
  # Timeout may be a non-neg int lit or an expression (`{"reg": R}`).
  defp lower_receive(opts, env, next, code) do
    clauses =
      case Keyword.get(opts, :do, []) do
        nil -> []
        {:__block__, _, []} -> []
        other -> List.wrap(other)
      end

    after_clauses = opts |> Keyword.get(:after, []) |> List.wrap()

    with {:ok, timeout, after_body} <- parse_receive_after(after_clauses) do
      lower_receive_loop(clauses, timeout, after_body, env, next, code)
    end
  end

  defp parse_receive_after([]) do
    # Infinity — after label unused (points at end).
    {:ok, :infinity, nil}
  end

  defp parse_receive_after([{:->, _, [[timeout], body]}])
       when is_integer(timeout) and timeout >= 0 do
    {:ok, {:lit, timeout}, body}
  end

  defp parse_receive_after([{:->, _, [[timeout_expr], body]}]) do
    {:ok, {:expr, timeout_expr}, body}
  end

  defp parse_receive_after(other) do
    {:error, "unsupported receive after: #{Macro.to_string(other)}"}
  end

  defp lower_receive_loop(clauses, timeout, after_body, env, next, code) do
    result_reg = next
    next = next + 1

    # After-only: no mailbox scan. `wait` retry == after so a non-empty mailbox
    # (or wake) jumps straight to the after body instead of busy-spinning.
    if clauses == [] do
      lower_receive_after_only(timeout, after_body, env, next, code, result_reg)
    else
      lower_receive_with_clauses(clauses, timeout, after_body, env, next, code, result_reg)
    end
  end

  defp lower_receive_after_only(timeout, after_body, env, next, code, result_reg) do
    with {:ok, code, env, next, timeout_json} <- emit_wait_timeout(timeout, env, next, code) do
      wait_idx = length(code)

      code =
        code ++
          [
            %{
              "op" => "wait",
              "retry" => 0,
              "after" => 0,
              "timeout" => timeout_json
            }
          ]

      after_ip = length(code)

      code =
        List.update_at(code, wait_idx, fn %{"op" => "wait"} = i ->
          %{i | "retry" => after_ip, "after" => after_ip}
        end)

      after_result =
        if after_body == nil do
          {:ok, code ++ [%{"op" => "load_lit", "reg" => result_reg, "lit" => nil}], env, next}
        else
          with {:ok, code, env, next, body_reg} <- expr(after_body, env, next, code) do
            {:ok, code ++ [%{"op" => "move", "dest" => result_reg, "src" => body_reg}], env, next}
          end
        end

      with {:ok, code, env, next} <- after_result do
        {:ok, code, env, next, result_reg}
      end
    end
  end

  defp lower_receive_with_clauses(clauses, timeout, after_body, env, next, code, result_reg) do
    idx_reg = next
    msg_reg = next + 1
    next = next + 2

    code = code ++ [%{"op" => "load_lit", "reg" => idx_reg, "lit" => %{"int" => 0}}]
    scan_ip = length(code)

    peek_idx = length(code)
    code = code ++ [%{"op" => "recv_peek", "dest" => msg_reg, "index" => idx_reg, "empty" => 0}]

    clause_result =
      Enum.reduce_while(clauses, {:ok, code, env, next, []}, fn clause,
                                                                {:ok, code, env, next, ends} ->
        case lower_receive_clause(clause, msg_reg, idx_reg, result_reg, env, next, code) do
          {:ok, code, env, next, end_jump} ->
            {:cont, {:ok, code, env, next, ends ++ [end_jump]}}

          {:error, _} = err ->
            {:halt, err}
        end
      end)

    with {:ok, code, env, next, body_ends} <- clause_result do
      # No clause matched this message — advance index and rescan.
      one_reg = next
      sum_reg = next + 1
      next = next + 2

      code =
        code ++
          [
            %{"op" => "load_lit", "reg" => one_reg, "lit" => %{"int" => 1}},
            %{"op" => "call", "dest" => sum_reg, "fun" => "+/2", "args" => [idx_reg, one_reg]},
            %{"op" => "move", "dest" => idx_reg, "src" => sum_reg},
            %{"op" => "jump", "target" => scan_ip}
          ]

      wait_ip = length(code)

      code =
        List.update_at(code, peek_idx, fn %{"op" => "recv_peek"} = i ->
          %{i | "empty" => wait_ip}
        end)

      with {:ok, code, env, next, timeout_json} <- emit_wait_timeout(timeout, env, next, code) do
        wait_idx = length(code)

        code =
          code ++
            [
              %{
                "op" => "wait",
                "retry" => scan_ip,
                "after" => 0,
                "timeout" => timeout_json
              }
            ]

        after_ip = length(code)

        code =
          List.update_at(code, wait_idx, fn %{"op" => "wait"} = i ->
            %{i | "after" => after_ip}
          end)

        after_result =
          if after_body == nil do
            {:ok, code ++ [%{"op" => "load_lit", "reg" => result_reg, "lit" => nil}], env, next}
          else
            with {:ok, code, env, next, body_reg} <- expr(after_body, env, next, code) do
              {:ok, code ++ [%{"op" => "move", "dest" => result_reg, "src" => body_reg}], env,
               next}
            end
          end

        with {:ok, code, env, next} <- after_result do
          end_ip = length(code)

          code =
            Enum.reduce(body_ends, code, fn idx, code ->
              List.update_at(code, idx, fn %{"op" => "jump"} = j ->
                %{j | "target" => end_ip}
              end)
            end)

          {:ok, code, env, next, result_reg}
        end
      end
    end
  end

  defp emit_wait_timeout(:infinity, env, next, code), do: {:ok, code, env, next, nil}

  defp emit_wait_timeout({:lit, n}, env, next, code), do: {:ok, code, env, next, n}

  defp emit_wait_timeout({:expr, timeout_expr}, env, next, code) do
    with {:ok, code, env, next, reg} <- expr(timeout_expr, env, next, code) do
      {:ok, code, env, next, %{"reg" => reg}}
    end
  end

  defp lower_receive_clause(
         {:->, _, [[{:when, _, [pat, guard]}], body]},
         msg_reg,
         idx_reg,
         result_reg,
         env,
         next,
         code
       ) do
    lower_receive_clause_guarded(pat, guard, body, msg_reg, idx_reg, result_reg, env, next, code)
  end

  defp lower_receive_clause(
         {:->, _, [[pat], body]},
         msg_reg,
         idx_reg,
         result_reg,
         env,
         next,
         code
       ) do
    lower_receive_clause_guarded(pat, nil, body, msg_reg, idx_reg, result_reg, env, next, code)
  end

  defp lower_receive_clause(other, _, _, _, _, _, _),
    do: {:error, "unsupported receive clause: #{Macro.to_string(other)}"}

  defp lower_receive_clause_guarded(
         pat,
         guard,
         body,
         msg_reg,
         idx_reg,
         result_reg,
         env,
         next,
         code
       ) do
    with {:ok, code, env, next, matched_jump_over} <-
           emit_pattern_test(pat, msg_reg, env, next, code),
         {:ok, code, env, next} <- emit_pattern_binds(pat, msg_reg, env, next, code),
         {:ok, code, env, next, guard_fail} <-
           maybe_emit_guard(guard, env, next, code) do
      code = code ++ [%{"op" => "recv_drop", "index" => idx_reg}]

      with {:ok, code, env, next, body_reg} <- expr(body, env, next, code) do
        code =
          code ++
            [
              %{"op" => "move", "dest" => result_reg, "src" => body_reg},
              %{"op" => "jump", "target" => 0}
            ]

        jump_idx = length(code) - 1
        after_clause = length(code)

        code =
          Enum.reduce([matched_jump_over | List.wrap(guard_fail)], code, fn idx, code ->
            List.update_at(code, idx, fn %{"op" => "jump"} = j ->
              %{j | "target" => after_clause}
            end)
          end)

        {:ok, code, env, next, jump_idx}
      end
    end
  end

  # Very small case compiler: literal patterns + wildcard + var + tuple + fixed list
  defp lower_case(scrutinee, clauses, env, next, code) do
    with {:ok, code, env, next, scr_reg} <- expr(scrutinee, env, next, code) do
      result_reg = next
      next = next + 1
      # We'll build: for each clause, test; on match bind+body+jump end; else fall through
      fail_labels = length(clauses)
      # Emit placeholder then patch absolute targets
      case_result =
        Enum.reduce_while(clauses, {:ok, code, env, next, []}, fn clause,
                                                                  {:ok, code, env, next, jumps} ->
          case lower_clause(clause, scr_reg, result_reg, env, next, code) do
            {:ok, code, env, next, after_body_jump_slot} ->
              {:cont, {:ok, code, env, next, jumps ++ [after_body_jump_slot]}}

            {:error, _} = err ->
              {:halt, err}
          end
        end)

      with {:ok, code, env, next, body_ends} <- case_result do
        # Fall-through: no match — raise :match_error (success clauses jump past this)
        err_reg = next
        next = next + 1

        code =
          code ++
            [
              %{"op" => "load_lit", "reg" => err_reg, "lit" => %{"atom" => "match_error"}},
              %{"op" => "raise", "reg" => err_reg}
            ]

        end_ip = length(code)

        code =
          Enum.reduce(body_ends, code, fn idx, code ->
            List.update_at(code, idx, fn %{"op" => "jump"} = j ->
              %{j | "target" => end_ip}
            end)
          end)

        _ = fail_labels
        {:ok, code, env, next, result_reg}
      end
    end
  end

  defp lower_clause(
         {:->, _, [[{:when, _, [pat, guard]}], body]},
         scr_reg,
         result_reg,
         env,
         next,
         code
       ) do
    lower_clause_guarded(pat, guard, body, scr_reg, result_reg, env, next, code)
  end

  # rescue e in [lit, …] / case-style `x in […]` (value-based tag filter)
  defp lower_clause(
         {:->, _, [[{:in, _, [var, targets]}], body]},
         scr_reg,
         result_reg,
         env,
         next,
         code
       ) do
    lower_clause_guarded(
      {:in, [], [var, targets]},
      nil,
      body,
      scr_reg,
      result_reg,
      env,
      next,
      code
    )
  end

  defp lower_clause({:->, _, [[pat], body]}, scr_reg, result_reg, env, next, code) do
    lower_clause_guarded(pat, nil, body, scr_reg, result_reg, env, next, code)
  end

  defp lower_clause(other, _, _, _, _, _),
    do: {:error, "unsupported case clause: #{Macro.to_string(other)}"}

  defp lower_clause_guarded(pat, guard, body, scr_reg, result_reg, env, next, code) do
    with {:ok, code, env, next, matched_jump_over} <-
           emit_pattern_test(pat, scr_reg, env, next, code),
         {:ok, code, env, next} <- emit_pattern_binds(pat, scr_reg, env, next, code),
         {:ok, code, env, next, guard_fail} <-
           maybe_emit_guard(guard, env, next, code),
         {:ok, code, env, next, body_reg} <- expr(body, env, next, code) do
      code =
        code ++
          [
            %{"op" => "move", "dest" => result_reg, "src" => body_reg},
            %{"op" => "jump", "target" => 0}
          ]

      jump_idx = length(code) - 1
      after_clause = length(code)

      code =
        Enum.reduce([matched_jump_over | List.wrap(guard_fail)], code, fn idx, code ->
          List.update_at(code, idx, fn %{"op" => "jump"} = j ->
            %{j | "target" => after_clause}
          end)
        end)

      {:ok, code, env, next, jump_idx}
    end
  end

  defp maybe_emit_guard(nil, env, next, code), do: {:ok, code, env, next, nil}

  defp maybe_emit_guard(guard, env, next, code) do
    # Evaluate guard to a bool reg; jump_if_eq true → fall through; else jump fail.
    with {:ok, code, env, next, g_reg} <- emit_guard_bool(guard, env, next, code) do
      matched = length(code) + 2

      code =
        code ++
          [
            %{
              "op" => "jump_if_eq",
              "target" => matched,
              "reg" => g_reg,
              "lit" => %{"bool" => true}
            },
            %{"op" => "jump", "target" => 0}
          ]

      fail_idx = length(code) - 1
      {:ok, code, env, next, fail_idx}
    end
  end

  # Guard → bool register. Supports and/or, is_* tags, comparisons, ==.
  defp emit_guard_bool({:and, _, [a, b]}, env, next, code) do
    # a and b: if not a → false; else b
    false_reg = next
    result_reg = next + 1
    next = next + 2

    code = code ++ [%{"op" => "load_lit", "reg" => false_reg, "lit" => %{"bool" => false}}]

    with {:ok, code, env, next, a_reg} <- emit_guard_bool(a, env, next, code) do
      then_ip = length(code) + 2

      code =
        code ++
          [
            %{
              "op" => "jump_if_eq",
              "target" => then_ip,
              "reg" => a_reg,
              "lit" => %{"bool" => true}
            },
            %{"op" => "jump", "target" => 0}
          ]

      short_idx = length(code) - 1

      with {:ok, code, env, next, b_reg} <- emit_guard_bool(b, env, next, code) do
        code =
          code ++
            [
              %{"op" => "move", "dest" => result_reg, "src" => b_reg},
              %{"op" => "jump", "target" => 0}
            ]

        join_from_b = length(code) - 1
        false_ip = length(code)

        code =
          code ++
            [
              %{"op" => "move", "dest" => result_reg, "src" => false_reg},
              %{"op" => "jump", "target" => 0}
            ]

        join_from_f = length(code) - 1
        end_ip = length(code)

        code =
          code
          |> List.update_at(short_idx, fn j -> %{j | "target" => false_ip} end)
          |> List.update_at(join_from_b, fn j -> %{j | "target" => end_ip} end)
          |> List.update_at(join_from_f, fn j -> %{j | "target" => end_ip} end)

        {:ok, code, env, next, result_reg}
      end
    end
  end

  defp emit_guard_bool({:or, _, [a, b]}, env, next, code) do
    true_reg = next
    result_reg = next + 1
    next = next + 2

    code = code ++ [%{"op" => "load_lit", "reg" => true_reg, "lit" => %{"bool" => true}}]

    with {:ok, code, env, next, a_reg} <- emit_guard_bool(a, env, next, code) do
      code =
        code ++
          [
            %{
              "op" => "jump_if_eq",
              "target" => 0,
              "reg" => a_reg,
              "lit" => %{"bool" => true}
            }
          ]

      true_jump = length(code) - 1

      with {:ok, code, env, next, b_reg} <- emit_guard_bool(b, env, next, code) do
        code =
          code ++
            [
              %{"op" => "move", "dest" => result_reg, "src" => b_reg},
              %{"op" => "jump", "target" => 0}
            ]

        join_b = length(code) - 1
        true_ip = length(code)

        code =
          code ++
            [
              %{"op" => "move", "dest" => result_reg, "src" => true_reg},
              %{"op" => "jump", "target" => 0}
            ]

        join_t = length(code) - 1
        end_ip = length(code)

        code =
          code
          |> List.update_at(true_jump, fn j -> %{j | "target" => true_ip} end)
          |> List.update_at(join_b, fn j -> %{j | "target" => end_ip} end)
          |> List.update_at(join_t, fn j -> %{j | "target" => end_ip} end)

        {:ok, code, env, next, result_reg}
      end
    end
  end

  defp emit_guard_bool({name, _, [arg]}, env, next, code)
       when is_map_key(@type_guards, name) do
    tag = Map.fetch!(@type_guards, name)

    with {:ok, code, env, next, reg} <- expr(arg, env, next, code) do
      dest = next

      code =
        code ++
          [
            %{"op" => "is_tag", "dest" => dest, "reg" => reg, "tag" => tag}
          ]

      {:ok, code, env, next + 1, dest}
    end
  end

  defp emit_guard_bool({op, _, [a, b]}, env, next, code)
       when op in [:<, :>, :<=, :>=, :==] do
    fun = Map.fetch!(@builtins, {op, 2})

    with {:ok, code, env, next, a_reg} <- expr(a, env, next, code),
         {:ok, code, env, next, b_reg} <- expr(b, env, next, code) do
      dest = next
      instr = %{"op" => "call", "dest" => dest, "fun" => fun, "args" => [a_reg, b_reg]}
      {:ok, code ++ [instr], env, next + 1, dest}
    end
  end

  defp emit_guard_bool(other, _env, _next, _code) do
    {:error, "unsupported guard: #{Macro.to_string(other)}"}
  end

  defp lower_dynamic_list(elems, env, next, code) do
    case split_list_pattern(elems) do
      {:cons, prefix, head, tail} ->
        # [p1, p2, h | t] → cons(h, t) then fold prefix right-to-left
        with {:ok, code, env, next, t_reg} <- expr(tail, env, next, code),
             {:ok, code, env, next, h_reg} <- expr(head, env, next, code) do
          dest = next

          code =
            code ++
              [%{"op" => "call", "dest" => dest, "fun" => "cons/2", "args" => [h_reg, t_reg]}]

          next = next + 1

          Enum.reduce_while(Enum.reverse(prefix), {:ok, code, env, next, dest}, fn
            elem, {:ok, code, env, next, acc} ->
              case expr(elem, env, next, code) do
                {:ok, code, env, next, er} ->
                  d = next

                  code =
                    code ++
                      [%{"op" => "call", "dest" => d, "fun" => "cons/2", "args" => [er, acc]}]

                  {:cont, {:ok, code, env, next + 1, d}}

                {:error, _} = err ->
                  {:halt, err}
              end
          end)
        end

      {:proper, proper} ->
        # Build from the right: start with []
        with {:ok, code, env, next, acc} <- emit_lit(%{"list" => []}, env, next, code) do
          Enum.reduce_while(Enum.reverse(proper), {:ok, code, env, next, acc}, fn
            elem, {:ok, code, env, next, acc} ->
              case expr(elem, env, next, code) do
                {:ok, code, env, next, er} ->
                  d = next

                  code =
                    code ++
                      [%{"op" => "call", "dest" => d, "fun" => "cons/2", "args" => [er, acc]}]

                  {:cont, {:ok, code, env, next + 1, d}}

                {:error, _} = err ->
                  {:halt, err}
              end
          end)
        end

      {:error, _} = err ->
        err
    end
  end

  defp lower_dynamic_tuple(elems, env, next, code) do
    with {:ok, code, env, next, regs} <- map_exprs(elems, env, next, code) do
      dest = next
      arity = length(regs)
      fun = "make_tuple/#{arity}"
      instr = %{"op" => "call", "dest" => dest, "fun" => fun, "args" => regs}
      {:ok, code ++ [instr], env, next + 1, dest}
    end
  end

  # Returns {:ok, code, env, next, jump_over_idx} where jump_over skips the clause on failure.
  # Strategy: for literal L: jump_if_eq match_label; jump fail; match_label: ...
  # Simpler approach: is_tag / jump_if_eq then jump to fail_label if not matched.
  #
  # Emit:
  #   jump_if_eq NEXT lit  (if pattern is lit)  -- if equal, fall through to body path
  #   Actually jump_if_eq jumps ON equal. So:
  #   jump_if_eq BODY_START scr lit
  #   jump FAIL
  #   BODY_START: ...
  # For our linear emit we do:
  #   jump_if_eq matched scr lit
  #   jump fail_placeholder  <-- return this index
  #   matched: (implicit next)

  defp emit_pattern_test({:_, _, nil}, _scr, env, next, code) do
    # always matches — emit a no-op jump that we'll set to skip nothing
    # insert a jump that goes to next instr (match) — i.e. no fail path needed
    # Use jump_if_eq true true? Easier: emit jump over fail that is never taken:
    # just push a dummy jump to next+1 that we patch as "fail" pointing to after clause,
    # and don't jump to it. Use jump_if_eq with impossible?
    # Simplest for `_`: insert `jump` to ip+2 and `jump` fail — first jump always taken to body.
    code = code ++ [%{"op" => "jump", "target" => length(code) + 2}]
    fail_idx = length(code)
    code = code ++ [%{"op" => "jump", "target" => 0}]
    # first jump target = fail_idx+1 = after fail jump = body
    code =
      List.update_at(code, fail_idx - 1, fn j ->
        %{j | "target" => fail_idx + 1}
      end)

    {:ok, code, env, next, fail_idx}
  end

  defp emit_pattern_test({name, _, nil}, scr, env, next, code) when is_atom(name) do
    # variable pattern — always matches
    emit_pattern_test({:_, [], nil}, scr, env, next, code)
  end

  # Pin: ^var — equality against the currently bound register (via ==/2).
  defp emit_pattern_test({:^, _, [{name, _, nil}]}, scr, env, next, code) when is_atom(name) do
    case Map.fetch(env, name) do
      :error ->
        {:error, "unbound pin ^#{name}"}

      {:ok, pin_reg} ->
        eq_reg = next
        next = next + 1

        code =
          code ++
            [
              %{
                "op" => "call",
                "dest" => eq_reg,
                "fun" => "==/2",
                "args" => [scr, pin_reg]
              }
            ]

        matched = length(code) + 2

        code =
          code ++
            [
              %{
                "op" => "jump_if_eq",
                "target" => matched,
                "reg" => eq_reg,
                "lit" => %{"bool" => true}
              },
              %{"op" => "jump", "target" => 0}
            ]

        fail_idx = length(code) - 1
        {:ok, code, env, next, fail_idx}
    end
  end

  defp emit_pattern_test(lit, scr, env, next, code)
       when is_integer(lit) or is_float(lit) or is_binary(lit) or is_atom(lit) or is_boolean(lit) or
              is_nil(lit) do
    {:ok, jlit} = lit_value(lit)
    matched = length(code) + 2

    code =
      code ++
        [
          %{"op" => "jump_if_eq", "target" => matched, "reg" => scr, "lit" => jlit},
          %{"op" => "jump", "target" => 0}
        ]

    fail_idx = length(code) - 1
    {:ok, code, env, next, fail_idx}
  end

  defp emit_pattern_test({a, b}, scr, env, next, code) do
    emit_pattern_test({:{}, [], [a, b]}, scr, env, next, code)
  end

  defp emit_pattern_test({:{}, _, elems}, scr, env, next, code) when is_list(elems) do
    emit_compound_pattern_test("tuple", "get_tuple_elem", "tuple", elems, scr, env, next, code,
      length_check: true
    )
  end

  # `e in [lit, …]` or `e in lit` — or of literal equality tests (rescue tags).
  defp emit_pattern_test({:in, _, [var, targets]}, scr, env, next, code) do
    emit_in_pattern_test(var, targets, scr, env, next, code)
  end

  # Map patterns %{lit_key => pat, ...} (literal keys only).
  defp emit_pattern_test({:%{}, _, pairs}, scr, env, next, code) when is_list(pairs) do
    emit_map_pattern_test(pairs, scr, env, next, code)
  end

  # Bitstring patterns `<<…>>` (teaching subset).
  defp emit_pattern_test({:<<>>, _, segs}, scr, env, next, code) when is_list(segs) do
    emit_bitstring_pattern_test(segs, scr, env, next, code)
  end

  # Empty list / fixed-length list / cons [… | t] patterns.
  defp emit_pattern_test(elems, scr, env, next, code) when is_list(elems) do
    case split_list_pattern(elems) do
      {:error, _} = err ->
        err

      {:proper, []} ->
        matched = length(code) + 2

        code =
          code ++
            [
              %{
                "op" => "jump_if_eq",
                "target" => matched,
                "reg" => scr,
                "lit" => %{"list" => []}
              },
              %{"op" => "jump", "target" => 0}
            ]

        fail_idx = length(code) - 1
        {:ok, code, env, next, fail_idx}

      {:proper, proper} ->
        emit_compound_pattern_test(
          "list",
          "get_list_elem",
          "list",
          proper,
          scr,
          env,
          next,
          code,
          length_check: true
        )

      {:cons, prefix, head, tail} ->
        emit_cons_pattern_test(prefix, head, tail, scr, env, next, code)
    end
  end

  defp emit_pattern_test(other, _, _, _, _),
    do:
      {:error,
       "match (=): unsupported pattern #{Macro.to_string(other)} (use case/fn clauses for complex heads)"}

  defp split_list_pattern(elems) when is_list(elems) do
    {prefix, rest} =
      Enum.split_while(elems, fn
        {:|, _, _} -> false
        _ -> true
      end)

    case rest do
      [] ->
        {:proper, elems}

      [{:|, _, [h, t]}] ->
        {:cons, prefix, h, t}

      _ ->
        {:error, "unsupported list pattern: #{Macro.to_string(elems)}"}
    end
  end

  defp emit_cons_pattern_test(prefix, head, tail, scr, env, next, code) do
    min_len = length(prefix) + 1
    tag_reg = next
    next = next + 1
    code = code ++ [%{"op" => "is_tag", "dest" => tag_reg, "reg" => scr, "tag" => "list"}]
    matched_after_tag = length(code) + 2

    code =
      code ++
        [
          %{
            "op" => "jump_if_eq",
            "target" => matched_after_tag,
            "reg" => tag_reg,
            "lit" => %{"bool" => true}
          },
          %{"op" => "jump", "target" => 0}
        ]

    fail_idx = length(code) - 1

    with {:ok, code, env, next, fail_idx} <-
           emit_fail_if_size_lt(scr, min_len, fail_idx, env, next, code),
         {:ok, code, env, next, fail_idx} <-
           emit_list_elem_lit_tests(prefix ++ [head], scr, fail_idx, env, next, code) do
      rest_reg = next
      next = next + 1
      rest_idx = length(prefix)

      code =
        code ++
          [
            %{
              "op" => "get_list_rest",
              "dest" => rest_reg,
              "list" => scr,
              "index" => rest_idx
            }
          ]

      case emit_pattern_test(tail, rest_reg, env, next, code) do
        {:ok, code, env, next, inner_fail} ->
          code =
            List.update_at(code, inner_fail, fn j ->
              %{j | "target" => fail_idx}
            end)

          {:ok, code, env, next, fail_idx}

        {:error, _} = err ->
          err
      end
    end
  end

  # Fail the clause if list_size(scr) is in 0..min_len-1.
  defp emit_fail_if_size_lt(scr, min_len, fail_idx, env, next, code) do
    size_reg = next
    next = next + 1

    code =
      code ++
        [%{"op" => "call", "dest" => size_reg, "fun" => "list_size/1", "args" => [scr]}]

    code =
      Enum.reduce(0..(min_len - 1), code, fn i, code ->
        size_is_i = length(code) + 2
        continue = size_is_i + 1

        code ++
          [
            %{
              "op" => "jump_if_eq",
              "target" => size_is_i,
              "reg" => size_reg,
              "lit" => %{"int" => i}
            },
            %{"op" => "jump", "target" => continue},
            %{"op" => "jump", "target" => fail_idx}
          ]
      end)

    {:ok, code, env, next, fail_idx}
  end

  defp emit_list_elem_lit_tests(elems, scr, fail_idx, env, next, code) do
    Enum.reduce_while(Enum.with_index(elems), {:ok, code, env, next, fail_idx}, fn
      {elem, idx}, {:ok, code, env, next, fail_idx} ->
        case lit_value(elem) do
          {:ok, jlit} ->
            er = next
            next = next + 1

            code =
              code ++
                [
                  %{
                    "op" => "get_list_elem",
                    "dest" => er,
                    "list" => scr,
                    "index" => idx
                  }
                ]

            matched = length(code) + 2

            code =
              code ++
                [
                  %{"op" => "jump_if_eq", "target" => matched, "reg" => er, "lit" => jlit},
                  %{"op" => "jump", "target" => 0}
                ]

            new_fail = length(code) - 1

            code =
              List.update_at(code, new_fail, fn j ->
                %{j | "target" => fail_idx}
              end)

            {:cont, {:ok, code, env, next, fail_idx}}

          :error ->
            case elem do
              {name, _, nil} when is_atom(name) ->
                {:cont, {:ok, code, env, next, fail_idx}}

              other ->
                emit_nested_elem_pattern_test(
                  "get_list_elem",
                  "list",
                  other,
                  idx,
                  scr,
                  fail_idx,
                  env,
                  next,
                  code
                )
            end
        end
    end)
  end

  defp emit_compound_pattern_test(tag, get_op, get_field, elems, scr, env, next, code, opts \\ []) do
    length_check? = Keyword.get(opts, :length_check, false)
    tag_reg = next
    next = next + 1
    code = code ++ [%{"op" => "is_tag", "dest" => tag_reg, "reg" => scr, "tag" => tag}]
    matched_after_tag = length(code) + 2

    code =
      code ++
        [
          %{
            "op" => "jump_if_eq",
            "target" => matched_after_tag,
            "reg" => tag_reg,
            "lit" => %{"bool" => true}
          },
          %{"op" => "jump", "target" => 0}
        ]

    fail_idx = length(code) - 1

    {code, env, next, fail_idx} =
      if length_check? do
        size_reg = next
        next = next + 1
        size_fun = if tag == "tuple", do: "tuple_size/1", else: "list_size/1"

        code =
          code ++
            [
              %{
                "op" => "call",
                "dest" => size_reg,
                "fun" => size_fun,
                "args" => [scr]
              }
            ]

        matched = length(code) + 2

        code =
          code ++
            [
              %{
                "op" => "jump_if_eq",
                "target" => matched,
                "reg" => size_reg,
                "lit" => %{"int" => length(elems)}
              },
              %{"op" => "jump", "target" => 0}
            ]

        new_fail = length(code) - 1

        code =
          List.update_at(code, new_fail, fn j ->
            %{j | "target" => fail_idx}
          end)

        {code, env, next, fail_idx}
      else
        {code, env, next, fail_idx}
      end

    Enum.reduce_while(Enum.with_index(elems), {:ok, code, env, next, fail_idx}, fn
      {elem, idx}, {:ok, code, env, next, fail_idx} ->
        case lit_value(elem) do
          {:ok, jlit} ->
            er = next
            next = next + 1

            code =
              code ++
                [
                  %{
                    "op" => get_op,
                    "dest" => er,
                    get_field => scr,
                    "index" => idx
                  }
                ]

            matched = length(code) + 2

            code =
              code ++
                [
                  %{"op" => "jump_if_eq", "target" => matched, "reg" => er, "lit" => jlit},
                  %{"op" => "jump", "target" => 0}
                ]

            new_fail = length(code) - 1

            code =
              List.update_at(code, new_fail, fn j ->
                %{j | "target" => fail_idx}
              end)

            {:cont, {:ok, code, env, next, fail_idx}}

          :error ->
            case elem do
              {name, _, nil} when is_atom(name) ->
                {:cont, {:ok, code, env, next, fail_idx}}

              other ->
                emit_nested_elem_pattern_test(
                  get_op,
                  get_field,
                  other,
                  idx,
                  scr,
                  fail_idx,
                  env,
                  next,
                  code
                )
            end
        end
    end)
  end

  defp emit_nested_elem_pattern_test(get_op, get_field, pat, idx, scr, fail_idx, env, next, code) do
    er = next
    next = next + 1

    code =
      code ++
        [
          %{
            "op" => get_op,
            "dest" => er,
            get_field => scr,
            "index" => idx
          }
        ]

    case emit_pattern_test(pat, er, env, next, code) do
      {:ok, code, env, next, inner_fail} ->
        code =
          List.update_at(code, inner_fail, fn j ->
            %{j | "target" => fail_idx}
          end)

        {:cont, {:ok, code, env, next, fail_idx}}

      {:error, _} = err ->
        {:halt, err}
    end
  end

  defp emit_pattern_binds({name, _, nil}, scr, env, next, code)
       when is_atom(name) and name != :_ do
    env = Map.put(env, name, scr)
    {:ok, code, env, next}
  end

  defp emit_pattern_binds({:^, _, _}, _scr, env, next, code), do: {:ok, code, env, next}

  defp emit_pattern_binds({:{}, _, elems}, scr, env, next, code) do
    emit_compound_pattern_binds("get_tuple_elem", "tuple", elems, scr, env, next, code)
  end

  defp emit_pattern_binds({a, b}, scr, env, next, code) do
    emit_pattern_binds({:{}, [], [a, b]}, scr, env, next, code)
  end

  defp emit_pattern_binds({:in, _, [var, _targets]}, scr, env, next, code) do
    emit_pattern_binds(var, scr, env, next, code)
  end

  defp emit_pattern_binds({:%{}, _, pairs}, scr, env, next, code) when is_list(pairs) do
    emit_map_pattern_binds(pairs, scr, env, next, code)
  end

  defp emit_pattern_binds({:<<>>, _, segs}, scr, env, next, code) when is_list(segs) do
    emit_bitstring_pattern_binds(segs, scr, env, next, code)
  end

  defp emit_pattern_binds(elems, scr, env, next, code) when is_list(elems) do
    case split_list_pattern(elems) do
      {:error, _} = err ->
        err

      {:proper, proper} ->
        emit_compound_pattern_binds("get_list_elem", "list", proper, scr, env, next, code)

      {:cons, prefix, head, tail} ->
        emit_cons_pattern_binds(prefix, head, tail, scr, env, next, code)
    end
  end

  defp emit_pattern_binds(_, _scr, env, next, code), do: {:ok, code, env, next}

  # Match scr against any literal in `targets` (list or single lit). Fail jump on miss.
  defp emit_in_pattern_test(_var, targets, scr, env, next, code) do
    lits =
      case targets do
        list when is_list(list) -> list
        one -> [one]
      end

    with {:ok, jlits} <-
           Enum.reduce_while(lits, {:ok, []}, fn lit, {:ok, acc} ->
             case lit_value(lit) do
               {:ok, jlit} -> {:cont, {:ok, acc ++ [jlit]}}
               :error -> {:halt, {:error, "rescue in-list elements must be literals"}}
             end
           end) do
      if jlits == [] do
        {:error, "empty rescue in-list"}
      else
        # For each lit: jump_if_eq matched; after all: jump fail; matched: fall through.
        fail_placeholder = length(code)
        # We'll emit: for lit in jlits: jump_if_eq MATCH lit; then jump FAIL; MATCH:
        {code, match_jumps} =
          Enum.reduce(jlits, {code, []}, fn jlit, {code, jumps} ->
            code =
              code ++
                [
                  %{
                    "op" => "jump_if_eq",
                    "target" => 0,
                    "reg" => scr,
                    "lit" => jlit
                  }
                ]

            {code, jumps ++ [length(code) - 1]}
          end)

        code = code ++ [%{"op" => "jump", "target" => 0}]
        fail_idx = length(code) - 1
        matched_ip = length(code)

        code =
          Enum.reduce(match_jumps, code, fn idx, code ->
            List.update_at(code, idx, fn j -> %{j | "target" => matched_ip} end)
          end)

        _ = fail_placeholder
        {:ok, code, env, next, fail_idx}
      end
    end
  end

  defp emit_bitstring_pattern_test(segs, scr, env, next, code) do
    case classify_bitstring_pattern(segs) do
      {:exact, jlit} ->
        matched = length(code) + 2

        code =
          code ++
            [
              %{"op" => "jump_if_eq", "target" => matched, "reg" => scr, "lit" => jlit},
              %{"op" => "jump", "target" => 0}
            ]

        {:ok, code, env, next, length(code) - 1}

      {:ok, parsed} ->
        emit_bitstring_match_test(parsed, scr, env, next, code)

      {:error, _} = err ->
        err
    end
  end

  defp emit_bitstring_match_test(parsed, scr, env, next, code) do
    fixed_bits =
      parsed
      |> Enum.reject(&(match?({:rest, _}, &1) or match?({:var_dyn, _, _}, &1)))
      |> Enum.map(fn
        {:lit, _, size} -> size
        {:var, _, size} -> size
      end)
      |> Enum.sum()

    dyn_sizes =
      parsed
      |> Enum.filter(&match?({:var_dyn, _, _}, &1))
      |> Enum.map(fn {:var_dyn, _, size_name} -> size_name end)

    has_rest = Enum.any?(parsed, &match?({:rest, _}, &1))

    # Exclude UTF-8 string (is_tag bitstring is true for string).
    str_reg = next
    next = next + 1
    code = code ++ [%{"op" => "is_tag", "dest" => str_reg, "reg" => scr, "tag" => "string"}]
    not_string = length(code) + 2

    code =
      code ++
        [
          %{
            "op" => "jump_if_eq",
            "target" => not_string,
            "reg" => str_reg,
            "lit" => %{"bool" => false}
          },
          %{"op" => "jump", "target" => 0}
        ]

    fail_idx = length(code) - 1

    # Require raw bitstring.
    tag_reg = next
    next = next + 1
    code = code ++ [%{"op" => "is_tag", "dest" => tag_reg, "reg" => scr, "tag" => "bitstring"}]
    is_bs = length(code) + 2

    code =
      code ++
        [
          %{
            "op" => "jump_if_eq",
            "target" => is_bs,
            "reg" => tag_reg,
            "lit" => %{"bool" => true}
          },
          %{"op" => "jump", "target" => fail_idx}
        ]

    # bit_size checks (static fixed bits + runtime ::size(var) widths)
    size_reg = next
    next = next + 1
    need_reg = next
    next = next + 1
    cmp_reg = next
    next = next + 1

    code =
      code ++
        [
          %{"op" => "call", "dest" => size_reg, "fun" => "bit_size/1", "args" => [scr]},
          %{"op" => "load_lit", "reg" => need_reg, "lit" => %{"int" => fixed_bits}}
        ]

    with {:ok, code, next, need_reg} <- emit_add_dyn_sizes(dyn_sizes, need_reg, env, next, code) do
      emit_bitstring_size_cmp(
        has_rest,
        size_reg,
        need_reg,
        cmp_reg,
        fail_idx,
        parsed,
        scr,
        env,
        next,
        code
      )
    end
  end

  defp emit_add_dyn_sizes(dyn_sizes, need_reg, env, next, code) do
    Enum.reduce_while(dyn_sizes, {:ok, code, next, need_reg}, fn
      size_name, {:ok, code, next, need_reg} ->
        case Map.fetch(env, size_name) do
          {:ok, size_src} ->
            sum_reg = next
            next = next + 1

            code =
              code ++
                [
                  %{
                    "op" => "call",
                    "dest" => sum_reg,
                    "fun" => "+/2",
                    "args" => [need_reg, size_src]
                  }
                ]

            {:cont, {:ok, code, next, sum_reg}}

          :error ->
            {:halt, {:error, "unbound size variable #{size_name} in bitstring pattern"}}
        end
    end)
  end

  defp emit_bitstring_size_cmp(
         has_rest,
         size_reg,
         need_reg,
         cmp_reg,
         fail_idx,
         parsed,
         scr,
         env,
         next,
         code
       ) do
    {code, next, cmp_reg} =
      if has_rest do
        # size >= fixed_bits
        code =
          code ++
            [
              %{
                "op" => "call",
                "dest" => cmp_reg,
                "fun" => ">=/2",
                "args" => [size_reg, need_reg]
              }
            ]

        ok = length(code) + 2

        code =
          code ++
            [
              %{
                "op" => "jump_if_eq",
                "target" => ok,
                "reg" => cmp_reg,
                "lit" => %{"bool" => true}
              },
              %{"op" => "jump", "target" => fail_idx}
            ]

        {code, next, cmp_reg}
      else
        # size == fixed_bits
        code =
          code ++
            [
              %{
                "op" => "call",
                "dest" => cmp_reg,
                "fun" => "==/2",
                "args" => [size_reg, need_reg]
              }
            ]

        ok = length(code) + 2

        code =
          code ++
            [
              %{
                "op" => "jump_if_eq",
                "target" => ok,
                "reg" => cmp_reg,
                "lit" => %{"bool" => true}
              },
              %{"op" => "jump", "target" => fail_idx}
            ]

        {code, next, cmp_reg}
      end

    _ = cmp_reg

    # Walk segments: lit equality + drop; vars only drop (bind later).
    case Enum.reduce_while(parsed, {:ok, code, env, next, scr}, fn
           seg, {:ok, code, env, next, cur} ->
             case emit_bitstring_seg_test(seg, cur, fail_idx, env, next, code) do
               {:ok, code, env, next, cur} -> {:cont, {:ok, code, env, next, cur}}
               {:error, _} = err -> {:halt, err}
             end
         end) do
      {:ok, code, env, next, _cur} ->
        {:ok, code, env, next, fail_idx}

      {:error, _} = err ->
        err
    end
  end

  defp emit_bitstring_seg_test({:rest, _name}, cur, fail_idx, env, next, code) do
    # Remaining must be aligned binary (string already excluded on original scr;
    # cursor is always a bitstring from bs_drop).
    tag_reg = next
    next = next + 1
    code = code ++ [%{"op" => "is_tag", "dest" => tag_reg, "reg" => cur, "tag" => "binary"}]
    ok = length(code) + 2

    code =
      code ++
        [
          %{
            "op" => "jump_if_eq",
            "target" => ok,
            "reg" => tag_reg,
            "lit" => %{"bool" => true}
          },
          %{"op" => "jump", "target" => fail_idx}
        ]

    {:ok, code, env, next, cur}
  end

  defp emit_bitstring_seg_test({:lit, value, size}, cur, fail_idx, env, next, code) do
    {:ok, code, next, val_reg, drop_reg} = emit_bs_get_chunked(cur, size, next, code)
    ok = length(code) + 2

    code =
      code ++
        [
          %{
            "op" => "jump_if_eq",
            "target" => ok,
            "reg" => val_reg,
            "lit" => %{"int" => value}
          },
          %{"op" => "jump", "target" => fail_idx}
        ]

    {:ok, code, env, next, drop_reg}
  end

  defp emit_bitstring_seg_test({:var, _name, size}, cur, _fail_idx, env, next, code) do
    size_reg = next
    next = next + 1
    drop_reg = next
    next = next + 1

    # Size already enforced by total bit_size check; just advance the cursor.
    code =
      code ++
        [
          %{"op" => "load_lit", "reg" => size_reg, "lit" => %{"int" => size}},
          %{
            "op" => "call",
            "dest" => drop_reg,
            "fun" => "bs_drop/2",
            "args" => [cur, size_reg]
          }
        ]

    {:ok, code, env, next, drop_reg}
  end

  defp emit_bitstring_seg_test({:var_dyn, _name, size_name}, cur, _fail_idx, env, next, code) do
    case Map.fetch(env, size_name) do
      {:ok, size_src} ->
        drop_reg = next
        next = next + 1

        code =
          code ++
            [
              %{
                "op" => "call",
                "dest" => drop_reg,
                "fun" => "bs_drop/2",
                "args" => [cur, size_src]
              }
            ]

        {:ok, code, env, next, drop_reg}

      :error ->
        {:error, "unbound size variable #{size_name} in bitstring pattern"}
    end
  end

  defp emit_bitstring_pattern_binds(segs, scr, env, next, code) do
    case classify_bitstring_pattern(segs) do
      {:exact, _} ->
        {:ok, code, env, next}

      {:ok, parsed} ->
        Enum.reduce_while(parsed, {:ok, code, env, next, scr}, fn
          seg, {:ok, code, env, next, cur} ->
            case emit_bitstring_seg_bind(seg, cur, env, next, code) do
              {:ok, code, env, next, cur} -> {:cont, {:ok, code, env, next, cur}}
              {:error, _} = err -> {:halt, err}
            end
        end)
        |> case do
          {:ok, code, env, next, _cur} -> {:ok, code, env, next}
          {:error, _} = err -> err
        end

      {:error, _} = err ->
        err
    end
  end

  defp emit_bitstring_seg_bind({:rest, name}, cur, env, next, code) do
    env = Map.put(env, name, cur)
    {:ok, code, env, next, cur}
  end

  defp emit_bitstring_seg_bind({:lit, _value, size}, cur, env, next, code) do
    size_reg = next
    next = next + 1
    drop_reg = next
    next = next + 1

    code =
      code ++
        [
          %{"op" => "load_lit", "reg" => size_reg, "lit" => %{"int" => size}},
          %{
            "op" => "call",
            "dest" => drop_reg,
            "fun" => "bs_drop/2",
            "args" => [cur, size_reg]
          }
        ]

    {:ok, code, env, next, drop_reg}
  end

  defp emit_bitstring_seg_bind({:var, :_, size}, cur, env, next, code) do
    # Same as lit: advance cursor only.
    size_reg = next
    next = next + 1
    drop_reg = next
    next = next + 1

    code =
      code ++
        [
          %{"op" => "load_lit", "reg" => size_reg, "lit" => %{"int" => size}},
          %{
            "op" => "call",
            "dest" => drop_reg,
            "fun" => "bs_drop/2",
            "args" => [cur, size_reg]
          }
        ]

    {:ok, code, env, next, drop_reg}
  end

  defp emit_bitstring_seg_bind({:var, name, size}, cur, env, next, code) do
    {:ok, code, next, val_reg, drop_reg} = emit_bs_get_chunked(cur, size, next, code)
    env = Map.put(env, name, val_reg)
    {:ok, code, env, next, drop_reg}
  end

  defp emit_bitstring_seg_bind({:var_dyn, :_, size_name}, cur, env, next, code) do
    case Map.fetch(env, size_name) do
      {:ok, size_src} ->
        drop_reg = next
        next = next + 1

        code =
          code ++
            [
              %{
                "op" => "call",
                "dest" => drop_reg,
                "fun" => "bs_drop/2",
                "args" => [cur, size_src]
              }
            ]

        {:ok, code, env, next, drop_reg}

      :error ->
        {:error, "unbound size variable #{size_name} in bitstring pattern"}
    end
  end

  defp emit_bitstring_seg_bind({:var_dyn, name, size_name}, cur, env, next, code) do
    case Map.fetch(env, size_name) do
      {:ok, size_src} ->
        val_reg = next
        next = next + 1
        drop_reg = next
        next = next + 1

        code =
          code ++
            [
              %{
                "op" => "call",
                "dest" => val_reg,
                "fun" => "bs_get_integer/2",
                "args" => [cur, size_src]
              },
              %{
                "op" => "call",
                "dest" => drop_reg,
                "fun" => "bs_drop/2",
                "args" => [cur, size_src]
              }
            ]

        env = Map.put(env, name, val_reg)
        {:ok, code, env, next, drop_reg}

      :error ->
        {:error, "unbound size variable #{size_name} in bitstring pattern"}
    end
  end

  # Match sizes 1…32: emit repeated 1…8-bit `bs_get_integer` + combine (MSB-first).
  defp match_bit_chunks(size) when size >= 1 and size <= 32 do
    rem = rem(size, 8)
    n8 = div(size, 8)
    prefix = if rem == 0, do: [], else: [rem]
    prefix ++ List.duplicate(8, n8)
  end

  defp emit_bs_get_chunked(cur, size, next, code) do
    chunks = match_bit_chunks(size)
    acc_reg = next
    next = next + 1
    code = code ++ [%{"op" => "load_lit", "reg" => acc_reg, "lit" => %{"int" => 0}}]

    {code, next, acc_reg, cursor} =
      Enum.reduce(chunks, {code, next, acc_reg, cur}, fn chunk, {code, next, acc, cursor} ->
        size_reg = next
        next = next + 1
        part_reg = next
        next = next + 1
        shift_reg = next
        next = next + 1
        mul_reg = next
        next = next + 1
        sum_reg = next
        next = next + 1
        drop_reg = next
        next = next + 1

        code =
          code ++
            [
              %{"op" => "load_lit", "reg" => size_reg, "lit" => %{"int" => chunk}},
              %{
                "op" => "call",
                "dest" => part_reg,
                "fun" => "bs_get_integer/2",
                "args" => [cursor, size_reg]
              },
              %{
                "op" => "load_lit",
                "reg" => shift_reg,
                "lit" => %{"int" => Bitwise.bsl(1, chunk)}
              },
              %{"op" => "call", "dest" => mul_reg, "fun" => "*/2", "args" => [acc, shift_reg]},
              %{"op" => "call", "dest" => sum_reg, "fun" => "+/2", "args" => [mul_reg, part_reg]},
              %{
                "op" => "call",
                "dest" => drop_reg,
                "fun" => "bs_drop/2",
                "args" => [cursor, size_reg]
              }
            ]

        {code, next, sum_reg, drop_reg}
      end)

    {:ok, code, next, acc_reg, cursor}
  end

  defp classify_bitstring_pattern(segs) do
    case literal_bitstring_lit(segs) do
      {:ok, jlit} ->
        {:exact, jlit}

      {:error, _} ->
        case parse_bitstring_match_segs(segs) do
          {:ok, parsed} -> {:ok, parsed}
          {:error, _} = err -> err
        end
    end
  end

  defp parse_bitstring_match_segs(segs) do
    case Enum.reduce_while(segs, {:ok, []}, fn seg, {:ok, acc} ->
           if Enum.any?(acc, &match?({:rest, _}, &1)) do
             {:halt, {:error, "rest::binary must be last in bitstring pattern"}}
           else
             case classify_bitstring_match_seg(seg) do
               {:ok, item} -> {:cont, {:ok, acc ++ [item]}}
               {:error, _} = err -> {:halt, err}
             end
           end
         end) do
      {:ok, parsed} ->
        rests = Enum.count(parsed, &match?({:rest, _}, &1))

        cond do
          rests > 1 ->
            {:error, "at most one rest::binary in bitstring pattern"}

          parsed == [] ->
            # empty <<>> — treat as exact empty binary via lit path normally
            {:ok, []}

          true ->
            {:ok, parsed}
        end

      {:error, _} = err ->
        err
    end
  end

  defp classify_bitstring_match_seg(n) when is_integer(n) and n >= 0 and n <= 255,
    do: {:ok, {:lit, n, 8}}

  defp classify_bitstring_match_seg({:"::", _, [n]})
       when is_integer(n) and n >= 0 and n <= 255,
       do: {:ok, {:lit, n, 8}}

  defp classify_bitstring_match_seg({:"::", _, [n, spec]}) when is_integer(n) do
    case segment_size(spec) do
      {:ok, size} when size >= 1 and size <= 32 ->
        max = Bitwise.bsl(1, size)

        if n < 0 or n >= max do
          {:error, "integer #{n} does not fit in ::#{size} in bitstring pattern"}
        else
          {:ok, {:lit, n, size}}
        end

      {:ok, size} ->
        {:error, "unsupported bitstring pattern size #{size} (teaching subset: 1..32)"}

      :error ->
        {:error, "unsupported bitstring pattern segment specifier"}
    end
  end

  defp classify_bitstring_match_seg({:"::", _, [{name, _, ctx}, spec]})
       when is_atom(name) and (is_atom(ctx) or is_nil(ctx)) do
    cond do
      binary_type_spec?(spec) ->
        if name == :_ do
          {:error, "anonymous rest::binary not supported; bind a variable"}
        else
          {:ok, {:rest, name}}
        end

      utf8_type_spec?(spec) ->
        {:error, "unsupported bitstring pattern ::utf8 (construct-only teaching subset)"}

      match?({:size, _, [{size_name, _, sctx}]}
            when is_atom(size_name) and (is_atom(sctx) or is_nil(sctx)), spec) ->
        {:size, _, [{size_name, _, _}]} = spec

        if name == :_ do
          {:ok, {:var_dyn, :_, size_name}}
        else
          {:ok, {:var_dyn, name, size_name}}
        end

      true ->
        case segment_size(spec) do
          {:ok, size} when size >= 1 and size <= 32 ->
            if name == :_ do
              {:ok, {:var, :_, size}}
            else
              {:ok, {:var, name, size}}
            end

          {:ok, size} ->
            {:error, "unsupported bitstring pattern size #{size} (teaching subset: 1..32)"}

          :error ->
            {:error, "unsupported bitstring pattern segment on variable"}
        end
    end
  end

  defp classify_bitstring_match_seg({name, _, ctx})
       when is_atom(name) and name != :_ and (is_atom(ctx) or is_nil(ctx)) do
    # Bare `<<x>>` ⇒ `<<x::8>>`
    {:ok, {:var, name, 8}}
  end

  defp classify_bitstring_match_seg(_),
    do: {:error, "unsupported bitstring pattern segment (teaching: lit ints / var::N / rest::binary)"}

  defp binary_type_spec?(:binary), do: true
  defp binary_type_spec?({:binary, _, _}), do: true
  defp binary_type_spec?(_), do: false

  defp utf8_type_spec?(:utf8), do: true
  defp utf8_type_spec?({:utf8, _, _}), do: true
  defp utf8_type_spec?(_), do: false

  defp emit_map_pattern_test(pairs, scr, env, next, code) do
    tag_reg = next
    next = next + 1
    code = code ++ [%{"op" => "is_tag", "dest" => tag_reg, "reg" => scr, "tag" => "map"}]
    matched_after_tag = length(code) + 2

    code =
      code ++
        [
          %{
            "op" => "jump_if_eq",
            "target" => matched_after_tag,
            "reg" => tag_reg,
            "lit" => %{"bool" => true}
          },
          %{"op" => "jump", "target" => 0}
        ]

    fail_idx = length(code) - 1

    Enum.reduce_while(pairs, {:ok, code, env, next, fail_idx}, fn
      {key, val_pat}, {:ok, code, env, next, fail_idx} ->
        case lit_value(key) do
          {:ok, jkey} ->
            key_reg = next
            next = next + 1
            val_reg = next
            next = next + 1

            code =
              code ++
                [
                  %{"op" => "load_lit", "reg" => key_reg, "lit" => jkey},
                  %{
                    "op" => "call",
                    "dest" => val_reg,
                    "fun" => "map_get/2",
                    "args" => [scr, key_reg]
                  }
                ]

            case emit_pattern_test(val_pat, val_reg, env, next, code) do
              {:ok, code, env, next, inner_fail} ->
                code =
                  List.update_at(code, inner_fail, fn j ->
                    %{j | "target" => fail_idx}
                  end)

                {:cont, {:ok, code, env, next, fail_idx}}

              {:error, _} = err ->
                {:halt, err}
            end

          :error ->
            {:halt, {:error, "map pattern keys must be literals"}}
        end

      _, _ ->
        {:halt, {:error, "unsupported map pattern"}}
    end)
  end

  defp emit_map_pattern_binds(pairs, scr, env, next, code) do
    Enum.reduce_while(pairs, {:ok, code, env, next}, fn
      {key, val_pat}, {:ok, code, env, next} ->
        case lit_value(key) do
          {:ok, jkey} ->
            key_reg = next
            next = next + 1
            val_reg = next
            next = next + 1

            code =
              code ++
                [
                  %{"op" => "load_lit", "reg" => key_reg, "lit" => jkey},
                  %{
                    "op" => "call",
                    "dest" => val_reg,
                    "fun" => "map_get/2",
                    "args" => [scr, key_reg]
                  }
                ]

            case emit_pattern_binds(val_pat, val_reg, env, next, code) do
              {:ok, code, env, next} ->
                {:cont, {:ok, code, env, next}}

              {:error, _} = err ->
                {:halt, err}
            end

          :error ->
            {:halt, {:error, "map pattern keys must be literals"}}
        end

      _, _ ->
        {:halt, {:error, "unsupported map pattern"}}
    end)
  end

  defp emit_cons_pattern_binds(prefix, head, tail, scr, env, next, code) do
    with {:ok, code, env, next} <-
           emit_compound_pattern_binds(
             "get_list_elem",
             "list",
             prefix ++ [head],
             scr,
             env,
             next,
             code
           ) do
      rest_reg = next
      next = next + 1
      rest_idx = length(prefix)

      code =
        code ++
          [
            %{
              "op" => "get_list_rest",
              "dest" => rest_reg,
              "list" => scr,
              "index" => rest_idx
            }
          ]

      emit_pattern_binds(tail, rest_reg, env, next, code)
    end
  end

  defp emit_compound_pattern_binds(get_op, get_field, elems, scr, env, next, code) do
    Enum.reduce_while(Enum.with_index(elems), {:ok, code, env, next}, fn
      {{name, _, nil}, idx}, {:ok, code, env, next} when is_atom(name) and name != :_ ->
        dest = next
        next = next + 1

        code =
          code ++
            [
              %{
                "op" => get_op,
                "dest" => dest,
                get_field => scr,
                "index" => idx
              }
            ]

        {:cont, {:ok, code, Map.put(env, name, dest), next}}

      # `_`, pins, and literals need no bind work.
      {{:_, _, nil}, _idx}, acc ->
        {:cont, acc}

      {{:^, _, _}, _idx}, acc ->
        {:cont, acc}

      {elem, idx}, {:ok, code, env, next} ->
        case lit_value(elem) do
          {:ok, _} ->
            {:cont, {:ok, code, env, next}}

          :error ->
            dest = next
            next = next + 1

            code =
              code ++
                [
                  %{
                    "op" => get_op,
                    "dest" => dest,
                    get_field => scr,
                    "index" => idx
                  }
                ]

            case emit_pattern_binds(elem, dest, env, next, code) do
              {:ok, code, env, next} ->
                {:cont, {:ok, code, env, next}}

              {:error, _} = err ->
                {:halt, err}
            end
        end
    end)
  end

  defp lower_call_named(fun, args, env, next, code) do
    with {:ok, code, env, next, arg_regs} <- map_exprs(args, env, next, code) do
      dest = next
      instr = %{"op" => "call", "dest" => dest, "fun" => fun, "args" => arg_regs}
      {:ok, code ++ [instr], env, next + 1, dest}
    end
  end

  defp map_exprs(exprs, env, next, code) do
    Enum.reduce_while(exprs, {:ok, code, env, next, []}, fn e, {:ok, code, env, next, regs} ->
      case expr(e, env, next, code) do
        {:ok, code, env, next, reg} ->
          {:cont, {:ok, code, env, next, regs ++ [reg]}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  defp emit_lit(lit, env, next, code) do
    reg = next
    instr = %{"op" => "load_lit", "reg" => reg, "lit" => lit}
    {:ok, code ++ [instr], env, next + 1, reg}
  end

  defp literal_tuple(elems) do
    Enum.reduce_while(elems, {:ok, []}, fn e, {:ok, acc} ->
      case lit_value(e) do
        {:ok, lit} -> {:cont, {:ok, acc ++ [lit]}}
        :error -> {:halt, :error}
      end
    end)
    |> case do
      {:ok, lits} -> {:ok, %{"tuple" => lits}}
      :error -> :error
    end
  end

  defp literal_list(elems) do
    Enum.reduce_while(elems, {:ok, []}, fn e, {:ok, acc} ->
      case lit_value(e) do
        {:ok, lit} -> {:cont, {:ok, acc ++ [lit]}}
        :error -> {:halt, :error}
      end
    end)
    |> case do
      {:ok, lits} -> {:ok, %{"list" => lits}}
      :error -> :error
    end
  end

  defp literal_map(pairs) do
    Enum.reduce_while(pairs, {:ok, []}, fn
      {k, v}, {:ok, acc} ->
        with {:ok, kl} <- lit_value(k),
             {:ok, vl} <- lit_value(v) do
          {:cont, {:ok, acc ++ [%{"key" => kl, "value" => vl}]}}
        else
          :error -> {:halt, :error}
        end

      _, _ ->
        {:halt, :error}
    end)
    |> case do
      {:ok, entries} -> {:ok, %{"map" => entries}}
      :error -> :error
    end
  end

  defp lit_value(nil), do: {:ok, nil}
  defp lit_value(b) when is_boolean(b), do: {:ok, %{"bool" => b}}
  defp lit_value(n) when is_integer(n), do: {:ok, %{"int" => n}}
  defp lit_value(f) when is_float(f), do: {:ok, %{"float" => f}}
  defp lit_value(s) when is_binary(s), do: {:ok, %{"string" => s}}
  defp lit_value(a) when is_atom(a), do: {:ok, %{"atom" => Atom.to_string(a)}}
  defp lit_value(list) when is_list(list), do: literal_list(list)

  defp lit_value({:%{}, _, pairs}) when is_list(pairs), do: literal_map(pairs)

  defp lit_value({:<<>>, _, segs}) when is_list(segs) do
    case literal_bitstring_lit(segs) do
      {:ok, lit} -> {:ok, lit}
      {:error, _} -> :error
    end
  end

  defp lit_value({:{}, _, elems}) do
    case literal_tuple(elems) do
      {:ok, lit} -> {:ok, lit}
      :error -> :error
    end
  end

  defp lit_value({a, b}), do: lit_value({:{}, [], [a, b]})
  defp lit_value(_), do: :error

  # Pack `<<…>>` into `binary` or partial `bitstring` lit (MSB-first).
  defp literal_bitstring_lit(segs) do
    case pack_bitstring_segments(segs) do
      {:ok, bytes, 0} ->
        {:ok, %{"binary" => bytes}}

      {:ok, bytes, trailing} ->
        {:ok, %{"bitstring" => %{"bytes" => bytes, "trailing_bits" => trailing}}}

      {:error, _} = err ->
        err
    end
  end

  defp pack_bitstring_segments(segs) do
    # Integer segments of size 1…8 may appear mid-construct (`<<1::3, 2::5>>`).
    # Byte/string segments still require bit alignment (cannot follow a partial).
    case Enum.reduce_while(segs, {:ok, []}, fn seg, {:ok, bits} ->
           case bitstring_segment_bits(seg) do
             {:ok, seg_bits, :bytes} ->
               if rem(length(bits), 8) != 0 do
                 {:halt,
                  {:error,
                   "byte segment cannot follow a partial bitstring segment in <<…>>"}}
               else
                 {:cont, {:ok, bits ++ seg_bits}}
               end

             {:ok, seg_bits, :partial} ->
               {:cont, {:ok, bits ++ seg_bits}}

             {:error, _} = err ->
               {:halt, err}
           end
         end) do
      {:ok, bits} ->
        pack_bits_to_bytes(bits)

      {:error, _} = err ->
        err
    end
  end

  defp pack_bits_to_bytes([]) do
    {:ok, [], 0}
  end

  defp pack_bits_to_bytes(bits) do
    total = length(bits)
    trailing = rem(8 - rem(total, 8), 8)
    padded = bits ++ List.duplicate(0, trailing)

    bytes =
      padded
      |> Enum.chunk_every(8)
      |> Enum.map(fn chunk ->
        Enum.reduce(chunk, 0, fn b, acc -> acc * 2 + b end)
      end)

    {:ok, bytes, trailing}
  end

  # Returns `{:ok, bits, :bytes | :partial}` — bits are MSB-first 0/1.
  defp bitstring_segment_bits(n) when is_integer(n) and n >= 0 and n <= 255,
    do: {:ok, int_to_bits(n, 8), :bytes}

  defp bitstring_segment_bits(bin) when is_binary(bin) do
    bits =
      for <<b <- bin>>, bit <- int_to_bits(b, 8), do: bit

    {:ok, bits, :bytes}
  end

  defp bitstring_segment_bits({:"::", _, [n]}) when is_integer(n) and n >= 0 and n <= 255,
    do: {:ok, int_to_bits(n, 8), :bytes}

  defp bitstring_segment_bits({:"::", _, [n, spec]}) when is_integer(n) do
    cond do
      utf8_type_spec?(spec) ->
        if n < 0 or n > 0x10FFFF do
          {:error, "invalid unicode codepoint #{n} in ::utf8"}
        else
          case :unicode.characters_to_binary([n]) do
            bin when is_binary(bin) ->
              bitstring_segment_bits(bin)

            _ ->
              {:error, "invalid unicode codepoint #{n} in ::utf8"}
          end
        end

      true ->
        case segment_size(spec) do
          {:ok, size} when size >= 1 and size <= 8 ->
            max = Bitwise.bsl(1, size)

            if n < 0 or n >= max do
              {:error, "integer #{n} does not fit in ::#{size} in <<…>>"}
            else
              kind = if size == 8, do: :bytes, else: :partial
              {:ok, int_to_bits(n, size), kind}
            end

          {:ok, size} ->
            {:error, "unsupported bitstring size #{size} in <<…>> (teaching subset: 1..8)"}

          :error ->
            {:error, "unsupported bitstring segment specifier in <<…>>"}
        end
    end
  end

  defp bitstring_segment_bits({:"::", _, [bin, spec]}) when is_binary(bin) do
    cond do
      utf8_type_spec?(spec) ->
        bitstring_segment_bits(bin)

      true ->
        case segment_size(spec) do
          {:ok, 8} ->
            bitstring_segment_bits(bin)

          {:ok, _} ->
            {:error, "string/binary chunks in <<…>> must be byte-sized (::8)"}

          :error ->
            # Bare `::binary` / unknown — reject
            {:error, "unsupported bitstring segment specifier on string in <<…>>"}
        end
    end
  end

  defp bitstring_segment_bits(_),
    do: {:error, "unsupported binary segment in <<…>>"}

  defp segment_size(n) when is_integer(n), do: {:ok, n}
  defp segment_size({:size, _, [n]}) when is_integer(n), do: {:ok, n}
  defp segment_size({:size, _, n}) when is_integer(n), do: {:ok, n}
  defp segment_size(_), do: :error

  defp int_to_bits(n, size) do
    for i <- (size - 1)..0//-1, do: Bitwise.band(Bitwise.bsr(n, i), 1)
  end

  defp resolve_locals(fun, mod_name) do
    code =
      Enum.map(fun["code"], fn
        %{"op" => op, "fun" => "__local__:" <> rest} = instr
        when op in ["call", "spawn", "make_fun"] ->
          %{instr | "fun" => "#{mod_name}.#{rest}"}

        instr ->
          instr
      end)

    %{fun | "code" => code}
  end

  defp lower_fn(params, body, env, next, code) do
    with {:ok, param_names} <- fn_param_names(params) do
      frees =
        body
        |> free_vars(MapSet.new(param_names))
        |> Enum.filter(&Map.has_key?(env, &1))
        |> Enum.sort()

      id = next_fn_id!()
      mod = Process.get({:autumn, :mod})
      arity = length(frees) + length(param_names)
      fun_name = "#{mod}.__fn_#{id}/#{arity}"
      lifted_params = frees ++ param_names

      with {:ok, lifted_code, locals} <- lower_body(body, lifted_params) do
        push_lifted!(%{
          "name" => fun_name,
          "arity" => arity,
          "locals" => locals,
          "code" => lifted_code
        })

        cap_regs = Enum.map(frees, &Map.fetch!(env, &1))
        dest = next

        instr = %{
          "op" => "make_fun",
          "dest" => dest,
          "fun" => fun_name,
          "captures" => cap_regs
        }

        {:ok, code ++ [instr], env, next + 1, dest}
      end
    end
  end

  defp lower_multi_fn(clauses, env, next, code) do
    with {:ok, parsed} <- parse_fn_clauses(clauses),
         {:ok, arity} <- fn_clauses_arity(parsed) do
      params = Enum.map(0..(arity - 1), fn i -> String.to_atom("a#{i}") end)

      scrut =
        case arity do
          1 -> {hd(params), [], nil}
          _ -> {:{}, [], Enum.map(params, &{&1, [], nil})}
        end

      case_clauses =
        Enum.map(parsed, fn {pats, body, guard} ->
          pat =
            case arity do
              1 -> hd(pats)
              _ -> {:{}, [], pats}
            end

          lhs = if guard == nil, do: [pat], else: [{:when, [], [pat, guard]}]
          {:->, [], [lhs, body]}
        end)

      body = {:case, [], [scrut, [do: case_clauses]]}

      frees =
        body
        |> free_vars(MapSet.new(params))
        |> Enum.filter(&Map.has_key?(env, &1))
        |> Enum.sort()

      id = next_fn_id!()
      mod = Process.get({:autumn, :mod})
      fun_arity = length(frees) + arity
      fun_name = "#{mod}.__fn_#{id}/#{fun_arity}"
      lifted_params = frees ++ params

      with {:ok, lifted_code, locals} <- lower_body(body, lifted_params) do
        push_lifted!(%{
          "name" => fun_name,
          "arity" => fun_arity,
          "locals" => locals,
          "code" => lifted_code
        })

        cap_regs = Enum.map(frees, &Map.fetch!(env, &1))
        dest = next

        instr = %{
          "op" => "make_fun",
          "dest" => dest,
          "fun" => fun_name,
          "captures" => cap_regs
        }

        {:ok, code ++ [instr], env, next + 1, dest}
      end
    end
  end

  defp parse_fn_clauses(clauses) do
    Enum.reduce_while(clauses, {:ok, []}, fn
      {:->, _, [lhs, body]}, {:ok, acc} ->
        case normalize_fn_lhs(lhs) do
          {:ok, pats, guard} -> {:cont, {:ok, acc ++ [{pats, body, guard}]}}
          {:error, _} = err -> {:halt, err}
        end

      other, _ ->
        {:halt, {:error, "fn: unsupported clause #{Macro.to_string(other)}"}}
    end)
  end

  defp normalize_fn_lhs([{:when, _, [pat, guard]}]) do
    {:ok, [pat], guard}
  end

  defp normalize_fn_lhs([{:when, _, pats_and_guard}]) when is_list(pats_and_guard) do
    case List.pop_at(pats_and_guard, -1) do
      {guard, pats} when pats != [] -> {:ok, pats, guard}
      _ -> {:error, "fn: malformed when-clause"}
    end
  end

  defp normalize_fn_lhs(pats) when is_list(pats), do: {:ok, pats, nil}
  defp normalize_fn_lhs(other), do: {:error, "fn: unsupported head #{Macro.to_string(other)}"}

  defp fn_clauses_arity([{pats, _, _} | rest]) do
    arity = length(pats)

    if arity == 0 do
      {:error, "fn: zero-arity multi-clause not supported (use fn -> … end)"}
    else
      if Enum.all?(rest, fn {p, _, _} -> length(p) == arity end) do
        {:ok, arity}
      else
        {:error, "fn: clauses must share the same arity"}
      end
    end
  end

  defp fn_param_names(params) when is_list(params) do
    if all_var_params?(params) do
      {:ok, Enum.map(params, fn {n, _, nil} -> n end)}
    else
      {:error, "fn: patterned params need multi-clause lowering"}
    end
  end

  defp fn_param_names(_), do: {:error, "fn: params must be a list (fn a, b -> … end)"}

  # Free variables relative to `bound` (already in scope).
  defp free_vars({name, _, nil}, bound) when is_atom(name) do
    if MapSet.member?(bound, name), do: MapSet.new(), else: MapSet.new([name])
  end

  defp free_vars({:=, _, [{name, _, nil}, rhs]}, bound) when is_atom(name) do
    free_vars(rhs, bound)
  end

  defp free_vars({:=, _, [pat, rhs]}, bound) do
    MapSet.union(free_vars(rhs, bound), free_vars_pattern(pat, bound))
  end

  defp free_vars({:__block__, _, stmts}, bound), do: free_vars_stmts(stmts, bound)

  defp free_vars({:fn, _, clauses}, bound) do
    Enum.reduce(clauses, MapSet.new(), fn
      {:->, _, [params, body]}, acc ->
        names =
          case fn_param_names(params) do
            {:ok, ns} -> ns
            _ -> []
          end

        MapSet.union(acc, free_vars(body, MapSet.union(bound, MapSet.new(names))))

      _, acc ->
        acc
    end)
  end

  defp free_vars({:case, _, [scrut, [do: clauses]]}, bound) do
    MapSet.union(free_vars(scrut, bound), free_vars_case_clauses(clauses, bound))
  end

  defp free_vars({:if, _, [cond_ast, opts]}, bound) when is_list(opts) do
    [
      free_vars(cond_ast, bound),
      free_vars(Keyword.get(opts, :do), bound),
      free_vars(Keyword.get(opts, :else), bound)
    ]
    |> Enum.reduce(MapSet.new(), &MapSet.union/2)
  end

  defp free_vars({:unless, _, [cond_ast, opts]}, bound) when is_list(opts) do
    free_vars({:if, [], [cond_ast, opts]}, bound)
  end

  defp free_vars({:cond, _, [[do: clauses]]}, bound) do
    Enum.reduce(clauses, MapSet.new(), fn
      {:->, _, [[c], body]}, acc ->
        MapSet.union(acc, MapSet.union(free_vars(c, bound), free_vars(body, bound)))

      _, acc ->
        acc
    end)
  end

  defp free_vars({{:., _, [{:__aliases__, _, _}, _]}, _, args}, bound) when is_list(args) do
    free_vars(args, bound)
  end

  defp free_vars({{:., _, [fun_ast]}, _, args}, bound) when is_list(args) do
    Enum.reduce([fun_ast | args], MapSet.new(), fn a, acc ->
      MapSet.union(acc, free_vars(a, bound))
    end)
  end

  defp free_vars({:%{}, _, pairs}, bound) when is_list(pairs) do
    Enum.reduce(pairs, MapSet.new(), fn
      {k, v}, acc ->
        MapSet.union(acc, MapSet.union(free_vars(k, bound), free_vars(v, bound)))

      _, acc ->
        acc
    end)
  end

  defp free_vars({:{}, _, elems}, bound) when is_list(elems), do: free_vars(elems, bound)
  defp free_vars({a, b}, bound), do: MapSet.union(free_vars(a, bound), free_vars(b, bound))

  defp free_vars(list, bound) when is_list(list) do
    Enum.reduce(list, MapSet.new(), fn a, acc -> MapSet.union(acc, free_vars(a, bound)) end)
  end

  defp free_vars({_name, _, args}, bound) when is_list(args), do: free_vars(args, bound)
  defp free_vars(_, _), do: MapSet.new()

  defp free_vars_stmts(stmts, bound) do
    {acc, _} =
      Enum.reduce(stmts, {MapSet.new(), bound}, fn stmt, {acc, bound} ->
        case stmt do
          {:=, _, [{name, _, nil}, rhs]} when is_atom(name) ->
            {MapSet.union(acc, free_vars(rhs, bound)), MapSet.put(bound, name)}

          {:=, _, [pat, rhs]} ->
            frees = MapSet.union(free_vars(rhs, bound), free_vars_pattern(pat, bound))
            {MapSet.union(acc, frees), MapSet.union(bound, pattern_vars(pat))}

          other ->
            {MapSet.union(acc, free_vars(other, bound)), bound}
        end
      end)

    acc
  end

  defp free_vars_case_clauses(clauses, bound) do
    Enum.reduce(clauses, MapSet.new(), fn
      {:->, _, [[{:when, _, [pat, guard]}], body]}, acc ->
        pb = MapSet.union(bound, pattern_vars(pat))

        MapSet.union(
          acc,
          MapSet.union(
            free_vars_pattern(pat, bound),
            MapSet.union(free_vars(guard, pb), free_vars(body, pb))
          )
        )

      {:->, _, [[pat], body]}, acc ->
        pb = MapSet.union(bound, pattern_vars(pat))

        MapSet.union(
          acc,
          MapSet.union(free_vars_pattern(pat, bound), free_vars(body, pb))
        )

      _, acc ->
        acc
    end)
  end

  # Free vars *used* by a pattern (pins); binders are not free.
  defp free_vars_pattern({:^, _, [{name, _, nil}]}, bound) when is_atom(name) do
    if MapSet.member?(bound, name), do: MapSet.new(), else: MapSet.new([name])
  end

  defp free_vars_pattern({:{}, _, elems}, bound) when is_list(elems),
    do: free_vars_pattern(elems, bound)

  defp free_vars_pattern({a, b}, bound),
    do: MapSet.union(free_vars_pattern(a, bound), free_vars_pattern(b, bound))

  defp free_vars_pattern(list, bound) when is_list(list) do
    Enum.reduce(list, MapSet.new(), fn e, acc ->
      MapSet.union(acc, free_vars_pattern(e, bound))
    end)
  end

  defp free_vars_pattern({:%{}, _, pairs}, bound) when is_list(pairs) do
    Enum.reduce(pairs, MapSet.new(), fn
      {_k, v}, acc -> MapSet.union(acc, free_vars_pattern(v, bound))
      _, acc -> acc
    end)
  end

  defp free_vars_pattern({:|, _, [h, t]}, bound),
    do: MapSet.union(free_vars_pattern(h, bound), free_vars_pattern(t, bound))

  defp free_vars_pattern({:in, _, [var, _]}, bound), do: free_vars_pattern(var, bound)

  defp free_vars_pattern({:<<>>, _, segs}, bound) when is_list(segs) do
    Enum.reduce(segs, MapSet.new(), fn seg, acc ->
      MapSet.union(acc, free_vars_bitstring_seg(seg, bound))
    end)
  end

  defp free_vars_pattern(_, _), do: MapSet.new()

  defp free_vars_bitstring_seg({:^, _, _} = pin, bound), do: free_vars_pattern(pin, bound)
  defp free_vars_bitstring_seg(_, _), do: MapSet.new()

  defp pattern_vars({name, _, nil}) when is_atom(name) and name != :_, do: MapSet.new([name])
  defp pattern_vars({:^, _, _}), do: MapSet.new()
  defp pattern_vars({:{}, _, elems}) when is_list(elems), do: pattern_vars(elems)
  defp pattern_vars({a, b}), do: MapSet.union(pattern_vars(a), pattern_vars(b))

  defp pattern_vars(list) when is_list(list) do
    Enum.reduce(list, MapSet.new(), fn e, acc -> MapSet.union(acc, pattern_vars(e)) end)
  end

  defp pattern_vars({:%{}, _, pairs}) when is_list(pairs) do
    Enum.reduce(pairs, MapSet.new(), fn
      {_k, v}, acc -> MapSet.union(acc, pattern_vars(v))
      _, acc -> acc
    end)
  end

  defp pattern_vars({:|, _, [h, t]}), do: MapSet.union(pattern_vars(h), pattern_vars(t))
  defp pattern_vars({:in, _, [var, _]}), do: pattern_vars(var)

  defp pattern_vars({:<<>>, _, segs}) when is_list(segs) do
    Enum.reduce(segs, MapSet.new(), fn seg, acc ->
      MapSet.union(acc, pattern_vars_bitstring_seg(seg))
    end)
  end

  defp pattern_vars(_), do: MapSet.new()

  defp pattern_vars_bitstring_seg({:"::", _, [{name, _, ctx}, _spec]})
       when is_atom(name) and name != :_ and (is_atom(ctx) or is_nil(ctx)),
       do: MapSet.new([name])

  defp pattern_vars_bitstring_seg({name, _, ctx})
       when is_atom(name) and name != :_ and (is_atom(ctx) or is_nil(ctx)),
       do: MapSet.new([name])

  defp pattern_vars_bitstring_seg(_), do: MapSet.new()
end
