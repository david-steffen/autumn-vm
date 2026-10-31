defmodule AutumnCompiler.Lower do
  @moduledoc false

  @builtins %{
    {:+, 2} => "+/2",
    {:-, 2} => "-/2",
    {:*, 2} => "*/2",
    {:==, 2} => "==/2",
    {:tuple_size, 1} => "tuple_size/1",
    {:list_size, 1} => "list_size/1",
    {:elem, 2} => "elem/2"
  }

  def lower({:defmodule, _meta, [alias_ast, [do: body]]}) do
    mod_name = module_name(alias_ast)
    defs = flatten_block(body)

    with {:ok, groups} <- group_defs(defs),
         {:ok, funs} <- lower_groups(groups, mod_name) do
      funs = Enum.map(funs, &resolve_locals(&1, mod_name))
      entry = "#{mod_name}.main/0"
      version = module_version(funs)

      if Enum.any?(funs, &(&1["name"] == entry)) do
        {:ok, %{"version" => version, "entry" => entry, "functions" => funs}}
      else
        {:error, "module #{mod_name} must define main/0 as entry"}
      end
    end
  end

  def lower(_) do
    {:error, "expected a single defmodule at the top level"}
  end

  defp module_version(funs) do
    cond do
      needs_v3?(funs) -> 3
      needs_v2?(funs) -> 2
      true -> 1
    end
  end

  defp needs_v3?(funs) do
    Enum.any?(funs, fn f ->
      Enum.any?(f["code"], fn instr -> instr["op"] == "get_list_elem" end)
    end)
  end

  defp needs_v2?(funs) do
    Enum.any?(funs, fn f ->
      Enum.any?(f["code"], fn instr ->
        instr["op"] in ~w(jump jump_if_eq get_tuple_elem is_tag spawn send recv) or
          list_lit?(instr)
      end)
    end)
  end

  defp list_lit?(%{"op" => "load_lit", "lit" => %{"list" => _}}), do: true
  defp list_lit?(_), do: false

  defp module_name({:__aliases__, _, parts}), do: Enum.map_join(parts, ".", &to_string/1)

  defp flatten_block({:__block__, _, stmts}), do: stmts
  defp flatten_block(other), do: [other]

  # Group defs by {name, arity}, preserving first-seen order.
  defp group_defs(defs) do
    Enum.reduce_while(defs, {:ok, [], %{}}, fn def_ast, {:ok, order, map} ->
      case take_def_clause(def_ast) do
        {:ok, name, params, body} ->
          key = {name, length(params)}

          {order, map} =
            if Map.has_key?(map, key) do
              {order, Map.update!(map, key, &(&1 ++ [{params, body}]))}
            else
              {order ++ [key], Map.put(map, key, [{params, body}])}
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

  defp take_def_clause({:def, _meta, [head, [do: body]]}) do
    with {:ok, name, params} <- parse_head_patterns(head) do
      {:ok, name, params, body}
    end
  end

  defp take_def_clause({:def, _, _}),
    do: {:error, "unsupported def form (guards/defaults not allowed)"}

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

  defp lower_grouped_def(name, arity, [{params, body}], mod_name) do
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
      lower_multi_clause(name, arity, [{params, body}], mod_name)
    end
  end

  defp lower_grouped_def(name, arity, clauses, mod_name) when length(clauses) > 1 do
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
      Enum.map(clauses, fn {pats, body} ->
        pat =
          case arity do
            1 -> hd(pats)
            _ -> {:{}, [], pats}
          end

        {:->, [], [[pat], body]}
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

  # Binding: a = expr
  defp expr({:=, _, [{name, _, nil}, rhs]}, env, next, code) when is_atom(name) do
    with {:ok, code, env, next, reg} <- expr(rhs, env, next, code) do
      {:ok, code, Map.put(env, name, reg), next, reg}
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

  defp expr(a, env, next, code) when is_atom(a),
    do: emit_lit(%{"atom" => Atom.to_string(a)}, env, next, code)

  defp expr({name, _, nil}, env, next, code) when is_atom(name) do
    case Map.fetch(env, name) do
      {:ok, reg} -> {:ok, code, env, next, reg}
      :error -> {:error, "unbound variable #{name}"}
    end
  end

  # list literal [a, b, c]
  defp expr(list, env, next, code) when is_list(list) do
    case literal_list(list) do
      {:ok, lit} -> emit_lit(lit, env, next, code)
      :error -> {:error, "list elements must be literals"}
    end
  end

  defp expr({:{}, _, elems}, env, next, code) when is_list(elems) do
    case literal_tuple(elems) do
      {:ok, lit} -> emit_lit(lit, env, next, code)
      :error -> {:error, "tuple elements must be literals"}
    end
  end

  defp expr({a, b}, env, next, code) do
    expr({:{}, [], [a, b]}, env, next, code)
  end

  # case expr do pat -> body; ... end
  defp expr({:case, _, [scrutinee, [do: clauses]]}, env, next, code) do
    lower_case(scrutinee, List.wrap(clauses), env, next, code)
  end

  # spawn(Mod.fun/arity isn't Elixir) — spawn(Main, :worker, [arg]) style via Autumn.spawn
  # We accept spawn(fun_name_atom, arg) as local MFA spawn: spawn(:worker, x) -> Main.worker/1
  defp expr({:spawn, _, [fun_ast, args_ast]}, env, next, code) when is_list(args_ast) or true do
    lower_spawn(fun_ast, args_ast, env, next, code)
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

  defp expr({:|>, _, [left, right]}, env, next, code) do
    case desugar_pipe(left, right) do
      {:ok, call} -> expr(call, env, next, code)
      {:error, _} = err -> err
    end
  end

  defp expr({name, _meta, args}, env, next, code)
       when is_atom(name) and is_list(args) and
              name not in [:{}, :__aliases__, :__block__, :case, :spawn, :send, :recv] do
    arity = length(args)

    fun =
      case Map.fetch(@builtins, {name, arity}) do
        {:ok, builtin} -> builtin
        :error -> "__local__:#{name}/#{arity}"
      end

    lower_call_named(fun, args, env, next, code)
  end

  defp expr(other, _env, _next, _code) do
    {:error, "unsupported expression: #{Macro.to_string(other)}"}
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
        # Fall-through: no match — load nil into result
        {:ok, code, env, next, _} = emit_lit(nil, env, next, code)
        # Last load_lit writes a temp; move to result_reg
        # Simpler: emit_lit to result_reg directly
        code = List.delete_at(code, -1)
        next = next - 1
        instr = %{"op" => "load_lit", "reg" => result_reg, "lit" => nil}
        code = code ++ [instr]
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

  defp lower_clause({:->, _, [[pat], body]}, scr_reg, result_reg, env, next, code) do
    with {:ok, code, env, next, matched_jump_over} <-
           emit_pattern_test(pat, scr_reg, env, next, code),
         {:ok, code, env, next} <- emit_pattern_binds(pat, scr_reg, env, next, code),
         {:ok, code, env, next, body_reg} <- expr(body, env, next, code) do
      code =
        code ++
          [
            %{"op" => "move", "dest" => result_reg, "src" => body_reg},
            %{"op" => "jump", "target" => 0}
          ]

      jump_idx = length(code) - 1
      # Patch jump_over (failed match) to point here (after clause)
      after_clause = length(code)

      code =
        List.update_at(code, matched_jump_over, fn %{"op" => "jump"} = j ->
          %{j | "target" => after_clause}
        end)

      {:ok, code, env, next, jump_idx}
    end
  end

  defp lower_clause(other, _, _, _, _, _),
    do: {:error, "unsupported case clause: #{Macro.to_string(other)}"}

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

  defp emit_pattern_test(lit, scr, env, next, code)
       when is_integer(lit) or is_atom(lit) or is_boolean(lit) or is_nil(lit) do
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
    emit_compound_pattern_test("tuple", "get_tuple_elem", "tuple", elems, scr, env, next, code)
  end

  # Empty list / fixed-length list patterns. Reject [h | t].
  defp emit_pattern_test(elems, scr, env, next, code) when is_list(elems) do
    if list_has_cons?(elems) do
      {:error, "cons list patterns [h | t] are not lowered yet"}
    else
      case elems do
        [] ->
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

        _ ->
          emit_compound_pattern_test(
            "list",
            "get_list_elem",
            "list",
            elems,
            scr,
            env,
            next,
            code,
            length_check: true
          )
      end
    end
  end

  defp emit_pattern_test(other, _, _, _, _),
    do: {:error, "unsupported pattern: #{Macro.to_string(other)}"}

  defp list_has_cons?(elems) when is_list(elems) do
    Enum.any?(elems, fn
      {:|, _, _} -> true
      _ -> false
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

        code =
          code ++
            [
              %{
                "op" => "call",
                "dest" => size_reg,
                "fun" => "list_size/1",
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

              _ ->
                {:halt, {:error, "unsupported #{tag} pattern element"}}
            end
        end
    end)
  end

  defp emit_pattern_binds({name, _, nil}, scr, env, next, code)
       when is_atom(name) and name != :_ do
    env = Map.put(env, name, scr)
    {:ok, code, env, next}
  end

  defp emit_pattern_binds({:{}, _, elems}, scr, env, next, code) do
    emit_compound_pattern_binds("get_tuple_elem", "tuple", elems, scr, env, next, code)
  end

  defp emit_pattern_binds({a, b}, scr, env, next, code) do
    emit_pattern_binds({:{}, [], [a, b]}, scr, env, next, code)
  end

  defp emit_pattern_binds(elems, scr, env, next, code) when is_list(elems) do
    if list_has_cons?(elems) do
      {:error, "cons list patterns [h | t] are not lowered yet"}
    else
      emit_compound_pattern_binds("get_list_elem", "list", elems, scr, env, next, code)
    end
  end

  defp emit_pattern_binds(_, _scr, env, next, code), do: {:ok, code, env, next}

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

      {_, _}, acc ->
        {:cont, acc}
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

  defp lit_value(nil), do: {:ok, nil}
  defp lit_value(b) when is_boolean(b), do: {:ok, %{"bool" => b}}
  defp lit_value(n) when is_integer(n), do: {:ok, %{"int" => n}}
  defp lit_value(a) when is_atom(a), do: {:ok, %{"atom" => Atom.to_string(a)}}
  defp lit_value(list) when is_list(list), do: literal_list(list)

  defp lit_value({:{}, _, elems}) do
    case literal_tuple(elems) do
      {:ok, lit} -> {:ok, lit}
      :error -> :error
    end
  end

  defp lit_value({a, b}), do: lit_value({:{}, [], [a, b]})
  defp lit_value(_), do: :error

  defp resolve_locals(fun, mod_name) do
    code =
      Enum.map(fun["code"], fn
        %{"op" => op, "fun" => "__local__:" <> rest} = instr when op in ["call", "spawn"] ->
          %{instr | "fun" => "#{mod_name}.#{rest}"}

        instr ->
          instr
      end)

    %{fun | "code" => code}
  end
end
