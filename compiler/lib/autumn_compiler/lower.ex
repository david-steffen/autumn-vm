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
    {:cons, 2} => "cons/2"
  }

  @type_guards %{
    is_integer: "int",
    is_atom: "atom",
    is_boolean: "bool",
    is_list: "list",
    is_tuple: "tuple",
    is_map: "map",
    is_pid: "pid",
    is_nil: "nil"
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
      needs_v8?(funs) -> 8
      needs_v7?(funs) -> 7
      needs_v6?(funs) -> 6
      needs_v5?(funs) -> 5
      needs_v4?(funs) -> 4
      needs_v3?(funs) -> 3
      needs_v2?(funs) -> 2
      true -> 1
    end
  end

  defp needs_v8?(funs) do
    Enum.any?(funs, fn f ->
      Enum.any?(f["code"], fn instr -> instr["op"] == "link" end)
    end)
  end

  defp needs_v7?(funs) do
    Enum.any?(funs, fn f ->
      Enum.any?(f["code"], fn instr ->
        instr["op"] in ~w(recv_peek recv_drop wait)
      end)
    end)
  end

  defp needs_v6?(funs) do
    Enum.any?(funs, fn f ->
      Enum.any?(f["code"], fn instr ->
        instr["op"] in ~w(enter_try leave_try raise)
      end)
    end)
  end

  defp needs_v5?(funs) do
    Enum.any?(funs, fn f ->
      Enum.any?(f["code"], fn
        %{"op" => "load_lit", "lit" => %{"map" => _}} -> true
        %{"op" => "call", "fun" => fun} when fun in ~w(map_size/1 map_get/2 map_put/3) -> true
        %{"op" => "is_tag", "tag" => "map"} -> true
        _ -> false
      end)
    end)
  end

  defp needs_v4?(funs) do
    Enum.any?(funs, fn f ->
      Enum.any?(f["code"], fn instr -> instr["op"] == "get_list_rest" end)
    end)
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

  # raise expr (language exception; not StepError)
  defp expr({:raise, _, [arg]}, env, next, code) do
    with {:ok, code, env, next, reg} <- expr(arg, env, next, code) do
      {:ok, code ++ [%{"op" => "raise", "reg" => reg}], env, next, reg}
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

  # spawn(Mod.fun/arity isn't Elixir) — spawn(Main, :worker, [arg]) style via Autumn.spawn
  # We accept spawn(fun_name_atom, arg) as local MFA spawn: spawn(:worker, x) -> Main.worker/1
  defp expr({:spawn, _, [fun_ast, args_ast]}, env, next, code) when is_list(args_ast) or true do
    lower_spawn(fun_ast, args_ast, env, next, code)
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
              name not in [
                :{},
                :%{},
                :__aliases__,
                :__block__,
                :case,
                :try,
                :raise,
                :receive,
                :spawn,
                :spawn_link,
                :link,
                :send,
                :recv
              ] do
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
  # Scan loop: recv_peek; pattern clauses with recv_drop on match; else idx++; wait.
  defp lower_receive(opts, env, next, code) do
    clauses = opts |> Keyword.get(:do, []) |> List.wrap()
    after_clauses = opts |> Keyword.get(:after, []) |> List.wrap()

    if clauses == [] do
      {:error, "receive requires at least one clause"}
    else
      with {:ok, timeout_lit, after_body} <- parse_receive_after(after_clauses) do
        lower_receive_loop(clauses, timeout_lit, after_body, env, next, code)
      end
    end
  end

  defp parse_receive_after([]) do
    # Infinity — after label unused (points at end).
    {:ok, nil, nil}
  end

  defp parse_receive_after([{:->, _, [[timeout], body]}])
       when is_integer(timeout) and timeout >= 0 do
    {:ok, timeout, body}
  end

  defp parse_receive_after(other) do
    {:error, "unsupported receive after: #{Macro.to_string(other)}"}
  end

  defp lower_receive_loop(clauses, timeout_lit, after_body, env, next, code) do
    idx_reg = next
    msg_reg = next + 1
    result_reg = next + 2
    next = next + 3

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

      # Placeholder after target; patched below.
      wait_idx = length(code)

      code =
        code ++
          [
            %{
              "op" => "wait",
              "retry" => scan_ip,
              "after" => 0,
              "timeout" => timeout_lit
            }
          ]

      after_ip = length(code)

      code =
        List.update_at(code, wait_idx, fn %{"op" => "wait"} = i ->
          %{i | "after" => after_ip}
        end)

      after_result =
        if after_body == nil do
          # Infinity path should never land here; keep a defined value.
          {:ok, code ++ [%{"op" => "load_lit", "reg" => result_reg, "lit" => nil}], env, next}
        else
          with {:ok, code, env, next, body_reg} <- expr(after_body, env, next, code) do
            {:ok, code ++ [%{"op" => "move", "dest" => result_reg, "src" => body_reg}], env, next}
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

  defp lower_clause({:->, _, [[{:when, _, [pat, guard]}], body]}, scr_reg, result_reg, env, next, code) do
    lower_clause_guarded(pat, guard, body, scr_reg, result_reg, env, next, code)
  end

  # rescue e in [lit, …] / case-style `x in […]` (value-based tag filter)
  defp lower_clause({:->, _, [[{:in, _, [var, targets]}], body]}, scr_reg, result_reg, env, next, code) do
    lower_clause_guarded({:in, [], [var, targets]}, nil, body, scr_reg, result_reg, env, next, code)
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
          code = code ++ [%{"op" => "call", "dest" => dest, "fun" => "cons/2", "args" => [h_reg, t_reg]}]
          next = next + 1

          Enum.reduce_while(Enum.reverse(prefix), {:ok, code, env, next, dest}, fn
            elem, {:ok, code, env, next, acc} ->
              case expr(elem, env, next, code) do
                {:ok, code, env, next, er} ->
                  d = next
                  code = code ++ [%{"op" => "call", "dest" => d, "fun" => "cons/2", "args" => [er, acc]}]
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
                  code = code ++ [%{"op" => "call", "dest" => d, "fun" => "cons/2", "args" => [er, acc]}]
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

  # `e in [lit, …]` or `e in lit` — or of literal equality tests (rescue tags).
  defp emit_pattern_test({:in, _, [var, targets]}, scr, env, next, code) do
    emit_in_pattern_test(var, targets, scr, env, next, code)
  end

  # Map patterns %{lit_key => pat, ...} (literal keys only).
  defp emit_pattern_test({:%{}, _, pairs}, scr, env, next, code) when is_list(pairs) do
    emit_map_pattern_test(pairs, scr, env, next, code)
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
    do: {:error, "unsupported pattern: #{Macro.to_string(other)}"}

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

              _ ->
                {:halt, {:error, "unsupported list pattern element"}}
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

  defp emit_pattern_binds({:in, _, [var, _targets]}, scr, env, next, code) do
    emit_pattern_binds(var, scr, env, next, code)
  end

  defp emit_pattern_binds({:%{}, _, pairs}, scr, env, next, code) when is_list(pairs) do
    emit_map_pattern_binds(pairs, scr, env, next, code)
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
  defp lit_value(a) when is_atom(a), do: {:ok, %{"atom" => Atom.to_string(a)}}
  defp lit_value(list) when is_list(list), do: literal_list(list)

  defp lit_value({:%{}, _, pairs}) when is_list(pairs), do: literal_map(pairs)

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
