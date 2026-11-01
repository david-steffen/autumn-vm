defmodule AutumnCompilerTest do
  use ExUnit.Case, async: true

  @fixtures Path.expand("../../tests/fixtures", __DIR__)

  defp all_funs(%{"modules" => mods}), do: Enum.flat_map(mods, & &1["functions"])
  defp all_code(module), do: Enum.flat_map(all_funs(module), & &1["code"])

  test "lowers add_main fixture" do
    path = Path.join(@fixtures, "add_main.ex")

    assert {:ok, _module} = AutumnCompiler.compile_file(path)
  end

  test "lowers mul_main with block binding and */-" do
    path = Path.join(@fixtures, "mul_main.ex")

    assert {:ok, _module} = AutumnCompiler.compile_file(path)
  end

  test "lowers case_pair" do
    path = Path.join(@fixtures, "case_pair.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    # case fallthrough emits `raise :match_error`
    assert Enum.any?(all_code(module), &(&1["op"] == "is_tag"))
  end

  test "lowers pipe_add" do
    path = Path.join(@fixtures, "pipe_add.ex")

    assert {:ok, _module} = AutumnCompiler.compile_file(path)
  end

  test "lowers multi_clause to case" do
    path = Path.join(@fixtures, "multi_clause.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    f = Enum.find(all_funs(module), &(&1["name"] == "Main.f/1"))
    assert f
    assert Enum.any?(f["code"], &(&1["op"] == "jump_if_eq"))
  end

  test "lowers case_list with get_list_elem" do
    path = Path.join(@fixtures, "case_list.ex")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    assert Enum.any?(all_code(module), &(&1["op"] == "get_list_elem"))
  end

  test "rejects unsupported pipe RHS" do
    source = """
    defmodule Main do
      def main, do: 1 |> [1, 2, 3]
    end
    """

    path = Path.join(System.tmp_dir!(), "autumn_reject_#{System.unique_integer([:positive])}.ex")
    File.write!(path, source)

    assert {:error, msg} = AutumnCompiler.compile_file(path)
    assert msg =~ "unsupported"
  end

  test "lowers closure_capture (make_fun/apply)" do
    path = Path.join(@fixtures, "closure_capture.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "make_fun"))
    assert Enum.any?(code, &(&1["op"] == "apply"))
    assert Enum.any?(all_funs(module), &String.contains?(&1["name"], "__fn_"))
  end

  test "lowers list_sum with cons patterns" do
    path = Path.join(@fixtures, "list_sum.ex")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    f = Enum.find(all_funs(module), &(&1["name"] == "Main.sum/1"))
    assert Enum.any?(f["code"], &(&1["op"] == "get_list_rest"))
  end

  test "lowers map_get with map lit and builtins" do
    path = Path.join(@fixtures, "map_get.ex")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "load_lit" && match?(%{"map" => _}, &1["lit"])))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "map_put/3"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "map_get/2"))
  end

  test "lowers try_rescue with enter_try/leave_try/raise" do
    path = Path.join(@fixtures, "try_rescue.ex")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    main = Enum.find(all_funs(module), &(&1["name"] == "Main.main/0"))
    code = main["code"]
    assert Enum.any?(code, &(&1["op"] == "enter_try"))
    assert Enum.any?(code, &(&1["op"] == "leave_try"))
    boom = Enum.find(all_funs(module), &(&1["name"] == "Main.boom/0"))
    assert Enum.any?(boom["code"], &(&1["op"] == "raise"))
  end

  test "lowers ping_pong with spawn/send/recv/self" do
    path = Path.join(@fixtures, "ping_pong.ex")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    main = Enum.find(all_funs(module), &(&1["name"] == "Main.main/0"))
    code = main["code"]
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "self/0"))
    assert Enum.any?(code, &(&1["op"] == "spawn"))
    assert Enum.any?(code, &(&1["op"] == "send"))
    assert Enum.any?(code, &(&1["op"] == "recv"))
  end

  test "lowers try_after so after runs on raise" do
    path = Path.join(@fixtures, "try_after.ex")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    assert Enum.any?(all_code(module), &(&1["op"] == "enter_try"))
  end

  test "lowers try_nested / try_reraise / raise_exit / match_error" do
    for name <- ["try_nested", "try_reraise", "raise_exit", "match_error"] do
      path = Path.join(@fixtures, "#{name}.ex")
      assert {:ok, _module} = AutumnCompiler.compile_file(path)
    end
  end

  test "lowers selective_recv / recv_timeout / counter_server" do
    for {name, ops} <- [
          {"selective_recv", ~w(recv_peek recv_drop wait)},
          {"recv_timeout", ~w(wait)},
          {"counter_server", ~w(recv_peek wait spawn)}
        ] do
      path = Path.join(@fixtures, "#{name}.ex")
      assert {:ok, module} = AutumnCompiler.compile_file(path)
      code = all_code(module)
      for op <- ops, do: assert(Enum.any?(code, &(&1["op"] == op)))
    end
  end

  test "lowers guards / dyn_list / dyn_tuple / map_pat" do
    for {name, check} <- [
          {"guards", fn code -> Enum.any?(code, &(&1["op"] == "is_tag")) end},
          {"dyn_list",
           fn code -> Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "cons/2")) end},
          {"dyn_tuple",
           fn code -> Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "make_tuple/2")) end},
          {"map_pat",
           fn code -> Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "map_get/2")) end}
        ] do
      path = Path.join(@fixtures, "#{name}.ex")
      assert {:ok, module} = AutumnCompiler.compile_file(path)
      code = all_code(module)
      assert check.(code)
    end
  end

  test "lowers rescue_in / link_exit" do
    path = Path.join(@fixtures, "rescue_in.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "enter_try"))

    path = Path.join(@fixtures, "link_exit.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "link"))
    assert Enum.any?(code, &(&1["op"] == "spawn"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "Process.flag/2"))
  end

  test "lowers Process.exit / drain / link_kill / badarg_rescue" do
    for {name, check} <- [
          {"process_exit_down",
           fn code -> Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "Process.exit/2")) end},
          {"link_kill", fn code -> Enum.any?(code, &(&1["op"] == "link")) end},
          {"drain_siblings", fn code -> Enum.any?(code, &(&1["op"] == "spawn")) end},
          {"badarg_rescue", fn code -> Enum.any?(code, &(&1["op"] == "enter_try")) end}
        ] do
      path = Path.join(@fixtures, "#{name}.ex")
      assert {:ok, module} = AutumnCompiler.compile_file(path)
      code = all_code(module)
      assert check.(code)
    end
  end

  test "lowers monitor_exit" do
    path = Path.join(@fixtures, "monitor_exit.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "monitor"))
    assert Enum.any?(code, &(&1["op"] == "spawn"))
  end

  test "lowers monitored_call / monitored_down" do
    path = Path.join(@fixtures, "counter_server.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "recv_peek"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "make_tuple/3"))

    path = Path.join(@fixtures, "monitored_call.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "monitor"))
    assert Enum.any?(code, &(&1["op"] == "demonitor"))

    path = Path.join(@fixtures, "monitored_down.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "monitor"))
    assert Enum.any?(code, &(&1["op"] == "raise"))
  end

  test "lowers genserver_counter / genserver_call_down (call+ref+monitor)" do
    path = Path.join(@fixtures, "genserver_counter.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "monitor"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "make_ref/0"))

    path = Path.join(@fixtures, "genserver_call_down.ex")
    assert {:ok, _module} = AutumnCompiler.compile_file(path)
  end

  @stdlib Path.expand("../../stdlib", __DIR__)

  test "lowers genserver_stdlib / genserver_stdlib_down with stdlib GenServer" do
    gs = Path.join(@stdlib, "genserver.ex")

    path = Path.join(@fixtures, "genserver_stdlib.ex")
    assert {:ok, module} = AutumnCompiler.compile_files([gs, path])
    names = Enum.map(module["modules"], & &1["name"])
    assert "GenServer" in names
    assert "Main" in names
    funs = Enum.flat_map(module["modules"], & &1["functions"])
    assert Enum.any?(funs, &(&1["name"] == "GenServer.call/2"))
    assert Enum.any?(funs, &(&1["name"] == "GenServer.reply/3"))
    assert Enum.any?(funs, &(&1["name"] == "GenServer.start/2"))

    path = Path.join(@fixtures, "genserver_stdlib_down.ex")
    assert {:ok, _module} = AutumnCompiler.compile_files([gs, path])
  end

  test "lowers genserver_behaviour (apply_mfa)" do
    gs = Path.join(@stdlib, "genserver.ex")
    path = Path.join(@fixtures, "genserver_behaviour.ex")
    assert {:ok, module} = AutumnCompiler.compile_files([gs, path])
    code = Enum.flat_map(module["modules"], & &1["functions"]) |> Enum.flat_map(& &1["code"])
    assert Enum.any?(code, &(&1["op"] == "apply_mfa"))
    names = Enum.map(module["modules"], & &1["name"])
    assert "Counter" in names
  end

  test "lowers supervisor_one_for_one" do
    gs = Path.join(@stdlib, "genserver.ex")
    sup = Path.join(@stdlib, "supervisor.ex")
    path = Path.join(@fixtures, "supervisor_one_for_one.ex")
    assert {:ok, module} = AutumnCompiler.compile_files([gs, sup, path])
    names = Enum.map(module["modules"], & &1["name"])
    assert "Supervisor" in names
    assert "CrashOnce" in names
  end

  test "lowers genserver_info (handle_info)" do
    gs = Path.join(@stdlib, "genserver.ex")
    path = Path.join(@fixtures, "genserver_info.ex")
    assert {:ok, module} = AutumnCompiler.compile_files([gs, path])
    funs = Enum.flat_map(module["modules"], & &1["functions"])
    assert Enum.any?(funs, &(&1["name"] == "InfoCounter.handle_info/2"))
    assert Enum.any?(funs, &(&1["name"] == "GenServer.do_info/3"))
  end

  test "lowers supervisor_intensity" do
    gs = Path.join(@stdlib, "genserver.ex")
    sup = Path.join(@stdlib, "supervisor.ex")
    path = Path.join(@fixtures, "supervisor_intensity.ex")
    assert {:ok, module} = AutumnCompiler.compile_files([gs, sup, path])
    funs = Enum.flat_map(module["modules"], & &1["functions"])
    assert Enum.any?(funs, &(&1["name"] == "Supervisor.start_link/2"))
    assert Enum.any?(funs, &(&1["name"] == "BoomChild.init/1"))
  end

  test "lowers supervisor_rest_for_one" do
    gs = Path.join(@stdlib, "genserver.ex")
    sup = Path.join(@stdlib, "supervisor.ex")
    path = Path.join(@fixtures, "supervisor_rest_for_one.ex")
    assert {:ok, module} = AutumnCompiler.compile_files([gs, sup, path])
    funs = Enum.flat_map(module["modules"], & &1["functions"])
    assert Enum.any?(funs, &(&1["name"] == "Supervisor.restart_for/3"))
  end

  test "lowers supervisor_one_for_all" do
    gs = Path.join(@stdlib, "genserver.ex")
    sup = Path.join(@stdlib, "supervisor.ex")
    path = Path.join(@fixtures, "supervisor_one_for_all.ex")
    assert {:ok, _module} = AutumnCompiler.compile_files([gs, sup, path])
  end

  test "lowers genserver_use (use GenServer + child_spec)" do
    gs = Path.join(@stdlib, "genserver.ex")
    sup = Path.join(@stdlib, "supervisor.ex")
    path = Path.join(@fixtures, "genserver_use.ex")
    assert {:ok, module} = AutumnCompiler.compile_files([gs, sup, path])

    funs = Enum.flat_map(module["modules"], & &1["functions"])
    names = Enum.map(funs, & &1["name"])
    assert "CrashOnce.child_spec/1" in names
    assert "GenServer.child_spec/1" in names
  end

  test "rejects unknown use" do
    src = """
    defmodule Foo do
      use Bar
      def main, do: 1
    end
    """

    assert {:error, msg} = AutumnCompiler.Lower.lower(Code.string_to_quoted!(src))
    assert msg =~ "unsupported use"
  end

  test "requires handle_continue under @behaviour GenServer" do
    src = """
    defmodule Foo do
      @behaviour GenServer
      def init(x), do: {:ok, x}
      def handle_call(_, _, s), do: {:reply, s, s}
      def handle_cast(_, s), do: {:noreply, s}
    end
    """

    assert {:error, msg} = AutumnCompiler.Lower.lower(Code.string_to_quoted!(src))
    assert msg =~ "handle_continue/2"
  end

  test "rejects unknown use GenServer option" do
    src = """
    defmodule Foo do
      use GenServer, hibernate_after: 1
      def init(x), do: {:ok, x}
      def handle_call(_, _, s), do: {:reply, s, s}
      def handle_cast(_, s), do: {:noreply, s}
      def handle_continue(_, s), do: {:noreply, s}
    end
    """

    assert {:error, msg} = AutumnCompiler.Lower.lower(Code.string_to_quoted!(src))
    assert msg =~ "unsupported use GenServer option"
  end

  test "lowers genserver_continue / supervisor_temporary / supervisor_significant" do
    gs = Path.join(@stdlib, "genserver.ex")
    sup = Path.join(@stdlib, "supervisor.ex")

    for {stem, extras} <- [
          {"genserver_continue", [gs]},
          {"supervisor_temporary", [gs, sup]},
          {"supervisor_significant", [gs, sup]}
        ] do
      path = Path.join(@fixtures, "#{stem}.ex")
      assert {:ok, _module} = AutumnCompiler.compile_files(extras ++ [path])
    end
  end

  test "lowers receive/hibernate/supervisor polish fixtures" do
    gs = Path.join(@stdlib, "genserver.ex")
    sup = Path.join(@stdlib, "supervisor.ex")

    for {stem, extras} <- [
          {"tuple_pattern_arity", []},
          {"receive_after_var", []},
          {"genserver_hibernate", [gs]},
          {"supervisor_shutdown_wait", [gs, sup]},
          {"supervisor_start_mfa", [gs, sup]}
        ] do
      path = Path.join(@fixtures, "#{stem}.ex")
      assert {:ok, _module} = AutumnCompiler.compile_files(extras ++ [path])
    end
  end

  test "lowers ets_basic" do
    ets = Path.join(@stdlib, "ets.ex")
    path = Path.join(@fixtures, "ets_basic.ex")
    assert {:ok, module} = AutumnCompiler.compile_files([ets, path])
    funs = Enum.flat_map(module["modules"], & &1["functions"])
    code = Enum.flat_map(funs, & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "ets_new/0"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "ets_insert/3"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "ets_lookup/2"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "ets_delete/2"))
  end

  test "lowers ets_bag / ets_named / ets_select" do
    ets = Path.join(@stdlib, "ets.ex")

    for {stem, funs} <- [
          {"ets_bag", ["ets_new/2"]},
          {"ets_named", ["ets_new/2"]},
          {"ets_select", ["ets_new/2", "ets_match_object/2", "ets_select/2"]}
        ] do
      path = Path.join(@fixtures, "#{stem}.ex")
      assert {:ok, module} = AutumnCompiler.compile_files([ets, path])

      code =
        module["modules"]
        |> Enum.flat_map(& &1["functions"])
        |> Enum.flat_map(& &1["code"])

      for fun <- funs do
        assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == fun)),
               "#{stem} missing #{fun}"
      end
    end
  end

  test "lowers ets_guards / ets_delete_object / ets_ordered / ets_heir" do
    ets = Path.join(@stdlib, "ets.ex")

    for {stem, funs} <- [
          {"ets_guards", ["ets_select/2"]},
          {"ets_delete_object", ["ets_delete_object/2"]},
          {"ets_ordered", ["ets_new/2"]},
          {"ets_heir", ["ets_heir/2"]}
        ] do
      path = Path.join(@fixtures, "#{stem}.ex")
      assert {:ok, module} = AutumnCompiler.compile_files([ets, path])

      code =
        module["modules"]
        |> Enum.flat_map(& &1["functions"])
        |> Enum.flat_map(& &1["code"])

      for fun <- funs do
        assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == fun)),
               "#{stem} missing #{fun}"
      end

      if stem == "ets_ordered" do
        assert Enum.any?(
                 code,
                 &(&1["op"] == "load_lit" && &1["lit"] == %{"atom" => "ordered_set"})
               )
      end
    end
  end

  test "lowers float_string (is_binary tag)" do
    path = Path.join(@fixtures, "float_string.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    # `is_binary/1` lowers to tag `binary`.
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "load_lit" && match?(%{"float" => _}, &1["lit"])))
    assert Enum.any?(code, &(&1["op"] == "load_lit" && match?(%{"string" => _}, &1["lit"])))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "<>/2"))
    assert Enum.any?(code, &(&1["op"] == "is_tag" && &1["tag"] == "binary"))
  end

  test "lowers bitstring_partial (Mix ::size)" do
    path = Path.join(@fixtures, "bitstring_partial.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)

    assert Enum.any?(
             code,
             &(&1["op"] == "load_lit" &&
                 match?(%{"bitstring" => %{"bytes" => [96], "trailing_bits" => 5}}, &1["lit"]))
           )

    assert Enum.any?(
             code,
             &(&1["op"] == "load_lit" &&
                 match?(
                   %{"bitstring" => %{"bytes" => [1, 64], "trailing_bits" => 5}},
                   &1["lit"]
                 ))
           )
  end

  test "lowers binary_match (bitstring patterns)" do
    path = Path.join(@fixtures, "binary_match.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)

    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "bit_size/1"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "bs_get_integer/2"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "bs_drop/2"))
  end

  test "lowers bitstring_wide (match sizes 9..32 via chunks)" do
    path = Path.join(@fixtures, "bitstring_wide.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    gets = Enum.count(code, &(&1["op"] == "call" && &1["fun"] == "bs_get_integer/2"))
    assert gets >= 3
  end

  test "lowers ::utf8 bitstring match" do
    path = Path.join(@fixtures, "binary_utf8_match.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "bs_get_utf8/1"))
  end

  test "lowers dynamic ::size(var) bitstring match" do
    path = Path.join(@fixtures, "bitstring_dyn_size.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "bs_get_integer/2"))
  end

  test "lowers mid-construct partials and ::utf8 construct" do
    assert {:ok, _} = AutumnCompiler.compile_file(Path.join(@fixtures, "bitstring_mid.ex"))
    assert {:ok, _} = AutumnCompiler.compile_file(Path.join(@fixtures, "binary_utf8.ex"))
  end

  test "lowers for comprehension to __for_map__ / __for_filter__" do
    path = Path.join(@fixtures, "for_basic.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    funs = all_funs(module)
    assert Enum.any?(funs, &(&1["name"] == "Main.__for_map__/2"))
    assert Enum.any?(funs, &(&1["name"] == "Main.__for_filter__/2"))
  end

  test "rejects nested for generators" do
    src = """
    defmodule Main do
      def main do
        for x <- [1], y <- [2], do: {x, y}
      end
    end
    """

    assert {:error, msg} = AutumnCompiler.Lower.lower(Code.string_to_quoted!(src))
    assert msg =~ "nested"
  end

  test "lowers with to nested case" do
    path = Path.join(@fixtures, "with_basic.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "is_tag"))
    assert Enum.any?(code, &(&1["op"] == "jump_if_eq"))
  end

  test "rejects with assignment clauses" do
    src = """
    defmodule Main do
      def main do
        with x = 1 do
          x
        end
      end
    end
    """

    assert {:error, msg} = AutumnCompiler.Lower.lower(Code.string_to_quoted!(src))
    assert msg =~ "with"
  end

  test "lowers if_else / cond_main" do
    path = Path.join(@fixtures, "if_else.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "jump_if_eq"))
    assert Enum.any?(code, &(&1["op"] == "jump"))

    path = Path.join(@fixtures, "cond_main.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "jump_if_eq"))
    # exhausted cond raises :cond_clause_error
    assert Enum.any?(code, &(&1["op"] == "raise"))
  end

  test "lowers match_pin (pat = expr and ^pin)" do
    path = Path.join(@fixtures, "match_pin.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "raise"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "==/2"))
    assert Enum.any?(code, &(&1["op"] == "get_list_rest"))
  end

  test "lowers multi_mod (modules[])" do
    path = Path.join(@fixtures, "multi_mod.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    assert is_list(module["modules"])
    assert length(module["modules"]) == 2
    names = Enum.map(module["modules"], & &1["name"])
    assert "Math" in names
    assert "Main" in names
    assert module["entry"] == "Main.main/0"
    funs = Enum.flat_map(module["modules"], & &1["functions"])
    assert Enum.any?(funs, &(&1["name"] == "Math.add/2"))

    assert Enum.any?(funs, fn f ->
             Enum.any?(f["code"], &(&1["op"] == "call" && &1["fun"] == "Math.add/2"))
           end)
  end

  test "lowers preempt_fair (busy hog + helper)" do
    path = Path.join(@fixtures, "preempt_fair.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    names = Enum.map(all_funs(module), & &1["name"])
    assert "Main.hog/0" in names
    assert "Main.helper/0" in names
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "spawn"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "Process.exit/2"))
  end

  test "lowers hot_load (Code.load_file)" do
    path = Path.join(@fixtures, "hot_load.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "load_file"))
    assert Enum.any?(code, &(&1["op"] == "enter_try"))
  end

  test "lowers list_lit" do
    path = Path.join(@fixtures, "list_lit.ex")

    assert {:ok, _module} = AutumnCompiler.compile_file(path)
  end

  test "lowers multi-clause fn" do
    path = Path.join(@fixtures, "fn_multi.ex")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    assert Enum.any?(all_funs(module), &String.contains?(&1["name"], "__fn_"))
  end

  test "lowers hd/tl/++ list helpers" do
    path = Path.join(@fixtures, "list_helpers.ex")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "get_list_elem"))
    assert Enum.any?(code, &(&1["op"] == "get_list_rest"))
    assert Enum.any?(all_funs(module), &(&1["name"] == "Main.__list_append__/2"))
  end

  test "eval_expr wraps expression as Repl.main/0" do
    assert {:ok, module, _expr} = AutumnCompiler.eval_expr("1 + 2")
    assert module["entry"] == "Repl.main/0"
    code = all_code(module)
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "+/2"))
  end

  test "eval_expr replays session bindings" do
    assert {:ok, _m1, e1} = AutumnCompiler.eval_expr("a = 1 + 4")
    bindings = AutumnCompiler.binding_after([], e1)
    assert [{:a, {:+, _, [1, 4]}}] = bindings

    assert {:ok, module, _e2} = AutumnCompiler.eval_expr("[a, a + 1]", bindings)
    code = all_code(module)
    # Prior `a = 1 + 4` is inlined before the list expr.
    assert Enum.count(code, &(&1["op"] == "call" && &1["fun"] == "+/2")) >= 2
  end
end
