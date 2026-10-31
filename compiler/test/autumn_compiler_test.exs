defmodule AutumnCompilerTest do
  use ExUnit.Case, async: true

  @fixtures Path.expand("../../tests/fixtures", __DIR__)

  test "lowers add_main fixture" do
    path = Path.join(@fixtures, "add_main.ex")
    expected_path = Path.join(@fixtures, "add_main.bc.json")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()

    assert module == expected
  end

  test "lowers mul_main with block binding and */-" do
    path = Path.join(@fixtures, "mul_main.ex")
    expected_path = Path.join(@fixtures, "mul_main.bc.json")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
  end

  test "lowers case_pair" do
    path = Path.join(@fixtures, "case_pair.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    # case fallthrough emits `raise :match_error` → IR v6
    assert module["version"] == 6
    assert Enum.any?(List.first(module["functions"])["code"], &(&1["op"] == "is_tag"))
  end

  test "lowers pipe_add" do
    path = Path.join(@fixtures, "pipe_add.ex")
    expected_path = Path.join(@fixtures, "pipe_add.bc.json")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
  end

  test "lowers multi_clause to case" do
    path = Path.join(@fixtures, "multi_clause.ex")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    assert module["version"] == 6
    f = Enum.find(module["functions"], &(&1["name"] == "Main.f/1"))
    assert f
    assert Enum.any?(f["code"], &(&1["op"] == "jump_if_eq"))
  end

  test "lowers case_list with get_list_elem" do
    path = Path.join(@fixtures, "case_list.ex")
    expected_path = Path.join(@fixtures, "case_list.bc.json")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 6
    assert Enum.any?(List.first(module["functions"])["code"], &(&1["op"] == "get_list_elem"))
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

  test "lowers closure_capture (IR v11)" do
    path = Path.join(@fixtures, "closure_capture.ex")
    expected_path = Path.join(@fixtures, "closure_capture.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 11
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "make_fun"))
    assert Enum.any?(code, &(&1["op"] == "apply"))
    assert Enum.any?(module["functions"], &String.contains?(&1["name"], "__fn_"))
  end

  test "lowers list_sum with cons patterns" do
    path = Path.join(@fixtures, "list_sum.ex")
    expected_path = Path.join(@fixtures, "list_sum.bc.json")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 6
    f = Enum.find(module["functions"], &(&1["name"] == "Main.sum/1"))
    assert Enum.any?(f["code"], &(&1["op"] == "get_list_rest"))
  end

  test "lowers map_get with map lit and builtins" do
    path = Path.join(@fixtures, "map_get.ex")
    expected_path = Path.join(@fixtures, "map_get.bc.json")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 5
    code = List.first(module["functions"])["code"]
    assert Enum.any?(code, &(&1["op"] == "load_lit" && match?(%{"map" => _}, &1["lit"])))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "map_put/3"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "map_get/2"))
  end

  test "lowers try_rescue with enter_try/leave_try/raise" do
    path = Path.join(@fixtures, "try_rescue.ex")
    expected_path = Path.join(@fixtures, "try_rescue.bc.json")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 6
    main = Enum.find(module["functions"], &(&1["name"] == "Main.main/0"))
    code = main["code"]
    assert Enum.any?(code, &(&1["op"] == "enter_try"))
    assert Enum.any?(code, &(&1["op"] == "leave_try"))
    boom = Enum.find(module["functions"], &(&1["name"] == "Main.boom/0"))
    assert Enum.any?(boom["code"], &(&1["op"] == "raise"))
  end

  test "lowers ping_pong with spawn/send/recv/self" do
    path = Path.join(@fixtures, "ping_pong.ex")
    expected_path = Path.join(@fixtures, "ping_pong.bc.json")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 2
    main = Enum.find(module["functions"], &(&1["name"] == "Main.main/0"))
    code = main["code"]
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "self/0"))
    assert Enum.any?(code, &(&1["op"] == "spawn"))
    assert Enum.any?(code, &(&1["op"] == "send"))
    assert Enum.any?(code, &(&1["op"] == "recv"))
  end

  test "lowers try_after so after runs on raise" do
    path = Path.join(@fixtures, "try_after.ex")
    expected_path = Path.join(@fixtures, "try_after.bc.json")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert Enum.any?(List.first(module["functions"])["code"], &(&1["op"] == "enter_try"))
  end

  test "lowers try_nested / try_reraise / raise_exit / match_error" do
    for {name, version} <- [
          {"try_nested", 6},
          {"try_reraise", 6},
          {"raise_exit", 6},
          {"match_error", 6}
        ] do
      path = Path.join(@fixtures, "#{name}.ex")
      expected_path = Path.join(@fixtures, "#{name}.bc.json")
      assert {:ok, module} = AutumnCompiler.compile_file(path)
      expected = expected_path |> File.read!() |> Jason.decode!()
      assert module == expected
      assert module["version"] == version
    end
  end

  test "lowers selective_recv / recv_timeout / counter_server (IR v7)" do
    for {name, ops} <- [
          {"selective_recv", ~w(recv_peek recv_drop wait)},
          {"recv_timeout", ~w(wait)},
          {"counter_server", ~w(recv_peek wait spawn)}
        ] do
      path = Path.join(@fixtures, "#{name}.ex")
      expected_path = Path.join(@fixtures, "#{name}.bc.json")
      assert {:ok, module} = AutumnCompiler.compile_file(path)
      expected = expected_path |> File.read!() |> Jason.decode!()
      assert module == expected
      assert module["version"] == 7
      code = Enum.flat_map(module["functions"], & &1["code"])
      for op <- ops, do: assert(Enum.any?(code, &(&1["op"] == op)))
    end
  end

  test "lowers guards / dyn_list / dyn_tuple / map_pat (Phase 3)" do
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
      expected_path = Path.join(@fixtures, "#{name}.bc.json")
      assert {:ok, module} = AutumnCompiler.compile_file(path)
      expected = expected_path |> File.read!() |> Jason.decode!()
      assert module == expected
      code = Enum.flat_map(module["functions"], & &1["code"])
      assert check.(code)
    end
  end

  test "lowers rescue_in / link_exit (Phase 4)" do
    path = Path.join(@fixtures, "rescue_in.ex")
    expected_path = Path.join(@fixtures, "rescue_in.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "enter_try"))

    path = Path.join(@fixtures, "link_exit.ex")
    expected_path = Path.join(@fixtures, "link_exit.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 14
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "link"))
    assert Enum.any?(code, &(&1["op"] == "spawn"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "Process.flag/2"))
  end

  test "lowers IR v14 Process.exit / drain / link_kill / badarg_rescue" do
    for {name, version, check} <- [
          {"process_exit_down", 14,
           fn code -> Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "Process.exit/2")) end},
          {"link_kill", 8, fn code -> Enum.any?(code, &(&1["op"] == "link")) end},
          {"drain_siblings", 2, fn code -> Enum.any?(code, &(&1["op"] == "spawn")) end},
          {"badarg_rescue", 6, fn code -> Enum.any?(code, &(&1["op"] == "enter_try")) end}
        ] do
      path = Path.join(@fixtures, "#{name}.ex")
      expected_path = Path.join(@fixtures, "#{name}.bc.json")
      assert {:ok, module} = AutumnCompiler.compile_file(path)
      expected = expected_path |> File.read!() |> Jason.decode!()
      assert module == expected
      assert module["version"] == version
      code = Enum.flat_map(module["functions"], & &1["code"])
      assert check.(code)
    end
  end

  test "lowers monitor_exit (Phase 5)" do
    path = Path.join(@fixtures, "monitor_exit.ex")
    expected_path = Path.join(@fixtures, "monitor_exit.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 9
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "monitor"))
    assert Enum.any?(code, &(&1["op"] == "spawn"))
  end

  test "lowers monitored_call / monitored_down (Phase 6)" do
    path = Path.join(@fixtures, "counter_server.ex")
    expected_path = Path.join(@fixtures, "counter_server.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 7
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "recv_peek"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "make_tuple/3"))

    path = Path.join(@fixtures, "monitored_call.ex")
    expected_path = Path.join(@fixtures, "monitored_call.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 9
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "monitor"))
    assert Enum.any?(code, &(&1["op"] == "demonitor"))

    path = Path.join(@fixtures, "monitored_down.ex")
    expected_path = Path.join(@fixtures, "monitored_down.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 9
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "monitor"))
    assert Enum.any?(code, &(&1["op"] == "raise"))
  end

  test "lowers genserver_counter / genserver_call_down (call+ref+monitor)" do
    path = Path.join(@fixtures, "genserver_counter.ex")
    expected_path = Path.join(@fixtures, "genserver_counter.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 9
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "monitor"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "make_ref/0"))

    path = Path.join(@fixtures, "genserver_call_down.ex")
    expected_path = Path.join(@fixtures, "genserver_call_down.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 9
  end

  test "lowers float_string (IR v10)" do
    path = Path.join(@fixtures, "float_string.ex")
    expected_path = Path.join(@fixtures, "float_string.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 10
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "load_lit" && match?(%{"float" => _}, &1["lit"])))
    assert Enum.any?(code, &(&1["op"] == "load_lit" && match?(%{"string" => _}, &1["lit"])))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "<>/2"))
  end

  test "lowers if_else / cond_main (Phase 7)" do
    path = Path.join(@fixtures, "if_else.ex")
    expected_path = Path.join(@fixtures, "if_else.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "jump_if_eq"))
    assert Enum.any?(code, &(&1["op"] == "jump"))

    path = Path.join(@fixtures, "cond_main.ex")
    expected_path = Path.join(@fixtures, "cond_main.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "jump_if_eq"))
    # exhausted cond raises :cond_clause_error
    assert Enum.any?(code, &(&1["op"] == "raise"))
  end

  test "lowers match_pin (pat = expr and ^pin)" do
    path = Path.join(@fixtures, "match_pin.ex")
    expected_path = Path.join(@fixtures, "match_pin.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "raise"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "==/2"))
    assert Enum.any?(code, &(&1["op"] == "get_list_rest"))
  end

  test "lowers multi_mod (IR v12 modules[])" do
    path = Path.join(@fixtures, "multi_mod.ex")
    expected_path = Path.join(@fixtures, "multi_mod.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 12
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
    expected_path = Path.join(@fixtures, "preempt_fair.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 14
    names = Enum.map(module["functions"], & &1["name"])
    assert "Main.hog/0" in names
    assert "Main.helper/0" in names
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "spawn"))
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "Process.exit/2"))
  end

  test "lowers hot_load (Code.load_file IR v13)" do
    path = Path.join(@fixtures, "hot_load.ex")
    expected_path = Path.join(@fixtures, "hot_load.bc.json")
    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 13
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "load_file"))
    assert Enum.any?(code, &(&1["op"] == "enter_try"))
  end

  test "lowers list_lit" do
    path = Path.join(@fixtures, "list_lit.ex")
    expected_path = Path.join(@fixtures, "list_lit.bc.json")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
  end

  test "lowers multi-clause fn" do
    path = Path.join(@fixtures, "fn_multi.ex")
    expected_path = Path.join(@fixtures, "fn_multi.bc.json")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    assert module["version"] == 11
    assert Enum.any?(module["functions"], &String.contains?(&1["name"], "__fn_"))
  end

  test "lowers hd/tl/++ list helpers" do
    path = Path.join(@fixtures, "list_helpers.ex")
    expected_path = Path.join(@fixtures, "list_helpers.bc.json")

    assert {:ok, module} = AutumnCompiler.compile_file(path)
    expected = expected_path |> File.read!() |> Jason.decode!()
    assert module == expected
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "get_list_elem"))
    assert Enum.any?(code, &(&1["op"] == "get_list_rest"))
    assert Enum.any?(module["functions"], &(&1["name"] == "Main.__list_append__/2"))
  end

  test "eval_expr wraps expression as Repl.main/0" do
    assert {:ok, module, _expr} = AutumnCompiler.eval_expr("1 + 2")
    assert module["entry"] == "Repl.main/0"
    assert module["version"] == 1
    code = List.first(module["functions"])["code"]
    assert Enum.any?(code, &(&1["op"] == "call" && &1["fun"] == "+/2"))
  end

  test "eval_expr replays session bindings" do
    assert {:ok, _m1, e1} = AutumnCompiler.eval_expr("a = 1 + 4")
    bindings = AutumnCompiler.binding_after([], e1)
    assert [{:a, {:+, _, [1, 4]}}] = bindings

    assert {:ok, module, _e2} = AutumnCompiler.eval_expr("[a, a + 1]", bindings)
    code = List.first(module["functions"])["code"]
    # Prior `a = 1 + 4` is inlined before the list expr.
    assert Enum.count(code, &(&1["op"] == "call" && &1["fun"] == "+/2")) >= 2
  end
end
