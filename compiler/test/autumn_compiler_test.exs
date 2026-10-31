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
      def main, do: 1 |> (fn x -> x end).()
    end
    """

    path = Path.join(System.tmp_dir!(), "autumn_reject_#{System.unique_integer([:positive])}.ex")
    File.write!(path, source)

    assert {:error, msg} = AutumnCompiler.compile_file(path)
    assert msg =~ "unsupported"
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
    assert module["version"] == 8
    code = Enum.flat_map(module["functions"], & &1["code"])
    assert Enum.any?(code, &(&1["op"] == "link"))
    assert Enum.any?(code, &(&1["op"] == "spawn"))
  end
end
