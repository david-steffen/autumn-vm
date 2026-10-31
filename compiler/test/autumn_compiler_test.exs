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
    assert module["version"] == 2
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
    assert module["version"] == 2
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
    assert module["version"] == 3
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

  test "rejects cons list patterns" do
    source = """
    defmodule Main do
      def main do
        case [1, 2] do
          [h | t] -> h
          _ -> 0
        end
      end
    end
    """

    path = Path.join(System.tmp_dir!(), "autumn_cons_#{System.unique_integer([:positive])}.ex")
    File.write!(path, source)
    assert {:error, msg} = AutumnCompiler.compile_file(path)
    assert msg =~ "cons"
  end
end
