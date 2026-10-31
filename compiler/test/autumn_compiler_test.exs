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

  test "rejects pipe operator" do
    source = """
    defmodule Main do
      def main, do: 1 |> abs()
    end
    """

    path = Path.join(System.tmp_dir!(), "autumn_reject_#{System.unique_integer([:positive])}.ex")
    File.write!(path, source)

    assert {:error, msg} = AutumnCompiler.compile_file(path)
    assert msg =~ "unsupported"
  end

  test "rejects duplicate defs" do
    source = """
    defmodule Main do
      def f(x), do: 0
      def f(x), do: x
      def main, do: f(1)
    end
    """

    path = Path.join(System.tmp_dir!(), "autumn_dup_#{System.unique_integer([:positive])}.ex")
    File.write!(path, source)
    assert {:error, msg} = AutumnCompiler.compile_file(path)
    assert msg =~ "duplicate"
  end
end
