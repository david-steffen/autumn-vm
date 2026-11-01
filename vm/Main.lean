import Autumn.Json.Decode
import Autumn.Json.Encode
import Autumn.GCDemo
import Autumn.Repl
import Autumn.Step
import Autumn.Step.Lemmas
import Autumn.Syntax

/-- Load once, warmup once, then time `runs` executions of `runModuleIO`. -/
def benchModule (mod : Autumn.Module) (runs : Nat) (fuel : Nat) : IO UInt32 := do
  match ← Autumn.Step.runModuleIO mod (fuel := fuel) with
  | .error e =>
    IO.eprintln s!"warmup error: {e}"
    return 1
  | .ok warm =>
    let t0 ← IO.monoNanosNow
    let mut last := warm
    let mut i := 0
    while i < runs do
      match ← Autumn.Step.runModuleIO mod (fuel := fuel) with
      | .error e =>
        IO.eprintln s!"runtime error on run {i}: {e}"
        return 1
      | .ok v =>
        last := v
      i := i + 1
    let t1 ← IO.monoNanosNow
    let total := t1 - t0
    let per := if runs = 0 then 0 else total / runs
    IO.println s!"runs={runs} total_ns={total} ns_per_run={per} result={toString last}"
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--repl"] =>
    Autumn.Repl.main
  | ["--lean-demo"] =>
    match ← Autumn.Step.runModuleIO Autumn.Syntax.leanDemoModule with
    | .error e =>
      IO.eprintln s!"runtime error: {e}"
      return 1
    | .ok v =>
      IO.println (toString v)
      return 0
  | ["--roundtrip", path] =>
    let contents ← IO.FS.readFile path
    match Autumn.Json.Decode.fromString contents with
    | .error e =>
      IO.eprintln s!"decode error: {e}"
      return 1
    | .ok mod =>
      let encoded := Autumn.Json.Encode.toString mod
      match Autumn.Json.Decode.fromString encoded with
      | .error e =>
        IO.eprintln s!"re-decode error: {e}"
        return 1
      | .ok mod2 =>
        match ← Autumn.Step.runModuleIO mod2 with
        | .error e =>
          IO.eprintln s!"runtime error: {e}"
          return 1
        | .ok v =>
          IO.println (toString v)
          return 0
  | ["--bench", runsStr, path] =>
    match runsStr.toNat? with
    | none =>
      IO.eprintln s!"--bench: invalid run count {runsStr}"
      return 2
    | some runs =>
      let contents ← IO.FS.readFile path
      match Autumn.Json.Decode.fromString contents with
      | .error e =>
        IO.eprintln s!"decode error: {e}"
        return 1
      | .ok mod =>
        -- Generous fuel for recursive bench fixtures.
        benchModule mod runs (fuel := 10_000_000)
  | [path] =>
    let contents ← IO.FS.readFile path
    match Autumn.Json.Decode.fromString contents with
    | .error e =>
      IO.eprintln s!"decode error: {e}"
      return 1
    | .ok mod =>
      match ← Autumn.Step.runModuleIO mod with
      | .error e =>
        IO.eprintln s!"runtime error: {e}"
        return 1
      | .ok v =>
        IO.println (toString v)
        return 0
  | _ =>
    IO.eprintln "usage: autumn <file.bc.json> | autumn --bench <N> <file.bc.json> | autumn --repl | autumn --lean-demo | autumn --roundtrip <file.bc.json>"
    return 2
