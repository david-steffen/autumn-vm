import Autumn.Json.Decode
import Autumn.Json.Encode
import Autumn.GCDemo
import Autumn.Repl
import Autumn.Step
import Autumn.Step.Lemmas
import Autumn.Syntax

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
    IO.eprintln "usage: autumn <file.bc.json> | autumn --repl | autumn --lean-demo | autumn --roundtrip <file.bc.json>"
    return 2
