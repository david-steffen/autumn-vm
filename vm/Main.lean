import Autumn.Decode
import Autumn.Encode
import Autumn.GCDemo
import Autumn.Step
import Autumn.StepLemmas
import Autumn.Syntax

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--lean-demo"] =>
    match Autumn.Step.runModule Autumn.Syntax.leanDemoModule with
    | .error e =>
      IO.eprintln s!"runtime error: {e}"
      return 1
    | .ok v =>
      IO.println (toString v)
      return 0
  | ["--roundtrip", path] =>
    let contents ← IO.FS.readFile path
    match Autumn.Decode.fromString contents with
    | .error e =>
      IO.eprintln s!"decode error: {e}"
      return 1
    | .ok mod =>
      let encoded := Autumn.Encode.toString mod
      match Autumn.Decode.fromString encoded with
      | .error e =>
        IO.eprintln s!"re-decode error: {e}"
        return 1
      | .ok mod2 =>
        match Autumn.Step.runModule mod2 with
        | .error e =>
          IO.eprintln s!"runtime error: {e}"
          return 1
        | .ok v =>
          IO.println (toString v)
          return 0
  | [path] =>
    let contents ← IO.FS.readFile path
    match Autumn.Decode.fromString contents with
    | .error e =>
      IO.eprintln s!"decode error: {e}"
      return 1
    | .ok mod =>
      match Autumn.Step.runModule mod with
      | .error e =>
        IO.eprintln s!"runtime error: {e}"
        return 1
      | .ok v =>
        IO.println (toString v)
        return 0
  | _ =>
    IO.eprintln "usage: autumn <file.bc.json> | autumn --lean-demo | autumn --roundtrip <file.bc.json>"
    return 2
