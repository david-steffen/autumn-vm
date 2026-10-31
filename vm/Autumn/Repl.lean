import Autumn.Json.Decode
import Autumn.Step
import Autumn.WellFormed

/-!
# Durable REPL session

Line protocol on stdin/stdout (Mix `autumn.repl` is the usual frontend):

* `EVAL <json>` — install into the session module, spawn a fresh entry process, run to
  machine result; reply `=> <term>` or `! <error>`.
* `LOAD <json>` — install only (no run); reply `=> :ok` or `! <error>`.
* `QUIT` — exit 0.

Modules persist across commands; process tables / heaps reset on each `EVAL`.
`nextRef` / `clock` carry over so refs stay unique across evals.
-/

namespace Autumn
namespace Repl

structure Session where
  module : Module
  nextRef : Nat := 0
  clock : Nat := 0
  deriving Repr

def defaultFuel : Nat := 100000

/-- Merge `incoming` into an optional host; keeps host entry unless `setEntry`. -/
def install (sess? : Option Session) (incoming : Module) (setEntry : Bool) :
    Except StepError Session :=
  let m :=
    match sess? with
    | none => incoming
    | some sess =>
      let m0 := Module.installModules sess.module incoming
      if setEntry then { m0 with entry := incoming.entry } else m0
  if !Module.checkWF m then
    .error (.typeError "module not well-formed")
  else
    match sess? with
    | none => .ok { module := m }
    | some sess => .ok { sess with module := m }

def replyOk (msg : String) : IO Unit := do
  IO.println s!"=> {msg}"
  (← IO.getStdout).flush

def replyErr (msg : String) : IO Unit := do
  IO.println s!"! {msg}"
  (← IO.getStdout).flush

def eval (sess? : Option Session) (incoming : Module) (fuel : Nat := defaultFuel) :
    IO (Except StepError (Session × Term)) := do
  match install sess? incoming (setEntry := true) with
  | .error e => pure (.error e)
  | .ok sess =>
    match State.initial sess.module with
    | .error e => pure (.error e)
    | .ok s0 =>
      let s0 := { s0 with nextRef := sess.nextRef, clock := sess.clock }
      match ← Step.runIOState fuel s0 with
      | .error e => pure (.error e)
      | .ok (s, v) =>
        pure (.ok ({ module := s.module, nextRef := s.nextRef, clock := s.clock }, v))

def load (sess? : Option Session) (incoming : Module) : Except StepError Session :=
  install sess? incoming (setEntry := false)

/-- Strip trailing ASCII whitespace (incl. CR/LF from `getLine`). -/
def trimLine (line : String) : String :=
  (String.trimAsciiEnd line).toString

partial def loop (sess? : Option Session) : IO UInt32 := do
  let raw ← (← IO.getStdin).getLine
  -- EOF
  if raw.isEmpty then
    return 0
  let line := trimLine raw
  if line.isEmpty then
    loop sess?
  else if line == "QUIT" then
    return 0
  else if line.startsWith "EVAL " then
    let json := (line.drop "EVAL ".length).toString
    match Json.Decode.fromString json with
    | .error e =>
      replyErr (toString e)
      loop sess?
    | .ok incoming =>
      match ← eval sess? incoming with
      | .error e =>
        replyErr (toString e)
        loop sess?
      | .ok (sess, v) =>
        replyOk (toString v)
        loop (some sess)
  else if line.startsWith "LOAD " then
    let json := (line.drop "LOAD ".length).toString
    match Json.Decode.fromString json with
    | .error e =>
      replyErr (toString e)
      loop sess?
    | .ok incoming =>
      match load sess? incoming with
      | .error e =>
        replyErr (toString e)
        loop sess?
      | .ok sess =>
        replyOk ":ok"
        loop (some sess)
  else
    replyErr s!"unknown command (want EVAL/LOAD/QUIT): {(line.take 40).toString}"
    loop sess?

/-- Entry for `autumn --repl`: announce readiness, then serve the line protocol. -/
def main : IO UInt32 := do
  IO.println "# ready"
  (← IO.getStdout).flush
  loop none

end Repl
end Autumn
