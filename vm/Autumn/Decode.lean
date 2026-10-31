import Lean.Data.Json
import Autumn.State

open Lean

namespace Autumn

namespace Decode

def err (msg : String) : Except StepError α :=
  throw (StepError.decodeError msg)

def field (j : Json) (k : String) : Except StepError Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error e => err e

def asNat (j : Json) : Except StepError Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error e => err e

def asInt (j : Json) : Except StepError Int :=
  match j.getInt? with
  | .ok n => pure n
  | .error e => err e

def asString (j : Json) : Except StepError String :=
  match j.getStr? with
  | .ok s => pure s
  | .error e => err e

def asBool (j : Json) : Except StepError Bool :=
  match j.getBool? with
  | .ok b => pure b
  | .error e => err e

def asArray (j : Json) : Except StepError (Array Json) :=
  match j.getArr? with
  | .ok a => pure a
  | .error e => err e

def decodeTag (j : Json) : Except StepError Tag := do
  let s ← asString j
  match s with
  | "nil" => pure .nil
  | "bool" => pure .bool
  | "int" => pure .int
  | "atom" => pure .atom
  | "tuple" => pure .tuple
  | "list" => pure .list
  | "map" => pure .map
  | "pid" => pure .pid
  | other => err s!"unknown tag: {other}"

partial def decodeLit (j : Json) : Except StepError Term := do
  if j.isNull then
    return Term.nil
  match j.getObjVal? "bool" with
  | .ok v => return Term.bool (← asBool v)
  | .error _ => pure ()
  match j.getObjVal? "int" with
  | .ok v => return Term.int (← asInt v)
  | .error _ => pure ()
  match j.getObjVal? "atom" with
  | .ok v => return Term.atom (← asString v)
  | .error _ => pure ()
  match j.getObjVal? "tuple" with
  | .ok v =>
    let elems ← asArray v
    return Term.tuple (← elems.mapM decodeLit)
  | .error _ => pure ()
  match j.getObjVal? "list" with
  | .ok v =>
    let elems ← asArray v
    return Term.list (← elems.mapM decodeLit)
  | .error _ => pure ()
  match j.getObjVal? "map" with
  | .ok v =>
    let elems ← asArray v
    let entries ← elems.mapM fun e => do
      let k ← decodeLit (← field e "key")
      let val ← decodeLit (← field e "value")
      pure (k, val)
    return Term.map entries
  | .error _ => pure ()
  match j.getObjVal? "pid" with
  | .ok v => return Term.pid (← asNat v)
  | .error _ => err "unknown literal tag"

def decodeInstr (j : Json) : Except StepError Instr := do
  let op ← asString (← field j "op")
  match op with
  | "load_lit" =>
    pure (.loadLit (← asNat (← field j "reg")) (← decodeLit (← field j "lit")))
  | "move" =>
    pure (.move (← asNat (← field j "dest")) (← asNat (← field j "src")))
  | "call" =>
    pure (.call (← asNat (← field j "dest")) (← asString (← field j "fun"))
      (← (← asArray (← field j "args")).mapM asNat))
  | "return" =>
    pure (.return_ (← asNat (← field j "reg")))
  | "halt" =>
    pure (.halt (← asNat (← field j "reg")))
  | "jump" =>
    pure (.jump (← asNat (← field j "target")))
  | "jump_if_eq" =>
    pure (.jumpIfEq (← asNat (← field j "target")) (← asNat (← field j "reg"))
      (← decodeLit (← field j "lit")))
  | "get_tuple_elem" =>
    pure (.getTupleElem (← asNat (← field j "dest")) (← asNat (← field j "tuple"))
      (← asNat (← field j "index")))
  | "get_list_elem" =>
    pure (.getListElem (← asNat (← field j "dest")) (← asNat (← field j "list"))
      (← asNat (← field j "index")))
  | "get_list_rest" =>
    pure (.getListRest (← asNat (← field j "dest")) (← asNat (← field j "list"))
      (← asNat (← field j "index")))
  | "is_tag" =>
    pure (.isTag (← asNat (← field j "dest")) (← asNat (← field j "reg"))
      (← decodeTag (← field j "tag")))
  | "spawn" =>
    pure (.spawn (← asNat (← field j "dest")) (← asString (← field j "fun"))
      (← (← asArray (← field j "args")).mapM asNat))
  | "send" =>
    pure (.send (← asNat (← field j "pid")) (← asNat (← field j "msg")))
  | "recv" =>
    pure (.recv (← asNat (← field j "dest")))
  | "recv_peek" =>
    pure (.recvPeek (← asNat (← field j "dest")) (← asNat (← field j "index"))
      (← asNat (← field j "empty")))
  | "recv_drop" =>
    pure (.recvDrop (← asNat (← field j "index")))
  | "wait" => do
    let retry ← asNat (← field j "retry")
    let after ← asNat (← field j "after")
    let timeout ←
      match j.getObjVal? "timeout" with
      | .error _ => pure none
      | .ok Json.null => pure none
      | .ok t => pure (some (← asNat t))
    pure (.wait retry after timeout)
  | "enter_try" =>
    pure (.enterTry (← asNat (← field j "rescue")) (← asNat (← field j "exc")))
  | "leave_try" =>
    pure .leaveTry
  | "raise" =>
    pure (.raise (← asNat (← field j "reg")))
  | "link" =>
    pure (.link (← asNat (← field j "pid")))
  | other => err s!"unknown op: {other}"

/-- Resolve `label` ops to jump targets; strip labels from code. -/
def resolveLabels (code : Array Instr) : Except StepError (Array Instr) := do
  -- Labels are encoded as jump/jumpIfEq already using absolute indices in v2 JSON.
  -- Optional: support {"op":"label","name":"L0"} via a prepass — handled in Mix lowerer
  -- by emitting absolute indices. Pass through.
  pure code

def decodeFunction (j : Json) : Except StepError Function := do
  let name ← asString (← field j "name")
  let arity ← asNat (← field j "arity")
  let locals_ ← asNat (← field j "locals")
  let raw ← (← asArray (← field j "code")).mapM decodeInstr
  let code ← resolveLabels raw
  if locals_ < arity then
    err s!"function {name}: locals ({locals_}) < arity ({arity})"
  pure { name, arity, locals := locals_, code }

def decodeModule (j : Json) : Except StepError Module := do
  let version ← asNat (← field j "version")
  if version != 1 && version != 2 && version != 3 && version != 4 && version != 5 &&
      version != 6 && version != 7 && version != 8 then
    err s!"unsupported IR version: {version}"
  let entry ← asString (← field j "entry")
  let functions ← (← asArray (← field j "functions")).mapM decodeFunction
  pure { version, entry, functions }

def fromString (s : String) : Except StepError Module :=
  match Json.parse s with
  | .error e => err e
  | .ok j => decodeModule j

end Decode

end Autumn
