import Lean.Data.Json
import Autumn.Instr

open Lean

namespace Autumn.Json.Encode

def encodeTag : Tag → Json
  | .nil => "nil"
  | .bool => "bool"
  | .int => "int"
  | .atom => "atom"
  | .tuple => "tuple"
  | .list => "list"
  | .map => "map"
  | .pid => "pid"
  | .ref => "ref"
  | .float => "float"
  | .string => "string"
  | .fun => "fun"

partial def encodeLit : Term → Json
  | .nil => Json.null
  | .bool b => Json.mkObj [("bool", b)]
  | .int n => Json.mkObj [("int", Json.num n)]
  | .float f =>
      match JsonNumber.fromFloat? f with
      | .inr n => Json.mkObj [("float", Json.num n)]
      | .inl _ => Json.mkObj [("float", Json.num ⟨0, 0⟩)]
  | .atom s => Json.mkObj [("atom", s)]
  | .string s => Json.mkObj [("string", s)]
  | .tuple elems => Json.mkObj [("tuple", Json.arr (elems.map encodeLit))]
  | .list elems => Json.mkObj [("list", Json.arr (elems.map encodeLit))]
  | .map entries =>
      Json.mkObj [("map", Json.arr (entries.map fun (k, v) =>
        Json.mkObj [("key", encodeLit k), ("value", encodeLit v)]))]
  | .pid id => Json.mkObj [("pid", id)]
  | .reference id => Json.mkObj [("ref", id)]
  | .closure funName env =>
      Json.mkObj [("closure", Json.mkObj
        [("fun", funName), ("env", Json.arr (env.map encodeLit))])]

def encodeInstr : Instr → Json
  | .loadLit r lit =>
      Json.mkObj [("op", "load_lit"), ("reg", r), ("lit", encodeLit lit)]
  | .move d s =>
      Json.mkObj [("op", "move"), ("dest", d), ("src", s)]
  | .call d f args =>
      Json.mkObj [("op", "call"), ("dest", d), ("fun", f),
        ("args", Json.arr (args.map (fun a => toJson a)))]
  | .return_ r => Json.mkObj [("op", "return"), ("reg", r)]
  | .halt r => Json.mkObj [("op", "halt"), ("reg", r)]
  | .jump t => Json.mkObj [("op", "jump"), ("target", t)]
  | .jumpIfEq t r lit =>
      Json.mkObj [("op", "jump_if_eq"), ("target", t), ("reg", r), ("lit", encodeLit lit)]
  | .getTupleElem d t i =>
      Json.mkObj [("op", "get_tuple_elem"), ("dest", d), ("tuple", t), ("index", i)]
  | .getListElem d t i =>
      Json.mkObj [("op", "get_list_elem"), ("dest", d), ("list", t), ("index", i)]
  | .getListRest d t i =>
      Json.mkObj [("op", "get_list_rest"), ("dest", d), ("list", t), ("index", i)]
  | .isTag d r tag =>
      Json.mkObj [("op", "is_tag"), ("dest", d), ("reg", r), ("tag", encodeTag tag)]
  | .spawn d f args =>
      Json.mkObj [("op", "spawn"), ("dest", d), ("fun", f),
        ("args", Json.arr (args.map (fun a => toJson a)))]
  | .send p m => Json.mkObj [("op", "send"), ("pid", p), ("msg", m)]
  | .recv d => Json.mkObj [("op", "recv"), ("dest", d)]
  | .recvPeek d i empty =>
      Json.mkObj [("op", "recv_peek"), ("dest", d), ("index", i), ("empty", empty)]
  | .recvDrop i => Json.mkObj [("op", "recv_drop"), ("index", i)]
  | .wait retry after timeout =>
      let base := [("op", Json.str "wait"), ("retry", toJson retry), ("after", toJson after)]
      let fields :=
        match timeout with
        | none => base ++ [("timeout", Json.null)]
        | some n => base ++ [("timeout", toJson n)]
      Json.mkObj fields
  | .enterTry rescueIp exc =>
      Json.mkObj [("op", "enter_try"), ("rescue", rescueIp), ("exc", exc)]
  | .leaveTry => Json.mkObj [("op", "leave_try")]
  | .raise r => Json.mkObj [("op", "raise"), ("reg", r)]
  | .link p => Json.mkObj [("op", "link"), ("pid", p)]
  | .monitor d p => Json.mkObj [("op", "monitor"), ("dest", d), ("pid", p)]
  | .demonitor r => Json.mkObj [("op", "demonitor"), ("ref", r)]
  | .makeFun d f caps =>
      Json.mkObj [("op", "make_fun"), ("dest", d), ("fun", f),
        ("captures", Json.arr (caps.map (fun a => toJson a)))]
  | .apply d f args =>
      Json.mkObj [("op", "apply"), ("dest", d), ("fun", f),
        ("args", Json.arr (args.map (fun a => toJson a)))]
  | .loadFile d p =>
      Json.mkObj [("op", "load_file"), ("dest", d), ("path", p)]

def encodeFunction (f : Function) : Json :=
  Json.mkObj [
    ("name", f.name),
    ("arity", f.arity),
    ("locals", f.locals),
    ("code", Json.arr (f.code.map encodeInstr))
  ]

def encodeCodeModule (cm : CodeModule) : Json :=
  Json.mkObj [
    ("name", cm.name),
    ("functions", Json.arr (cm.functions.map encodeFunction))
  ]

/-- Always emit first-class `modules[]` (IR v12 shape). -/
def encodeModule (m : Module) : Json :=
  Json.mkObj [
    ("version", m.version),
    ("entry", m.entry),
    ("modules", Json.arr (m.modules.map encodeCodeModule))
  ]

def toString (m : Module) : String := (encodeModule m).pretty

end Autumn.Json.Encode
