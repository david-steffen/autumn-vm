import Lean.Data.Json
import Autumn.Instr

open Lean

namespace Autumn
namespace Encode

def encodeTag : Tag → Json
  | .nil => "nil"
  | .bool => "bool"
  | .int => "int"
  | .atom => "atom"
  | .tuple => "tuple"
  | .list => "list"
  | .pid => "pid"

partial def encodeLit : Term → Json
  | .nil => Json.null
  | .bool b => Json.mkObj [("bool", b)]
  | .int n => Json.mkObj [("int", Json.num n)]
  | .atom s => Json.mkObj [("atom", s)]
  | .tuple elems => Json.mkObj [("tuple", Json.arr (elems.map encodeLit))]
  | .list elems => Json.mkObj [("list", Json.arr (elems.map encodeLit))]
  | .pid id => Json.mkObj [("pid", id)]

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
  | .isTag d r tag =>
      Json.mkObj [("op", "is_tag"), ("dest", d), ("reg", r), ("tag", encodeTag tag)]
  | .spawn d f args =>
      Json.mkObj [("op", "spawn"), ("dest", d), ("fun", f),
        ("args", Json.arr (args.map (fun a => toJson a)))]
  | .send p m => Json.mkObj [("op", "send"), ("pid", p), ("msg", m)]
  | .recv d => Json.mkObj [("op", "recv"), ("dest", d)]

def encodeFunction (f : Function) : Json :=
  Json.mkObj [
    ("name", f.name),
    ("arity", f.arity),
    ("locals", f.locals),
    ("code", Json.arr (f.code.map encodeInstr))
  ]

def encodeModule (m : Module) : Json :=
  Json.mkObj [
    ("version", m.version),
    ("entry", m.entry),
    ("functions", Json.arr (m.functions.map encodeFunction))
  ]

def toString (m : Module) : String := (encodeModule m).pretty

end Encode
end Autumn
