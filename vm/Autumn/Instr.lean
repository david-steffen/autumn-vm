import Autumn.Term

namespace Autumn

abbrev FunName := String
abbrev Reg := Nat
abbrev Label := Nat

inductive Tag where
  | nil | bool | int | atom | tuple | list | pid
  deriving Repr, BEq, Inhabited

inductive Instr where
  | loadLit (reg : Reg) (lit : Term)
  | move (dest src : Reg)
  | call (dest : Reg) (funName : FunName) (args : Array Reg)
  | return_ (reg : Reg)
  | halt (reg : Reg)
  -- IR v2 sequential
  | jump (target : Label)
  | jumpIfEq (target : Label) (reg : Reg) (lit : Term)
  | getTupleElem (dest : Reg) (tupleReg : Reg) (index : Nat)
  | isTag (dest : Reg) (reg : Reg) (tag : Tag)
  -- IR v2 processes
  | spawn (dest : Reg) (funName : FunName) (args : Array Reg)
  | send (pidReg msgReg : Reg)
  | recv (dest : Reg)
  -- IR v3 list patterns
  | getListElem (dest : Reg) (listReg : Reg) (index : Nat)
  deriving Repr, BEq, Inhabited

structure Function where
  name : FunName
  arity : Nat
  locals : Nat
  code : Array Instr
  deriving Repr, BEq, Inhabited

structure Module where
  version : Nat
  entry : FunName
  functions : Array Function
  deriving Repr, BEq, Inhabited

namespace Module

/-- Lookup by MFA name (list-based for proof-friendly `find?` lemmas). -/
def findFunction (m : Module) (name : FunName) : Option Function :=
  m.functions.toList.find? (fun f => f.name == name)

end Module

/-- Builtin MFA names. -/
def isBuiltinName (name : FunName) : Bool :=
  name == "+/2" || name == "-/2" || name == "*/2" || name == "==/2" ||
  name == "tuple_size/1" || name == "elem/2" || name == "list_size/1"

end Autumn
