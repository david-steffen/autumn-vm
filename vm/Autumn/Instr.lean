import Autumn.Term

namespace Autumn

abbrev FunName := String
abbrev Reg := Nat
abbrev Label := Nat

inductive Tag where
  | nil | bool | int | atom | tuple | list | map | pid
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
  -- IR v4 cons / list rest
  | getListRest (dest : Reg) (listReg : Reg) (index : Nat)
  -- IR v6 exceptions
  | enterTry (rescueIp : Label) (excReg : Reg)
  | leaveTry
  | raise (reg : Reg)
  -- IR v7 selective receive
  | recvPeek (dest : Reg) (indexReg : Reg) (empty : Label)
  | recvDrop (indexReg : Reg)
  /-- Park until message (`retry`) or logical-clock timeout (`after`). `none` timeout = infinity. -/
  | wait (retry after : Label) (timeout : Option Nat)
  -- IR v8 process links
  | link (pidReg : Reg)
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

/-- `make_tuple/N` for any N — used by the lowerer for non-literal tuples. -/
def isMakeTupleName (name : FunName) : Bool :=
  name.startsWith "make_tuple/"

/-- Builtin MFA names (including allocating `cons/2` / `make_tuple/N`). -/
def isBuiltinName (name : FunName) : Bool :=
  name == "+/2" || name == "-/2" || name == "*/2" || name == "==/2" ||
  name == "</2" || name == ">/2" || name == "<=/2" || name == ">=/2" ||
  name == "tuple_size/1" || name == "elem/2" || name == "list_size/1" ||
  name == "map_size/1" || name == "map_get/2" || name == "map_put/3" ||
  name == "self/0" || name == "cons/2" || isMakeTupleName name

end Autumn
