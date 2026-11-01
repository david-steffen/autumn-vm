import Autumn.Term

namespace Autumn

abbrev FunName := String
abbrev Reg := Nat
abbrev Label := Nat

inductive Tag where
  | nil | bool | int | float | atom | string | binary | bitstring
  | tuple | list | map | pid | ref | fun
  deriving Repr, BEq, Inhabited

/-- IR v7/v19 `wait` timeout: infinity, immediate ticks, or register holding a non-neg int. -/
inductive WaitTimeout where
  | infinity
  | lit (n : Nat)
  | reg (r : Reg)
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
  /-- Park until message (`retry`) or logical-clock timeout (`after`). -/
  | wait (retry after : Label) (timeout : WaitTimeout)
  -- IR v8 process links
  | link (pidReg : Reg)
  -- IR v9 monitors
  | monitor (dest : Reg) (pidReg : Reg)
  | demonitor (refReg : Reg)
  -- IR v11 closures
  | makeFun (dest : Reg) (funName : FunName) (captures : Array Reg)
  | apply (dest : Reg) (funReg : Reg) (args : Array Reg)
  -- IR v13 dynamic load (`Code.load_file`); IO runner services the read
  | loadFile (dest pathReg : Reg)
  -- IR v15 dynamic MFA: mod/fun atoms → `"#{mod}.#{fun}/#{arity}"`
  | applyMfa (dest : Reg) (modReg funReg : Reg) (args : Array Reg)
  deriving Repr, BEq, Inhabited

structure Function where
  name : FunName
  arity : Nat
  locals : Nat
  code : Array Instr
  deriving Repr, BEq, Inhabited

/-- Named code unit inside a loadable image (IR v12). -/
structure CodeModule where
  name : String
  functions : Array Function
  deriving Repr, BEq, Inhabited

/-- Loadable program image: one or more named modules + entry MFA. -/
structure Module where
  version : Nat
  entry : FunName
  modules : Array CodeModule
  deriving Repr, BEq, Inhabited

namespace Module

/-- Flatten all functions across modules (MFA names are globally unique in WF images). -/
def allFunctions (m : Module) : Array Function :=
  m.modules.foldl (fun acc cm => acc ++ cm.functions) #[]

/-- Lookup by MFA name (list-based for proof-friendly `find?` lemmas). -/
def findFunction (m : Module) (name : FunName) : Option Function :=
  m.allFunctions.toList.find? (fun f => f.name == name)

/-- Build a single-module image (legacy / Examples helper). -/
def ofFunctions (version : Nat) (entry : FunName) (functions : Array Function)
    (modName : String := "") : Module :=
  let name :=
    if modName != "" then modName
    else
      let head := (entry.splitOn "/").headD entry
      let parts := head.splitOn "."
      if parts.length ≤ 1 then head
      else String.intercalate "." parts.dropLast
  { version, entry, modules := #[{ name, functions }] }

/-- Install `incoming` code modules into `host`: replace same `name`, else append.
Keeps `host.entry`. Bumps version to at least 13. -/
def installModules (host incoming : Module) : Module :=
  let mods :=
    incoming.modules.foldl
      (fun acc cm =>
        match acc.findIdx? (fun c => c.name == cm.name) with
        | some i => acc.set! i cm
        | none => acc.push cm)
      host.modules
  { host with
    modules := mods
    version := max host.version (max incoming.version 13) }

end Module

/-- `make_tuple/N` for any N — used by the lowerer for non-literal tuples. -/
def isMakeTupleName (name : FunName) : Bool :=
  name.startsWith "make_tuple/"

/-- Builtin MFA names (including allocating `cons/2` / `make_tuple/N`).
`Process.flag/2` / `Process.exit/2` are State-mutating and handled in `stepInstr`. -/
def isBuiltinName (name : FunName) : Bool :=
  name == "+/2" || name == "-/2" || name == "*/2" || name == "==/2" ||
  name == "</2" || name == ">/2" || name == "<=/2" || name == ">=/2" ||
  name == "tuple_size/1" || name == "elem/2" || name == "list_size/1" ||
  name == "map_size/1" || name == "map_get/2" || name == "map_put/3" ||
  name == "self/0" || name == "make_ref/0" || name == "<>/2" ||
  name == "bit_size/1" || name == "bs_get_integer/2" || name == "bs_drop/2" ||
  name == "cons/2" || name == "Process.flag/2" || name == "Process.exit/2" ||
  name == "Process.hibernate/0" ||
  name == "ets_new/0" || name == "ets_new/2" || name == "ets_insert/3" ||
  name == "ets_lookup/2" || name == "ets_delete/2" || name == "ets_delete_object/2" ||
  name == "ets_match_object/2" || name == "ets_select/2" || name == "ets_heir/2" ||
  name == "ets_first/1" || name == "ets_next/2" || name == "ets_give_away/3" ||
  isMakeTupleName name

end Autumn
