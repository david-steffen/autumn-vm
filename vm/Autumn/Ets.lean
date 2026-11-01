import Autumn.Term
import Autumn.State.Types

namespace Autumn

namespace Ets

/-- Parse `:set` / `:bag` / `:duplicate_bag` / `:ordered_set`. -/
def kindOfAtom (s : String) : Option EtsKind :=
  if s == "set" then some .set
  else if s == "bag" then some .bag
  else if s == "duplicate_bag" then some .duplicateBag
  else if s == "ordered_set" then some .orderedSet
  else none

/-- Resolve tab id: non-neg int tid, or atom name (live tables only). -/
def resolveTab (tables : Array EtsTable) (tab : Term) : Option Nat :=
  match tab with
  | .int n =>
    if n < 0 then none
    else
      let tid := n.toNat
      if h : tid < tables.size then
        if tables[tid]'h |>.alive then some tid else none
      else
        none
  | .atom name =>
    (List.range tables.size).findSome? fun i =>
      let t := tables[i]!
      if t.alive then
        match t.name with
        | some n => if n == name then some i else none
        | none => none
      else
        none
  | _ => none

/-- True if some **live** table already uses this atom name. -/
def nameTaken (tables : Array EtsTable) (name : String) : Bool :=
  tables.any fun t => t.alive && t.name == some name

/-- Object term for an entry. -/
def objectOf (key val : Term) : Term :=
  .tuple #[key, val]

/-- Insert into ordered_set: overwrite same key, keep `Term.lt` key order. -/
def insertOrdered (entries : Array (Term × Term)) (key val : Term) : Array (Term × Term) :=
  let rest := entries.filter (fun (k, _) => !(k == key))
  let rec go (i : Nat) : Array (Term × Term) :=
    if h : i < rest.size then
      let (k, _) := rest[i]'h
      if Term.lt key k then
        rest.insertIdx! i (key, val)
      else
        go (i + 1)
    else
      rest.push (key, val)
  go 0

/-- Insert by table kind. -/
def insertEntry (t : EtsTable) (key val : Term) : EtsTable :=
  match t.kind with
  | .set =>
    let rest := t.entries.filter (fun (k, _) => !(k == key))
    { t with entries := rest.push (key, val) }
  | .bag =>
    if t.entries.any (fun (k, v) => k == key && v == val) then t
    else { t with entries := t.entries.push (key, val) }
  | .duplicateBag =>
    { t with entries := t.entries.push (key, val) }
  | .orderedSet =>
    { t with entries := insertOrdered t.entries key val }

def lookupValues (t : EtsTable) (key : Term) : Array Term :=
  t.entries.filterMap fun (k, v) => if k == key then some v else none

def deleteKey (t : EtsTable) (key : Term) : EtsTable :=
  { t with entries := t.entries.filter (fun (k, _) => !(k == key)) }

/-- Remove first exact `{key,val}` match (one object). -/
def deleteObject (t : EtsTable) (key val : Term) : EtsTable :=
  let rec go (i : Nat) (acc : Array (Term × Term)) : Array (Term × Term) :=
    if h : i < t.entries.size then
      let (k, v) := t.entries[i]'h
      if k == key && v == val then
        acc ++ t.entries.extract (i + 1) t.entries.size
      else
        go (i + 1) (acc.push (k, v))
    else
      acc
  { t with entries := go 0 #[] }

/-- Mark table dead after owner exit without heir. -/
def killTable (t : EtsTable) : EtsTable :=
  { t with alive := false, entries := #[], name := none, heir := none, owner := none }

/-- Pattern variable index for `:"$1"` … `:"$9"`; `none` if not a `$N` atom. -/
def patternVar? (s : String) : Option Nat :=
  match s with
  | "$1" => some 0 | "$2" => some 1 | "$3" => some 2
  | "$4" => some 3 | "$5" => some 4 | "$6" => some 5
  | "$7" => some 6 | "$8" => some 7 | "$9" => some 8
  | _ => none

/-- Empty binding vector for `$1`…`$9`. -/
def emptyBinds : Array (Option Term) := Array.replicate 9 none

/-- Bind or check `$N`; fail on conflicting rebind. -/
def bindVar (binds : Array (Option Term)) (idx : Nat) (v : Term) :
    Option (Array (Option Term)) :=
  if h : idx < binds.size then
    match binds[idx] with
    | none => some (binds.set idx (some v) h)
    | some w => if w == v then some binds else none
  else
    none

/-- Recursive ETS pattern match. Atoms `:_` and `:"$N"` are wildcards / binds. -/
partial def matchPattern (pat obj : Term) (binds : Array (Option Term)) :
    Option (Array (Option Term)) :=
  match pat with
  | .atom "_" => some binds
  | .atom s =>
    match patternVar? s with
    | some idx => bindVar binds idx obj
    | none => if pat == obj then some binds else none
  | .tuple ps =>
    match obj with
    | .tuple os =>
      if ps.size != os.size then none
      else matchArray ps os 0 binds
    | _ => none
  | .list ps =>
    match obj with
    | .list os =>
      if ps.size != os.size then none
      else matchArray ps os 0 binds
    | _ => none
  | .map pe =>
    match obj with
    | .map oe =>
      if pe.size != oe.size then none
      else matchEntries pe oe 0 binds
    | _ => none
  | _ => if pat == obj then some binds else none
where
  matchArray (ps os : Array Term) (i : Nat) (binds : Array (Option Term)) :
      Option (Array (Option Term)) :=
    if h : i < ps.size then
      match matchPattern (ps[i]'h) os[i]! binds with
      | none => none
      | some binds => matchArray ps os (i + 1) binds
    else
      some binds
  matchEntries (pe oe : Array (Term × Term)) (i : Nat) (binds : Array (Option Term)) :
      Option (Array (Option Term)) :=
    if h : i < pe.size then
      let (pk, pv) := pe[i]'h
      let (ok, ov) := oe[i]!
      if !(pk == ok) then none
      else
        match matchPattern pv ov binds with
        | none => none
        | some binds => matchEntries pe oe (i + 1) binds
    else
      some binds

/-- Collect bound `$1`…`$9` values in order (skip unbound). -/
def boundList (binds : Array (Option Term)) : Array Term :=
  binds.filterMap id

/-- Resolve guard operand: literal or bound `$N`. -/
def resolveOperand (t : Term) (binds : Array (Option Term)) : Option Term :=
  match t with
  | .atom s =>
    match patternVar? s with
    | some idx =>
      if h : idx < binds.size then binds[idx] else none
    | none => some t
  | _ => some t

/-- Compare two terms using ETS guard operators. -/
def compareGuard (op : String) (a b : Term) : Option Bool :=
  if op == "==" then some (a == b)
  else if op == "=/=" then some (!(a == b))
  else if op == "<" then some (Term.lt a b)
  else if op == ">" then some (Term.lt b a)
  else if op == "=<" then some (Term.lt a b || a == b)
  else if op == ">=" then some (Term.lt b a || a == b)
  else none

def typeGuard (tag : String) (t : Term) : Option Bool :=
  match tag with
  | "is_atom" =>
    some (match t with | .atom _ => true | _ => false)
  | "is_integer" =>
    some (match t with | .int _ => true | _ => false)
  | "is_list" =>
    some (match t with | .list _ => true | _ => false)
  | "is_tuple" =>
    some (match t with | .tuple _ => true | _ => false)
  | "is_nil" =>
    some (match t with | .nil => true | _ => false)
  | "is_pid" =>
    some (match t with | .pid _ => true | _ => false)
  | _ => none

/-- Evaluate one teaching match-spec guard. `none` = unsupported / unbound. -/
partial def evalGuard (g : Term) (binds : Array (Option Term)) : Option Bool :=
  match g with
  | .tuple #[.atom op, a, b] =>
    if op == "andalso" then
      match evalGuard a binds with
      | some false => some false
      | some true => evalGuard b binds
      | none => none
    else if op == "orelse" then
      match evalGuard a binds with
      | some true => some true
      | some false => evalGuard b binds
      | none => none
    else
      match resolveOperand a binds, resolveOperand b binds with
      | some va, some vb => compareGuard op va vb
      | _, _ => none
  | .tuple #[.atom "not", a] =>
    match evalGuard a binds with
    | some b => some (!b)
    | none => none
  | .tuple #[.atom tag, a] =>
    match resolveOperand a binds with
    | some va => typeGuard tag va
    | none => none
  | _ => none

/-- All guards true; `none` if any guard is unsupported. -/
def evalGuards (guards : Array Term) (binds : Array (Option Term)) : Option Bool :=
  let rec go (i : Nat) : Option Bool :=
    if h : i < guards.size then
      match evalGuard (guards[i]'h) binds with
      | none => none
      | some false => some false
      | some true => go (i + 1)
    else
      some true
  go 0

/-- Build a select/match result construct from bindings + whole object. -/
partial def buildResult (body obj : Term) (binds : Array (Option Term)) : Option Term :=
  match body with
  | .atom "$_" => some obj
  | .atom "$$" => some (.list (boundList binds))
  | .atom s =>
    match patternVar? s with
    | some idx =>
      if h : idx < binds.size then binds[idx] else none
    | none => some body
  | .tuple elems =>
    match buildArray elems 0 #[] with
    | none => none
    | some vs => some (.tuple vs)
  | .list elems =>
    match buildArray elems 0 #[] with
    | none => none
    | some vs => some (.list vs)
  | _ => some body
where
  buildArray (elems : Array Term) (i : Nat) (acc : Array Term) : Option (Array Term) :=
    if h : i < elems.size then
      match buildResult (elems[i]'h) obj binds with
      | none => none
      | some v => buildArray elems (i + 1) (acc.push v)
    else
      some acc

/-- Clause: head, guards list, body construct. -/
structure Clause where
  head : Term
  guards : Array Term
  body : Term
  deriving Repr

/-- Parse one match-spec clause `{Head, Guards, [Body]}`. -/
def parseClause (clause : Term) : Option Clause :=
  match clause with
  | .tuple #[head, guards, bodyList] =>
    match guards, bodyList with
    | .list gs, .list #[body] => some { head, guards := gs, body }
    | _, _ => none
  | _ => none

/-- Parse match-spec list; `none` = malformed. -/
def parseSpec (spec : Term) : Option (Array Clause) :=
  match spec with
  | .list clauses =>
    let rec go (i : Nat) (acc : Array Clause) : Option (Array Clause) :=
      if h : i < clauses.size then
        match parseClause (clauses[i]'h) with
        | none => none
        | some c => go (i + 1) (acc.push c)
      else
        some acc
    go 0 #[]
  | _ => none

/-- First matching clause for one object → result, or `.error` if a guard is bad. -/
inductive SelectOne where
  | miss
  | hit (t : Term)
  | badGuard
  deriving Repr

def selectObject (clauses : Array Clause) (obj : Term) : SelectOne :=
  let rec go (i : Nat) : SelectOne :=
    if h : i < clauses.size then
      let c := clauses[i]'h
      match matchPattern c.head obj emptyBinds with
      | none => go (i + 1)
      | some binds =>
        match evalGuards c.guards binds with
        | none => .badGuard
        | some false => go (i + 1)
        | some true =>
          match buildResult c.body obj binds with
          | none => go (i + 1)
          | some t => .hit t
    else
      .miss
  go 0

/-- All objects matching `pattern` (as whole `{key,val}`). -/
def matchObject (t : EtsTable) (pattern : Term) : Array Term :=
  t.entries.filterMap fun (k, v) =>
    let obj := objectOf k v
    match matchPattern pattern obj emptyBinds with
    | some _ => some obj
    | none => none

/-- `ets:select` teaching subset; `none` = bad guard in a matching clause path. -/
def select (t : EtsTable) (clauses : Array Clause) : Option (Array Term) :=
  let rec go (i : Nat) (acc : Array Term) : Option (Array Term) :=
    if h : i < t.entries.size then
      let (k, v) := t.entries[i]'h
      match selectObject clauses (objectOf k v) with
      | .miss => go (i + 1) acc
      | .hit r => go (i + 1) (acc.push r)
      | .badGuard => none
    else
      some acc
  go 0 #[]

end Ets

end Autumn
