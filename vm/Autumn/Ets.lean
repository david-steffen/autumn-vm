import Autumn.Term
import Autumn.State.Types

namespace Autumn

namespace Ets

/-- Parse `:set` / `:bag` / `:duplicate_bag`. -/
def kindOfAtom (s : String) : Option EtsKind :=
  if s == "set" then some .set
  else if s == "bag" then some .bag
  else if s == "duplicate_bag" then some .duplicateBag
  else none

/-- Resolve tab id: non-neg int tid, or atom name. -/
def resolveTab (tables : Array EtsTable) (tab : Term) : Option Nat :=
  match tab with
  | .int n =>
    if n < 0 then none
    else
      let tid := n.toNat
      if tid < tables.size then some tid else none
  | .atom name =>
    (List.range tables.size).findSome? fun i =>
      match tables[i]!.name with
      | some n => if n == name then some i else none
      | none => none
  | _ => none

/-- True if some table already uses this atom name. -/
def nameTaken (tables : Array EtsTable) (name : String) : Bool :=
  tables.any fun t => t.name == some name

/-- Object term for an entry. -/
def objectOf (key val : Term) : Term :=
  .tuple #[key, val]

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

def lookupValues (t : EtsTable) (key : Term) : Array Term :=
  t.entries.filterMap fun (k, v) => if k == key then some v else none

def deleteKey (t : EtsTable) (key : Term) : EtsTable :=
  { t with entries := t.entries.filter (fun (k, _) => !(k == key)) }

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

/-- Parse one match-spec clause `{Head, [], [Body]}`. -/
def parseClause (clause : Term) : Option (Term × Term) :=
  match clause with
  | .tuple #[head, guards, bodyList] =>
    match guards, bodyList with
    | .list #[], .list #[body] => some (head, body)
    | .list #[], .list _ => none
    | .list _, _ => none
    | _, _ => none
  | _ => none

/-- Parse match-spec list; `none` = malformed. -/
def parseSpec (spec : Term) : Option (Array (Term × Term)) :=
  match spec with
  | .list clauses =>
    let rec go (i : Nat) (acc : Array (Term × Term)) : Option (Array (Term × Term)) :=
      if h : i < clauses.size then
        match parseClause (clauses[i]'h) with
        | none => none
        | some c => go (i + 1) (acc.push c)
      else
        some acc
    go 0 #[]
  | _ => none

/-- First matching clause for one object → result term. -/
def selectObject (clauses : Array (Term × Term)) (obj : Term) : Option Term :=
  let rec go (i : Nat) : Option Term :=
    if h : i < clauses.size then
      let (head, body) := clauses[i]'h
      match matchPattern head obj emptyBinds with
      | none => go (i + 1)
      | some binds => buildResult body obj binds
    else
      none
  go 0

/-- All objects matching `pattern` (as whole `{key,val}`). -/
def matchObject (t : EtsTable) (pattern : Term) : Array Term :=
  t.entries.filterMap fun (k, v) =>
    let obj := objectOf k v
    match matchPattern pattern obj emptyBinds with
    | some _ => some obj
    | none => none

/-- `ets:select` teaching subset over table entries. -/
def select (t : EtsTable) (clauses : Array (Term × Term)) : Array Term :=
  t.entries.filterMap fun (k, v) =>
    selectObject clauses (objectOf k v)

end Ets

end Autumn
