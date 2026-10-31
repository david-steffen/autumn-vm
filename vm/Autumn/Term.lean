namespace Autumn

/-- Runtime terms (IR v1–v11). Unique `reference` is distinct from heap pointers. -/
inductive Term where
  | nil
  | bool (b : Bool)
  | int (n : Int)
  | float (f : Float)
  | atom (s : String)
  | string (s : String)
  | tuple (elems : Array Term)
  | list (elems : Array Term)
  | map (entries : Array (Term × Term))
  | pid (id : Nat)
  | reference (id : Nat)
  | closure (funName : String) (env : Array Term)
  deriving Repr, BEq, Inhabited

namespace Term

partial def toString : Term → String
  | .nil => "nil"
  | .bool b => if b then "true" else "false"
  | .int n => s!"{n}"
  | .float f => s!"{f}"
  | .atom s => s!":{s}"
  | .string s => s!"\"{s}\""
  | .tuple elems =>
    let inner := (elems.map Term.toString).toList |> String.intercalate ", "
    s!"\{{inner}}"
  | .list elems =>
    let inner := (elems.map Term.toString).toList |> String.intercalate ", "
    s!"[{inner}]"
  | .map entries =>
    let inner :=
      (entries.map fun (k, v) => Term.toString k ++ " => " ++ Term.toString v).toList
        |> String.intercalate ", "
    "%{" ++ inner ++ "}"
  | .pid id => s!"#PID<{id}>"
  | .reference id => s!"#Ref<{id}>"
  | .closure funName env =>
    let inner := (env.map Term.toString).toList |> String.intercalate ", "
    s!"#Fun<{funName}/[{inner}]>"

instance : ToString Term where
  toString := Term.toString

/-- Tag ordinal: nil < bool < int < float < atom < string < pid < reference < tuple < list < map < closure. -/
def tagOrd : Term → Nat
  | .nil => 0
  | .bool _ => 1
  | .int _ => 2
  | .float _ => 3
  | .atom _ => 4
  | .string _ => 5
  | .pid _ => 6
  | .reference _ => 7
  | .tuple _ => 8
  | .list _ => 9
  | .map _ => 10
  | .closure _ _ => 11

mutual
  /-- Total order for stable map key sorting (tag order, then structure). -/
  partial def lt : Term → Term → Bool
    | a, b =>
      let oa := tagOrd a
      let ob := tagOrd b
      if oa != ob then decide (oa < ob)
      else
        match a, b with
        | .nil, .nil => false
        | .bool x, .bool y => decide (!x && y)
        | .int x, .int y => decide (x < y)
        | .float x, .float y => Float.lt x y
        | .atom x, .atom y => decide (x < y)
        | .string x, .string y => decide (x < y)
        | .pid x, .pid y => decide (x < y)
        | .reference x, .reference y => decide (x < y)
        | .tuple x, .tuple y => ltArray x y 0
        | .list x, .list y => ltArray x y 0
        | .map x, .map y => ltEntries x y 0
        | .closure fa ea, .closure fb eb =>
          if fa != fb then decide (fa < fb) else ltArray ea eb 0
        | _, _ => false

  partial def ltArray (a b : Array Term) (i : Nat) : Bool :=
    if i < a.size && i < b.size then
      if beq a[i]! b[i]! then ltArray a b (i + 1)
      else lt a[i]! b[i]!
    else
      decide (a.size < b.size)

  partial def ltEntries (a b : Array (Term × Term)) (i : Nat) : Bool :=
    if i < a.size && i < b.size then
      let (ka, va) := a[i]!
      let (kb, vb) := b[i]!
      if beq ka kb then
        if beq va vb then ltEntries a b (i + 1) else lt va vb
      else lt ka kb
    else
      decide (a.size < b.size)

  partial def beq : Term → Term → Bool
    | .nil, .nil => true
    | .bool a, .bool b => a == b
    | .int a, .int b => a == b
    | .float a, .float b => a == b
    | .atom a, .atom b => a == b
    | .string a, .string b => a == b
    | .tuple a, .tuple b => a.size == b.size && beqArray a b 0
    | .list a, .list b => a.size == b.size && beqArray a b 0
    | .map a, .map b => a.size == b.size && beqEntries a b 0
    | .pid a, .pid b => a == b
    | .reference a, .reference b => a == b
    | .closure fa ea, .closure fb eb => fa == fb && ea.size == eb.size && beqArray ea eb 0
    | _, _ => false

  partial def beqArray (a b : Array Term) (i : Nat) : Bool :=
    if h : i < a.size then
      beq a[i] b[i]! && beqArray a b (i + 1)
    else
      true

  partial def beqEntries (a b : Array (Term × Term)) (i : Nat) : Bool :=
    if h : i < a.size then
      let (ka, va) := a[i]
      let (kb, vb) := b[i]!
      beq ka kb && beq va vb && beqEntries a b (i + 1)
    else
      true
end

def sortMapEntries (entries : Array (Term × Term)) : Array (Term × Term) :=
  entries.qsort fun (k1, _) (k2, _) => lt k1 k2

end Term

end Autumn
