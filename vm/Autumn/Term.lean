namespace Autumn

/-- Runtime terms (IR v1–v5). -/
inductive Term where
  | nil
  | bool (b : Bool)
  | int (n : Int)
  | atom (s : String)
  | tuple (elems : Array Term)
  | list (elems : Array Term)
  | map (entries : Array (Term × Term))
  | pid (id : Nat)
  deriving Repr, BEq, Inhabited

namespace Term

partial def toString : Term → String
  | .nil => "nil"
  | .bool b => if b then "true" else "false"
  | .int n => s!"{n}"
  | .atom s => s!":{s}"
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

instance : ToString Term where
  toString := Term.toString

mutual
  /-- Total order for stable map key sorting (tag order, then structure). -/
  partial def lt : Term → Term → Bool
    | .nil, .nil => false
    | .nil, _ => true
    | .bool _, .nil => false
    | .bool a, .bool b => decide (!a && b)
    | .bool _, .int _ => true
    | .bool _, .atom _ => true
    | .bool _, .pid _ => true
    | .bool _, .tuple _ => true
    | .bool _, .list _ => true
    | .bool _, .map _ => true
    | .int _, .nil => false
    | .int _, .bool _ => false
    | .int a, .int b => decide (a < b)
    | .int _, .atom _ => true
    | .int _, .pid _ => true
    | .int _, .tuple _ => true
    | .int _, .list _ => true
    | .int _, .map _ => true
    | .atom _, .nil => false
    | .atom _, .bool _ => false
    | .atom _, .int _ => false
    | .atom a, .atom b => decide (a < b)
    | .atom _, .pid _ => true
    | .atom _, .tuple _ => true
    | .atom _, .list _ => true
    | .atom _, .map _ => true
    | .pid _, .nil => false
    | .pid _, .bool _ => false
    | .pid _, .int _ => false
    | .pid _, .atom _ => false
    | .pid a, .pid b => decide (a < b)
    | .pid _, .tuple _ => true
    | .pid _, .list _ => true
    | .pid _, .map _ => true
    | .tuple _, .nil => false
    | .tuple _, .bool _ => false
    | .tuple _, .int _ => false
    | .tuple _, .atom _ => false
    | .tuple _, .pid _ => false
    | .tuple a, .tuple b => ltArray a b 0
    | .tuple _, .list _ => true
    | .tuple _, .map _ => true
    | .list _, .nil => false
    | .list _, .bool _ => false
    | .list _, .int _ => false
    | .list _, .atom _ => false
    | .list _, .pid _ => false
    | .list _, .tuple _ => false
    | .list a, .list b => ltArray a b 0
    | .list _, .map _ => true
    | .map _, .nil => false
    | .map _, .bool _ => false
    | .map _, .int _ => false
    | .map _, .atom _ => false
    | .map _, .pid _ => false
    | .map _, .tuple _ => false
    | .map _, .list _ => false
    | .map a, .map b => ltEntries a b 0

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
    | .atom a, .atom b => a == b
    | .tuple a, .tuple b => a.size == b.size && beqArray a b 0
    | .list a, .list b => a.size == b.size && beqArray a b 0
    | .map a, .map b => a.size == b.size && beqEntries a b 0
    | .pid a, .pid b => a == b
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
