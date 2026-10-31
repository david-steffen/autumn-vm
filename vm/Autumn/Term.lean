namespace Autumn

/-- Runtime terms (IR v1–v2). -/
inductive Term where
  | nil
  | bool (b : Bool)
  | int (n : Int)
  | atom (s : String)
  | tuple (elems : Array Term)
  | list (elems : Array Term)
  | pid (id : Nat)
  deriving Repr, BEq, Inhabited

namespace Term

def toString : Term → String
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
  | .pid id => s!"#PID<{id}>"

instance : ToString Term where
  toString := Term.toString

mutual
  partial def beq : Term → Term → Bool
    | .nil, .nil => true
    | .bool a, .bool b => a == b
    | .int a, .int b => a == b
    | .atom a, .atom b => a == b
    | .tuple a, .tuple b => a.size == b.size && beqArray a b 0
    | .list a, .list b => a.size == b.size && beqArray a b 0
    | .pid a, .pid b => a == b
    | _, _ => false

  partial def beqArray (a b : Array Term) (i : Nat) : Bool :=
    if h : i < a.size then
      beq a[i] b[i]! && beqArray a b (i + 1)
    else
      true
end

end Term

end Autumn
