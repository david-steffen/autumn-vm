import Autumn.Instr

namespace Autumn

/-- Index into a process heap's node table. -/
abbrev Ref := Nat

/-- Register / mailbox payload: immediates or a heap reference. -/
inductive Value where
  | nil
  | bool (b : Bool)
  | int (n : Int)
  | atom (s : String)
  | pid (id : Nat)
  | ref (r : Ref)
  deriving Repr, BEq, Inhabited

/-- Heap-resident compound terms. -/
inductive Node where
  | tuple (elems : Array Value)
  | list (elems : Array Value)
  deriving Repr, Inhabited

/--
Per-process generational heap. Layout of `nodes` is **old ++ young**:
refs `r < oldSize` are old; the rest are young. Allocation bump-fills young
until `youngCapacity` (or total `capacity`); minor GC promotes survivors to old.
-/
structure Heap where
  nodes : Array Node
  /-- Frontier: `nodes[0:oldSize)` is old generation. -/
  oldSize : Nat
  /-- Max young objects before minor GC. -/
  youngCapacity : Nat
  /-- Total capacity for `nodes` (old + young). -/
  capacity : Nat
  /-- Completed major GC cycles (for tests). -/
  gcCount : Nat
  /-- Completed minor GC cycles (for tests). -/
  minorCount : Nat
  deriving Repr, Inhabited

namespace Heap

def defaultCapacity : Nat := 64
def defaultYoungCapacity : Nat := 16

def empty (capacity : Nat := defaultCapacity)
    (youngCapacity : Nat := defaultYoungCapacity) : Heap :=
  { nodes := #[]
    oldSize := 0
    youngCapacity := min youngCapacity (max capacity 1)
    capacity := max capacity 1
    gcCount := 0
    minorCount := 0 }

def youngSize (h : Heap) : Nat := h.nodes.size - h.oldSize

def isOld (h : Heap) (r : Ref) : Bool := decide (r < h.oldSize)
def isYoung (h : Heap) (r : Ref) : Bool := decide (h.oldSize ≤ r && r < h.nodes.size)

def get? (h : Heap) (r : Ref) : Option Node :=
  if r < h.nodes.size then some h.nodes[r]! else none

def get! (h : Heap) (r : Ref) : Node :=
  h.nodes[r]!

/-- Bump-allocate into young. Returns `none` if young or total capacity is full. -/
def alloc? (h : Heap) (n : Node) : Option (Heap × Ref) :=
  if h.youngSize >= h.youngCapacity || h.nodes.size >= h.capacity then
    none
  else
    let r := h.nodes.size
    some ({ h with nodes := h.nodes.push n }, r)

/-- Unconditional bump (may exceed capacity — used after grow). -/
def allocForce (h : Heap) (n : Node) : Heap × Ref :=
  let r := h.nodes.size
  ({ h with nodes := h.nodes.push n }, r)

/-- Grow total capacity when `nodes` already fills it. -/
def ensureCapacity (h : Heap) : Heap :=
  if h.nodes.size >= h.capacity then
    { h with capacity := max (h.capacity * 2) (h.nodes.size + 1) }
  else h

/-- Grow young capacity when the nursery is already saturated. -/
def ensureYoung (h : Heap) : Heap :=
  if h.youngSize >= h.youngCapacity then
    { h with youngCapacity := max (h.youngCapacity * 2) (h.youngSize + 1) }
  else h

/-- Allocate, growing total capacity if needed (no GC). Used by inter-heap copy.
Also grows `youngCapacity` when young is saturated so copy can proceed. -/
def allocGrow (h : Heap) (n : Node) : Heap × Ref :=
  allocForce (ensureYoung (ensureCapacity h)) n

-- Materialize a Value to a Term tree (for printing / machine result).
mutual
  partial def toTerm (h : Heap) (v : Value) : Term :=
    match v with
    | .nil => .nil
    | .bool b => .bool b
    | .int n => .int n
    | .atom s => .atom s
    | .pid id => .pid id
    | .ref r =>
      match get? h r with
      | none => .atom "<dangling>"
      | some (.tuple elems) => .tuple (toTermArray h elems 0 #[])
      | some (.list elems) => .list (toTermArray h elems 0 #[])

  partial def toTermArray (h : Heap) (elems : Array Value) (i : Nat)
      (acc : Array Term) : Array Term :=
    if _hlt : i < elems.size then
      toTermArray h elems (i + 1) (acc.push (toTerm h elems[i]!))
    else
      acc
end

-- Structural equality of values under a heap.
mutual
  partial def beq (h : Heap) (a b : Value) : Bool :=
    match a, b with
    | .nil, .nil => true
    | .bool x, .bool y => x == y
    | .int x, .int y => x == y
    | .atom x, .atom y => x == y
    | .pid x, .pid y => x == y
    | .ref ra, .ref rb =>
      match get? h ra, get? h rb with
      | some (.tuple xa), some (.tuple xb) =>
        xa.size == xb.size && beqArray h xa xb 0
      | some (.list xa), some (.list xb) =>
        xa.size == xb.size && beqArray h xa xb 0
      | _, _ => false
    | _, _ => false

  partial def beqArray (h : Heap) (a b : Array Value) (i : Nat) : Bool :=
    if _hlt : i < a.size then
      beq h a[i]! b[i]! && beqArray h a b (i + 1)
    else
      true
end

-- Compare a runtime value to an IR literal term.
mutual
  partial def beqTerm (h : Heap) (v : Value) (t : Term) : Bool :=
    match v, t with
    | .nil, .nil => true
    | .bool a, .bool b => a == b
    | .int a, .int b => a == b
    | .atom a, .atom b => a == b
    | .pid a, .pid b => a == b
    | .ref r, .tuple te =>
      match get? h r with
      | some (.tuple ve) =>
        ve.size == te.size && beqTermArray h ve te 0
      | _ => false
    | .ref r, .list te =>
      match get? h r with
      | some (.list ve) =>
        ve.size == te.size && beqTermArray h ve te 0
      | _ => false
    | _, _ => false

  partial def beqTermArray (h : Heap) (a : Array Value) (b : Array Term) (i : Nat) : Bool :=
    if _hlt : i < a.size then
      beqTerm h a[i]! b[i]! && beqTermArray h a b (i + 1)
    else
      true
end

/-! ### Deep-copy (fuel-bounded; enough fuel = full copy for WF heaps) -/

/-- Upper bound on work for copying a value graph with at most `nNodes` nodes. -/
def copyFuel (nNodes : Nat) : Nat := nNodes * 64 + 64

mutual
  /-- Fuel exhaustion maps refs to `nil` so destination heaps stay well-formed. -/
  def copyValueFuel (fuel : Nat) (src dst : Heap) (v : Value) : Heap × Value :=
    match fuel with
    | 0 =>
      match v with
      | .ref _ => (dst, .nil)
      | _ => (dst, v)
    | fuel + 1 =>
      match v with
      | .nil => (dst, .nil)
      | .bool b => (dst, .bool b)
      | .int n => (dst, .int n)
      | .atom s => (dst, .atom s)
      | .pid id => (dst, .pid id)
      | .ref r =>
        match get? src r with
        | none => (dst, .nil)
        | some (.tuple elems) =>
          let (dst, elems') := copyArrayFuel fuel src dst elems 0 #[]
          let (dst, r') := allocGrow dst (.tuple elems')
          (dst, .ref r')
        | some (.list elems) =>
          let (dst, elems') := copyArrayFuel fuel src dst elems 0 #[]
          let (dst, r') := allocGrow dst (.list elems')
          (dst, .ref r')
  termination_by fuel

  def copyArrayFuel (fuel : Nat) (src dst : Heap) (elems : Array Value) (i : Nat)
      (acc : Array Value) : Heap × Array Value :=
    match fuel with
    | 0 => (dst, acc)
    | fuel + 1 =>
      if hlt : i < elems.size then
        let (dst, v) := copyValueFuel fuel src dst (elems[i]'hlt)
        copyArrayFuel fuel src dst elems (i + 1) (acc.push v)
      else
        (dst, acc)
  termination_by fuel
end

def copyValue (src dst : Heap) (v : Value) : Heap × Value :=
  copyValueFuel (copyFuel src.nodes.size) src dst v

def copyArray (src dst : Heap) (elems : Array Value) (i : Nat)
    (acc : Array Value) : Heap × Array Value :=
  copyArrayFuel (copyFuel src.nodes.size) src dst elems i acc

/-! ### Allocate IR Term (fuel on `sizeOf`) -/

mutual
  def allocTermFuel (fuel : Nat) (h : Heap) (t : Term) : Heap × Value :=
    match fuel with
    | 0 => (h, .nil)
    | fuel + 1 =>
      match t with
      | .nil => (h, .nil)
      | .bool b => (h, .bool b)
      | .int n => (h, .int n)
      | .atom s => (h, .atom s)
      | .pid id => (h, .pid id)
      | .tuple elems =>
        let (h, vs) := allocTermArrayFuel fuel h elems 0 #[]
        match alloc? h (.tuple vs) with
        | some (h, r) => (h, .ref r)
        | none =>
          let (h, r) := allocGrow h (.tuple vs)
          (h, .ref r)
      | .list elems =>
        let (h, vs) := allocTermArrayFuel fuel h elems 0 #[]
        match alloc? h (.list vs) with
        | some (h, r) => (h, .ref r)
        | none =>
          let (h, r) := allocGrow h (.list vs)
          (h, .ref r)
  termination_by fuel

  def allocTermArrayFuel (fuel : Nat) (h : Heap) (elems : Array Term) (i : Nat)
      (acc : Array Value) : Heap × Array Value :=
    match fuel with
    | 0 => (h, acc)
    | fuel + 1 =>
      if hlt : i < elems.size then
        let (h, v) := allocTermFuel fuel h (elems[i]'hlt)
        allocTermArrayFuel fuel h elems (i + 1) (acc.push v)
      else
        (h, acc)
  termination_by fuel
end

/-- Structural size for fuel (avoids `sizeOf` in compiled code). -/
def termFuel : Term → Nat
  | .nil | .bool _ | .int _ | .atom _ | .pid _ => 1
  | .tuple elems => elems.foldl (fun n e => n + termFuel e) 1
  | .list elems => elems.foldl (fun n e => n + termFuel e) 1

def allocTerm (h : Heap) (t : Term) : Heap × Value :=
  allocTermFuel (termFuel t + 1) h t

def allocTermArray (h : Heap) (elems : Array Term) (i : Nat)
    (acc : Array Value) : Heap × Array Value :=
  allocTermArrayFuel (elems.foldl (fun n e => n + termFuel e) 1) h elems i acc
/-! ### Cheney-style evacuation (fuel-bounded) -/

abbrev Fwd := Array (Option Ref)

def evacuateFuel (nNodes : Nat) : Nat := nNodes * 64 + 64

mutual
  /-- Fuel exhaustion drops refs to `nil` so the to-space stays well-formed. -/
  def evacuateValue (fuel : Nat) (old : Heap) (fwd : Fwd) (neu : Array Node)
      (v : Value) : Fwd × Array Node × Value :=
    match fuel with
    | 0 =>
      match v with
      | .ref _ => (fwd, neu, .nil)
      | _ => (fwd, neu, v)
    | fuel + 1 =>
      match v with
      | .nil => (fwd, neu, .nil)
      | .bool b => (fwd, neu, .bool b)
      | .int n => (fwd, neu, .int n)
      | .atom s => (fwd, neu, .atom s)
      | .pid id => (fwd, neu, .pid id)
      | .ref r =>
        if hbound : r < fwd.size then
          match fwd[r] with
          | some r' => (fwd, neu, .ref r')
          | none =>
            match get? old r with
            | none => (fwd, neu, .nil)
            | some node =>
              let (fwd, neu, node') := evacuateNode fuel old fwd neu node
              let r' := neu.size
              let neu := neu.push node'
              let fwd := fwd.setIfInBounds r (some r')
              (fwd, neu, .ref r')
        else
          (fwd, neu, .nil)
  termination_by fuel

  def evacuateNode (fuel : Nat) (old : Heap) (fwd : Fwd) (neu : Array Node)
      (node : Node) : Fwd × Array Node × Node :=
    match fuel with
    | 0 => (fwd, neu, .tuple #[])
    | fuel + 1 =>
      match node with
      | .tuple elems =>
        let (fwd, neu, elems') := evacuateArray fuel old fwd neu elems 0 #[]
        (fwd, neu, .tuple elems')
      | .list elems =>
        let (fwd, neu, elems') := evacuateArray fuel old fwd neu elems 0 #[]
        (fwd, neu, .list elems')
  termination_by fuel

  def evacuateArray (fuel : Nat) (old : Heap) (fwd : Fwd) (neu : Array Node)
      (elems : Array Value) (i : Nat) (acc : Array Value) :
      Fwd × Array Node × Array Value :=
    match fuel with
    | 0 => (fwd, neu, acc)
    | fuel + 1 =>
      if hlt : i < elems.size then
        let (fwd, neu, v) := evacuateValue fuel old fwd neu (elems[i]'hlt)
        evacuateArray fuel old fwd neu elems (i + 1) (acc.push v)
      else
        (fwd, neu, acc)
  termination_by fuel
end

/-- Replace out-of-range refs with `nil` (no-op on a well-evacuated to-space). -/
def sanitizeValue (bound : Nat) : Value → Value
  | .ref r => if r < bound then .ref r else .nil
  | v => v

def sanitizeNode (bound : Nat) : Node → Node
  | .tuple elems => .tuple (elems.map (sanitizeValue bound))
  | .list elems => .list (elems.map (sanitizeValue bound))

def sanitizeNodes (neu : Array Node) : Array Node :=
  neu.map (sanitizeNode neu.size)

def evacuateRoots.go (fuel : Nat) (h : Heap) (roots : Array Value)
    (i : Nat) (fwd : Fwd) (neu : Array Node) (acc : Array Value) :
    Fwd × Array Node × Array Value :=
  if hlt : i < roots.size then
    let (fwd, neu, v') := evacuateValue fuel h fwd neu (roots[i]'hlt)
    evacuateRoots.go fuel h roots (i + 1) fwd neu (acc.push v')
  else
    (fwd, neu, acc)
termination_by roots.size - i

/-- Evacuate a list of root values; return new heap + rewritten roots.
Each root is processed exactly once (`roots'.size = roots.size`).
A final sanitize ensures `Heap.WF` even if fuel was exhausted mid-graph.
Result is entirely old generation (major-style). -/
def evacuateRoots (h : Heap) (roots : Array Value) : Heap × Array Value :=
  let fuel := evacuateFuel h.nodes.size
  let fwd0 : Fwd := Array.replicate h.nodes.size none
  let (_fwd, neu, roots') := evacuateRoots.go fuel h roots 0 fwd0 #[] #[]
  let neu := sanitizeNodes neu
  let roots' := roots'.map (sanitizeValue neu.size)
  let cap := max h.capacity (max neu.size 1)
  ({ nodes := neu
     oldSize := neu.size
     youngCapacity := h.youngCapacity
     capacity := cap
     gcCount := h.gcCount + 1
     minorCount := h.minorCount }, roots')

/-! ### Minor (young-only) evacuation — promote survivors into old -/

mutual
  /-- Evacuate a value for minor GC: old refs are left unchanged; young refs are
  promoted into `neu` (which must already hold the old prefix). -/
  def evacuateYoungValue (fuel : Nat) (old : Heap) (fwd : Fwd) (neu : Array Node)
      (v : Value) : Fwd × Array Node × Value :=
    match fuel with
    | 0 =>
      match v with
      | .ref r =>
        if r < old.oldSize then (fwd, neu, .ref r) else (fwd, neu, .nil)
      | _ => (fwd, neu, v)
    | fuel + 1 =>
      match v with
      | .nil => (fwd, neu, .nil)
      | .bool b => (fwd, neu, .bool b)
      | .int n => (fwd, neu, .int n)
      | .atom s => (fwd, neu, .atom s)
      | .pid id => (fwd, neu, .pid id)
      | .ref r =>
        if r < old.oldSize then
          (fwd, neu, .ref r)
        else if hbound : r < fwd.size then
          match fwd[r] with
          | some r' => (fwd, neu, .ref r')
          | none =>
            match get? old r with
            | none => (fwd, neu, .nil)
            | some node =>
              let (fwd, neu, node') := evacuateYoungNode fuel old fwd neu node
              let r' := neu.size
              let neu := neu.push node'
              let fwd := fwd.setIfInBounds r (some r')
              (fwd, neu, .ref r')
        else
          (fwd, neu, .nil)
  termination_by fuel

  def evacuateYoungNode (fuel : Nat) (old : Heap) (fwd : Fwd) (neu : Array Node)
      (node : Node) : Fwd × Array Node × Node :=
    match fuel with
    | 0 => (fwd, neu, .tuple #[])
    | fuel + 1 =>
      match node with
      | .tuple elems =>
        let (fwd, neu, elems') := evacuateYoungArray fuel old fwd neu elems 0 #[]
        (fwd, neu, .tuple elems')
      | .list elems =>
        let (fwd, neu, elems') := evacuateYoungArray fuel old fwd neu elems 0 #[]
        (fwd, neu, .list elems')
  termination_by fuel

  def evacuateYoungArray (fuel : Nat) (old : Heap) (fwd : Fwd) (neu : Array Node)
      (elems : Array Value) (i : Nat) (acc : Array Value) :
      Fwd × Array Node × Array Value :=
    match fuel with
    | 0 => (fwd, neu, acc)
    | fuel + 1 =>
      if hlt : i < elems.size then
        let (fwd, neu, v) := evacuateYoungValue fuel old fwd neu (elems[i]'hlt)
        evacuateYoungArray fuel old fwd neu elems (i + 1) (acc.push v)
      else
        (fwd, neu, acc)
  termination_by fuel
end

end Heap

namespace Value

def tagOf (h : Heap) (v : Value) : Tag :=
  match v with
  | .nil => .nil
  | .bool _ => .bool
  | .int _ => .int
  | .atom _ => .atom
  | .pid _ => .pid
  | .ref r =>
    match Heap.get? h r with
    | some (.tuple _) => .tuple
    | some (.list _) => .list
    | none => .nil

end Value

end Autumn
