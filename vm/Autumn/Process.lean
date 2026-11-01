import Autumn.State.Types
import Autumn.Heap

namespace Autumn

namespace Process

/-- Flatten GC roots: all frame registers, mailbox, optional result. -/
def collectRoots (p : Process) : Array Value :=
  let fromStack := p.stack.foldl (fun acc f => acc ++ f.regs) (#[] : Array Value)
  let withMb := fromStack ++ p.mailbox
  match p.result with
  | some v => withMb.push v
  | none => withMb

/-- Evacuator for one value: forward table, to-space, value ↦ updated triple. -/
abbrev Evac := Heap.Fwd → Array Node → Value → Heap.Fwd × Array Node × Value

/-- Evacuate one value array through a shared forward-table / to-space. -/
def evacuateVals.go (ev : Evac) (vals : Array Value)
    (i : Nat) (fwd : Heap.Fwd) (neu : Array Node) (acc : Array Value) :
    Heap.Fwd × Array Node × Array Value :=
  if hlt : i < vals.size then
    let (fwd, neu, v') := ev fwd neu (vals[i]'hlt)
    evacuateVals.go ev vals (i + 1) fwd neu (acc.push v')
  else
    (fwd, neu, acc)
termination_by vals.size - i

def evacuateVals (ev : Evac) (fwd : Heap.Fwd) (neu : Array Node)
    (vals : Array Value) : Heap.Fwd × Array Node × Array Value :=
  evacuateVals.go ev vals 0 fwd neu #[]

def evacuateFrame (ev : Evac) (fwd : Heap.Fwd) (neu : Array Node)
    (frame : Frame) : Heap.Fwd × Array Node × Frame :=
  let (fwd, neu, regs) := evacuateVals ev fwd neu frame.regs
  (fwd, neu, { frame with regs })

def evacuateStack.go (ev : Evac) (stack : Array Frame)
    (i : Nat) (fwd : Heap.Fwd) (neu : Array Node) (acc : Array Frame) :
    Heap.Fwd × Array Node × Array Frame :=
  if hlt : i < stack.size then
    let (fwd, neu, f') := evacuateFrame ev fwd neu (stack[i]'hlt)
    evacuateStack.go ev stack (i + 1) fwd neu (acc.push f')
  else
    (fwd, neu, acc)
termination_by stack.size - i

/-- Rewrite every root of `p` through `ev` (stack regs, mailbox, result), then
sanitize. Shared by minor and major GC; they differ only in `ev` / initial to-space.
Returns `(to-space, stack, mailbox, result)`. -/
def collectWith (ev : Evac) (fwd0 : Heap.Fwd) (neu0 : Array Node) (p : Process) :
    Array Node × Array Frame × Array Value × Option Value :=
  let r1 := evacuateStack.go ev p.stack 0 fwd0 neu0 #[]
  let r2 := evacuateVals ev r1.1 r1.2.1 p.mailbox
  let r3 : Array Node × Option Value :=
    match p.result with
    | none => (r2.2.1, none)
    | some v =>
      let r := ev r2.1 r2.2.1 v
      (r.2.1, some r.2.2)
  let neu := Heap.sanitizeNodes r3.1
  let sanitizeV := Heap.sanitizeValue neu.size
  (neu,
   r1.2.2.map (fun f => { f with regs := f.regs.map sanitizeV }),
   r2.2.2.map sanitizeV,
   r3.2.map sanitizeV)

/-- Install a collected to-space: everything in `neu` is old, young is empty.
Total capacity never shrinks and always covers `neu`; `want c.1.size` lets a
collection ask for headroom (major GC does, minor GC does not). -/
def commitCollect (p : Process)
    (c : Array Node × Array Frame × Array Value × Option Value)
    (gcCount minorCount : Nat) (want : Nat → Nat) : Process :=
  let cap := max p.heap.capacity (max (want c.1.size) (max c.1.size 1))
  { p with
    heap :=
      { nodes := c.1
        oldSize := c.1.size
        youngCapacity := p.heap.youngCapacity
        capacity := cap
        gcCount
        minorCount }
    stack := c.2.1
    mailbox := c.2.2.1
    result := c.2.2.2 }

/-- Minor GC: evacuate young objects reachable from roots; promote into old.
Old refs are leaves (old prefix is kept verbatim at the front of the to-space). -/
def minorGc (p : Process) : Process :=
  let h := p.heap
  let fuel := Heap.evacuateFuel h.nodes.size
  commitCollect p
    (collectWith (Heap.evacuateYoungValue fuel h)
      (Array.replicate h.nodes.size none) (h.nodes.extract 0 h.oldSize) p)
    h.gcCount (h.minorCount + 1) (fun _ => 0)

/-- Major GC: full-heap Cheney; result is entirely old generation. -/
def majorGc (p : Process) : Process :=
  let h := p.heap
  let fuel := Heap.evacuateFuel h.nodes.size
  commitCollect p
    (collectWith (Heap.evacuateValue fuel h)
      (Array.replicate h.nodes.size none) #[] p)
    (h.gcCount + 1) h.minorCount (fun n => max (n * 2) (n + h.youngCapacity))

/-- Alloc-failure GC: minor first (promote survivors); if old can no longer hold a
full nursery (`nodes.size + youngCapacity > capacity`, or young still full), major. -/
def gc (p : Process) : Process :=
  let p := minorGc p
  if p.heap.youngSize >= p.heap.youngCapacity ||
      p.heap.nodes.size >= p.heap.capacity ||
      p.heap.nodes.size + p.heap.youngCapacity > p.heap.capacity then
    majorGc p
  else
    p

/-- Grow total capacity (and young room if needed) then force-alloc. -/
def growAlloc (p : Process) (n : Node) : Process × Ref :=
  let cap := max (p.heap.capacity * 2) (p.heap.nodes.size + 1)
  let ycap := max p.heap.youngCapacity (p.heap.youngSize + 1)
  let h := { p.heap with capacity := cap, youngCapacity := ycap }
  let (h, r) := h.allocForce n
  ({ p with heap := h }, r)

/-- Allocate a node; minor → major → grow if young/total is full.
Prefer `allocCompound` when the node embeds child refs that must survive GC. -/
def allocNode (p : Process) (n : Node) : Process × Ref :=
  match p.heap.alloc? n with
  | some (h, r) => ({ p with heap := h }, r)
  | none =>
    let p := gc p
    match p.heap.alloc? n with
    | some (h, r) => ({ p with heap := h }, r)
    | none => growAlloc p n

/-- Park `temps` as mailbox roots for the duration of `k`, then restore length. -/
def withTempRoots (p : Process) (temps : Array Value)
    (k : Process → Process × Value) : Process × Value :=
  let mb0 := p.mailbox.size
  let p := { p with mailbox := p.mailbox ++ temps }
  let (p, v) := k p
  let p := { p with mailbox := p.mailbox.extract 0 mb0 }
  (p, v)

/-- Install allocated heap and sanitize so `Heap.WF` holds even if fuel truncated.
Does not inflate capacity/youngCapacity (only covers `nodes.size`). -/
def installHeap (p : Process) (h0 : Heap) : Process :=
  let neu := Heap.sanitizeNodes h0.nodes
  let h : Heap :=
    { nodes := neu
      oldSize := min h0.oldSize neu.size
      youngCapacity := h0.youngCapacity
      capacity := max h0.capacity (max neu.size 1)
      gcCount := h0.gcCount
      minorCount := h0.minorCount }
  { p with heap := h }

/-- Allocate a compound node whose children are `vs`.
Children are parked on the mailbox so Cheney rewrites them; after GC the node is
**rebuilt from the live mailbox suffix** (never from stale pre-GC `vs`). -/
def allocCompound (p : Process) (mk : Array Value → Node) (vs : Array Value) :
    Process × Value :=
  let mb0 := p.mailbox.size
  let p := { p with mailbox := p.mailbox ++ vs }
  let vsLive := p.mailbox.extract mb0 p.mailbox.size
  let (p, v) :=
    match p.heap.alloc? (mk vsLive) with
    | some (h, r) =>
      let p := installHeap p h
      (p, Heap.sanitizeValue p.heap.nodes.size (.ref r))
    | none =>
      let p := gc p
      let vsLive := p.mailbox.extract mb0 p.mailbox.size
      match p.heap.alloc? (mk vsLive) with
      | some (h, r) =>
        let p := installHeap p h
        (p, Heap.sanitizeValue p.heap.nodes.size (.ref r))
      | none =>
        let (p, r) := growAlloc p (mk vsLive)
        let p := installHeap p p.heap
        (p, Heap.sanitizeValue p.heap.nodes.size (.ref r))
  ({ p with mailbox := p.mailbox.extract 0 mb0 }, v)

/-- Flatten map entries to `[k0,v0,k1,v1,…]` for mailbox rooting. -/
def flattenMapEntries (entries : Array (Value × Value)) : Array Value :=
  entries.foldl (fun acc (k, v) => acc.push k |>.push v) #[]

/-- Rebuild map pairs from a flat `[k,v,…]` mailbox suffix. -/
def pairsFromFlat (flat : Array Value) : Array (Value × Value) :=
  Id.run do
    let mut acc : Array (Value × Value) := #[]
    let mut i := 0
    while h : i + 1 < flat.size do
      acc := acc.push (flat[i]!, flat[i + 1]!)
      i := i + 2
    pure acc

/-- Allocate a map node; keys and values are mailbox-rooted like `allocCompound`. -/
def allocMap (p : Process) (entries : Array (Value × Value)) : Process × Value :=
  let flat := flattenMapEntries entries
  let mb0 := p.mailbox.size
  let p := { p with mailbox := p.mailbox ++ flat }
  let mkLive := fun () => Node.map (pairsFromFlat (p.mailbox.extract mb0 p.mailbox.size))
  let (p, v) :=
    match p.heap.alloc? (mkLive ()) with
    | some (h, r) =>
      let p := installHeap p h
      (p, Heap.sanitizeValue p.heap.nodes.size (.ref r))
    | none =>
      let p := gc p
      let node := Node.map (pairsFromFlat (p.mailbox.extract mb0 p.mailbox.size))
      match p.heap.alloc? node with
      | some (h, r) =>
        let p := installHeap p h
        (p, Heap.sanitizeValue p.heap.nodes.size (.ref r))
      | none =>
        let (p, r) := growAlloc p node
        let p := installHeap p p.heap
        (p, Heap.sanitizeValue p.heap.nodes.size (.ref r))
  ({ p with mailbox := p.mailbox.extract 0 mb0 }, v)

-- Allocate an IR term; compound nodes go through `allocCompound` (GC-safe).
mutual
  def allocTermFuel (fuel : Nat) (p : Process) (t : Term) : Process × Value :=
    match fuel with
    | 0 => (p, .nil)
    | fuel + 1 =>
      match t with
      | .nil => (p, .nil)
      | .bool b => (p, .bool b)
      | .int n => (p, .int n)
      | .atom s => (p, .atom s)
      | .pid id => (p, .pid id)
      | .reference id => (p, .reference id)
      | .float f => (p, .float f)
      | .string s => (p, .string s)
      | .bitstring b => (p, .bitstring b)
      | .tuple elems =>
        let (p, vs) := allocTermArrayFuel fuel p elems 0 #[]
        allocCompound p Node.tuple vs
      | .list elems =>
        let (p, vs) := allocTermArrayFuel fuel p elems 0 #[]
        allocCompound p Node.list vs
      | .map entries =>
        let entries := Term.sortMapEntries entries
        let (p, vs) := allocTermEntriesFuel fuel p entries 0 #[]
        allocMap p vs
      | .closure funName env =>
        let (p, vs) := allocTermArrayFuel fuel p env 0 #[]
        allocCompound p (fun e => Node.closure funName e) vs
  termination_by fuel

  def allocTermArrayFuel (fuel : Nat) (p : Process) (elems : Array Term) (i : Nat)
      (acc : Array Value) : Process × Array Value :=
    match fuel with
    | 0 => (p, acc)
    | fuel + 1 =>
      if hlt : i < elems.size then
        -- Park already-built siblings so a GC inside the next child cannot
        -- invalidate refs held only in `acc`.
        let mb0 := p.mailbox.size
        let p := { p with mailbox := p.mailbox ++ acc }
        let (p, v) := allocTermFuel fuel p (elems[i]'hlt)
        let acc' := p.mailbox.extract mb0 p.mailbox.size
        let p := { p with mailbox := p.mailbox.extract 0 mb0 }
        allocTermArrayFuel fuel p elems (i + 1) (acc'.push v)
      else
        (p, acc)
  termination_by fuel

  def allocTermEntriesFuel (fuel : Nat) (p : Process) (entries : Array (Term × Term))
      (i : Nat) (acc : Array (Value × Value)) : Process × Array (Value × Value) :=
    match fuel with
    | 0 => (p, acc)
    | fuel + 1 =>
      if hlt : i < entries.size then
        let (k, v) := entries[i]'hlt
        let flat := flattenMapEntries acc
        let mb0 := p.mailbox.size
        let p := { p with mailbox := p.mailbox ++ flat }
        let (p, k') := allocTermFuel fuel p k
        let (p, v') := allocTermFuel fuel p v
        let live := pairsFromFlat (p.mailbox.extract mb0 p.mailbox.size)
        let p := { p with mailbox := p.mailbox.extract 0 mb0 }
        allocTermEntriesFuel fuel p entries (i + 1) (live.push (k', v'))
      else
        (p, acc)
  termination_by fuel
end

def allocTerm (p : Process) (t : Term) : Process × Value :=
  allocTermFuel (Heap.termFuel t + 1) p t

def allocTermArray (p : Process) (elems : Array Term) (i : Nat)
    (acc : Array Value) : Process × Array Value :=
  allocTermArrayFuel (elems.foldl (fun n e => n + Heap.termFuel e) 1) p elems i acc
/-- Copy values from another heap into this process (may grow; no GC of src).
Sanitize so destination heap WF holds even if copy fuel truncates. -/
def copyFrom (p : Process) (src : Heap) (v : Value) : Process × Value :=
  let (h0, v0) := Heap.copyValue src p.heap v
  let neu := Heap.sanitizeNodes h0.nodes
  let h : Heap :=
    { nodes := neu
      oldSize := min h0.oldSize neu.size
      youngCapacity := h0.youngCapacity
      capacity := max h0.capacity (max neu.size 1)
      gcCount := h0.gcCount
      minorCount := h0.minorCount }
  let v' := Heap.sanitizeValue neu.size v0
  ({ p with heap := h }, v')

def copyArrayFrom.go (p : Process) (src : Heap) (vs : Array Value) (i : Nat)
    (acc : Array Value) : Process × Array Value :=
  if hlt : i < vs.size then
    let (p, v') := copyFrom p src (vs[i]'hlt)
    copyArrayFrom.go p src vs (i + 1) (acc.push v')
  else
    (p, acc)
termination_by vs.size - i

def copyArrayFrom (p : Process) (src : Heap) (vs : Array Value) : Process × Array Value :=
  copyArrayFrom.go p src vs 0 (Array.mkEmpty vs.size)

end Process

end Autumn
