import Autumn.State
import Autumn.Process
import Autumn.Step
import Autumn.Examples

namespace Autumn
namespace GCDemo

/-- Process with an explicit total / nursery capacity (small values force GC). -/
def tinyProcessWith (capacity youngCapacity : Nat) : Process where
  pid := 0
  stack := #[{
    function := addMainModule.functions[1]!
    regs := State.mkRegs 3 #[]
    ip := 0
    retDest := 0
  }]
  mailbox := #[]
  status := .runnable
  result := none
  heap := Heap.empty capacity youngCapacity
  handlers := #[]

/-- Tiny-heap process used to force collections via `allocNode`. -/
def tinyProcess : Process := tinyProcessWith 2 2

/-- Allocate many small tuples (nothing retained); returns `(minorCount, gcCount)`. -/
def allocUntilGc (n : Nat) : Nat × Nat :=
  Id.run do
    let mut p := tinyProcess
    for i in [0:n] do
      let (p', _) := Process.allocNode p (.tuple #[.int i])
      p := p'
    pure (p.heap.minorCount, p.heap.gcCount)

/-- With a tiny nursery (young=2) and plenty of total room, only minor GCs fire:
`minorCount` increases while `gcCount` (major) stays 0. -/
def allocUntilMinor (n : Nat) : Nat × Nat :=
  Id.run do
    let mut p := tinyProcessWith 64 2
    for i in [0:n] do
      let (p', _) := Process.allocNode p (.tuple #[.int i])
      p := p'
    pure (p.heap.minorCount, p.heap.gcCount)

/-- Minor GC runs under allocation pressure on a tiny nursery. -/
def forcedMinor : Bool :=
  (allocUntilMinor 16).1 > 0 && (allocUntilMinor 16).2 == 0

#eval allocUntilGc 16
#eval allocUntilMinor 16
#eval forcedMinor
#guard forcedMinor

/-- Retain every allocated tuple as a mailbox root: survivors are promoted to old
until old can no longer hold a nursery, which triggers a major GC. Returns
`(minorCount, gcCount, retained, all retained roots still materialize correctly)`. -/
def retainUntilMajor (n : Nat) : Nat × Nat × Nat × Bool :=
  Id.run do
    let mut p := tinyProcessWith 6 2
    for i in [0:n] do
      let (p1, r) := Process.allocNode p (.tuple #[.int i])
      p := { p1 with mailbox := p1.mailbox.push (.ref r) }
    let mut ok := true
    for i in [0:n] do
      if Heap.toTerm' p.heap p.mailbox[i]! != .tuple #[.int i] then ok := false
    pure (p.heap.minorCount, p.heap.gcCount, p.mailbox.size, ok)

/-- Both generations get exercised: minors promote retained roots into old, and the
old generation filling up forces at least one major. -/
def forcedMajor : Bool :=
  let (minors, majors, size, ok) := retainUntilMajor 24
  minors > 0 && majors > 0 && size == 24 && ok

#eval retainUntilMajor 24
#eval forcedMajor
#guard forcedMajor

/-- Nested term with shared depth; needs several allocations on a capacity-2 heap. -/
def nestedTerm : Term :=
  .tuple #[
    .int 1,
    .list #[.int 2, .tuple #[.atom "a", .int 3], .nil],
    .tuple #[.list #[.int 4], .tuple #[.int 5, .bool true]]]

/-- Nested `allocTerm` under a tiny heap: GC fires mid-build, the term must still
materialize identically via fueled `toTerm'` (children parked on the mailbox). -/
def nestedAllocRoundtrip : Nat × Nat × Bool × Bool :=
  let (p, v) := Process.allocTerm tinyProcess nestedTerm
  (p.heap.minorCount, p.heap.gcCount, p.mailbox.isEmpty, Heap.toTerm' p.heap v == nestedTerm)

/-- Same, but a tiny nursery with roomy total heap (minor-only collections). -/
def nestedAllocRoundtripMinor : Nat × Nat × Bool × Bool :=
  let (p, v) := Process.allocTerm (tinyProcessWith 64 2) nestedTerm
  (p.heap.minorCount, p.heap.gcCount, p.mailbox.isEmpty, Heap.toTerm' p.heap v == nestedTerm)

/-- Alloc nested term, then force one more explicit GC with the value rooted in the
mailbox; fueled materialization of the evacuated root must agree with the original. -/
def nestedGcPreservesToTerm : Bool :=
  let (p, v) := Process.allocTerm tinyProcess nestedTerm
  let before := Heap.toTerm' p.heap v
  let p := { p with mailbox := #[v] }
  let p := Process.gc p
  Heap.toTerm' p.heap p.mailbox[0]! == before && before == nestedTerm

/-- Explicit minor GC with the nested value rooted: promoted into old, `toTerm'` agrees. -/
def nestedMinorPreservesToTerm : Bool :=
  let (p, v) := Process.allocTerm (tinyProcessWith 64 2) nestedTerm
  let before := Heap.toTerm' p.heap v
  let p := { p with mailbox := #[v] }
  let mc := p.heap.minorCount
  let p := Process.minorGc p
  p.heap.minorCount == mc + 1 && p.heap.oldSize == p.heap.nodes.size &&
    Heap.toTerm' p.heap p.mailbox[0]! == before && before == nestedTerm

/-- Explicit major GC with the nested value rooted. -/
def nestedMajorPreservesToTerm : Bool :=
  let (p, v) := Process.allocTerm (tinyProcessWith 64 2) nestedTerm
  let before := Heap.toTerm' p.heap v
  let p := { p with mailbox := #[v] }
  let gc0 := p.heap.gcCount
  let p := Process.majorGc p
  p.heap.gcCount == gc0 + 1 &&
    Heap.toTerm' p.heap p.mailbox[0]! == before && before == nestedTerm

/-- Map literal rooted across a major GC: fueled materialization agrees. -/
def mapMajorPreservesToTerm : Bool :=
  let t : Term := .map #[(.atom "a", .int 3), (.atom "b", .list #[.int 1, .int 2])]
  let (p, v) := Process.allocTerm (tinyProcessWith 64 2) t
  let before := Heap.toTerm' p.heap v
  let p := { p with mailbox := #[v] }
  let p := Process.majorGc p
  Heap.toTerm' p.heap p.mailbox[0]! == before && before == t

#eval nestedAllocRoundtrip
#eval nestedAllocRoundtripMinor
#eval nestedGcPreservesToTerm
#eval nestedMinorPreservesToTerm
#eval nestedMajorPreservesToTerm
#eval mapMajorPreservesToTerm
#guard nestedGcPreservesToTerm
#guard nestedMinorPreservesToTerm
#guard nestedMajorPreservesToTerm
#guard mapMajorPreservesToTerm

/-- Same program as `add_main` but with a tiny heap (exercises GC during run). -/
def runAddMainTinyHeap : Except StepError Term :=
  Step.runModule addMainModule (fuel := 100) (heapCapacity := 2)

#eval runAddMainTinyHeap

end GCDemo
end Autumn
