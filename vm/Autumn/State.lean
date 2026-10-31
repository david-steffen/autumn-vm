import Autumn.StateTypes
import Autumn.Process

namespace Autumn

namespace State

def reductionBudget : Nat := 8

/-- Default heap capacity for new processes (overridable in tests). -/
def defaultHeapCapacity : Nat := Heap.defaultCapacity

def getReg (f : Frame) (r : Reg) : Except StepError Value :=
  if h : r < f.regs.size then
    pure f.regs[r]
  else
    throw (.badRegister r f.function.locals)

def setReg (f : Frame) (r : Reg) (v : Value) : Except StepError Frame :=
  if _h : r < f.regs.size then
    pure { f with regs := f.regs.setIfInBounds r v }
  else
    throw (.badRegister r f.function.locals)

def mkRegs (locals : Nat) (args : Array Value) : Array Value :=
  Array.ofFn (n := locals) fun i =>
    if h : i.val < args.size then args[i.val] else Value.nil

def currentProcess? (s : State) : Option Process :=
  if h : s.current < s.processes.size then
    some s.processes[s.current]
  else
    none

def setCurrentProcess (s : State) (p : Process) : State :=
  if h : s.current < s.processes.size then
    { s with processes := s.processes.set s.current p h }
  else
    s

def findProcessIdx (s : State) (pid : Nat) : Option Nat :=
  s.processes.findIdx? (fun p => p.pid == pid)

/-- Drop `pid` from a links array. -/
def unlinkPid (links : Array Nat) (pid : Nat) : Array Nat :=
  links.filter (fun id => id != pid)

/-- True if `pid` is already in `links`. -/
def hasLink (links : Array Nat) (pid : Nat) : Bool :=
  links.any (fun id => id == pid)

/-- Bidirectional link between the current process and `otherPid`. -/
def linkWith (s : State) (otherPid : Nat) : Except StepError State :=
  match s.findProcessIdx otherPid with
  | none => .error (.badPid otherPid)
  | some idx =>
    if ¬(s.current < s.processes.size) then
      .error .noRunnable
    else
      let cur0 := s.processes[s.current]!
      if otherPid == cur0.pid then
        .ok s
      else
        let other0 := s.processes[idx]!
        if other0.status == .exited then
          .error (.typeError "link to exited process")
        else
          let curLinks :=
            if hasLink cur0.links otherPid then cur0.links else cur0.links.push otherPid
          let otherLinks :=
            if hasLink other0.links cur0.pid then other0.links else other0.links.push cur0.pid
          let cur := { cur0 with links := curLinks }
          let other := { other0 with links := otherLinks }
          let s := s.setCurrentProcess cur
          .ok { s with processes := s.processes.setIfInBounds idx other }

def setCurrentFrame (p : Process) (f : Frame) : Process :=
  if h : 0 < p.stack.size then
    { p with stack := p.stack.set (p.stack.size - 1) f (Nat.sub_one_lt_of_lt h) }
  else
    p

def initial (m : Module) (heapCapacity : Nat := defaultHeapCapacity) :
    Except StepError State := do
  let some f := m.findFunction m.entry
    | throw (.unknownFunction m.entry)
  if f.arity != 0 then
    throw (.badArity m.entry 0 f.arity)
  let frame : Frame := {
    function := f
    regs := mkRegs f.locals #[]
    ip := 0
    retDest := 0
  }
  let proc : Process := {
    pid := 0
    stack := #[frame]
    mailbox := #[]
    status := .runnable
    result := none
    heap := Heap.empty heapCapacity
    handlers := #[]
  }
  pure {
    module := m
    processes := #[proc]
    current := 0
    reductions := reductionBudget
    entryPid := 0
    result := none
    nextPid := 1
    clock := 0
  }

def clearWait (p : Process) : Process :=
  { p with waitDeadline := none }

/-- Wake a waiting process after `send`. Leaves IP on `wait`/`recv` so the
instruction re-runs (`wait` jumps to `retry` when the mailbox is non-empty). -/
def wakeOnMessage (p : Process) : Process :=
  match p.status with
  | .waiting => { clearWait p with status := .runnable }
  | _ => clearWait p

/-- Deliver one `{:EXIT, fromPid, reason}` notification to `peerPid`, if present and alive. -/
def notifyExitPeer (s : State) (fromPid : Nat) (heap : Heap) (reason : Value)
    (peerPid : Nat) : State :=
  match s.findProcessIdx peerPid with
  | none => s
  | some idx =>
    if hpeer : idx < s.processes.size then
      let peer0 := s.processes[idx]'hpeer
      if peer0.status == .exited then
        s
      else
        let peer0 := { peer0 with links := unlinkPid peer0.links fromPid }
        let (peer0, reason') := peer0.copyFrom heap reason
        let (peer0, msg) :=
          Process.allocCompound peer0 Node.tuple
            #[.atom "EXIT", .pid fromPid, reason']
        let peer1 := { peer0 with mailbox := peer0.mailbox.push msg }
        let peer :=
          if peer0.status == .waiting then wakeOnMessage peer1 else peer1
        { s with processes := s.processes.set idx peer hpeer }
    else
      s

/-- Fold `notifyExitPeer` over a peer-pid list (proof-friendly form of the old `for` loop). -/
def propagateExit.go (s : State) (fromPid : Nat) (heap : Heap) (reason : Value) :
    List Nat → State
  | [] => s
  | peerPid :: rest =>
    propagateExit.go (notifyExitPeer s fromPid heap reason peerPid) fromPid heap reason rest

/--
Notify linked peers that the process at `exitedIdx` has exited with `reason`.
The exited process must already be stored at `exitedIdx` with its exit `result`.
Peers receive `{:EXIT, from_pid, reason}` (copied into their heap) and are woken;
links are cleared both ways. Teaching subset: peers always trap EXIT (mailbox only).
-/
def propagateExit (s : State) (exitedIdx : Nat) (reason : Value) : State :=
  if hlt : exitedIdx < s.processes.size then
    let exited0 := s.processes[exitedIdx]'hlt
    let fromPid := exited0.pid
    let linkPids := exited0.links
    let heap := exited0.heap
    let exited := { exited0 with links := #[] }
    let s := { s with processes := s.processes.set exitedIdx exited hlt }
    propagateExit.go s fromPid heap reason linkPids.toList
  else
    s

/-- Wake a waiting process after a timeout deadline. Leaves IP on `wait` and
keeps `waitDeadline` so `wait` jumps to its `after` label. -/
def wakeOnTimeout (p : Process) : Process :=
  match p.status with
  | .waiting => { p with status := .runnable }
  | _ => p

/-- Wake every waiting process whose deadline is ≤ `clock`. -/
def wakeExpired (procs : Array Process) (clock : Nat) : Array Process :=
  procs.map fun p =>
    match p.status, p.waitDeadline with
    | .waiting, some d =>
      if d ≤ clock then wakeOnTimeout p else p
    | _, _ => p

/-- Earliest finite wait deadline among waiting processes, if any. -/
def nextDeadline (procs : Array Process) : Option Nat :=
  Id.run do
    let mut best : Option Nat := none
    for p in procs do
      match p.status, p.waitDeadline with
      | .waiting, some d =>
        best :=
          match best with
          | none => some d
          | some b => some (min b d)
      | _, _ => pure ()
    pure best

/-- Look for a runnable process in the next `fuel` slots after `idx` (exclusive start). -/
def findRunnable (procs : Array Process) (idx : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if procs.size = 0 then none
    else
      let idx := (idx + 1) % procs.size
      let p := procs[idx]!
      if p.status == .runnable && p.result.isNone then some idx
      else findRunnable procs idx fuel

/-- Round-robin: find next runnable process starting after `fromIdx`.
Wakes timed-out waiters (advancing `clock` to the next deadline if needed). -/
def scheduleNext (s : State) (fromIdx : Nat) : Except StepError State :=
  if s.processes.size = 0 then
    .error .noRunnable
  else
    let procs := wakeExpired s.processes s.clock
    let s := { s with processes := procs }
    match findRunnable s.processes fromIdx s.processes.size with
    | some idx =>
      .ok { s with current := idx, reductions := reductionBudget }
    | none =>
      match nextDeadline s.processes with
      | some t =>
        let s := { s with clock := max s.clock t, processes := wakeExpired s.processes (max s.clock t) }
        match findRunnable s.processes fromIdx s.processes.size with
        | some idx =>
          .ok { s with current := idx, reductions := reductionBudget }
        | none =>
          match s.processes.toList.find? (fun p => p.pid == s.entryPid) with
          | some ep =>
            match ep.result with
            | some v =>
              .ok { s with result := some (Heap.toTerm ep.heap v), reductions := reductionBudget }
            | none => .error .noRunnable
          | none => .error .noRunnable
      | none =>
        match s.processes.toList.find? (fun p => p.pid == s.entryPid) with
        | some ep =>
          match ep.result with
          | some v =>
            .ok { s with result := some (Heap.toTerm ep.heap v), reductions := reductionBudget }
          | none => .error .noRunnable
        | none => .error .noRunnable

end State

end Autumn
