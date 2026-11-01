import Autumn.State.Types
import Autumn.Process
import Autumn.Ets

namespace Autumn

namespace State

/-- Preemption quantum: instructions per process before `scheduleNext`. -/
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
    nextRef := 0
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

/-- Drop entries whose second component equals `refId`. -/
def dropByRef (arr : Array (Nat × Nat)) (refId : Nat) : Array (Nat × Nat) :=
  arr.filter (fun (_, r) => r != refId)

/-- Drop inbound monitor `(fromPid, refId)`. -/
def dropMonitoredBy (arr : Array (Nat × Nat)) (fromPid refId : Nat) : Array (Nat × Nat) :=
  arr.filter (fun (p, r) => !(p == fromPid && r == refId))

/-- Deliver `{:ETS-TRANSFER, tid, fromPid, data}` to heir and wake if waiting. -/
def notifyEtsTransfer (s : State) (tid fromPid heirPid : Nat) (data : Term) : State :=
  match s.findProcessIdx heirPid with
  | none => s
  | some idx =>
    if hpeer : idx < s.processes.size then
      let peer0 := s.processes[idx]'hpeer
      if peer0.status == .exited then
        s
      else
        let (peer0, dataV) := Process.allocTerm peer0 data
        let (peer0, msg) :=
          Process.allocCompound peer0 Node.tuple
            #[.atom "ETS-TRANSFER", .int tid, .pid fromPid, dataV]
        let peer1 := { peer0 with mailbox := peer0.mailbox.push msg }
        let peer :=
          if peer0.status == .waiting then wakeOnMessage peer1 else peer1
        { s with processes := s.processes.set idx peer hpeer }
    else
      s

/-- True if `pid` is a non-exited process. -/
def processLive (s : State) (pid : Nat) : Bool :=
  match s.findProcessIdx pid with
  | none => false
  | some idx =>
    if h : idx < s.processes.size then
      (s.processes[idx]'h).status != .exited
    else
      false

/-- One table index: transfer to live heir or kill. -/
def etsOnOwnerExit.one (s : State) (fromPid i : Nat) : State :=
  if h : i < s.etsTables.size then
    let t := s.etsTables[i]'h
    if ht : t.alive && t.owner == some fromPid then
      match th : t.heir with
      | some (heirPid, data) =>
        if processLive s heirPid then
          let t := { t with owner := some heirPid, heir := none }
          let s := { s with etsTables := s.etsTables.set i t h }
          notifyEtsTransfer s i fromPid heirPid data
        else
          { s with etsTables := s.etsTables.set i (Ets.killTable t) h }
      | none =>
        { s with etsTables := s.etsTables.set i (Ets.killTable t) h }
    else
      s
  else
    s

/-- Fold owner-exit handling over table indices. -/
def etsOnOwnerExit.go (s : State) (fromPid : Nat) : List Nat → State
  | [] => s
  | i :: rest => etsOnOwnerExit.go (etsOnOwnerExit.one s fromPid i) fromPid rest

/-- After owner exit: transfer to live heir or kill the table. -/
def etsOnOwnerExit (s : State) (fromPid : Nat) : State :=
  etsOnOwnerExit.go s fromPid (List.range s.etsTables.size)

/-- Deliver one `{:EXIT, fromPid, reason}` to a **trapping** peer (mailbox only). -/
def notifyExitMailbox (s : State) (fromPid : Nat) (heap : Heap) (reason : Value)
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

/-- Alias kept for lemmas / call sites that mean mailbox EXIT delivery. -/
def notifyExitPeer (s : State) (fromPid : Nat) (heap : Heap) (reason : Value)
    (peerPid : Nat) : State :=
  notifyExitMailbox s fromPid heap reason peerPid

/-- Deliver one `{:DOWN, ref, :process, fromPid, reason}` to `fromPid` (monitorer). -/
def notifyDownPeer (s : State) (fromPid : Nat) (heap : Heap) (reason : Value)
    (monitorerPid refId : Nat) : State :=
  match s.findProcessIdx monitorerPid with
  | none => s
  | some idx =>
    if hpeer : idx < s.processes.size then
      let peer0 := s.processes[idx]'hpeer
      if peer0.status == .exited then
        s
      else
        let peer0 := { peer0 with monitors := dropByRef peer0.monitors refId }
        let (peer0, reason') := peer0.copyFrom heap reason
        let (peer0, msg) :=
          Process.allocCompound peer0 Node.tuple
            #[.atom "DOWN", .reference refId, .atom "process", .pid fromPid, reason']
        let peer1 := { peer0 with mailbox := peer0.mailbox.push msg }
        let peer :=
          if peer0.status == .waiting then wakeOnMessage peer1 else peer1
        { s with processes := s.processes.set idx peer hpeer }
    else
      s

/-- Remove an outbound monitor from a still-living target (exiting monitorer's cleanup). -/
def clearTargetMonitor (s : State) (fromPid targetPid refId : Nat) : State :=
  match s.findProcessIdx targetPid with
  | none => s
  | some idx =>
    if h : idx < s.processes.size then
      let t0 := s.processes[idx]'h
      let t := { t0 with monitoredBy := dropMonitoredBy t0.monitoredBy fromPid refId }
      { s with processes := s.processes.set idx t h }
    else
      s

/-- Fold DOWN notifications over inbound monitors `(monitorerPid, refId)`. -/
def propagateExit.goDown (s : State) (fromPid : Nat) (heap : Heap) (reason : Value) :
    List (Nat × Nat) → State
  | [] => s
  | (monitorerPid, refId) :: rest =>
    propagateExit.goDown
      (notifyDownPeer s fromPid heap reason monitorerPid refId) fromPid heap reason rest

/-- Fold outbound-monitor cleanup over `(targetPid, refId)`. -/
def propagateExit.goClear (s : State) (fromPid : Nat) : List (Nat × Nat) → State
  | [] => s
  | (targetPid, refId) :: rest =>
    propagateExit.goClear (clearTargetMonitor s fromPid targetPid refId) fromPid rest

mutual
  /--
  Signal one linked peer: mailbox EXIT if `trapExit`, else kill and cascade
  (`fuel` bounds kill depth). With `fuel = 0`, always mailbox (no further kills).
  -/
  def signalLink (fuel : Nat) (s : State) (fromPid : Nat) (heap : Heap) (reason : Value)
      (peerPid : Nat) : State :=
    match s.findProcessIdx peerPid with
    | none => s
    | some idx =>
      if hpeer : idx < s.processes.size then
        let peer0 := s.processes[idx]'hpeer
        if peer0.status == .exited then
          s
        else
          match fuel with
          | 0 => notifyExitMailbox s fromPid heap reason peerPid
          | fuel + 1 =>
            if peer0.trapExit then
              notifyExitMailbox s fromPid heap reason peerPid
            else
              let peer0 := { peer0 with links := unlinkPid peer0.links fromPid }
              let (peer0, reason') := peer0.copyFrom heap reason
              let linkPids := peer0.links
              let peerDowns := peer0.monitoredBy
              let peerOuts := peer0.monitors
              let peerHeap := peer0.heap
              let peerPid' := peer0.pid
              let peer := {
                peer0 with
                stack := #[]
                result := some reason'
                status := .exited
                handlers := #[]
                links := #[]
                monitors := #[]
                monitoredBy := #[]
                waitDeadline := none
              }
              let s := { s with processes := s.processes.set idx peer hpeer }
              propagateExit.from fuel s peerPid' peerHeap reason'
                linkPids.toList peerDowns.toList peerOuts.toList
      else
        s

  /-- Fold `signalLink` over linked peer pids. -/
  def signalLinks (fuel : Nat) (s : State) (fromPid : Nat) (heap : Heap) (reason : Value) :
      List Nat → State
    | [] => s
    | peerPid :: rest =>
      signalLinks fuel (signalLink fuel s fromPid heap reason peerPid) fromPid heap reason rest

  /--
  Fan out EXIT/DOWN after a process exit. Linked peers with `trapExit` get a mailbox
  `{:EXIT, …}`; others are killed (cascading, fuel-bounded by process count).
  -/
  def propagateExit.from (fuel : Nat) (s : State) (fromPid : Nat) (heap : Heap)
      (reason : Value) (links : List Nat) (downs : List (Nat × Nat))
      (outs : List (Nat × Nat)) : State :=
    let s := signalLinks fuel s fromPid heap reason links
    let s := propagateExit.goDown s fromPid heap reason downs
    propagateExit.goClear s fromPid outs
end

/--
Notify linked peers and monitorers that the process at `exitedIdx` has exited with `reason`.
Trapping peers get `{:EXIT, …}`; non-trapping linked peers are killed and cascade.
-/
def propagateExit (s : State) (exitedIdx : Nat) (reason : Value) : State :=
  if hlt : exitedIdx < s.processes.size then
    let exited0 := s.processes[exitedIdx]'hlt
    let fromPid := exited0.pid
    let linkPids := exited0.links
    let downs := exited0.monitoredBy
    let outs := exited0.monitors
    let heap := exited0.heap
    let exited := { exited0 with links := #[], monitors := #[], monitoredBy := #[] }
    let s := { s with processes := s.processes.set exitedIdx exited hlt }
    let s :=
      propagateExit.from s.processes.size s fromPid heap reason
        linkPids.toList downs.toList outs.toList
    -- ETS owner exit → heir transfer or kill table.
    etsOnOwnerExit s fromPid
  else
    s

/-- Force-exit process `pid` with `reason` (ignores `trapExit`; like OTP `exit(Pid, kill)`).
No-op if missing or already exited. -/
def forceExitPid (s : State) (pid : Nat) (reason : Value) : State :=
  match s.findProcessIdx pid with
  | none => s
  | some idx =>
    if h : idx < s.processes.size then
      let p0 := s.processes[idx]'h
      if p0.status == .exited then
        s
      else
        -- Reason lives on the caller's heap; copy into the target before exit.
        let srcHeap :=
          if hcur : s.current < s.processes.size then
            s.processes[s.current]'hcur |>.heap
          else
            p0.heap
        let (p0, reason') := p0.copyFrom srcHeap reason
        let p := {
          p0 with
          stack := #[]
          result := some reason'
          status := .exited
          handlers := #[]
          waitDeadline := none
        }
        let s := { s with processes := s.processes.set idx p h }
        propagateExit s idx reason'
    else
      s

/--
Install monitor `refId` from the current process onto `targetPid`.
Caller allocates `refId` (and typically bumps `nextRef`) beforehand.
-/
def monitorWith (s : State) (targetPid : Nat) (refId : Nat) : Except StepError State :=
  match s.findProcessIdx targetPid with
  | none => .error (.badPid targetPid)
  | some idx =>
    if ¬(s.current < s.processes.size) then
      .error .noRunnable
    else
      let cur0 := s.processes[s.current]!
      let target0 := s.processes[idx]!
      if target0.status == .exited then
        let reason :=
          match target0.result with
          | some v => v
          | none => Value.nil
        .ok (notifyDownPeer s target0.pid target0.heap reason cur0.pid refId)
      else if idx == s.current then
        let cur := {
          cur0 with
          monitors := cur0.monitors.push (targetPid, refId)
          monitoredBy := cur0.monitoredBy.push (cur0.pid, refId)
        }
        .ok (s.setCurrentProcess cur)
      else
        let cur := { cur0 with monitors := cur0.monitors.push (targetPid, refId) }
        let target := { target0 with monitoredBy := target0.monitoredBy.push (cur0.pid, refId) }
        let s := s.setCurrentProcess cur
        .ok { s with processes := s.processes.setIfInBounds idx target }

/-- True when `v` is a heap `{:DOWN, refId, …}` tuple (OTP flush). -/
def isDownRefMsg (h : Heap) (v : Value) (refId : Nat) : Bool :=
  match v with
  | .ref r =>
    match h.get? r with
    | some (.tuple elems) =>
      elems.size == 5 &&
        match elems[0]!, elems[1]! with
        | .atom "DOWN", .reference id => decide (id = refId)
        | _, _ => false
    | _ => false
  | _ => false

/-- Drop mailbox messages that are `{:DOWN, refId, …}` (does not touch other mail). -/
def flushDownRef (h : Heap) (mailbox : Array Value) (refId : Nat) : Array Value :=
  mailbox.filter (fun v => !(isDownRefMsg h v refId))

/-! ## ETS (public tables; tid = index; ) -/

/-- Anonymous `:set` table (compat `ets_new/0`); `owner` = creator pid. -/
def etsNew (s : State) (ownerPid : Nat) : State × Nat :=
  let tid := s.etsTables.size
  let t : EtsTable := { owner := some ownerPid }
  ({ s with etsTables := s.etsTables.push t }, tid)

/-- `ets_new/2`: `name` is `none` (anonymous) or atom text; fails on dup name. -/
def etsNewNamed (s : State) (ownerPid : Nat) (name : Option String) (kind : EtsKind) :
    Option (State × Nat) :=
  match name with
  | some n =>
    if Ets.nameTaken s.etsTables n then none
    else
      let tid := s.etsTables.size
      let t : EtsTable := { name := some n, kind, owner := some ownerPid }
      some ({ s with etsTables := s.etsTables.push t }, tid)
  | none =>
    let tid := s.etsTables.size
    let t : EtsTable := { kind, owner := some ownerPid }
    some ({ s with etsTables := s.etsTables.push t }, tid)

/-- Resolve tab term (int tid or name atom) to a **live** index. -/
def etsResolve (s : State) (tab : Term) : Option Nat :=
  Ets.resolveTab s.etsTables tab

def etsInsert (s : State) (tid : Nat) (key val : Term) : Option State :=
  if h : tid < s.etsTables.size then
    if ha : !(s.etsTables[tid]'h).alive then none
    else
      let t := Ets.insertEntry (s.etsTables[tid]'h) key val
      some { s with etsTables := s.etsTables.set tid t h }
  else
    none

def etsLookup (s : State) (tid : Nat) (key : Term) : Option (Array Term) :=
  if h : tid < s.etsTables.size then
    if ha : !(s.etsTables[tid]'h).alive then none
    else some (Ets.lookupValues (s.etsTables[tid]'h) key)
  else
    none

def etsDelete (s : State) (tid : Nat) (key : Term) : Option State :=
  if h : tid < s.etsTables.size then
    if ha : !(s.etsTables[tid]'h).alive then none
    else
      let t := Ets.deleteKey (s.etsTables[tid]'h) key
      some { s with etsTables := s.etsTables.set tid t h }
  else
    none

def etsDeleteObject (s : State) (tid : Nat) (key val : Term) : Option State :=
  if h : tid < s.etsTables.size then
    if ha : !(s.etsTables[tid]'h).alive then none
    else
      let t := Ets.deleteObject (s.etsTables[tid]'h) key val
      some { s with etsTables := s.etsTables.set tid t h }
  else
    none

def etsMatchObject (s : State) (tid : Nat) (pattern : Term) : Option (Array Term) :=
  if h : tid < s.etsTables.size then
    if ha : !(s.etsTables[tid]'h).alive then none
    else some (Ets.matchObject (s.etsTables[tid]'h) pattern)
  else
    none

/-- `none` = bad tab; `some (.error ())` = malformed/unsupported guard; `some (.ok vals)` = ok. -/
def etsSelect (s : State) (tid : Nat) (spec : Term) : Option (Except Unit (Array Term)) :=
  if h : tid < s.etsTables.size then
    if ha : !(s.etsTables[tid]'h).alive then none
    else
      match Ets.parseSpec spec with
      | none => some (.error ())
      | some clauses =>
        match Ets.select (s.etsTables[tid]'h) clauses with
        | none => some (.error ())
        | some vals => some (.ok vals)
  else
    none

/-- Set or clear heir: `heirT` is `{pid, data}` or atom `none`. -/
def etsHeir (s : State) (tid : Nat) (heirT : Term) : Option State :=
  if h : tid < s.etsTables.size then
    if ha : !(s.etsTables[tid]'h).alive then none
    else
      let t0 := s.etsTables[tid]'h
      match heirT with
      | .atom name =>
        if name == "none" then
          some { s with etsTables := s.etsTables.set tid { t0 with heir := none } h }
        else
          none
      | .tuple elems =>
        if hsz : elems.size = 2 then
          match elems[0]'(by omega) with
          | .pid pid =>
            some {
              s with
              etsTables :=
                s.etsTables.set tid { t0 with heir := some (pid, elems[1]'(by omega)) } h
            }
          | _ => none
        else
          none
      | _ => none
  else
    none

/-- `ets_first/1` — first key or `"$end_of_table"`. -/
def etsFirst (s : State) (tid : Nat) : Option Term :=
  if h : tid < s.etsTables.size then
    if !(s.etsTables[tid]'h).alive then none
    else some (Ets.firstKey (s.etsTables[tid]'h))
  else
    none

/-- `ets_next/2` — next key after `key` or `"$end_of_table"`. -/
def etsNext (s : State) (tid : Nat) (key : Term) : Option Term :=
  if h : tid < s.etsTables.size then
    if !(s.etsTables[tid]'h).alive then none
    else some (Ets.nextKey (s.etsTables[tid]'h) key)
  else
    none

/-- `ets_give_away/3` — owner transfers table; delivers `ETS-TRANSFER`. -/
def etsGiveAway (s : State) (tid : Nat) (fromPid toPid : Nat) (data : Term) :
    Option State :=
  if h : tid < s.etsTables.size then
    if !(s.etsTables[tid]'h).alive then none
    else if (s.etsTables[tid]'h).owner != some fromPid then none
    else if !processLive s toPid then none
    else
      let t1 := { (s.etsTables[tid]'h) with owner := some toPid, heir := none }
      let s := { s with etsTables := s.etsTables.set tid t1 h }
      some (notifyEtsTransfer s tid fromPid toPid data)
  else
    none

/-- Drop the current process's monitor for `refId` and flush a pending DOWN
(OTP `demonitor(Ref, [:flush])` — Autumn always flushes). No-op if absent. -/
def demonitorWith (s : State) (refId : Nat) : Except StepError State :=
  if ¬(s.current < s.processes.size) then
    .error .noRunnable
  else
    let cur0 := s.processes[s.current]!
    let mailbox := flushDownRef cur0.heap cur0.mailbox refId
    match cur0.monitors.find? (fun (_, r) => r == refId) with
    | none =>
      let cur := { cur0 with mailbox }
      .ok (s.setCurrentProcess cur)
    | some (targetPid, _) =>
      let cur := {
        cur0 with
        monitors := dropByRef cur0.monitors refId
        mailbox
      }
      let s := s.setCurrentProcess cur
      .ok (clearTargetMonitor s cur.pid targetPid refId)

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

/-- Scheduler preference for proof / `runScheduled` (not stored on `State`). -/
inductive ScheduleChoice where
  /-- Deterministic round-robin (default `scheduleNext`). -/
  | roundRobin
  /-- Select this process index when runnable; otherwise fall back to round-robin. -/
  | prefer (idx : Nat)
  deriving Repr, BEq, Inhabited

def processRunnable (p : Process) : Bool :=
  p.status == .runnable && p.result.isNone

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

/-- Quantified scheduler: `.prefer idx` when that slot is runnable, else `scheduleNext`. -/
def scheduleNextWith (s : State) (fromIdx : Nat) (choice : ScheduleChoice) :
    Except StepError State :=
  match choice with
  | .roundRobin => scheduleNext s fromIdx
  | .prefer idx =>
    if s.processes.size = 0 then
      .error .noRunnable
    else
      let procs := wakeExpired s.processes s.clock
      if h : idx < procs.size then
        if processRunnable (procs[idx]) then
          .ok { s with processes := procs, current := idx, reductions := reductionBudget }
        else
          scheduleNext { s with processes := procs } fromIdx
      else
        scheduleNext { s with processes := procs } fromIdx

/-- Pop one choice; empty tape means round-robin forever. -/
def popChoice (choices : List ScheduleChoice) : ScheduleChoice × List ScheduleChoice :=
  match choices with
  | [] => (.roundRobin, [])
  | c :: rest => (c, rest)

end State

end Autumn
