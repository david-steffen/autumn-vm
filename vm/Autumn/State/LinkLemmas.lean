import Autumn.State.ProcessLemmas

namespace Autumn

/-! # Links / EXIT propagation -/

theorem process_set_links_WF (m : Module) (p : Process) (links : Array Nat)
    (hp : Process.WF m p) :
    Process.WF m { p with links := links } := hp

theorem process_set_monitors_WF (m : Module) (p : Process)
    (monitors monitoredBy : Array (Nat × Nat)) (hp : Process.WF m p) :
    Process.WF m { p with monitors := monitors, monitoredBy := monitoredBy } := hp

theorem process_set_waitDeadline_WF (m : Module) (p : Process) (d : Option Nat)
    (hp : Process.WF m p) :
    Process.WF m { p with waitDeadline := d } := hp

theorem processes_set_WF (s : State) (idx : Nat) (p : Process)
    (hs : State.WF s) (hidx : idx < s.processes.size)
    (hp : Process.WF s.module p) :
    State.WF { s with processes := s.processes.set idx p hidx } := by
  refine ⟨hs.1, ?_, ?_, ?_⟩
  · simpa [Array.size_set] using hs.2.1
  · simpa [Array.size_set] using hs.2.2.1
  · intro i hi
    have hsz : (s.processes.set idx p hidx).size = s.processes.size := Array.size_set _
    have hi0 : i < s.processes.size := by simpa [hsz] using hi
    by_cases heq : i = idx
    · have hget : (s.processes.set idx p hidx)[i]'hi = p := by
        simp [heq, Array.getElem_set_self]
      rw [hget]; exact hp
    · have hget : (s.processes.set idx p hidx)[i]'hi = s.processes[i]'hi0 :=
        Array.getElem_set_ne (v := p) hidx hi0 (Ne.symm heq)
      rw [hget]; exact hs.2.2.2 i hi0

theorem notifyExitMailbox_preserves (s : State) (fromPid : Nat) (heap : Heap)
    (reason : Value) (peerPid : Nat) (hs : State.WF s) :
    State.WF (State.notifyExitMailbox s fromPid heap reason peerPid) := by
  cases hfnd : s.findProcessIdx peerPid with
  | none => simp [State.notifyExitMailbox, hfnd]; exact hs
  | some idx =>
    simp [State.notifyExitMailbox, hfnd]
    split
    · rename_i hpeer
      split
      · exact hs
      · let peer0 := s.processes[idx]'hpeer
        have hpeer0 : Process.WF s.module peer0 := hs.2.2.2 idx hpeer
        have hpLinks : Process.WF s.module
            { peer0 with links := State.unlinkPid peer0.links fromPid } :=
          process_set_links_WF _ _ _ hpeer0
        let copied :=
          ({ peer0 with links := State.unlinkPid peer0.links fromPid }).copyFrom heap reason
        have hpC : Process.WF s.module copied.1 :=
          Process.copyFrom_preserves_WF _ _ _ _ hpLinks
        let allocated :=
          Process.allocCompound copied.1 Node.tuple
            #[.atom "EXIT", .pid fromPid, copied.2]
        have hpA : Process.WF s.module allocated.1 :=
          Process.allocCompound_preserves_WF _ _ Node.tuple _ hpC
        have hpW : Process.WF s.module
            (let p1 := { allocated.1 with mailbox := allocated.1.mailbox.push allocated.2 }
              if allocated.1.status == .waiting then State.wakeOnMessage p1 else p1) :=
          process_wake_mailbox_WF _ allocated.1 allocated.2 hpA
        change State.WF
          { s with
            processes :=
              s.processes.set idx
                (let p1 := { allocated.1 with mailbox := allocated.1.mailbox.push allocated.2 }
                  if allocated.1.status == .waiting then State.wakeOnMessage p1 else p1)
                hpeer }
        exact processes_set_WF s idx _ hs hpeer hpW
    · exact hs

theorem notifyExitPeer_preserves (s : State) (fromPid : Nat) (heap : Heap)
    (reason : Value) (peerPid : Nat) (hs : State.WF s) :
    State.WF (State.notifyExitPeer s fromPid heap reason peerPid) := by
  simpa [State.notifyExitPeer] using notifyExitMailbox_preserves s fromPid heap reason peerPid hs

theorem process_set_trapExit_WF (m : Module) (p : Process) (b : Bool)
    (hp : Process.WF m p) :
    Process.WF m { p with trapExit := b } := hp

theorem exited_force_process_WF (m : Module) (p : Process) (reason : Value)
    (hp : Process.WF m p) :
    Process.WF m
      { p with
        stack := #[]
        result := some reason
        status := .exited
        handlers := #[]
        links := #[]
        monitors := #[]
        monitoredBy := #[]
        waitDeadline := none } :=
  ⟨hp.1, by simp⟩

theorem notifyDownPeer_preserves (s : State) (fromPid : Nat) (heap : Heap)
    (reason : Value) (monitorerPid refId : Nat) (hs : State.WF s) :
    State.WF (State.notifyDownPeer s fromPid heap reason monitorerPid refId) := by
  cases hfnd : s.findProcessIdx monitorerPid with
  | none => simp [State.notifyDownPeer, hfnd]; exact hs
  | some idx =>
    simp [State.notifyDownPeer, hfnd]
    split
    · rename_i hpeer
      split
      · exact hs
      · let peer0 := s.processes[idx]'hpeer
        have hpeer0 : Process.WF s.module peer0 := hs.2.2.2 idx hpeer
        have hpMon : Process.WF s.module
            { peer0 with monitors := State.dropByRef peer0.monitors refId } :=
          process_set_monitors_WF _ _ _ _ hpeer0
        let copied :=
          ({ peer0 with monitors := State.dropByRef peer0.monitors refId }).copyFrom heap reason
        have hpC : Process.WF s.module copied.1 :=
          Process.copyFrom_preserves_WF _ _ _ _ hpMon
        let allocated :=
          Process.allocCompound copied.1 Node.tuple
            #[.atom "DOWN", .reference refId, .atom "process", .pid fromPid, copied.2]
        have hpA : Process.WF s.module allocated.1 :=
          Process.allocCompound_preserves_WF _ _ Node.tuple _ hpC
        have hpW : Process.WF s.module
            (let p1 := { allocated.1 with mailbox := allocated.1.mailbox.push allocated.2 }
              if allocated.1.status == .waiting then State.wakeOnMessage p1 else p1) :=
          process_wake_mailbox_WF _ allocated.1 allocated.2 hpA
        change State.WF
          { s with
            processes :=
              s.processes.set idx
                (let p1 := { allocated.1 with mailbox := allocated.1.mailbox.push allocated.2 }
                  if allocated.1.status == .waiting then State.wakeOnMessage p1 else p1)
                hpeer }
        exact processes_set_WF s idx _ hs hpeer hpW
    · exact hs

theorem clearTargetMonitor_preserves (s : State) (fromPid targetPid refId : Nat)
    (hs : State.WF s) :
    State.WF (State.clearTargetMonitor s fromPid targetPid refId) := by
  cases hfnd : s.findProcessIdx targetPid with
  | none => simp [State.clearTargetMonitor, hfnd]; exact hs
  | some idx =>
    simp [State.clearTargetMonitor, hfnd]
    split
    · rename_i h
      let t0 := s.processes[idx]'h
      have ht0 : Process.WF s.module t0 := hs.2.2.2 idx h
      have ht : Process.WF s.module
          { t0 with monitoredBy := State.dropMonitoredBy t0.monitoredBy fromPid refId } :=
        process_set_monitors_WF _ _ _ _ ht0
      exact processes_set_WF s idx _ hs h ht
    · exact hs

theorem propagateExit.goDown_preserves (s : State) (fromPid : Nat) (heap : Heap)
    (reason : Value) (downs : List (Nat × Nat)) (hs : State.WF s) :
    State.WF (State.propagateExit.goDown s fromPid heap reason downs) := by
  induction downs generalizing s with
  | nil => exact hs
  | cons head rest ih =>
    exact ih _ (notifyDownPeer_preserves s fromPid heap reason head.1 head.2 hs)

theorem propagateExit.goClear_preserves (s : State) (fromPid : Nat)
    (outs : List (Nat × Nat)) (hs : State.WF s) :
    State.WF (State.propagateExit.goClear s fromPid outs) := by
  induction outs generalizing s with
  | nil => exact hs
  | cons head rest ih =>
    exact ih _ (clearTargetMonitor_preserves s fromPid head.1 head.2 hs)

mutual
  theorem signalLink_preserves (fuel : Nat) (s : State) (fromPid : Nat) (heap : Heap)
      (reason : Value) (peerPid : Nat) (hs : State.WF s) :
      State.WF (State.signalLink fuel s fromPid heap reason peerPid) := by
    cases fuel with
    | zero =>
      simp only [State.signalLink]
      cases hfnd : s.findProcessIdx peerPid with
      | none => simpa [hfnd] using hs
      | some idx =>
        simp [hfnd]
        split
        · rename_i hpeer
          split
          · exact hs
          · exact notifyExitMailbox_preserves s fromPid heap reason peerPid hs
        · exact hs
    | succ fuel =>
      simp only [State.signalLink]
      cases hfnd : s.findProcessIdx peerPid with
      | none => simpa [hfnd] using hs
      | some idx =>
        simp [hfnd]
        split
        · rename_i hpeer
          split
          · exact hs
          · split
            · exact notifyExitMailbox_preserves s fromPid heap reason peerPid hs
            · let peer0 := s.processes[idx]'hpeer
              have hpeer0 : Process.WF s.module peer0 := hs.2.2.2 idx hpeer
              have hpLinks : Process.WF s.module
                  { peer0 with links := State.unlinkPid peer0.links fromPid } :=
                process_set_links_WF _ _ _ hpeer0
              let copied :=
                ({ peer0 with links := State.unlinkPid peer0.links fromPid }).copyFrom heap reason
              have hpC : Process.WF s.module copied.1 :=
                Process.copyFrom_preserves_WF _ _ _ _ hpLinks
              let peer := {
                copied.1 with
                stack := #[]
                result := some copied.2
                status := .exited
                handlers := #[]
                links := #[]
                monitors := #[]
                monitoredBy := #[]
                waitDeadline := none
              }
              have hpE : Process.WF s.module peer := exited_force_process_WF _ _ _ hpC
              have hs1 : State.WF
                  { s with processes := s.processes.set idx peer hpeer } :=
                processes_set_WF s idx _ hs hpeer hpE
              exact propagateExit.from_preserves fuel _ _ _ _ _ _ _ hs1
        · exact hs

  theorem signalLinks_preserves (fuel : Nat) (s : State) (fromPid : Nat) (heap : Heap)
      (reason : Value) (peers : List Nat) (hs : State.WF s) :
      State.WF (State.signalLinks fuel s fromPid heap reason peers) := by
    induction peers generalizing s with
    | nil => simpa [State.signalLinks] using hs
    | cons peerPid rest ih =>
      simp only [State.signalLinks]
      exact ih _ (signalLink_preserves fuel s fromPid heap reason peerPid hs)

  theorem propagateExit.from_preserves (fuel : Nat) (s : State) (fromPid : Nat)
      (heap : Heap) (reason : Value) (links : List Nat) (downs : List (Nat × Nat))
      (outs : List (Nat × Nat)) (hs : State.WF s) :
      State.WF (State.propagateExit.from fuel s fromPid heap reason links downs outs) := by
    simp only [State.propagateExit.from]
    have hs1 := signalLinks_preserves fuel s fromPid heap reason links hs
    have hs2 := propagateExit.goDown_preserves _ fromPid heap reason downs hs1
    exact propagateExit.goClear_preserves _ fromPid outs hs2
end

theorem propagateExit_preserves (s : State) (exitedIdx : Nat) (reason : Value)
    (hs : State.WF s) :
    State.WF (State.propagateExit s exitedIdx reason) := by
  unfold State.propagateExit
  split
  · rename_i hlt
    let exited0 := s.processes[exitedIdx]'hlt
    have hex0 : Process.WF s.module exited0 := hs.2.2.2 exitedIdx hlt
    have hex : Process.WF s.module
        { exited0 with links := #[], monitors := #[], monitoredBy := #[] } :=
      process_set_monitors_WF _ _
        #[] #[] (process_set_links_WF _ _ #[] hex0)
    let s1 :=
      { s with
        processes :=
          s.processes.set exitedIdx
            { exited0 with links := #[], monitors := #[], monitoredBy := #[] } hlt }
    have hs1 : State.WF s1 := processes_set_WF s exitedIdx _ hs hlt hex
    simpa [s1] using
      propagateExit.from_preserves s1.processes.size s1 exited0.pid exited0.heap reason
        exited0.links.toList exited0.monitoredBy.toList exited0.monitors.toList hs1
  · exact hs

theorem forceExitPid_preserves (s : State) (pid : Nat) (reason : Value)
    (hs : State.WF s) :
    State.WF (State.forceExitPid s pid reason) := by
  cases hfnd : s.findProcessIdx pid with
  | none => simp [State.forceExitPid, hfnd]; exact hs
  | some idx =>
    simp [State.forceExitPid, hfnd]
    split
    · rename_i h
      split
      · exact hs
      · split
        · rename_i hcur
          let p0 := s.processes[idx]'h
          have hp0 : Process.WF s.module p0 := hs.2.2.2 idx h
          let srcHeap := s.processes[s.current]'hcur |>.heap
          let copied := p0.copyFrom srcHeap reason
          have hpC : Process.WF s.module copied.1 :=
            Process.copyFrom_preserves_WF s.module p0 srcHeap reason hp0
          have h1 := exited_process_WF s.module copied.1 copied.2 hpC.1
          have hpE : Process.WF s.module
              { copied.1 with
                stack := #[]
                result := some copied.2
                status := .exited
                handlers := #[]
                waitDeadline := none } :=
            process_set_waitDeadline_WF s.module _ none h1
          have hs1 := processes_set_WF s idx _ hs h hpE
          exact propagateExit_preserves _ _ _ hs1
        · let p0 := s.processes[idx]'h
          have hp0 : Process.WF s.module p0 := hs.2.2.2 idx h
          let copied := p0.copyFrom p0.heap reason
          have hpC : Process.WF s.module copied.1 :=
            Process.copyFrom_preserves_WF s.module p0 p0.heap reason hp0
          have h1 := exited_process_WF s.module copied.1 copied.2 hpC.1
          have hpE : Process.WF s.module
              { copied.1 with
                stack := #[]
                result := some copied.2
                status := .exited
                handlers := #[]
                waitDeadline := none } :=
            process_set_waitDeadline_WF s.module _ none h1
          have hs1 := processes_set_WF s idx _ hs h hpE
          exact propagateExit_preserves _ _ _ hs1
    · exact hs

theorem nextRef_preserves (s : State) (n : Nat) (hs : State.WF s) :
    State.WF { s with nextRef := n } :=
  ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩

theorem monitorWith_preserves (s : State) (targetPid : Nat) (refId : Nat) {s' : State}
    (hs : State.WF s) (h : State.monitorWith s targetPid refId = .ok s') :
    State.WF s' := by
  cases hfnd : s.findProcessIdx targetPid with
  | none => simp [State.monitorWith, hfnd] at h
  | some idx =>
    have hcur : s.current < s.processes.size := hs.2.2.1
    have hcurNeg : ¬¬(s.current < s.processes.size) := not_not_intro hcur
    have hidx := findProcessIdx_lt hfnd
    simp [State.monitorWith, hfnd, hcurNeg] at h
    split at h
    · cases h
      exact notifyDownPeer_preserves _ _ _ _ _ _ hs
    · split at h
      · cases h
        let cur0 := s.processes[s.current]!
        have hcur0 : Process.WF s.module cur0 := by
          simpa [cur0, getElem!_pos s.processes s.current hcur] using
            hs.2.2.2 s.current hcur
        let cur := {
          cur0 with
          monitors := cur0.monitors.push (targetPid, refId)
          monitoredBy := cur0.monitoredBy.push (cur0.pid, refId)
        }
        have hcurL : Process.WF s.module cur := process_set_monitors_WF _ _ _ _ hcur0
        exact setCurrentProcess_WF s cur hs hcurL
      · cases h
        let cur0 := s.processes[s.current]!
        let other0 := s.processes[idx]!
        have hcur0 : Process.WF s.module cur0 := by
          simpa [cur0, getElem!_pos s.processes s.current hcur] using
            hs.2.2.2 s.current hcur
        have hother0 : Process.WF s.module other0 := by
          simpa [other0, getElem!_pos s.processes idx hidx] using
            hs.2.2.2 idx hidx
        let cur := { cur0 with monitors := cur0.monitors.push (targetPid, refId) }
        let other :=
          { other0 with monitoredBy := other0.monitoredBy.push (cur0.pid, refId) }
        have hcurL : Process.WF s.module cur := process_set_monitors_WF _ _ _ _ hcur0
        have hotherL : Process.WF s.module other := process_set_monitors_WF _ _ _ _ hother0
        let s1 := s.setCurrentProcess cur
        have hs1 : State.WF s1 := setCurrentProcess_WF s cur hs hcurL
        have hidx1 : idx < s1.processes.size := by
          simpa [s1, State.setCurrentProcess, hcur, Array.size_set] using hidx
        have hmod : s1.module = s.module := by
          dsimp [s1, State.setCurrentProcess]; simp [hcur]
        exact setProcess_WF s1 idx other hs1 hidx1 (by simpa [hmod] using hotherL)

theorem demonitorWith_preserves (s : State) (refId : Nat) {s' : State}
    (hs : State.WF s) (h : State.demonitorWith s refId = .ok s') :
    State.WF s' := by
  have hcur : s.current < s.processes.size := hs.2.2.1
  have hcurNeg : ¬¬(s.current < s.processes.size) := not_not_intro hcur
  simp [State.demonitorWith, hcurNeg] at h
  split at h
  · cases h; exact hs
  · cases h
    let cur0 := s.processes[s.current]!
    have hcur0 : Process.WF s.module cur0 := by
      simpa [cur0, getElem!_pos s.processes s.current hcur] using
        hs.2.2.2 s.current hcur
    let cur := { cur0 with monitors := State.dropByRef cur0.monitors refId }
    have hcurL : Process.WF s.module cur := process_set_monitors_WF _ _ _ _ hcur0
    exact clearTargetMonitor_preserves _ _ _ _
      (setCurrentProcess_WF s cur hs hcurL)

theorem monitorWith_error_not_structural (s : State) (targetPid : Nat) (refId : Nat) {e}
    (h : State.monitorWith s targetPid refId = .error e) : isStructuralError e = false := by
  cases hfnd : s.findProcessIdx targetPid with
  | none =>
    simp [State.monitorWith, hfnd, isStructuralError] at h ⊢
    subst h; rfl
  | some idx =>
    simp [State.monitorWith, hfnd] at h
    split at h
    · cases h; rfl
    · split at h
      · exact nomatch h
      · split at h
        · exact nomatch h
        · exact nomatch h

theorem demonitorWith_error_not_structural (s : State) (refId : Nat) {e}
    (h : State.demonitorWith s refId = .error e) : isStructuralError e = false := by
  simp [State.demonitorWith] at h
  split at h
  · cases h; rfl
  · split at h
    · exact nomatch h
    · exact nomatch h

/-- Successful `linkWith` preserves WF (links are ignored by `Process.WF`). -/
theorem linkWith_preserves (s : State) (otherPid : Nat) {s'}
    (hs : State.WF s) (h : State.linkWith s otherPid = .ok s') :
    State.WF s' := by
  cases hfnd : s.findProcessIdx otherPid with
  | none => simp [State.linkWith, hfnd] at h
  | some idx =>
    have hidx := findProcessIdx_lt hfnd
    have hcur : s.current < s.processes.size := hs.2.2.1
    have hcurNeg : ¬¬(s.current < s.processes.size) := not_not_intro hcur
    simp [State.linkWith, hfnd, hcurNeg] at h
    split at h
    · cases h; exact hs
    · split at h
      · exact nomatch h
      · cases h
        let cur0 := s.processes[s.current]!
        have hcur0 : Process.WF s.module cur0 := by
          simpa [cur0, getElem!_pos s.processes s.current hcur] using
            hs.2.2.2 s.current hcur
        let other0 := s.processes[idx]!
        have hother0 : Process.WF s.module other0 := by
          simpa [other0, getElem!_pos s.processes idx hidx] using hs.2.2.2 idx hidx
        let curLinks :=
          if State.hasLink cur0.links otherPid then cur0.links
          else cur0.links.push otherPid
        let otherLinks :=
          if State.hasLink other0.links cur0.pid then other0.links
          else other0.links.push cur0.pid
        let cur := { cur0 with links := curLinks }
        let other := { other0 with links := otherLinks }
        have hcurL : Process.WF s.module cur := process_set_links_WF _ _ _ hcur0
        have hotherL : Process.WF s.module other := process_set_links_WF _ _ _ hother0
        let s1 := s.setCurrentProcess cur
        have hs1 : State.WF s1 := setCurrentProcess_WF s cur hs hcurL
        have hidx1 : idx < s1.processes.size := by
          simpa [s1, State.setCurrentProcess, hcur, Array.size_set] using hidx
        have hmod : s1.module = s.module := by
          dsimp [s1, State.setCurrentProcess]; simp [hcur]
        exact setProcess_WF s1 idx other hs1 hidx1 (by simpa [hmod] using hotherL)

/-- `linkWith` errors are never structural. -/
theorem linkWith_error_not_structural (s : State) (otherPid : Nat) {e}
    (h : State.linkWith s otherPid = .error e) : isStructuralError e = false := by
  cases hfnd : s.findProcessIdx otherPid with
  | none =>
    simp [State.linkWith, hfnd, isStructuralError] at h ⊢
    subst h; rfl
  | some idx =>
    simp [State.linkWith, hfnd] at h
    split at h
    · cases h; rfl
    · split at h
      · exact nomatch h
      · split at h
        · cases h; rfl
        · exact nomatch h

/-! ## Machine `result` is stable under process-only mutations -/

theorem notifyDownPeer_result (s : State) (fromPid : Nat) (heap : Heap)
    (reason : Value) (monitorerPid refId : Nat) :
    (State.notifyDownPeer s fromPid heap reason monitorerPid refId).result = s.result := by
  cases hfnd : s.findProcessIdx monitorerPid with
  | none => simp [State.notifyDownPeer, hfnd]
  | some idx =>
    simp [State.notifyDownPeer, hfnd]
    split
    · split <;> simp [processes_update_result]
    · rfl

theorem clearTargetMonitor_result (s : State) (fromPid targetPid refId : Nat) :
    (State.clearTargetMonitor s fromPid targetPid refId).result = s.result := by
  cases hfnd : s.findProcessIdx targetPid with
  | none => simp [State.clearTargetMonitor, hfnd]
  | some idx =>
    simp [State.clearTargetMonitor, hfnd]
    split <;> simp [processes_update_result]

theorem propagateExit.goDown_result (s : State) (fromPid : Nat) (heap : Heap)
    (reason : Value) (downs : List (Nat × Nat)) :
    (State.propagateExit.goDown s fromPid heap reason downs).result = s.result := by
  induction downs generalizing s with
  | nil => simp [State.propagateExit.goDown]
  | cons head rest ih =>
    cases head with
    | mk monitorerPid refId =>
      simp only [State.propagateExit.goDown]
      rw [ih, notifyDownPeer_result]

theorem propagateExit.goClear_result (s : State) (fromPid : Nat)
    (outs : List (Nat × Nat)) :
    (State.propagateExit.goClear s fromPid outs).result = s.result := by
  induction outs generalizing s with
  | nil => simp [State.propagateExit.goClear]
  | cons head rest ih =>
    cases head with
    | mk targetPid refId =>
      simp only [State.propagateExit.goClear]
      rw [ih, clearTargetMonitor_result]

theorem notifyExitMailbox_result (s : State) (fromPid : Nat) (heap : Heap)
    (reason : Value) (peerPid : Nat) :
    (State.notifyExitMailbox s fromPid heap reason peerPid).result = s.result := by
  cases hfnd : s.findProcessIdx peerPid with
  | none => simp [State.notifyExitMailbox, hfnd]
  | some idx =>
    simp [State.notifyExitMailbox, hfnd]
    split
    · split <;> simp [processes_update_result]
    · rfl

mutual
  theorem signalLink_result (fuel : Nat) (s : State) (fromPid : Nat) (heap : Heap)
      (reason : Value) (peerPid : Nat) :
      (State.signalLink fuel s fromPid heap reason peerPid).result = s.result := by
    cases fuel with
    | zero =>
      cases hfnd : s.findProcessIdx peerPid with
      | none => simp [State.signalLink, hfnd]
      | some idx =>
        simp [State.signalLink, hfnd]
        split
        · split
          · rfl
          · exact notifyExitMailbox_result _ _ _ _ _
        · rfl
    | succ fuel =>
      cases hfnd : s.findProcessIdx peerPid with
      | none => simp [State.signalLink, hfnd]
      | some idx =>
        simp [State.signalLink, hfnd]
        split
        · split
          · rfl
          · split
            · exact notifyExitMailbox_result _ _ _ _ _
            · -- kill: `{s with processes := _}` then `from`
              rw [propagateExit.from_result]
        · rfl

  theorem signalLinks_result (fuel : Nat) (s : State) (fromPid : Nat) (heap : Heap)
      (reason : Value) (links : List Nat) :
      (State.signalLinks fuel s fromPid heap reason links).result = s.result := by
    induction links generalizing s with
    | nil => simp [State.signalLinks]
    | cons peer rest ih =>
      simp only [State.signalLinks]
      rw [ih, signalLink_result]

  theorem propagateExit.from_result (fuel : Nat) (s : State) (fromPid : Nat)
      (heap : Heap) (reason : Value) (links : List Nat) (downs outs : List (Nat × Nat)) :
      (State.propagateExit.from fuel s fromPid heap reason links downs outs).result =
        s.result := by
    simp only [State.propagateExit.from]
    rw [propagateExit.goClear_result, propagateExit.goDown_result, signalLinks_result]
end

theorem propagateExit_result (s : State) (exitedIdx : Nat) (reason : Value) :
    (State.propagateExit s exitedIdx reason).result = s.result := by
  unfold State.propagateExit
  split
  · rw [propagateExit.from_result]
  · rfl

theorem forceExitPid_result (s : State) (pid : Nat) (reason : Value) :
    (State.forceExitPid s pid reason).result = s.result := by
  cases hfnd : s.findProcessIdx pid with
  | none => simp [State.forceExitPid, hfnd]
  | some idx =>
    simp [State.forceExitPid, hfnd]
    split
    · split
      · rfl
      · rw [propagateExit_result]
    · rfl

theorem linkWith_result (s : State) (otherPid : Nat) {s' : State}
    (h : State.linkWith s otherPid = .ok s') :
    s'.result = s.result := by
  cases hfnd : s.findProcessIdx otherPid with
  | none => simp [State.linkWith, hfnd] at h
  | some idx =>
    simp [State.linkWith, hfnd] at h
    split at h
    · exact nomatch h
    · split at h
      · cases h; rfl
      · split at h
        · exact nomatch h
        · cases h
          rw [setCurrentProcess_result]

theorem monitorWith_result (s : State) (targetPid refId : Nat) {s' : State}
    (h : State.monitorWith s targetPid refId = .ok s') :
    s'.result = s.result := by
  cases hfnd : s.findProcessIdx targetPid with
  | none => simp [State.monitorWith, hfnd] at h
  | some idx =>
    simp [State.monitorWith, hfnd] at h
    split at h
    · exact nomatch h
    · split at h
      · cases h
        exact notifyDownPeer_result _ _ _ _ _ _
      · split at h
        · cases h
          exact setCurrentProcess_result _ _
        · cases h
          rw [setCurrentProcess_result]

theorem demonitorWith_result (s : State) (refId : Nat) {s' : State}
    (h : State.demonitorWith s refId = .ok s') :
    s'.result = s.result := by
  simp [State.demonitorWith] at h
  split at h
  · exact nomatch h
  · split at h
    · cases h; rfl
    · cases h
      rw [clearTargetMonitor_result, setCurrentProcess_result]

/-! ## Observational OTP: `trap_exit` delivers mailbox EXIT (does not kill) -/

/-- With positive fuel and `trapExit`, `signalLink` is mailbox EXIT delivery. -/
theorem signalLink_trapExit_eq_mailbox
    (fuel : Nat) (s : State) (fromPid : Nat) (heap : Heap) (reason : Value)
    (peerPid : Nat) {idx : Nat}
    (hfnd : s.findProcessIdx peerPid = some idx)
    (hpeer : idx < s.processes.size)
    (hlive : ((s.processes[idx]'hpeer).status == .exited) = false)
    (htrap : (s.processes[idx]'hpeer).trapExit = true) :
    State.signalLink (fuel + 1) s fromPid heap reason peerPid =
      State.notifyExitMailbox s fromPid heap reason peerPid := by
  simp [State.signalLink, hfnd, hpeer, hlive, htrap]

end Autumn
