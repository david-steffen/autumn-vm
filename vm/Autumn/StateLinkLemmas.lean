import Autumn.StateProcessLemmas

namespace Autumn

/-! # Links / EXIT propagation -/

theorem process_set_links_WF (m : Module) (p : Process) (links : Array Nat)
    (hp : Process.WF m p) :
    Process.WF m { p with links := links } := hp

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

theorem notifyExitPeer_preserves (s : State) (fromPid : Nat) (heap : Heap)
    (reason : Value) (peerPid : Nat) (hs : State.WF s) :
    State.WF (State.notifyExitPeer s fromPid heap reason peerPid) := by
  cases hfnd : s.findProcessIdx peerPid with
  | none => simp [State.notifyExitPeer, hfnd]; exact hs
  | some idx =>
    simp [State.notifyExitPeer, hfnd]
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
        -- Goal is the same update spelled with nested matches/`have`
        change State.WF
          { s with
            processes :=
              s.processes.set idx
                (let p1 := { allocated.1 with mailbox := allocated.1.mailbox.push allocated.2 }
                  if allocated.1.status == .waiting then State.wakeOnMessage p1 else p1)
                hpeer }
        exact processes_set_WF s idx _ hs hpeer hpW
    · exact hs

theorem propagateExit.go_preserves (s : State) (fromPid : Nat) (heap : Heap)
    (reason : Value) (peers : List Nat) (hs : State.WF s) :
    State.WF (State.propagateExit.go s fromPid heap reason peers) := by
  induction peers generalizing s with
  | nil => exact hs
  | cons peerPid rest ih =>
    exact ih _ (notifyExitPeer_preserves s fromPid heap reason peerPid hs)

theorem propagateExit_preserves (s : State) (exitedIdx : Nat) (reason : Value)
    (hs : State.WF s) :
    State.WF (State.propagateExit s exitedIdx reason) := by
  unfold State.propagateExit
  split
  · rename_i hlt
    let exited0 := s.processes[exitedIdx]'hlt
    have hex0 : Process.WF s.module exited0 := hs.2.2.2 exitedIdx hlt
    have hex : Process.WF s.module { exited0 with links := #[] } :=
      process_set_links_WF _ _ _ hex0
    have hs1 : State.WF
        { s with processes := s.processes.set exitedIdx { exited0 with links := #[] } hlt } :=
      processes_set_WF s exitedIdx _ hs hlt hex
    exact propagateExit.go_preserves _ exited0.pid exited0.heap reason exited0.links.toList hs1
  · exact hs

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

end Autumn
