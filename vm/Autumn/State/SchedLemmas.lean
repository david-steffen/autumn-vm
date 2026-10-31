import Autumn.State.ProcessLemmas

namespace Autumn

/-! # Scheduler lemmas -/

theorem findRunnable_lt (procs : Array Process) (idx fuel : Nat) {j : Nat}
    (hne : 0 < procs.size) (h : State.findRunnable procs idx fuel = some j) :
    j < procs.size := by
  induction fuel generalizing idx with
  | zero => simp [State.findRunnable] at h
  | succ fuel ih =>
    unfold State.findRunnable at h
    simp [Nat.ne_of_gt hne] at h
    split at h
    · cases h; exact Nat.mod_lt _ hne
    · exact ih _ h

theorem clock_preserves (s : State) (n : Nat) (hs : State.WF s) :
    State.WF { s with clock := n } :=
  ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩

/-- Phase 2 scheduler: error is always `noRunnable`. -/
theorem scheduleNext_error_is_noRunnable (s : State) (fromIdx : Nat) {e}
    (h : State.scheduleNext s fromIdx = .error e) : e = .noRunnable := by
  unfold State.scheduleNext at h
  split at h
  · cases h; rfl
  · -- size ≠ 0 path: only `.error .noRunnable` leaves
    revert h
    simp only []
    split
    · intro h; exact nomatch h
    · split
      · intro h; split at h
        · exact nomatch h
        · split at h
          · split at h
            · exact nomatch h
            · cases h; rfl
          · cases h; rfl
      · intro h; split at h
        · split at h
          · exact nomatch h
          · cases h; rfl
        · cases h; rfl

theorem reductions_preserves (s : State) (n : Nat) (hs : State.WF s) :
    State.WF { s with reductions := n } :=
  ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩

theorem scheduleNext_preserves (s : State) (fromIdx : Nat) {s'}
    (hs : State.WF s) (h : State.scheduleNext s fromIdx = .ok s') :
    State.WF s' := by
  have hszne : ¬(s.processes.size = 0) := by
    intro hz; have := hs.2.1; omega
  have hszW : (State.wakeExpired s.processes s.clock).size = s.processes.size := by
    simp [State.wakeExpired, Array.size_map]
  have hprocs0 := wakeExpired_preserves_procs s.module s.processes s.clock hs.2.2.2
  let procs1 := State.wakeExpired s.processes s.clock
  have hs1 : State.WF { s with processes := procs1 } := by
    refine ⟨hs.1, by simpa [procs1, hszW] using hs.2.1, ?_, ?_⟩
    · simpa [procs1, hszW] using hs.2.2.1
    · intro i hi; simpa [procs1] using hprocs0 i hi
  simp [State.scheduleNext, hszne] at h
  split at h
  · rename_i idx hfnd
    cases h
    have hidx := findRunnable_lt procs1 fromIdx procs1.size
      (by simpa [procs1, hszW] using hs.2.1) (by simpa [procs1] using hfnd)
    exact ⟨hs.1, by simpa [procs1, hszW] using hs.2.1, hidx, by
      intro i hi; simpa [procs1] using hprocs0 i (by simpa [procs1, hszW] using hi)⟩
  · split at h
    · rename_i t hdl
      let procs2 := State.wakeExpired procs1 (max s.clock t)
      have hsz2 : procs2.size = procs1.size := by
        simp [procs2, procs1, State.wakeExpired, Array.size_map]
      have hprocs2 :=
        wakeExpired_preserves_procs s.module procs1 (max s.clock t) (by
          intro i hi; simpa [procs1] using hprocs0 i (by simpa [procs1, hszW] using hi))
      have hs2 : State.WF { s with processes := procs2, clock := max s.clock t } := by
        refine ⟨hs.1, by simpa [procs2, hsz2, procs1, hszW] using hs.2.1, ?_, ?_⟩
        · simpa [procs2, hsz2, procs1, hszW] using hs.2.2.1
        · intro i hi; simpa [procs2] using hprocs2 i hi
      split at h
      · rename_i idx hfnd
        cases h
        have hidx := findRunnable_lt procs2 fromIdx procs2.size
          (by simpa [procs2, hsz2, procs1, hszW] using hs.2.1)
          (by simpa [procs2, procs1] using hfnd)
        exact ⟨hs.1, by simpa [procs2, hsz2, procs1, hszW] using hs.2.1, hidx, by
          intro i hi; simpa [procs2] using hprocs2 i
            (by simpa [procs2, hsz2, procs1, hszW] using hi)⟩
      · split at h
        · split at h
          · cases h
            exact ⟨hs2.1, hs2.2.1, hs2.2.2.1, hs2.2.2.2⟩
          · exact nomatch h
        · exact nomatch h
    · split at h
      · split at h
        · cases h
          exact ⟨hs1.1, hs1.2.1, hs1.2.2.1, hs1.2.2.2⟩
        · exact nomatch h
      · exact nomatch h

/-! ## Durable drain (IR v14): machine result is entry exit `toTerm` -/

/--
When `scheduleNext` publishes a machine `result` from a state with no machine
result yet, it is `Heap.toTerm` of the entry process's exit value.
-/
theorem scheduleNext_result_is_toTerm
    (s : State) (fromIdx : Nat) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : State.scheduleNext s fromIdx = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (v : Value), t = Heap.toTerm heap v := by
  have hszne : ¬(s.processes.size = 0) := by
    intro hz; simp [State.scheduleNext, hz] at h
  simp [State.scheduleNext, hszne] at h
  split at h
  · cases h; simp [hsr] at ht
  · split at h
    · split at h
      · cases h; simp [hsr] at ht
      · split at h
        · rename_i ep hep
          split at h
          · rename_i v hv
            cases h
            have ht' : Heap.toTerm ep.heap v = t := by
              simpa using ht
            exact ⟨ep.heap, v, ht'.symm⟩
          · exact nomatch h
        · exact nomatch h
    · split at h
      · rename_i ep hep
        split at h
        · rename_i v hv
          cases h
          have ht' : Heap.toTerm ep.heap v = t := by
            simpa using ht
          exact ⟨ep.heap, v, ht'.symm⟩
        · exact nomatch h
      · exact nomatch h

end Autumn
