import Autumn.State.ProcessLemmas

namespace Autumn

/-! # Scheduler lemmas (public proof surface)

Prefer `findRunnable_*` / `scheduleNext_*` here over unfolding the scheduler.
Part of the `State/Lemmas` barrel. See `AGENTS.md` (“Public proof surface”).
-/

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

/-- Scheduler: error is always `noRunnable`. -/
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

/-! ## Durable drain: machine result is entry exit `toTerm` -/

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

/-! ## ScheduleChoice / `scheduleNextWith` -/

@[simp] theorem scheduleNextWith_roundRobin (s : State) (fromIdx : Nat) :
    State.scheduleNextWith s fromIdx .roundRobin = State.scheduleNext s fromIdx :=
  rfl

theorem wakeExpired_size (procs : Array Process) (clock : Nat) :
    (State.wakeExpired procs clock).size = procs.size := by
  simp [State.wakeExpired, Array.size_map]

/-- `wakeExpired` does not demote an already-runnable process. -/
theorem wakeExpired_preserves_runnable (procs : Array Process) (clock idx : Nat)
    (hlt : idx < procs.size)
    (hrun : State.processRunnable (procs[idx]) = true) :
    State.processRunnable
      ((State.wakeExpired procs clock)[idx]'(by simpa [wakeExpired_size] using hlt)) = true := by
  revert hrun
  cases hst : procs[idx].status with
  | runnable =>
    intro hrun
    have heq :
        (State.wakeExpired procs clock)[idx]'(by simpa [wakeExpired_size] using hlt) =
          procs[idx] := by
      simp only [State.wakeExpired, Array.getElem_map, hst]
    simpa [heq] using hrun
  | waiting =>
    intro hrun
    simp only [State.processRunnable, hst, Bool.and_eq_true] at hrun
    have : (ProcStatus.waiting == .runnable) = false := rfl
    rw [this] at hrun; cases hrun.1
  | exited =>
    intro hrun
    simp only [State.processRunnable, hst, Bool.and_eq_true] at hrun
    have : (ProcStatus.exited == .runnable) = false := rfl
    rw [this] at hrun; cases hrun.1

theorem scheduleNextWith_preserves (s : State) (fromIdx : Nat) (c : State.ScheduleChoice)
    {s'} (hs : State.WF s) (h : State.scheduleNextWith s fromIdx c = .ok s') :
    State.WF s' := by
  cases c with
  | roundRobin =>
    exact scheduleNext_preserves s fromIdx hs (by simpa [State.scheduleNextWith] using h)
  | prefer idx =>
    simp only [State.scheduleNextWith] at h
    by_cases hsz : s.processes.size = 0
    · simp [hsz] at h
    · rw [if_neg hsz] at h
      have hszW := wakeExpired_size s.processes s.clock
      have hprocs := wakeExpired_preserves_procs s.module s.processes s.clock hs.2.2.2
      have hs1 : State.WF { s with processes := State.wakeExpired s.processes s.clock } := by
        refine ⟨hs.1, by simpa [hszW] using hs.2.1, ?_, ?_⟩
        · simpa [hszW] using hs.2.2.1
        · intro i hi; simpa using hprocs i (by simpa [hszW] using hi)
      by_cases hlt : idx < (State.wakeExpired s.processes s.clock).size
      · rw [dif_pos hlt] at h
        by_cases hrun :
            State.processRunnable ((State.wakeExpired s.processes s.clock)[idx]'hlt) = true
        · rw [if_pos hrun] at h
          cases h
          exact ⟨hs1.1, hs1.2.1, hlt, hs1.2.2.2⟩
        · rw [if_neg hrun] at h
          exact scheduleNext_preserves _ fromIdx hs1 h
      · rw [dif_neg hlt] at h
        exact scheduleNext_preserves _ fromIdx hs1 h

/-- `scheduleNextWith` errors are always `noRunnable` (like `scheduleNext`). -/
theorem scheduleNextWith_error_is_noRunnable (s : State) (fromIdx : Nat)
    (c : State.ScheduleChoice) {e}
    (h : State.scheduleNextWith s fromIdx c = .error e) : e = .noRunnable := by
  cases c with
  | roundRobin =>
    exact scheduleNext_error_is_noRunnable s fromIdx (by simpa [State.scheduleNextWith] using h)
  | prefer idx =>
    simp only [State.scheduleNextWith] at h
    by_cases hsz : s.processes.size = 0
    · simp [hsz] at h; cases h; rfl
    · rw [if_neg hsz] at h
      by_cases hlt : idx < (State.wakeExpired s.processes s.clock).size
      · rw [dif_pos hlt] at h
        by_cases hrun :
            State.processRunnable ((State.wakeExpired s.processes s.clock)[idx]'hlt) = true
        · simp [hrun] at h
        · rw [if_neg hrun] at h
          exact scheduleNext_error_is_noRunnable _ fromIdx h
      · rw [dif_neg hlt] at h
        exact scheduleNext_error_is_noRunnable _ fromIdx h

/-- Preferring a runnable index selects it. -/
theorem scheduleNextWith_prefer_runnable (s : State) (fromIdx idx : Nat)
    (hne : 0 < s.processes.size) (hlt : idx < s.processes.size)
    (hrun : State.processRunnable (s.processes[idx]) = true)
    {s'} (h : State.scheduleNextWith s fromIdx (.prefer idx) = .ok s') :
    s'.current = idx := by
  have hlt' : idx < (State.wakeExpired s.processes s.clock).size := by
    simpa [wakeExpired_size] using hlt
  have hrun' := wakeExpired_preserves_runnable s.processes s.clock idx hlt hrun
  simp only [State.scheduleNextWith] at h
  rw [if_neg (Nat.ne_of_gt hne), dif_pos hlt', if_pos hrun'] at h
  cases h; rfl

/-- `.prefer j` schedules `j` when that process is runnable (∃ schedule). -/
theorem exists_schedule_prefer (s : State) (fromIdx j : Nat)
    (hne : 0 < s.processes.size) (hj : j < s.processes.size)
    (hrj : State.processRunnable (s.processes[j]) = true) :
    ∃ s', State.scheduleNextWith s fromIdx (.prefer j) = .ok s' ∧ s'.current = j := by
  refine ⟨{ s with
      processes := State.wakeExpired s.processes s.clock
      current := j
      reductions := State.reductionBudget }, ?_, rfl⟩
  have hlt' : j < (State.wakeExpired s.processes s.clock).size := by
    simpa [wakeExpired_size] using hj
  have hrunj := wakeExpired_preserves_runnable s.processes s.clock j hj hrj
  simp only [State.scheduleNextWith]
  rw [if_neg (Nat.ne_of_gt hne), dif_pos hlt', if_pos hrunj]

/-- Round-robin is always available as a schedule choice (∀ includes this strategy). -/
theorem forall_includes_roundRobin (s : State) (fromIdx : Nat) {s'}
    (h : State.scheduleNext s fromIdx = .ok s') :
    State.scheduleNextWith s fromIdx .roundRobin = .ok s' := by
  simpa using h

end Autumn
