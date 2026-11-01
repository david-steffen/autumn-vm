import Autumn.Step.ProgressInstr
import Autumn.Step.PreserveInstr
import Autumn.Step.Schedule
import Autumn.Examples
import Autumn.Json.Lemmas

namespace Autumn
namespace Step

/-! # Step safety: progress + preservation barrel (public proof surface)

Imports `ProgressInstr` + `PreserveInstr` + `Schedule`. Prefer `step_preserves` /
`step_progress` / `run_*` / `stepScheduled_preserves` here over unfolding
`step` / `stepInstr` / `stepScheduled`.

Larger Mix goldens stay on disk under `tests/fixtures/*.bc.json` (Mix +
`lake exe autumn`), not embedded here. See `AGENTS.md` (“Public proof surface”).
-/

/-- Preservation: successful steps stay well-formed. -/
theorem step_preserves (s s' : State)
    (hs : State.WF s) (h : step s = .ok s') : State.WF s' := by
  by_cases hdone : s.result.isSome = true
  · unfold step at h; simp [hdone] at h; cases h; exact hs
  · have hr : s.result = none := by
      cases hx : s.result with
      | none => rfl
      | some _ => simp [Option.isSome, hx] at hdone
    have hcur := hs.2.2.1
    unfold step at h
    simp [hdone, hcur] at h
    by_cases hnr :
        ((s.processes[s.current]).status != .runnable) = true ∨
          (s.processes[s.current]).result.isSome = true
    · simp [hnr] at h
      exact scheduleNext_preserves s s.current hs h
    · simp [hnr] at h
      have hp := hs.2.2.2 s.current hcur
      have ⟨hrun, hnone⟩ := status_runnable_of_not_deschedule _ _ hnr
      have hsz := runnable_stack_pos hp hrun hnone
      have hempty : ¬((s.processes[s.current]).stack = #[]) := by
        intro heq
        have hsz0 : (s.processes[s.current]).stack.size = 0 := by simp [heq]
        exact (Nat.ne_of_gt hsz) hsz0
      simp [hempty] at h
      have hfwf := runnable_top_WF hp hrun hnone
      have hipok :
          ¬(((s.processes[s.current]).stack[
              (s.processes[s.current]).stack.size - 1]!).function.code.size ≤
            ((s.processes[s.current]).stack[
              (s.processes[s.current]).stack.size - 1]!).ip) := by
        have := hfwf.2.2.1; omega
      simp [hipok] at h
      split at h
      · cases h
      · rename_i s1 hsi
        have hs1 : State.WF s1 :=
          stepInstr_preserves s (s.processes[s.current])
            ((s.processes[s.current]).stack[(s.processes[s.current]).stack.size - 1]!)
            _
            hs hp hfwf hnone hrun hsz rfl rfl hsi
        -- clock tick after a successful instruction
        have hs1c : State.WF { s1 with clock := s1.clock + 1 } := clock_preserves s1 _ hs1
        simp [afterInstr] at h
        split at h
        · cases h; exact hs1c
        · split at h
          · exact scheduleNext_preserves _ s1.current hs1c h
          · cases h
            exact reductions_preserves _ (s1.reductions - 1) hs1c

/-! ## Multi-step `run` -/

/-- After a successful instruction, clock/reductions/`scheduleNext` keep WF. -/
theorem afterInstr_preserves (s s' : State)
    (hs : State.WF s) (h : afterInstr s = .ok s') : State.WF s' := by
  simp [afterInstr] at h
  split at h
  · cases h
    exact clock_preserves s (s.clock + 1) hs
  · split at h
    · exact scheduleNext_preserves { s with clock := s.clock + 1 } s.current
        (clock_preserves s (s.clock + 1) hs) h
    · cases h
      exact reductions_preserves { s with clock := s.clock + 1 } (s.reductions - 1)
        (clock_preserves s (s.clock + 1) hs)

/-- Preservation: successful `stepScheduled` stays well-formed. -/
theorem stepScheduled_preserves (choices : List State.ScheduleChoice) (s : State)
    {s' : State} {rest : List State.ScheduleChoice}
    (hs : State.WF s) (h : stepScheduled choices s = .ok (s', rest)) :
    State.WF s' := by
  by_cases hdone : s.result.isSome = true
  · simp [stepScheduled, hdone] at h
    rcases h with ⟨rfl, rfl⟩
    exact hs
  · have hr : s.result = none := by
      cases hx : s.result with
      | none => rfl
      | some _ => simp [Option.isSome, hx] at hdone
    have hcur := hs.2.2.1
    have hres : s.result.isSome = false := by simp [Option.isSome, hr]
    simp only [stepScheduled, hres, ↓reduceIte, hcur, ↓reduceDIte] at h
    by_cases hnr :
        ((s.processes[s.current]).status != .runnable) = true ∨
          (s.processes[s.current]).result.isSome = true
    · have hpark : ((s.processes[s.current]).status != .runnable ||
          (s.processes[s.current]).result.isSome) = true := by
        cases hnr with
        | inl hp => simp [hp]
        | inr hp => simp [hp]
      simp [hpark] at h
      cases hpop : State.popChoice choices with
      | mk c rest0 =>
        simp only [hpop] at h
        split at h
        · cases h
        · rename_i s1 hsch
          rcases h with ⟨rfl, rfl⟩
          exact scheduleNextWith_preserves s s.current c hs hsch
    · have hpark : ((s.processes[s.current]).status != .runnable ||
          (s.processes[s.current]).result.isSome) = false := by
        cases hst : (s.processes[s.current]).status != .runnable <;>
          cases hr' : (s.processes[s.current]).result.isSome <;>
            simp_all
      simp [hpark] at h
      have hp := hs.2.2.2 s.current hcur
      have ⟨hrun, hnone⟩ := status_runnable_of_not_deschedule _ _ hnr
      have hsz := runnable_stack_pos hp hrun hnone
      have hempty : ¬((s.processes[s.current]).stack = #[]) := by
        intro heq
        have hsz0 : (s.processes[s.current]).stack.size = 0 := by simp [heq]
        exact (Nat.ne_of_gt hsz) hsz0
      simp [hempty] at h
      have hfwf := runnable_top_WF hp hrun hnone
      have hipok :
          ¬(((s.processes[s.current]).stack[
              (s.processes[s.current]).stack.size - 1]!).function.code.size ≤
            ((s.processes[s.current]).stack[
              (s.processes[s.current]).stack.size - 1]!).ip) := by
        have := hfwf.2.2.1; omega
      simp [hipok] at h
      split at h
      · cases h
      · rename_i s1 hsi
        have hs1 : State.WF s1 :=
          stepInstr_preserves s (s.processes[s.current])
            ((s.processes[s.current]).stack[(s.processes[s.current]).stack.size - 1]!)
            _
            hs hp hfwf hnone hrun hsz rfl rfl hsi
        cases hpop : State.popChoice choices with
        | mk c rest0 =>
          simp only [hpop] at h
          split at h
          · cases h
          · rename_i s2 hai
            rcases h with ⟨rfl, rfl⟩
            exact afterInstrWith_preserves c s1 hs1 hai

/-- Well-formed states never fail `run` structurally (only fuel or non-structural errors). -/
theorem run_progress (fuel : Nat) (s : State) (hs : State.WF s) {e : StepError}
    (h : run fuel s = .error e) :
    e = .typeError "out of fuel" ∨ isStructuralError e = false := by
  induction fuel generalizing s with
  | zero =>
    simp [run] at h
    left; cases h; rfl
  | succ fuel ih =>
    simp [run] at h
    cases hr : s.result with
    | some _ => simp [hr] at h; exact nomatch h
    | none =>
      simp [hr] at h
      cases hs' : step s with
      | error e' =>
        simp [hs'] at h
        cases h
        right
        have hp := step_progress s hs hr
        simpa [hs'] using hp
      | ok s' =>
        simp [hs'] at h
        exact ih s' (step_preserves s s' hs hs') h

/-- Multi-step dual of `step_preserves`: a successful `run` witnesses a WF state
whose machine result is the returned term. -/
theorem run_preserves (fuel : Nat) (s : State) (hs : State.WF s) {t : Term}
    (h : run fuel s = .ok t) :
    ∃ s', State.WF s' ∧ s'.result = some t := by
  induction fuel generalizing s with
  | zero =>
    simp [run] at h
  | succ fuel ih =>
    simp [run] at h
    cases hr : s.result with
    | some v =>
      simp [hr] at h
      cases h
      exact ⟨s, hs, by simp [hr]⟩
    | none =>
      simp [hr] at h
      cases hs' : step s with
      | error _ => simp [hs'] at h; exact nomatch h
      | ok s' =>
        simp [hs'] at h
        exact ih s' (step_preserves s s' hs hs') h

/-- `afterInstrWith` errors are never structural. -/
theorem afterInstrWith_error_not_structural (choice : State.ScheduleChoice) (s : State)
    {e : StepError} (h : afterInstrWith choice s = .error e) :
    isStructuralError e = false := by
  simp only [afterInstrWith] at h
  split at h
  · cases h
  · split at h
    · simp [scheduleNextWith_error_is_noRunnable _ _ choice h, isStructuralError]
    · cases h

/-- Progress: well-formed `stepScheduled` never fails structurally. -/
theorem stepScheduled_progress (choices : List State.ScheduleChoice) (s : State)
    (hs : State.WF s) (hr : s.result = none) {e : StepError}
    (h : stepScheduled choices s = .error e) :
    isStructuralError e = false := by
  have hres : s.result.isSome = false := by simp [Option.isSome, hr]
  have hcur := hs.2.2.1
  simp only [stepScheduled, hres, ↓reduceIte, hcur, ↓reduceDIte] at h
  by_cases hnr :
      ((s.processes[s.current]).status != .runnable) = true ∨
        (s.processes[s.current]).result.isSome = true
  · have hpark : ((s.processes[s.current]).status != .runnable ||
        (s.processes[s.current]).result.isSome) = true := by
      cases hnr with
      | inl hp => simp [hp]
      | inr hp => simp [hp]
    simp [hpark] at h
    cases hpop : State.popChoice choices with
    | mk c rest0 =>
      simp only [hpop] at h
      split at h
      · rename_i e' hsch
        cases h
        simp [scheduleNextWith_error_is_noRunnable s s.current c hsch, isStructuralError]
      · cases h
  · have hpark : ((s.processes[s.current]).status != .runnable ||
        (s.processes[s.current]).result.isSome) = false := by
      cases hst : (s.processes[s.current]).status != .runnable <;>
        cases hr' : (s.processes[s.current]).result.isSome <;>
          simp_all
    simp [hpark] at h
    have hp := hs.2.2.2 s.current hcur
    have ⟨hrun, hnone⟩ := status_runnable_of_not_deschedule _ _ hnr
    have hsz := runnable_stack_pos hp hrun hnone
    have hempty : ¬((s.processes[s.current]).stack = #[]) := by
      intro heq
      have hsz0 : (s.processes[s.current]).stack.size = 0 := by simp [heq]
      exact (Nat.ne_of_gt hsz) hsz0
    simp [hempty] at h
    have hfwf := runnable_top_WF hp hrun hnone
    have hipok :
        ¬(((s.processes[s.current]).stack[
            (s.processes[s.current]).stack.size - 1]!).function.code.size ≤
          ((s.processes[s.current]).stack[
            (s.processes[s.current]).stack.size - 1]!).ip) := by
      have := hfwf.2.2.1; omega
    simp [hipok] at h
    split at h
    · rename_i e' hsi
      cases h
      exact stepInstr_error_not_structural _ _ _ _ hsi
    · rename_i s1 hsi
      cases hpop : State.popChoice choices with
      | mk c rest0 =>
        simp only [hpop] at h
        split at h
        · rename_i e' hai
          cases h
          exact afterInstrWith_error_not_structural c s1 hai
        · cases h

/-- Multi-step dual of `stepScheduled_preserves`. -/
theorem runScheduled_preserves (fuel : Nat) (choices : List State.ScheduleChoice)
    (s : State) (hs : State.WF s) {t : Term}
    (h : runScheduled fuel choices s = .ok t) :
    ∃ s', State.WF s' ∧ s'.result = some t := by
  induction fuel generalizing s choices with
  | zero =>
    simp [runScheduled] at h
  | succ fuel ih =>
    simp [runScheduled] at h
    cases hr : s.result with
    | some v =>
      simp [hr] at h
      cases h
      exact ⟨s, hs, by simp [hr]⟩
    | none =>
      simp [hr] at h
      cases hs' : stepScheduled choices s with
      | error _ =>
        simp [hs'] at h
      | ok pair =>
        rcases pair with ⟨s', rest⟩
        simp [hs'] at h
        exact ih rest s' (stepScheduled_preserves choices s hs hs') h

/-- Well-formed states never fail `runScheduled` structurally (only fuel or non-structural). -/
theorem runScheduled_progress (fuel : Nat) (choices : List State.ScheduleChoice)
    (s : State) (hs : State.WF s) {e : StepError}
    (h : runScheduled fuel choices s = .error e) :
    e = .typeError "out of fuel" ∨ isStructuralError e = false := by
  induction fuel generalizing s choices with
  | zero =>
    simp [runScheduled] at h
    left; cases h; rfl
  | succ fuel ih =>
    simp [runScheduled] at h
    cases hr : s.result with
    | some _ =>
      simp [hr] at h
      exact nomatch h
    | none =>
      simp [hr] at h
      cases hs' : stepScheduled choices s with
      | error e' =>
        simp [hs'] at h
        cases h
        right
        exact stepScheduled_progress choices s hs hr hs'
      | ok pair =>
        rcases pair with ⟨s', rest⟩
        simp [hs'] at h
        exact ih rest s' (stepScheduled_preserves choices s hs hs') h

/-- Empty choice tape: `stepScheduled` agrees with ordinary `step`. -/
theorem stepScheduled_nil_eq_step (s : State) :
    stepScheduled ([] : List State.ScheduleChoice) s =
      match step s with
      | .ok s' => .ok (s', [])
      | .error e => .error e := by
  by_cases hdone : s.result.isSome = true
  · simp [stepScheduled, step, hdone]
  · have hr : s.result = none := by
      cases hx : s.result with
      | none => rfl
      | some _ => simp [Option.isSome, hx] at hdone
    have hres : s.result.isSome = false := by simp [Option.isSome, hr]
    by_cases hcur : s.current < s.processes.size
    · simp only [stepScheduled, step, hres, ↓reduceIte, hcur, ↓reduceDIte]
      by_cases hpark :
          ((s.processes[s.current]).status != .runnable ||
            (s.processes[s.current]).result.isSome) = true
      · cases hsch : State.scheduleNext s s.current with
        | error e =>
          simp [hpark, State.popChoice, scheduleNextWith_roundRobin, hsch]
        | ok s' =>
          simp [hpark, State.popChoice, scheduleNextWith_roundRobin, hsch]
      · simp [hpark]
        by_cases hempty : (s.processes[s.current]).stack = #[]
        · simp [hempty]
        · simp [hempty]
          by_cases hip :
              ((s.processes[s.current]).stack[
                (s.processes[s.current]).stack.size - 1]!).function.code.size ≤
              ((s.processes[s.current]).stack[
                (s.processes[s.current]).stack.size - 1]!).ip
          · simp [hip]
          · have hip' :
                ¬(((s.processes[s.current]).stack[
                    (s.processes[s.current]).stack.size - 1]!).function.code.size ≤
                  ((s.processes[s.current]).stack[
                    (s.processes[s.current]).stack.size - 1]!).ip) := hip
            simp [hip']
            cases hsi :
                stepInstr s (s.processes[s.current])
                  ((s.processes[s.current]).stack[
                    (s.processes[s.current]).stack.size - 1]!)
                  (((s.processes[s.current]).stack[
                      (s.processes[s.current]).stack.size - 1]!).function.code[
                    ((s.processes[s.current]).stack[
                      (s.processes[s.current]).stack.size - 1]!).ip]!) with
            | error e =>
              simp [hsi]
            | ok s1 =>
              simp [hsi, State.popChoice, afterInstrWith_roundRobin]
              cases hai : afterInstr s1 with
              | error e => simp [hai]
              | ok s2 => simp [hai]
    · have hcur' : ¬(s.current < s.processes.size) := hcur
      simp [stepScheduled, step, hres, hcur']

/-- Empty choice tape: `runScheduled` agrees with ordinary `run`. -/
theorem runScheduled_nil_eq_run (fuel : Nat) (s : State) :
    runScheduled fuel ([] : List State.ScheduleChoice) s = run fuel s := by
  induction fuel generalizing s with
  | zero =>
    simp [runScheduled, run]
  | succ fuel ih =>
    simp only [runScheduled, run]
    cases s.result with
    | some _ => rfl
    | none =>
      rw [stepScheduled_nil_eq_step]
      cases step s with
      | error _ => rfl
      | ok s' =>
        change runScheduled fuel [] s' = run fuel s'
        exact ih s'

/-- If `initial` succeeds, a successful `runModule` witnesses a WF state with that result. -/
theorem runModule_preserves (m : Module) (fuel cap : Nat)
    (hm : Module.WF m) (hcap : 0 < cap) {t : Term}
    (h : runModule m fuel cap = .ok t) :
    ∃ s', State.WF s' ∧ s'.result = some t := by
  cases hi : State.initial m cap with
  | error _ => simp [runModule, hi] at h; exact nomatch h
  | ok s =>
    simp [runModule, hi] at h
    exact run_preserves fuel s (initial_WF m cap hm hcap hi) h

/-! ## Idle-drain observational: machine result is `Heap.toTerm` -/

/-- `raiseValue` publishes machine result only via `scheduleNext`. -/
theorem raiseValue_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (exc : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : raiseValue s p frame exc = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [raiseValue] at h
  split at h
  · -- uncaught: exit + propagateExit + scheduleNext
    refine scheduleNext_result_is_toTerm _ _ ?_ h ht
    rw [propagateExit_result, setCurrentProcess_result, hsr]
  · -- caught: handlers path — result unchanged
    split at h
    · exact nomatch h
    · split at h
      · exact nomatch h
      · cases h
        simp [setCurrentProcess_result, hsr] at ht

/-- `Process.exit/2` publishes only via `raiseValue` or `scheduleNext`. -/
theorem processExit_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (pidV reason : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : processExit s p frame dest pidV reason = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [processExit] at h
  split at h
  · rename_i pid
    split at h
    · exact raiseValue_result_is_toTerm s p frame reason hsr h ht
    · refine scheduleNext_result_is_toTerm _ _ ?_ h ht
      rw [forceExitPid_result, setCurrentProcess_result, hsr]
  · exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht

/-- After a successful instruction, a newly published machine result is a `toTerm`. -/
theorem afterInstr_result_is_toTerm
    (s : State) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : afterInstr s = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (v : Value), t = Heap.toTerm heap v := by
  simp [afterInstr] at h
  have hsr' : ({ s with clock := s.clock + 1 } : State).result = none := by
    simpa [clock_result] using hsr
  split at h
  · cases h
    simp [hsr] at ht
  · split at h
    · exact scheduleNext_result_is_toTerm _ _ hsr' h ht
    · cases h
      simp [hsr] at ht

theorem loadLit_result (s : State) (p : Process) (frame : Frame) (reg : Reg) (lit : Term) :
    (loadLit s p frame reg lit).result = s.result := by
  simp [loadLit, setCurrentProcess_result]

theorem makeTuple_result (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (elems : Array Value) :
    (makeTuple s p frame dest elems).result = s.result := by
  simp [makeTuple, setCurrentProcess_result]

theorem makeFun_result (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (funName : FunName) (caps : Array Value) :
    (makeFun s p frame dest funName caps).result = s.result := by
  simp [makeFun, setCurrentProcess_result]

theorem getListRest_result (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (elems : Array Value) (index : Nat) :
    (getListRest s p frame dest elems index).result = s.result := by
  simp [getListRest, setCurrentProcess_result]

theorem mapPut_result (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (mapV key val : Value) {s' : State}
    (h : mapPut s p frame dest mapV key val = some s') :
    s'.result = s.result := by
  simp [mapPut] at h
  split at h
  · split at h
    · cases h; exact setCurrentProcess_result _ _
    · exact nomatch h
  · exact nomatch h

theorem cons_result (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (head tail : Value) {s' : State}
    (h : cons s p frame dest head tail = some s') :
    s'.result = s.result := by
  simp [cons] at h
  split at h
  · split at h
    · cases h; exact setCurrentProcess_result _ _
    · exact nomatch h
  · exact nomatch h

theorem processFlag_result (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (flagV valV : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : processFlag s p frame dest flagV valV = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [processFlag] at h
  split at h
  · cases h; simp [setCurrentProcess_result, hsr] at ht
  · exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht

theorem processHibernate_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : processHibernate s p frame dest = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [processHibernate] at h; cases h
  simp [setCurrentProcess_result, hsr] at ht

theorem etsTables_result (s : State) (tables : Array EtsTable) :
    ({ s with etsTables := tables } : State).result = s.result := rfl

theorem etsNew_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : etsNew s p frame dest = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [etsNew, State.etsNew] at h; cases h
  simp [setCurrentProcess_result, hsr] at ht

theorem finishWithTerm_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg) (lit : Term)
    {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : finishWithTerm s p frame dest lit = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [finishWithTerm] at h; cases h
  simp [setCurrentProcess_result, hsr] at ht

theorem etsNew2_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (nameV typeV : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : etsNew2 s p frame dest nameV typeV = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [etsNew2] at h
  cases hty : Heap.toTerm p.heap typeV with
  | atom ty =>
    simp [hty] at h
    cases hk : Ets.kindOfAtom ty with
    | none =>
      simp [hk] at h
      exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
    | some kind =>
      simp [hk] at h
      cases hn : Heap.toTerm p.heap nameV with
      | nil =>
        simp [hn] at h
        cases hnew : State.etsNewNamed s p.pid none kind with
        | none =>
          simp [hnew] at h
          exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
        | some st =>
          simp [hnew] at h; cases h
          have hs1r : st.1.result = none := by
            unfold State.etsNewNamed at hnew
            split at hnew
            · split at hnew
              · exact nomatch hnew
              · cases hnew; simpa [etsTables_result] using hsr
            · cases hnew; simpa [etsTables_result] using hsr
          simp [setCurrentProcess_result, hs1r] at ht
      | atom n =>
        simp [hn] at h
        cases hnew : State.etsNewNamed s p.pid (some n) kind with
        | none =>
          simp [hnew] at h
          exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
        | some st =>
          simp [hnew] at h; cases h
          have hs1r : st.1.result = none := by
            unfold State.etsNewNamed at hnew
            split at hnew
            · split at hnew
              · exact nomatch hnew
              · cases hnew; simpa [etsTables_result] using hsr
            · cases hnew; simpa [etsTables_result] using hsr
          simp [setCurrentProcess_result, hs1r] at ht
      | _ =>
        simp [hn] at h
        exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
  | _ =>
    simp [hty] at h
    exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht

theorem etsInsert_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (tabV keyV valV : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : etsInsert s p frame dest tabV keyV valV = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [etsInsert] at h
  cases hr : State.etsResolve s (Heap.toTerm p.heap tabV) with
  | none =>
    simp [hr] at h
    exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
  | some tid =>
    simp [hr] at h
    cases hins : State.etsInsert s tid (Heap.toTerm p.heap keyV)
        (Heap.toTerm p.heap valV) with
    | none =>
      simp [hins] at h
      exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
    | some s1 =>
      simp [hins] at h; cases h
      have hs1r : s1.result = none := by
        unfold State.etsInsert at hins
        split at hins
        · split at hins
          · exact nomatch hins
          · cases hins; simpa [etsTables_result] using hsr
        · exact nomatch hins
      simp [setCurrentProcess_result, hs1r] at ht

theorem etsLookup_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (tabV keyV : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : etsLookup s p frame dest tabV keyV = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [etsLookup] at h
  cases hr : State.etsResolve s (Heap.toTerm p.heap tabV) with
  | none =>
    simp [hr] at h
    exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
  | some tid =>
    simp [hr] at h
    cases hl : State.etsLookup s tid (Heap.toTerm p.heap keyV) with
    | none =>
      simp [hl] at h
      exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
    | some vals =>
      simp [hl] at h
      exact finishWithTerm_result_is_toTerm s p frame dest (.list vals) hsr h ht

theorem etsDelete_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (tabV keyV : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : etsDelete s p frame dest tabV keyV = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [etsDelete] at h
  cases hr : State.etsResolve s (Heap.toTerm p.heap tabV) with
  | none =>
    simp [hr] at h
    exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
  | some tid =>
    simp [hr] at h
    cases hd : State.etsDelete s tid (Heap.toTerm p.heap keyV) with
    | none =>
      simp [hd] at h
      exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
    | some s1 =>
      simp [hd] at h; cases h
      have hs1r : s1.result = none := by
        unfold State.etsDelete at hd
        split at hd
        · split at hd
          · exact nomatch hd
          · cases hd; simpa [etsTables_result] using hsr
        · exact nomatch hd
      simp [setCurrentProcess_result, hs1r] at ht

theorem etsDeleteObject_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (tabV objV : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : etsDeleteObject s p frame dest tabV objV = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [etsDeleteObject] at h
  cases hr : State.etsResolve s (Heap.toTerm p.heap tabV) with
  | none =>
    simp [hr] at h
    exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
  | some tid =>
    simp [hr] at h
    cases ho : Heap.toTerm p.heap objV with
    | tuple elems =>
      simp [ho] at h
      split at h
      · cases hd : State.etsDeleteObject s tid (elems[0]'(by omega)) (elems[1]'(by omega)) with
        | none =>
          simp [hd] at h
          exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
        | some s1 =>
          simp [hd] at h; cases h
          have hs1r : s1.result = none := by
            unfold State.etsDeleteObject at hd
            split at hd
            · split at hd
              · exact nomatch hd
              · cases hd; simpa [etsTables_result] using hsr
            · exact nomatch hd
          simp [setCurrentProcess_result, hs1r] at ht
      · exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
    | _ =>
      simp [ho] at h
      exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht

theorem etsHeir_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (tabV heirV : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : etsHeir s p frame dest tabV heirV = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [etsHeir] at h
  cases hr : State.etsResolve s (Heap.toTerm p.heap tabV) with
  | none =>
    simp [hr] at h
    exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
  | some tid =>
    simp [hr] at h
    cases hh : State.etsHeir s tid (Heap.toTerm p.heap heirV) with
    | none =>
      simp [hh] at h
      exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
    | some s1 =>
      simp [hh] at h; cases h
      have hs1r : s1.result = none := by
        unfold State.etsHeir at hh
        split at hh
        · split at hh
          · exact nomatch hh
          · split at hh
            · split at hh
              · cases hh; simpa [etsTables_result] using hsr
              · exact nomatch hh
            · split at hh
              · split at hh
                · cases hh; simpa [etsTables_result] using hsr
                · exact nomatch hh
              · exact nomatch hh
            · exact nomatch hh
        · exact nomatch hh
      simp [setCurrentProcess_result, hs1r] at ht

theorem etsFirst_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (tabV : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : etsFirst s p frame dest tabV = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [etsFirst] at h
  cases hr : State.etsResolve s (Heap.toTerm p.heap tabV) with
  | none =>
    simp [hr] at h
    exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
  | some tid =>
    simp [hr] at h
    cases hf : State.etsFirst s tid with
    | none =>
      simp [hf] at h
      exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
    | some k =>
      simp [hf] at h
      exact finishWithTerm_result_is_toTerm s p frame dest k hsr h ht

theorem etsNext_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (tabV keyV : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : etsNext s p frame dest tabV keyV = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [etsNext] at h
  cases hr : State.etsResolve s (Heap.toTerm p.heap tabV) with
  | none =>
    simp [hr] at h
    exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
  | some tid =>
    simp [hr] at h
    cases hn : State.etsNext s tid (Heap.toTerm p.heap keyV) with
    | none =>
      simp [hn] at h
      exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
    | some k =>
      simp [hn] at h
      exact finishWithTerm_result_is_toTerm s p frame dest k hsr h ht

theorem etsGiveAway_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (tabV pidV dataV : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : etsGiveAway s p frame dest tabV pidV dataV = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [etsGiveAway] at h
  cases hr : State.etsResolve s (Heap.toTerm p.heap tabV) with
  | none =>
    simp [hr] at h
    exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
  | some tid =>
    simp [hr] at h
    cases hpid : Heap.toTerm p.heap pidV with
    | pid toPid =>
      simp [hpid] at h
      cases hg : State.etsGiveAway s tid p.pid toPid (Heap.toTerm p.heap dataV) with
      | none =>
        simp [hg] at h
        exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
      | some s1 =>
        simp [hg] at h; cases h
        have hs1r : s1.result = none := by
          have := notifyEtsTransfer_result
          unfold State.etsGiveAway at hg
          split at hg
          · split at hg
            · exact nomatch hg
            · split at hg
              · exact nomatch hg
              · split at hg
                · exact nomatch hg
                · cases hg
                  simpa [notifyEtsTransfer_result, etsTables_result] using hsr
          · exact nomatch hg
        simp [setCurrentProcess_result, hs1r] at ht
    | _ =>
      simp [hpid] at h
      exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht

theorem etsMatchObject_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (tabV patV : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : etsMatchObject s p frame dest tabV patV = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [etsMatchObject] at h
  cases hr : State.etsResolve s (Heap.toTerm p.heap tabV) with
  | none =>
    simp [hr] at h
    exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
  | some tid =>
    simp [hr] at h
    cases hl : State.etsMatchObject s tid (Heap.toTerm p.heap patV) with
    | none =>
      simp [hl] at h
      exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
    | some objs =>
      simp [hl] at h
      exact finishWithTerm_result_is_toTerm s p frame dest (.list objs) hsr h ht

theorem etsSelect_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (tabV specV : Value) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : etsSelect s p frame dest tabV specV = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [etsSelect] at h
  cases hr : State.etsResolve s (Heap.toTerm p.heap tabV) with
  | none =>
    simp [hr] at h
    exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
  | some tid =>
    simp [hr] at h
    cases hl : State.etsSelect s tid (Heap.toTerm p.heap specV) with
    | none =>
      simp [hl] at h
      exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
    | some r =>
      simp [hl] at h
      match r with
      | .error () =>
        exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
      | .ok vals =>
        exact finishWithTerm_result_is_toTerm s p frame dest (.list vals) hsr h ht

/-- `call` case of `stepInstr_result_is_toTerm`. -/
theorem call_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (dest : Reg) (funName : FunName)
    (argRegs : Array Reg) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : stepInstr s p frame (.call dest funName argRegs) = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  simp [stepInstr] at h
  by_cases hmp : funName = "map_put/3"
  · simp [hmp] at h
    by_cases har : (readArgs! frame argRegs).size = 3
    · simp only [har, ↓reduceIte, ite_false] at h
      cases hmpu : mapPut s p frame dest (readArgs! frame argRegs)[0]!
          (readArgs! frame argRegs)[1]! (readArgs! frame argRegs)[2]! with
      | some s1 =>
        simp [hmpu] at h; cases h
        have := mapPut_result s p frame dest _ _ _ hmpu
        simp [this, hsr] at ht
      | none =>
        simp [hmpu] at h
        exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
    · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
  · simp [hmp] at h
    by_cases hc : funName = "cons/2"
    · simp [hc] at h
      by_cases har : (readArgs! frame argRegs).size = 2
      · simp only [har, ↓reduceIte, ite_false] at h
        cases hco : cons s p frame dest (readArgs! frame argRegs)[0]!
            (readArgs! frame argRegs)[1]! with
        | some s1 =>
          simp [hco] at h; cases h
          have := cons_result s p frame dest _ _ hco
          simp [this, hsr] at ht
        | none =>
          simp [hco] at h
          exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
      · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
    · simp [hc] at h
      by_cases hflag : funName = "Process.flag/2"
      · simp [hflag] at h
        by_cases har : (readArgs! frame argRegs).size = 2
        · simp only [har, ↓reduceIte, ite_false] at h
          exact processFlag_result s p frame dest _ _ hsr h ht
        · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
      · simp [hflag] at h
        by_cases hex : funName = "Process.exit/2"
        · simp [hex] at h
          by_cases har : (readArgs! frame argRegs).size = 2
          · simp only [har, ↓reduceIte, ite_false] at h
            exact processExit_result_is_toTerm s p frame dest _ _ hsr h ht
          · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
        · simp [hex] at h
          by_cases hhib : funName = "Process.hibernate/0"
          · simp [hhib] at h
            split at h
            · exact processHibernate_result_is_toTerm s p frame dest hsr h ht
            · exact nomatch h
          · simp [hhib] at h
            by_cases hetsn : funName = "ets_new/0"
            · simp [hetsn] at h
              split at h
              · exact etsNew_result_is_toTerm s p frame dest hsr h ht
              · exact nomatch h
            · simp [hetsn] at h
              by_cases hetsn2 : funName = "ets_new/2"
              · simp [hetsn2] at h
                by_cases har : (readArgs! frame argRegs).size = 2
                · simp only [har, ↓reduceIte, ite_false] at h
                  exact etsNew2_result_is_toTerm s p frame dest
                    (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                    hsr h ht
                · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
              · simp [hetsn2] at h
                by_cases hetsi : funName = "ets_insert/3"
                · simp [hetsi] at h
                  by_cases har : (readArgs! frame argRegs).size = 3
                  · simp only [har, ↓reduceIte, ite_false] at h
                    exact etsInsert_result_is_toTerm s p frame dest
                      (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                      (readArgs! frame argRegs)[2]! hsr h ht
                  · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
                · simp [hetsi] at h
                  by_cases hetsl : funName = "ets_lookup/2"
                  · simp [hetsl] at h
                    by_cases har : (readArgs! frame argRegs).size = 2
                    · simp only [har, ↓reduceIte, ite_false] at h
                      exact etsLookup_result_is_toTerm s p frame dest
                        (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                        hsr h ht
                    · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
                  · simp [hetsl] at h
                    by_cases hetsd : funName = "ets_delete/2"
                    · simp [hetsd] at h
                      by_cases har : (readArgs! frame argRegs).size = 2
                      · simp only [har, ↓reduceIte, ite_false] at h
                        exact etsDelete_result_is_toTerm s p frame dest
                          (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                          hsr h ht
                      · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
                    · simp [hetsd] at h
                      by_cases hetsdo : funName = "ets_delete_object/2"
                      · simp [hetsdo] at h
                        by_cases har : (readArgs! frame argRegs).size = 2
                        · simp only [har, ↓reduceIte, ite_false] at h
                          exact etsDeleteObject_result_is_toTerm s p frame dest
                            (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                            hsr h ht
                        · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
                      · simp [hetsdo] at h
                        by_cases hetsm : funName = "ets_match_object/2"
                        · simp [hetsm] at h
                          by_cases har : (readArgs! frame argRegs).size = 2
                          · simp only [har, ↓reduceIte, ite_false] at h
                            exact etsMatchObject_result_is_toTerm s p frame dest
                              (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                              hsr h ht
                          · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
                        · simp [hetsm] at h
                          by_cases hetss : funName = "ets_select/2"
                          · simp [hetss] at h
                            by_cases har : (readArgs! frame argRegs).size = 2
                            · simp only [har, ↓reduceIte, ite_false] at h
                              exact etsSelect_result_is_toTerm s p frame dest
                                (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                                hsr h ht
                            · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
                          · simp [hetss] at h
                            by_cases hetsh : funName = "ets_heir/2"
                            · simp [hetsh] at h
                              by_cases har : (readArgs! frame argRegs).size = 2
                              · simp only [har, ↓reduceIte, ite_false] at h
                                exact etsHeir_result_is_toTerm s p frame dest
                                  (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                                  hsr h ht
                              · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
                            · simp [hetsh] at h
                              by_cases hetsf : funName = "ets_first/1"
                              · simp [hetsf] at h
                                by_cases har : (readArgs! frame argRegs).size = 1
                                · simp only [har, ↓reduceIte, ite_false] at h
                                  exact etsFirst_result_is_toTerm s p frame dest
                                    (readArgs! frame argRegs)[0]! hsr h ht
                                · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
                              · simp [hetsf] at h
                                by_cases hetsn : funName = "ets_next/2"
                                · simp [hetsn] at h
                                  by_cases har : (readArgs! frame argRegs).size = 2
                                  · simp only [har, ↓reduceIte, ite_false] at h
                                    exact etsNext_result_is_toTerm s p frame dest
                                      (readArgs! frame argRegs)[0]!
                                      (readArgs! frame argRegs)[1]! hsr h ht
                                  · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
                                · simp [hetsn] at h
                                  by_cases hetsg : funName = "ets_give_away/3"
                                  · simp [hetsg] at h
                                    by_cases har : (readArgs! frame argRegs).size = 3
                                    · simp only [har, ↓reduceIte, ite_false] at h
                                      exact etsGiveAway_result_is_toTerm s p frame dest
                                        (readArgs! frame argRegs)[0]!
                                        (readArgs! frame argRegs)[1]!
                                        (readArgs! frame argRegs)[2]! hsr h ht
                                    · simp only [har, ↓reduceIte, ite_true] at h; exact nomatch h
                                  · simp [hetsg] at h
                                    by_cases hmref : funName = "make_ref/0"
                                    · simp [hmref] at h
                                      split at h
                                      · cases h
                                        simp [setCurrentProcess_result, nextRef_result, hsr] at ht
                                      · exact nomatch h
                                    · simp [hmref] at h
                                      by_cases htu : isMakeTupleName funName = true
                                      · simp [htu] at h; cases h
                                        simp [makeTuple_result, hsr] at ht
                                      · simp [htu] at h
                                        by_cases hbi : isBuiltinName funName = true
                                        · simp [hbi] at h
                                          cases hb : builtin p.heap p.pid funName
                                              (readArgs! frame argRegs) with
                                          | error _ => simp [hb] at h
                                          | badarg =>
                                            simp [hb] at h
                                            exact raiseValue_result_is_toTerm s p frame
                                              (.atom "badarg") hsr h ht
                                          | ok v =>
                                            simp [hb] at h; cases h
                                            simp [setCurrentProcess_result, hsr] at ht
                                        · simp [hbi] at h
                                          cases hff : s.module.findFunction funName with
                                          | none => simp [hff] at h
                                          | some callee =>
                                            simp [hff] at h
                                            by_cases har :
                                                callee.arity = (readArgs! frame argRegs).size
                                            · simp [har] at h; cases h
                                              simp [setCurrentProcess_result, hsr] at ht
                                            · simp [har] at h; exact nomatch h

/-- `stepInstr` publishes machine result only via `scheduleNext` (as `toTerm`). -/
theorem stepInstr_result_is_toTerm
    (s : State) (p : Process) (frame : Frame) (instr : Instr) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : stepInstr s p frame instr = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  cases instr with
  | loadLit reg lit =>
    simp [stepInstr] at h; cases h
    simp [loadLit_result, hsr] at ht
  | move dest src =>
    simp [stepInstr] at h; cases h
    simp [setCurrentProcess_result, hsr] at ht
  | call dest funName argRegs =>
    exact call_result_is_toTerm s p frame dest funName argRegs hsr h ht
  | return_ reg =>
    simp [stepInstr] at h
    by_cases hsz : p.stack.size = 1
    · simp [hsz] at h
      refine scheduleNext_result_is_toTerm _ _ ?_ h ht
      rw [propagateExit_result, setCurrentProcess_result, hsr]
    · simp [hsz] at h
      split at h
      · exact nomatch h
      · cases h; simp [setCurrentProcess_result, hsr] at ht
  | halt reg =>
    simp [stepInstr] at h
    refine scheduleNext_result_is_toTerm _ _ ?_ h ht
    rw [propagateExit_result, setCurrentProcess_result, hsr]
  | jump target =>
    simp [stepInstr] at h; cases h
    simp [setCurrentProcess_result, hsr] at ht
  | jumpIfEq target reg lit =>
    simp [stepInstr] at h; cases h
    simp [setCurrentProcess_result, hsr] at ht
  | getTupleElem dest tupleReg index =>
    simp [stepInstr] at h
    split at h
    all_goals (
      try split at h
      all_goals (
        try split at h
        all_goals (
          try { cases h; simp [setCurrentProcess_result, hsr] at ht }
          try { exact nomatch h }
        )
      )
    )
  | isTag dest reg tag =>
    simp [stepInstr] at h; cases h
    simp [setCurrentProcess_result, hsr] at ht
  | spawn dest funName argRegs =>
    simp [stepInstr] at h
    split at h
    all_goals (
      try split at h
      all_goals (
        try { cases h; simp [setCurrentProcess_result, hsr] at ht }
        try { exact nomatch h }
      )
    )
  | send pidReg msgReg =>
    simp [stepInstr] at h
    split at h
    all_goals (
      try split at h
      all_goals (
        try { cases h; simp [setCurrentProcess_result, hsr] at ht }
        try { exact nomatch h }
      )
    )
  | recv dest =>
    simp [stepInstr] at h
    split at h
    · cases h; simp [setCurrentProcess_result, hsr] at ht
    · refine scheduleNext_result_is_toTerm _ _ ?_ h ht
      rw [setCurrentProcess_result, hsr]
  | getListElem dest listReg index =>
    simp [stepInstr] at h
    split at h
    all_goals (
      try split at h
      all_goals (
        try split at h
        all_goals (
          try { cases h; simp [setCurrentProcess_result, hsr] at ht }
          try { exact nomatch h }
        )
      )
    )
  | getListRest dest listReg index =>
    simp [stepInstr] at h
    split at h
    all_goals (
      try split at h
      all_goals (
        try split at h
        all_goals (
          try { cases h; simp [getListRest_result, hsr] at ht }
          try { exact nomatch h }
        )
      )
    )
  | enterTry rescueIp excReg =>
    simp [stepInstr] at h; cases h
    simp [setCurrentProcess_result, hsr] at ht
  | leaveTry =>
    simp [stepInstr] at h
    split at h
    · exact nomatch h
    · cases h; simp [setCurrentProcess_result, hsr] at ht
  | raise reg =>
    simp [stepInstr] at h
    exact raiseValue_result_is_toTerm s p frame (getReg! frame reg) hsr h ht
  | recvPeek dest indexReg empty =>
    simp [stepInstr] at h
    split at h
    · split at h
      · exact nomatch h
      · split at h <;> (cases h; simp [setCurrentProcess_result, hsr] at ht)
    · exact nomatch h
  | recvDrop indexReg =>
    simp [stepInstr] at h
    split at h
    · split at h
      · exact nomatch h
      · split at h
        · exact nomatch h
        · cases h; simp [setCurrentProcess_result, hsr] at ht
    · exact nomatch h
  | wait retry after timeout =>
    simp [stepInstr] at h
    split at h
    · cases h; simp [setCurrentProcess_result, hsr] at ht
    · split at h
      · split at h
        · cases h; simp [setCurrentProcess_result, hsr] at ht
        · refine scheduleNext_result_is_toTerm _ _ ?_ h ht
          rw [setCurrentProcess_result, hsr]
      · cases hr : resolveWaitTimeout frame timeout with
        | error _ =>
          simp [hr, Bind.bind, Except.bind] at h
        | ok ticks? =>
          simp [hr, Bind.bind, Except.bind] at h
          cases hto : ticks? with
          | some n =>
            cases n with
            | zero =>
              simp [hto] at h; cases h
              simp [setCurrentProcess_result, hsr] at ht
            | succ n =>
              simp [hto] at h
              refine scheduleNext_result_is_toTerm _ _ ?_ h ht
              rw [setCurrentProcess_result, hsr]
          | none =>
            simp [hto] at h
            refine scheduleNext_result_is_toTerm _ _ ?_ h ht
            rw [setCurrentProcess_result, hsr]
  | link pidReg =>
    simp [stepInstr] at h
    split at h
    · have := linkWith_result _ _ h
      simp [this, setCurrentProcess_result, hsr] at ht
    · exact nomatch h
  | monitor dest pidReg =>
    simp [stepInstr] at h
    split at h
    · have := monitorWith_result _ _ _ h
      simp [this, nextRef_result, setCurrentProcess_result, hsr] at ht
    · exact nomatch h
  | demonitor refReg =>
    simp [stepInstr] at h
    split at h
    · have := demonitorWith_result _ _ h
      simp [this, setCurrentProcess_result, hsr] at ht
    · exact nomatch h
  | makeFun dest funName caps =>
    simp [stepInstr] at h; cases h
    simp [makeFun_result, hsr] at ht
  | apply dest funReg argRegs =>
    simp [stepInstr] at h
    split at h
    · split at h
      · split at h
        · exact nomatch h
        · split at h
          · cases h; simp [setCurrentProcess_result, hsr] at ht
          · exact nomatch h
      · exact nomatch h
    · exact nomatch h
  | loadFile dest pathReg =>
    simp [stepInstr] at h
    split at h
    · exact raiseValue_result_is_toTerm s p frame (.atom "enoent") hsr h ht
    · exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
  | applyMfa dest modReg funReg argRegs =>
    simp [stepInstr] at h
    cases hmod : getReg! frame modReg with
    | atom modName =>
      simp [hmod] at h
      cases hfun : getReg! frame funReg with
      | atom funName =>
        simp [hfun] at h
        generalize hff0 : s.module.findFunction
            (modName ++ "." ++ funName ++ "/" ++
              toString (readArgs! frame argRegs).size) = oFind at h
        cases oFind with
        | none =>
          simp [hff0] at h
          exact raiseValue_result_is_toTerm s p frame (.atom "undef") hsr h ht
        | some callee =>
          simp [hff0] at h
          split at h
          · cases h; simp [setCurrentProcess_result, hsr] at ht
          · exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
      | nil | bool _ | int _ | float _ | string _ | bitstring _ | pid _ | reference _ | ref _ =>
        simp [hfun] at h
        exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht
    | nil | bool _ | int _ | float _ | string _ | bitstring _ | pid _ | reference _ | ref _ =>
      simp [hmod] at h
      exact raiseValue_result_is_toTerm s p frame (.atom "badarg") hsr h ht

/-- Successful `step` that publishes a machine result does so as `Heap.toTerm`. -/
theorem step_result_is_toTerm
    (s : State) {s' : State} {t : Term}
    (hsr : s.result = none)
    (h : step s = .ok s')
    (ht : s'.result = some t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  have hres : s.result.isSome = false := by simp [Option.isSome, hsr]
  unfold step at h
  simp [hres] at h
  by_cases hcur : s.current < s.processes.size
  · simp [hcur] at h
    by_cases hnr :
        ((s.processes[s.current]).status != .runnable) = true ∨
          (s.processes[s.current]).result.isSome = true
    · simp [hnr] at h
      exact scheduleNext_result_is_toTerm _ _ hsr h ht
    · simp [hnr] at h
      by_cases hempty : (s.processes[s.current]).stack = #[]
      · simp [hempty] at h
      · simp [hempty] at h
        by_cases hipok :
            ((s.processes[s.current]).stack[
              (s.processes[s.current]).stack.size - 1]!).function.code.size ≤
            ((s.processes[s.current]).stack[
              (s.processes[s.current]).stack.size - 1]!).ip
        · simp [hipok] at h
        · simp [hipok] at h
          cases hsi : stepInstr s (s.processes[s.current])
              ((s.processes[s.current]).stack[
                (s.processes[s.current]).stack.size - 1]!)
              ((s.processes[s.current]).stack[
                (s.processes[s.current]).stack.size - 1]!).function.code[
                ((s.processes[s.current]).stack[
                  (s.processes[s.current]).stack.size - 1]!).ip]! with
          | error _ => simp [hsi] at h
          | ok s1 =>
            simp [hsi] at h
            cases hr1 : s1.result with
            | none =>
              exact afterInstr_result_is_toTerm s1 hr1 h ht
            | some t1 =>
              have hpub :
                  ∃ (heap : Heap) (val : Value), t1 = Heap.toTerm heap val :=
                stepInstr_result_is_toTerm s (s.processes[s.current])
                  ((s.processes[s.current]).stack[
                    (s.processes[s.current]).stack.size - 1]!)
                  _
                  hsr hsi (by simp [hr1])
              simp [afterInstr] at h
              have hisome : (s1.result.isSome = true) := by
                simp [Option.isSome, hr1]
              simp [hisome] at h
              cases h
              have htt : t = t1 := by
                have hr := ht
                -- clock bump preserves result
                change s1.result = some t at hr
                simpa [hr1] using hr.symm
              simpa [htt] using hpub
  · simp [hcur] at h

/-- Once the machine result is set, further `run` fuel returns that same term. -/
theorem run_of_result (fuel : Nat) (s : State) {t t' : Term}
    (hr : s.result = some t) (h : run fuel s = .ok t') :
    t' = t := by
  cases fuel with
  | zero => simp [run] at h
  | succ fuel =>
    unfold run at h
    simp [hr] at h
    -- h : pure t = Except.ok t'  ⇒  t = t'
    injection h with heq
    exact heq.symm

/-- If `run` succeeds from a state with no machine result, the term is a `toTerm`. -/
theorem run_result_is_toTerm (fuel : Nat) (s : State)
    (hsr : s.result = none) {t : Term}
    (h : run fuel s = .ok t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  induction fuel generalizing s with
  | zero => simp [run] at h
  | succ fuel ih =>
    simp [run, hsr] at h
    cases hs' : step s with
    | error _ => simp [hs'] at h; exact nomatch h
    | ok s' =>
      simp [hs', Bind.bind, Except.bind] at h
      cases hr' : s'.result with
      | some t' =>
        have hpub :=
          step_result_is_toTerm (t := t') s hsr hs' (by simp [hr'])
        have htt : t = t' :=
          run_of_result (fuel := fuel) (s := s') (t := t') (t' := t) hr' h
        simpa [htt] using hpub
      | none =>
        exact ih s' hr' h

/-- `State.initial` always starts with no machine result. -/
theorem initial_result_none (m : Module) (cap : Nat) {s : State}
    (h : State.initial m cap = .ok s) : s.result = none := by
  simp [State.initial] at h
  split at h
  all_goals (
    try split at h
    all_goals (
      try { cases h; rfl }
      try { exact nomatch h }
    )
  )

/-- `runModule` from `initial` publishes a `toTerm` machine result. -/
theorem runModule_result_is_toTerm (m : Module) (fuel cap : Nat) {t : Term}
    (h : runModule m fuel cap = .ok t) :
    ∃ (heap : Heap) (val : Value), t = Heap.toTerm heap val := by
  cases hi : State.initial m cap with
  | error _ => simp [runModule, hi] at h; exact nomatch h
  | ok s =>
    simp [runModule, hi] at h
    exact run_result_is_toTerm fuel s (initial_result_none m cap hi) h

/-- `afterInstr` errors are never structural (`scheduleNext` → `noRunnable`). -/
theorem afterInstr_error_not_structural (s : State) {e : StepError}
    (h : afterInstr s = .error e) : isStructuralError e = false := by
  simp [afterInstr] at h
  split at h
  · cases h
  · split at h
    · simp [scheduleNext_error_is_noRunnable _ _ h, isStructuralError]
    · cases h

/-- Classify `finishLoadFile` errors under peek (non-structural). -/
theorem finishLoadFile_error_not_structural (s : State) (dest : Reg) (contents : String)
    {e : StepError} (hs : State.WF s) {path : String}
    (hpeek : peekLoadFile s = some (dest, path))
    (h : finishLoadFile s dest contents = .error e) :
    isStructuralError e = false := by
  have hspec := peekLoadFile_spec s dest path hs hpeek
  have hcur := hs.2.2.1
  have hsz := hspec.2.2.2.1
  simp [finishLoadFile, hcur, show 0 < (s.processes[s.current]).stack.size from hsz] at h
  cases hdec : Json.Decode.fromString contents with
  | error _ =>
    simp [hdec] at h
    exact raiseValue_error_not_structural _ _ _ _ h
  | ok incoming =>
    simp [hdec] at h
    by_cases hok :
        Module.checkWF (Module.installModules s.module incoming) = true ∧
          State.processesModuleOkB (Module.installModules s.module incoming) s = true
    · simp [hok, ↓reduceIte] at h
    · simp [hok, ↓reduceIte] at h
      exact raiseValue_error_not_structural _ _ _ _ h

theorem raiseLoadAtCurrent_error_not_structural (s : State) (reason : String)
    {e : StepError} (hs : State.WF s) {dest : Reg} {path : String}
    (hpeek : peekLoadFile s = some (dest, path))
    (h : raiseLoadAtCurrent s reason = .error e) :
    isStructuralError e = false := by
  have hspec := peekLoadFile_spec s dest path hs hpeek
  have hcur := hs.2.2.1
  have hsz := hspec.2.2.2.1
  simp [raiseLoadAtCurrent, hcur, show 0 < (s.processes[s.current]).stack.size from hsz] at h
  exact raiseValue_error_not_structural _ _ _ _ h

theorem interpretLoadFile_error_not_structural (s : State) (dest : Reg) (read : Option String)
    {e : StepError} (hs : State.WF s) {path : String}
    (hpeek : peekLoadFile s = some (dest, path))
    (h : interpretLoadFile s dest read = .error e) :
    isStructuralError e = false := by
  cases read with
  | some contents =>
    simp [interpretLoadFile] at h
    exact finishLoadFile_error_not_structural s dest contents hs hpeek h
  | none =>
    simp [interpretLoadFile] at h
    exact raiseLoadAtCurrent_error_not_structural s "enoent" hs hpeek h

/-- Pure FS runner preserves well-formedness. -/
theorem runIOStatePure_preserves (fs : String → Option String) (fuel : Nat)
    (s s' : State) (hs : State.WF s)
    (h : runIOStatePure fs fuel s = .ok s') : State.WF s' := by
  induction fuel generalizing s s' with
  | zero => exact nomatch h
  | succ fuel ih =>
    unfold runIOStatePure at h
    cases hr : s.result with
    | some _ =>
      simp [hr] at h
      cases h
      exact hs
    | none =>
      simp [hr] at h
      cases hpeek : peekLoadFile s with
      | some pair =>
        cases pair with
        | mk dest path =>
          simp [hpeek] at h
          have hspec := peekLoadFile_spec s dest path hs hpeek
          have hstat := hspec.2.1
          have hpres := hspec.2.2.1
          have ⟨pathReg, hcode, _⟩ := hspec.2.2.2.2.2
          have hfwf := runnable_top_WF (hs.2.2.2 s.current hs.2.2.1) hstat hpres
          have hip :
              ((s.processes[s.current]'hs.2.2.1).stack[
                (s.processes[s.current]'hs.2.2.1).stack.size - 1]!).ip + 1 <
              ((s.processes[s.current]'hs.2.2.1).stack[
                (s.processes[s.current]'hs.2.2.1).stack.size - 1]!).function.code.size :=
            ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode rfl
          cases hload : interpretLoadFile s dest (fs path) with
          | error _ => simp [hload] at h
          | ok s1 =>
            simp [hload] at h
            have hs1 : State.WF s1 :=
              interpretLoadFile_preserves s dest (fs path) hs hstat hpres hip hload
            cases ha : afterInstr s1 with
            | error _ => simp [ha] at h
            | ok s2 =>
              simp [ha] at h
              exact ih s2 s' (afterInstr_preserves s1 s2 hs1 ha) h
      | none =>
        simp [hpeek] at h
        cases hs1 : step s with
        | error _ => simp [hs1] at h
        | ok s1 =>
          simp [hs1] at h
          exact ih s1 s' (step_preserves s s1 hs hs1) h

/-- Pure FS runner errors are only fuel or non-structural. -/
theorem runIOStatePure_progress (fs : String → Option String) (fuel : Nat)
    (s : State) (hs : State.WF s) {e : StepError}
    (h : runIOStatePure fs fuel s = .error e) :
    e = .typeError "out of fuel" ∨ isStructuralError e = false := by
  induction fuel generalizing s with
  | zero =>
    left
    simp [runIOStatePure] at h
    cases h; rfl
  | succ fuel ih =>
    unfold runIOStatePure at h
    cases hr : s.result with
    | some _ => simp [hr] at h
    | none =>
      simp [hr] at h
      cases hpeek : peekLoadFile s with
      | some pair =>
        cases pair with
        | mk dest path =>
          simp [hpeek] at h
          have hspec := peekLoadFile_spec s dest path hs hpeek
          have hstat := hspec.2.1
          have hpres := hspec.2.2.1
          have ⟨pathReg, hcode, _⟩ := hspec.2.2.2.2.2
          have hfwf := runnable_top_WF (hs.2.2.2 s.current hs.2.2.1) hstat hpres
          have hip :
              ((s.processes[s.current]'hs.2.2.1).stack[
                (s.processes[s.current]'hs.2.2.1).stack.size - 1]!).ip + 1 <
              ((s.processes[s.current]'hs.2.2.1).stack[
                (s.processes[s.current]'hs.2.2.1).stack.size - 1]!).function.code.size :=
            ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode rfl
          cases hload : interpretLoadFile s dest (fs path) with
          | error e' =>
            simp [hload] at h; cases h
            right
            exact interpretLoadFile_error_not_structural s dest (fs path) hs hpeek hload
          | ok s1 =>
            simp [hload] at h
            have hs1 : State.WF s1 :=
              interpretLoadFile_preserves s dest (fs path) hs hstat hpres hip hload
            cases ha : afterInstr s1 with
            | error e' =>
              simp [ha] at h; cases h
              right
              exact afterInstr_error_not_structural s1 ha
            | ok s2 =>
              simp [ha] at h
              exact ih s2 (afterInstr_preserves s1 s2 hs1 ha) h
      | none =>
        simp [hpeek] at h
        cases hs1 : step s with
        | error e' =>
          simp [hs1] at h
          cases h
          right
          have hp := step_progress s hs hr
          simpa [hs1] using hp
        | ok s1 =>
          simp [hs1] at h
          exact ih s1 (step_preserves s s1 hs hs1) h

/-- If `initial` succeeds, `runModule` errors are only fuel or non-structural. -/
theorem runModule_progress (m : Module) (fuel cap : Nat)
    (hm : Module.WF m) (hcap : 0 < cap) {s : State} {e : StepError}
    (hi : State.initial m cap = .ok s)
    (h : runModule m fuel cap = .error e) :
    e = .typeError "out of fuel" ∨ isStructuralError e = false := by
  simp [runModule, hi] at h
  exact run_progress fuel s (initial_WF m cap hm hcap hi) h

theorem addMain_has_entry :
    (addMainModule.findFunction addMainModule.entry).isSome := by
  native_decide

theorem tryRescue_has_entry :
    (tryRescueModule.findFunction tryRescueModule.entry).isSome := by
  native_decide

#eval Step.runModule addMainModule (fuel := 100)

#guard (match Step.runModule tryRescueModule (fuel := 100) with
  | .ok (.int 3) => true
  | _ => false)

end Step
end Autumn
