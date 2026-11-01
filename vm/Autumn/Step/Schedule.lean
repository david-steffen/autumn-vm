import Autumn.Step
import Autumn.State.Lemmas

namespace Autumn
namespace Step

/-! # Schedule-quantified runners

`State.ScheduleChoice` / `scheduleNextWith` live on `State`. This module provides
runners that consume a choice tape at **top-level** schedule points (`step`
deschedule + `afterInstr` preemption).

Park/exit inside instructions honor a choice via `stepInstrWith` (used by
observational laws / prefer-at-park demos). The multi-step `stepScheduled` tape
still runs `stepInstr` (round-robin park/exit) so preserve/progress stay on the
existing RR tower; full tape-through-park remains a thin follow-up.

Default `run` / smoke paths are unchanged.

Public schedule lemmas: `covers_*`, `afterInstrWith_preserves`,
`stepScheduled_deschedule_roundRobin` (see also `stepScheduled_preserves` in
`Step/Lemmas`). Names are listed in `vm/tests/proof_surface.names`.
-/

open State

/-- After a successful instruction, bump clock; on preemption use `choice`. -/
def afterInstrWith (choice : ScheduleChoice) (s : State) : Except StepError State :=
  let s := { s with clock := s.clock + 1 }
  if s.result.isSome then
    .ok s
  else if s.reductions ≤ 1 then
    scheduleNextWith s s.current choice
  else
    .ok { s with reductions := s.reductions - 1 }

/-- One machine step; schedule points consume from `choices` (empty ⇒ round-robin). -/
def stepScheduled (choices : List ScheduleChoice) (s : State) :
    Except StepError (State × List ScheduleChoice) :=
  if s.result.isSome then
    .ok (s, choices)
  else if hcur : s.current < s.processes.size then
    let p := s.processes[s.current]
    if p.status != .runnable || p.result.isSome then
      let (c, rest) := popChoice choices
      match scheduleNextWith s s.current c with
      | .error e => .error e
      | .ok s' => .ok (s', rest)
    else if p.stack.isEmpty then
      .error .emptyStack
    else
      let frame := p.stack[p.stack.size - 1]!
      let code := frame.function.code
      if frame.ip ≥ code.size then
        .error (.badIp frame.ip code.size)
      else
        match stepInstr s p frame code[frame.ip]! with
        | .error e => .error e
        | .ok s1 =>
          let (c, rest) := popChoice choices
          match afterInstrWith c s1 with
          | .error e => .error e
          | .ok s2 => .ok (s2, rest)
  else
    .error .noRunnable

/-- Like `run`, but consumes `choices` at top-level schedule points. -/
def runScheduled (fuel : Nat) (choices : List ScheduleChoice) (s : State) :
    Except StepError Term :=
  match fuel with
  | 0 => throw (.typeError "out of fuel")
  | fuel + 1 =>
    match s.result with
    | some v => pure v
    | none =>
      match stepScheduled choices s with
      | .error e => .error e
      | .ok (s', rest) => runScheduled fuel rest s'

/-- Apply a chain of `scheduleNextWith` (no instruction execution). -/
def applyScheduleChoices (choices : List ScheduleChoice) (s : State) (fromIdx : Nat) :
    Except StepError State :=
  match choices with
  | [] => .ok s
  | c :: rest => do
    let s ← scheduleNextWith s fromIdx c
    applyScheduleChoices rest s s.current

/-- Every process index appears as `.prefer` at least once. -/
def covers (choices : List ScheduleChoice) (nprocs : Nat) : Prop :=
  ∀ i, i < nprocs → choices.any (fun c => c == .prefer i) = true

@[simp] theorem covers_nil (nprocs : Nat) :
    covers ([] : List ScheduleChoice) nprocs ↔ nprocs = 0 := by
  constructor
  · intro h
    cases nprocs with
    | zero => rfl
    | succ _ =>
      have := h 0 (by omega)
      simp at this
  · intro h; subst h; intro i hi; omega

theorem covers_cons_prefer (idx : Nat) (rest : List ScheduleChoice) (nprocs : Nat)
    (hrest : covers rest nprocs) :
    covers (.prefer idx :: rest) nprocs := by
  intro i hi
  rw [List.any_cons, Bool.or_eq_true]
  exact Or.inr (hrest i hi)

theorem covers_mono (choices : List ScheduleChoice) {n m : Nat}
    (hle : n ≤ m) (h : covers choices m) : covers choices n := by
  intro i hi
  exact h i (Nat.lt_of_lt_of_le hi hle)

@[simp] theorem afterInstrWith_roundRobin (s : State) :
    afterInstrWith .roundRobin s = afterInstr s := by
  simp [afterInstrWith, afterInstr, scheduleNextWith_roundRobin]

theorem afterInstrWith_preserves (choice : ScheduleChoice) (s : State) {s'}
    (hs : State.WF s) (h : afterInstrWith choice s = .ok s') : State.WF s' := by
  simp only [afterInstrWith] at h
  have hs1 : State.WF { s with clock := s.clock + 1 } := clock_preserves s _ hs
  split at h
  · cases h; exact hs1
  · split at h
    · exact scheduleNextWith_preserves _ _ choice hs1 h
    · cases h; exact reductions_preserves _ (s.reductions - 1) hs1

/-- Empty choice tape at a deschedule matches ordinary `scheduleNext`. -/
theorem stepScheduled_deschedule_roundRobin (s : State)
    (hnone : s.result.isNone = true)
    (hcur : s.current < s.processes.size)
    (hpark : ((s.processes[s.current]).status != .runnable) = true ∨
        (s.processes[s.current]).result.isSome = true)
    {s'} (h : State.scheduleNext s s.current = .ok s') :
    stepScheduled [] s = .ok (s', []) := by
  have hres : s.result.isSome = false := by
    cases hr : s.result <;> simp_all
  simp only [stepScheduled, hres, ↓reduceIte, hcur, ↓reduceDIte]
  have hpark' : ((s.processes[s.current]).status != .runnable ||
      (s.processes[s.current]).result.isSome) = true := by
    cases hpark with
    | inl hp => simp [hp]
    | inr hp => simp [hp]
  simp [hpark', popChoice, scheduleNextWith_roundRobin, h]

end Step
end Autumn
