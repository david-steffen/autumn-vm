import Autumn.Step.Lemmas
import Autumn.Examples

namespace Autumn
namespace Obs
namespace Schedule

/-! # Observational schedule laws (choice-tape API)

Lean-authored `drainSiblingsModule` (same idea as `drain_siblings` smoke expect
`0`). Laws stay observational: result equality under tapes — not a GenServer
refinement. No committed `.bc.json`.
-/

theorem drainSiblings_has_entry :
    (drainSiblingsModule.findFunction drainSiblingsModule.entry).isSome := by
  native_decide

theorem drainSiblings_checkWF : Module.checkWF drainSiblingsModule = true := by
  native_decide

/-- Empty tape matches ordinary `run` on an initial drain-siblings state. -/
theorem drainSiblings_nil_tape_eq_run (fuel : Nat)
    {s : State} (_hi : State.initial drainSiblingsModule 64 = .ok s) :
    Step.runScheduled fuel ([] : List State.ScheduleChoice) s = Step.run fuel s :=
  Step.runScheduled_nil_eq_run fuel s

/-- Prefer worker then main, repeated (covers a 2-process world). -/
def drainPreferTape : List State.ScheduleChoice :=
  List.replicate 32 (.prefer 1) ++ List.replicate 32 (.prefer 0)

theorem drainPreferTape_covers_two : Step.covers drainPreferTape 2 := by
  intro i hi
  have : i = 0 ∨ i = 1 := by omega
  cases this with
  | inl h => subst h; native_decide
  | inr h => subst h; native_decide

/-- Round-robin `run`, empty `runScheduled`, and a prefer tape all yield `0`. -/
theorem drainSiblings_tapes_observe_zero :
    (match State.initial drainSiblingsModule 64 with
      | .ok s =>
        (match Step.run 1000 s with
          | .ok (.int 0) => true
          | _ => false) &&
          (match Step.runScheduled 1000 ([] : List State.ScheduleChoice) s with
            | .ok (.int 0) => true
            | _ => false) &&
          (match Step.runScheduled 1000 drainPreferTape s with
            | .ok (.int 0) => true
            | _ => false)
      | .error _ => false) =
      true := by
  native_decide

#guard (match State.initial drainSiblingsModule 64 with
  | .ok s =>
    match Step.runScheduled 1000 drainPreferTape s with
    | .ok (.int 0) => true
    | _ => false
  | _ => false)

/-! ## Prefer-at-park (`stepInstrWith`)

`stepInstrWith` threads `ScheduleChoice` into `recv`/`wait`/exit schedule sites.
After `spawn`, the empty `recv` parks the entry process; `.prefer 1` selects the
worker. -/

theorem parkRecv_checkWF : Module.checkWF parkRecvModule = true := by
  native_decide

/-- After spawn, empty `recv` with `.prefer 1` schedules the worker (index 1). -/
theorem park_recv_prefer_selects_worker :
    (match State.initial parkRecvModule 64 with
      | .ok s0 =>
        (match Step.step s0 with
          | .ok s1 =>
            let p := s1.processes[s1.current]!
            let frame := p.stack[p.stack.size - 1]!
            (match Step.stepInstrWith (.prefer 1) s1 p frame (.recv 1) with
              | .ok s2 => decide (s2.current == 1)
              | _ => false)
          | _ => false)
      | .error _ => false) =
      true := by
  native_decide

#guard (match State.initial parkRecvModule 64 with
  | .ok s0 =>
    match Step.step s0 with
    | .ok s1 =>
      let p := s1.processes[s1.current]!
      let frame := p.stack[p.stack.size - 1]!
      match Step.stepInstrWith (.prefer 1) s1 p frame (.recv 1) with
      | .ok s2 => s2.current == 1
      | _ => false
    | _ => false
  | _ => false)

end Schedule
end Obs
end Autumn
