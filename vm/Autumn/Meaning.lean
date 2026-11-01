import Autumn.Step.Lemmas

namespace Autumn
namespace Meaning

/-! # Meaning layers (verified-compiler sketch)

Interfaces for purity layers described in `vm/MEANING.md`. `sorry`-free stubs:
layer tags + stated intended equalities that reduce to existing public lemmas.
Unfinished program-level proofs stay out of the preserve surface.
-/

/-- Law level: pure term → sequential one-step → concurrent multi-step. -/
inductive LawLevel where
  | pure
  | sequential
  | concurrent
  deriving Repr, BEq, Inhabited

/-- Concurrent runner: ordinary `run` (deterministic schedule). -/
abbrev ConcurrentRun := Nat → State → Except StepError Term

/-- Concurrent runner with an explicit schedule choice tape. -/
abbrev ConcurrentRunScheduled :=
  Nat → List State.ScheduleChoice → State → Except StepError Term

/-- Empty tape is the ordinary concurrent runner. -/
theorem concurrent_nil_tape (fuel : Nat) (s : State) :
    (Step.runScheduled fuel ([] : List State.ScheduleChoice) s : Except StepError Term) =
      Step.run fuel s :=
  Step.runScheduled_nil_eq_run fuel s

/-- Successful concurrent runs stay in the WF image (witness state). -/
theorem concurrent_run_preserves (fuel : Nat) (s : State) (hs : State.WF s) {t : Term}
    (h : Step.run fuel s = .ok t) :
    ∃ s', State.WF s' ∧ s'.result = some t :=
  Step.run_preserves fuel s hs h

/-- Successful taped runs stay in the WF image. -/
theorem concurrent_runScheduled_preserves (fuel : Nat)
    (choices : List State.ScheduleChoice) (s : State) (hs : State.WF s) {t : Term}
    (h : Step.runScheduled fuel choices s = .ok t) :
    ∃ s', State.WF s' ∧ s'.result = some t :=
  Step.runScheduled_preserves fuel choices s hs h

/-- Mix image gate: `Module.checkWF` is the Lean-side contract for lowered JSON. -/
theorem lowered_image_WF (m : Module) (h : Module.checkWF m = true) : Module.WF m :=
  Module.checkWF_sound m h

end Meaning
end Autumn
