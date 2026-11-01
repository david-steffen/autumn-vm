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

/-! ## IR induction + program-level law

Case analysis on `Instr` is the structural induction principle over opcodes.
WF functions yield per-instruction `regsOk` / jump-target facts without
unfolding the stepper.
-/

/-- Prop-level induction over IR instructions (case split on every constructor). -/
theorem instr_induction (P : Instr → Prop)
    (loadLit : ∀ r l, P (.loadLit r l))
    (move : ∀ d s, P (.move d s))
    (call : ∀ d f a, P (.call d f a))
    (return_ : ∀ r, P (.return_ r))
    (halt : ∀ r, P (.halt r))
    (jump : ∀ t, P (.jump t))
    (jumpIfEq : ∀ t r l, P (.jumpIfEq t r l))
    (getTupleElem : ∀ d t i, P (.getTupleElem d t i))
    (isTag : ∀ d r t, P (.isTag d r t))
    (spawn : ∀ d f a, P (.spawn d f a))
    (send : ∀ p m, P (.send p m))
    (recv : ∀ d, P (.recv d))
    (getListElem : ∀ d t i, P (.getListElem d t i))
    (getListRest : ∀ d t i, P (.getListRest d t i))
    (enterTry : ∀ ip e, P (.enterTry ip e))
    (leaveTry : P .leaveTry)
    (raise : ∀ r, P (.raise r))
    (recvPeek : ∀ d i e, P (.recvPeek d i e))
    (recvDrop : ∀ i, P (.recvDrop i))
    (wait : ∀ r a t, P (.wait r a t))
    (link : ∀ p, P (.link p))
    (monitor : ∀ d p, P (.monitor d p))
    (demonitor : ∀ r, P (.demonitor r))
    (makeFun : ∀ d f c, P (.makeFun d f c))
    (apply : ∀ d f a, P (.apply d f a))
    (loadFile : ∀ d p, P (.loadFile d p))
    (applyMfa : ∀ d m f a, P (.applyMfa d m f a))
    (i : Instr) : P i := by
  cases i with
  | loadLit r l => exact loadLit r l
  | move d s => exact move d s
  | call d f a => exact call d f a
  | return_ r => exact return_ r
  | halt r => exact halt r
  | jump t => exact jump t
  | jumpIfEq t r l => exact jumpIfEq t r l
  | getTupleElem d t i => exact getTupleElem d t i
  | isTag d r t => exact isTag d r t
  | spawn d f a => exact spawn d f a
  | send p m => exact send p m
  | recv d => exact recv d
  | getListElem d t i => exact getListElem d t i
  | getListRest d t i => exact getListRest d t i
  | enterTry ip e => exact enterTry ip e
  | leaveTry => exact leaveTry
  | raise r => exact raise r
  | recvPeek d i e => exact recvPeek d i e
  | recvDrop i => exact recvDrop i
  | wait r a t => exact wait r a t
  | link p => exact link p
  | monitor d p => exact monitor d p
  | demonitor r => exact demonitor r
  | makeFun d f c => exact makeFun d f c
  | apply d f a => exact apply d f a
  | loadFile d p => exact loadFile d p
  | applyMfa d m f a => exact applyMfa d m f a

/-- Every instruction in a WF function is register-safe. -/
theorem wf_instr_regsOk {m : Module} {f : Function}
    (hwf : Function.WF m f) (i : Fin f.code.size) :
    Instr.regsOk f.locals (f.code[i]) = true :=
  (hwf.2.2.2 i).1

/-- Every instruction in a WF function has an in-range jump target. -/
theorem wf_instr_jumpOk {m : Module} {f : Function}
    (hwf : Function.WF m f) (i : Fin f.code.size) :
    Instr.jumpTargetOk f.code.size (f.code[i]) = true :=
  (hwf.2.2.2 i).2.1

/-- WF functions end in a terminal opcode (`return` / `halt` / `raise`). -/
theorem wf_code_terminal {m : Module} {f : Function}
    (hwf : Function.WF m f) :
    Instr.isTerminal (f.code[f.code.size - 1]!) = true :=
  hwf.2.2.1

/-- Program-level observational law: Lean-authored `addMainModule` observes `3`. -/
theorem addMain_observes_three :
    (match Step.runModule addMainModule (fuel := 100) with
      | .ok (.int 3) => true
      | _ => false) =
      true := by
  native_decide

/-- Mix-image gate on the same demo module. -/
theorem addMain_image_WF : Module.WF addMainModule :=
  lowered_image_WF addMainModule (by native_decide)

#guard (match Step.runModule addMainModule (fuel := 100) with
  | .ok (.int 3) => true
  | _ => false)

end Meaning
end Autumn
