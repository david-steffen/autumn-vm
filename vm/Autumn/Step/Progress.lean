import Autumn.State.Lemmas
import Autumn.Step

namespace Autumn
namespace Step

/-! # Progress helpers (public proof surface)

Shared by `Step.ProgressInstr`. Prefer `builtin_error_not_structural`,
`raiseValue_error_not_structural`, and frame/IP helpers over unfolding
`builtin` / `raiseValue`. See `AGENTS.md` (“Public proof surface”).
-/

theorem setReg!_WF (f : Frame) (r : Reg) (v : Value) (m : Module)
    (hwf : Frame.WF m f) : Frame.WF m (setReg! f r v) := by
  dsimp [setReg!]
  refine ⟨hwf.1, ?_, hwf.2.2.1, hwf.2.2.2⟩
  simpa [Array.size_setIfInBounds] using hwf.2.1

theorem bumpIp_frame (f : Frame) (m : Module) (hwf : Frame.WF m f)
    (h : f.ip + 1 < f.function.code.size) :
    Frame.WF m { f with ip := f.ip + 1 } :=
  ⟨hwf.1, hwf.2.1, h, hwf.2.2.2⟩

theorem setIp_frame (f : Frame) (ip : Nat) (m : Module) (hwf : Frame.WF m f)
    (h : ip < f.function.code.size) :
    Frame.WF m { f with ip := ip } :=
  ⟨hwf.1, hwf.2.1, h, hwf.2.2.2⟩


/-- Common path: replace top frame (same function/retDest) then write into `s.current`. -/
theorem apply_top_frame_preserves (s : State) (p : Process) (frame' : Frame)
    (hs : State.WF s) (hp : Process.WF s.module p)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (hsz : 0 < p.stack.size) (hfwf : Frame.WF s.module frame')
    (hsameFun : frame'.function = (p.stack[p.stack.size - 1]!).function)
    (hsameRet : frame'.retDest = (p.stack[p.stack.size - 1]!).retDest) :
    State.WF (s.setCurrentProcess (State.setCurrentFrame p frame')) :=
  setCurrentProcess_WF s _ hs
    (setCurrentFrame_sameMeta_WF s.module p frame' hres hstat hsz hp hfwf hsameFun hsameRet)


theorem status_runnable_of_not_deschedule (st : ProcStatus) (r : Option Value)
    (hnr : ¬(((st != .runnable) = true) ∨ (r.isSome = true))) :
    st = .runnable ∧ r = none := by
  cases st with
  | runnable =>
    cases r with
    | none => exact ⟨rfl, rfl⟩
    | some _ => simp [Option.isSome] at hnr
  | waiting =>
    have ht : (ProcStatus.waiting != .runnable) = true := rfl
    simp [ht] at hnr
  | exited =>
    have ht : (ProcStatus.exited != .runnable) = true := rfl
    simp [ht] at hnr


/-! ## Progress: `stepInstr` errors are never structural -/

theorem builtin_error_not_structural {heap : Heap} {selfPid : Nat} {name : FunName}
    {args : Array Value} {e : StepError}
    (herr : builtin heap selfPid name args = .error e) : isStructuralError e = false := by
  unfold builtin at herr
  split at herr
  all_goals (
    try split at herr
    all_goals (
      try split at herr
      all_goals (
        try split at herr
        all_goals (
          try split at herr
          all_goals (
            try split at herr
            all_goals (
              try split at herr
              all_goals (
                first
                | injection herr with heq; subst heq; rfl
                | exact False.elim (floatBinop_ne_error _ _ _ e herr)
                | cases herr
                | exact nomatch herr
              )
            )
          )
        )
      )
    )
  )

/-- `raiseValue` errors are never structural (shared by `raise`, badarg, load_file, …). -/
theorem raiseValue_error_not_structural
    (s : State) (p : Process) (frame : Frame) (v : Value) {e : StepError}
    (herr : raiseValue s p frame v = .error e) :
    isStructuralError e = false := by
  cases hEmp : p.handlers.isEmpty with
  | false =>
    simp [raiseValue, hEmp] at herr
    split at herr
    · injection herr with heq; subst heq; rfl
    · split at herr
      · injection herr with heq; subst heq; rfl
      · exact nomatch herr
  | true =>
    simp [raiseValue, hEmp] at herr
    exact (scheduleNext_error_is_noRunnable _ _ herr) ▸ rfl


end Step
end Autumn
