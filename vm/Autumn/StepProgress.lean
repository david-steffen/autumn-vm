import Autumn.StateLemmas
import Autumn.Step

namespace Autumn
namespace Step

/-! # Progress: stepInstr errors are never structural -/

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
                try { injection herr with heq; subst heq; rfl }
                try { cases herr }
                try { exact nomatch herr }
              )
            )
          )
        )
      )
    )
  )

theorem mapPut_error_not_structural
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (mapV key val : Value) {e : StepError}
    (herr : mapPut s p frame dest mapV key val = .error e) :
    isStructuralError e = false := by
  unfold mapPut at herr
  split at herr
  · split at herr
    · exact nomatch herr
    · cases herr; rfl
  · cases herr; rfl

theorem cons_error_not_structural
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (head tail : Value) {e : StepError}
    (herr : cons s p frame dest head tail = .error e) :
    isStructuralError e = false := by
  unfold cons at herr
  split at herr
  · split at herr
    · exact nomatch herr
    · cases herr; rfl
  · cases herr; rfl

theorem stepInstr_error_not_structural
    (s : State) (p : Process) (frame : Frame) (instr : Instr) {e : StepError}
    (herr : stepInstr s p frame instr = .error e) :
    isStructuralError e = false := by
  cases instr with
  | loadLit reg lit =>
    simp [stepInstr] at herr; exact nomatch herr
  | move dest src =>
    simp [stepInstr] at herr; exact nomatch herr
  | call dest funName argRegs =>
    simp [stepInstr] at herr
    by_cases hmp : funName = "map_put/3"
    · simp [hmp] at herr
      by_cases har : (readArgs! frame argRegs).size = 3
      · simp [har] at herr
        exact mapPut_error_not_structural _ _ _ _ _ _ _ herr
      · simp [har] at herr; cases herr; rfl
    · simp [hmp] at herr
      by_cases hc : funName = "cons/2"
      · simp [hc] at herr
        by_cases har : (readArgs! frame argRegs).size = 2
        · simp [har] at herr
          exact cons_error_not_structural _ _ _ _ _ _ herr
        · simp [har] at herr; cases herr; rfl
      · simp [hc] at herr
        by_cases hmref : funName = "make_ref/0"
        · simp [hmref] at herr
          split at herr
          · exact nomatch herr
          · cases herr; rfl
        · simp [hmref] at herr
          by_cases htu : isMakeTupleName funName = true
          · simp [htu] at herr; exact nomatch herr
          · simp [htu] at herr
            by_cases hbi : isBuiltinName funName = true
            · simp [hbi] at herr
              cases hb : builtin p.heap p.pid funName (readArgs! frame argRegs) with
              | ok v => simp [hb] at herr; exact nomatch herr
              | error e' =>
                simp [hb] at herr
                cases herr
                exact builtin_error_not_structural hb
            · simp [hbi] at herr
              split at herr
              · -- `some callee` then arity check
                split at herr
                · exact nomatch herr
                · cases herr; rfl
              · cases herr; rfl
  | return_ reg =>
    simp [stepInstr] at herr
    by_cases hsz : p.stack.size = 1
    · simp [hsz] at herr
      split at herr
      · exact nomatch herr
      · exact (scheduleNext_error_is_noRunnable _ _ herr) ▸ rfl
    · simp [hsz] at herr
      split at herr
      · cases herr; rfl
      · exact nomatch herr
  | halt reg =>
    simp [stepInstr] at herr
    split at herr
    · exact nomatch herr
    · exact (scheduleNext_error_is_noRunnable _ _ herr) ▸ rfl
  | jump target =>
    simp [stepInstr] at herr; exact nomatch herr
  | jumpIfEq target reg lit =>
    simp [stepInstr] at herr; exact nomatch herr
  | enterTry rescueIp excReg =>
    simp [stepInstr] at herr; exact nomatch herr
  | leaveTry =>
    simp [stepInstr] at herr
    split at herr
    · injection herr with heq; subst heq; rfl
    · exact nomatch herr
  | raise reg =>
    simp [stepInstr, raiseValue] at herr
    split at herr
    · split at herr
      · exact nomatch herr
      · simp [scheduleNext_error_is_noRunnable _ _ herr, isStructuralError]
    · split at herr
      · injection herr with heq; subst heq; rfl
      · split at herr
        · injection herr with heq; subst heq; rfl
        · exact nomatch herr
  | loadFile dest pathReg =>
    simp [stepInstr] at herr
    split at herr
    · simp [raiseValue] at herr
      split at herr
      · split at herr
        · exact nomatch herr
        · simp [scheduleNext_error_is_noRunnable _ _ herr, isStructuralError]
      · split at herr
        · injection herr with heq; subst heq; rfl
        · split at herr
          · injection herr with heq; subst heq; rfl
          · exact nomatch herr
    · simp [raiseValue] at herr
      split at herr
      · split at herr
        · exact nomatch herr
        · simp [scheduleNext_error_is_noRunnable _ _ herr, isStructuralError]
      · split at herr
        · injection herr with heq; subst heq; rfl
        · split at herr
          · injection herr with heq; subst heq; rfl
          · exact nomatch herr
  | getTupleElem dest tupleReg index =>
    simp [stepInstr] at herr
    split at herr
    all_goals (
      try split at herr
      all_goals (
        try split at herr
        all_goals (
          try { injection herr with heq; subst heq; rfl }
          try { cases herr }
          try { exact nomatch herr }
        )
      )
    )
  | getListElem dest listReg index =>
    simp [stepInstr] at herr
    split at herr
    all_goals (
      try split at herr
      all_goals (
        try split at herr
        all_goals (
          try { injection herr with heq; subst heq; rfl }
          try { cases herr }
          try { exact nomatch herr }
        )
      )
    )
  | getListRest dest listReg index =>
    simp [stepInstr] at herr
    split at herr
    all_goals (
      try split at herr
      all_goals (
        try split at herr
        all_goals (
          try { injection herr with heq; subst heq; rfl }
          try { cases herr }
          try { exact nomatch herr }
        )
      )
    )
  | isTag dest reg tag =>
    simp [stepInstr] at herr; exact nomatch herr
  | spawn dest funName argRegs =>
    simp [stepInstr] at herr
    split at herr
    all_goals (
      try split at herr
      all_goals (
        try { injection herr with heq; subst heq; rfl }
        try { exact nomatch herr }
        try { cases herr }
      )
    )
  | send pidReg msgReg =>
    simp [stepInstr] at herr
    split at herr
    all_goals (
      try split at herr
      all_goals (
        try { injection herr with heq; subst heq; rfl }
        try { exact nomatch herr }
        try { cases herr }
      )
    )
  | recv dest =>
    simp [stepInstr] at herr
    split at herr
    · exact nomatch herr
    · simp [scheduleNext_error_is_noRunnable _ _ herr, isStructuralError]
  | recvPeek dest indexReg empty =>
    simp [stepInstr] at herr
    split at herr
    all_goals (
      try split at herr
      all_goals (
        try split at herr
        all_goals (
          try { injection herr with heq; subst heq; rfl }
          try { exact nomatch herr }
          try { cases herr }
        )
      )
    )
  | recvDrop indexReg =>
    simp [stepInstr] at herr
    split at herr
    all_goals (
      try split at herr
      all_goals (
        try split at herr
        all_goals (
          try { injection herr with heq; subst heq; rfl }
          try { exact nomatch herr }
          try { cases herr }
        )
      )
    )
  | wait retry after timeout =>
    simp [stepInstr] at herr
    by_cases hmb : 0 < p.mailbox.size
    · simp [hmb] at herr; exact nomatch herr
    · simp [hmb] at herr
      cases hd : p.waitDeadline with
      | some d =>
        simp [hd] at herr
        by_cases hle : d ≤ s.clock
        · simp [hle] at herr; exact nomatch herr
        · simp [hle] at herr
          exact (scheduleNext_error_is_noRunnable _ _ herr) ▸ rfl
      | none =>
        simp [hd] at herr
        cases hto : timeout with
        | some n =>
          cases n with
          | zero =>
            simp [hto] at herr; exact nomatch herr
          | succ n =>
            simp [hto] at herr
            exact (scheduleNext_error_is_noRunnable _ _ herr) ▸ rfl
        | none =>
          simp [hto] at herr
          exact (scheduleNext_error_is_noRunnable _ _ herr) ▸ rfl
  | link pidReg =>
    simp [stepInstr] at herr
    split at herr
    · exact linkWith_error_not_structural _ _ herr
    · cases herr; rfl
  | monitor dest pidReg =>
    simp [stepInstr] at herr
    split at herr
    · exact monitorWith_error_not_structural _ _ _ herr
    · cases herr; rfl
  | demonitor refReg =>
    simp [stepInstr] at herr
    split at herr
    · exact demonitorWith_error_not_structural _ _ herr
    · cases herr; rfl
  | makeFun dest funName capRegs =>
    simp [stepInstr] at herr; exact nomatch herr
  | apply dest funReg argRegs =>
    simp [stepInstr] at herr
    cases hreg : getReg! frame funReg with
    | ref r =>
      simp [hreg] at herr
      cases hnode : p.heap.get? r with
      | none =>
        simp [hnode] at herr; cases herr; rfl
      | some node =>
        cases node with
        | closure funName env =>
          simp [hnode] at herr
          cases hff : s.module.findFunction funName with
          | none =>
            simp [hff] at herr; cases herr; rfl
          | some callee =>
            simp [hff] at herr
            split at herr
            · exact nomatch herr
            · cases herr; rfl
        | tuple _ | list _ | map _ =>
          simp [hnode] at herr; cases herr; rfl
    | nil | bool _ | int _ | float _ | atom _ | string _ | pid _ | reference _ =>
      simp [hreg] at herr; cases herr; rfl

/-- Progress: well-formed running states never fail structurally. -/
theorem step_progress (s : State) (hs : State.WF s) (hr : s.result = none) :
    match step s with
    | .ok _ => True
    | .error e => isStructuralError e = false := by
  cases hstep : step s with
  | ok _ => trivial
  | error e =>
    have hres : s.result.isSome = false := by simp [Option.isSome, hr]
    have hcur := hs.2.2.1
    unfold step at hstep
    simp [hres, hcur] at hstep
    by_cases hnr :
        ((s.processes[s.current]).status != .runnable) = true ∨
          (s.processes[s.current]).result.isSome = true
    · simp [hnr] at hstep
      simp [scheduleNext_error_is_noRunnable s s.current hstep, isStructuralError]
    · simp [hnr] at hstep
      have hp := hs.2.2.2 s.current hcur
      have ⟨hrun, hnone⟩ := status_runnable_of_not_deschedule _ _ hnr
      have hsz := runnable_stack_pos hp hrun hnone
      have hempty : ¬((s.processes[s.current]).stack = #[]) := by
        intro heq
        have hsz0 : (s.processes[s.current]).stack.size = 0 := by simp [heq]
        exact (Nat.ne_of_gt hsz) hsz0
      simp [hempty] at hstep
      have hfwf := runnable_top_WF hp hrun hnone
      have hipok :
          ¬(((s.processes[s.current]).stack[
              (s.processes[s.current]).stack.size - 1]!).function.code.size ≤
            ((s.processes[s.current]).stack[
              (s.processes[s.current]).stack.size - 1]!).ip) := by
        have := hfwf.2.2.1; omega
      simp [hipok] at hstep
      split at hstep
      · rename_i e' hsi
        injection hstep with heq; subst heq
        exact stepInstr_error_not_structural _ _ _ _ hsi
      · rename_i s1 hsi
        -- clock is bumped before the reductions / scheduleNext branch
        simp [afterInstr] at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · simp [scheduleNext_error_is_noRunnable _ _ hstep, isStructuralError]
          · cases hstep


end Step
end Autumn
