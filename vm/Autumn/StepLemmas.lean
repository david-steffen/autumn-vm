import Autumn.WellFormed
import Autumn.HeapLemmas
import Autumn.Step
import Autumn.Examples

namespace Autumn
namespace Step

/-! # Safety theorems for the Autumn stepper -/

/-! ## Scheduler -/

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

theorem scheduleNext_error_is_noRunnable (s : State) (fromIdx : Nat) {e}
    (h : State.scheduleNext s fromIdx = .error e) : e = .noRunnable := by
  unfold State.scheduleNext at h
  split at h
  · injection h; rename_i he; exact he.symm
  · split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · injection h; rename_i he; exact he.symm
      · injection h; rename_i he; exact he.symm

theorem scheduleNext_preserves (s : State) (fromIdx : Nat) {s'}
    (hs : State.WF s) (h : State.scheduleNext s fromIdx = .ok s') :
    State.WF s' := by
  unfold State.scheduleNext at h
  have hpos := hs.2.1
  simp [Nat.ne_of_gt hpos] at h
  split at h
  · rename_i idx hf
    injection h with heq; subst heq
    exact ⟨hs.1, hs.2.1, findRunnable_lt _ _ _ hpos hf, hs.2.2.2⟩
  · split at h
    · split at h
      · injection h with heq; subst heq
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      · cases h
    · cases h

theorem reductions_preserves (s : State) (n : Nat) (hs : State.WF s) :
    State.WF { s with reductions := n } :=
  ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩

/-! ## Process / frame helpers -/

theorem runnable_stack_pos {m p} (hp : Process.WF m p)
    (h1 : p.status = .runnable) (h2 : p.result = none) :
    0 < p.stack.size := by
  simp [Process.WF, h1, h2] at hp; exact hp.2.1

theorem runnable_top_WF {m p} (hp : Process.WF m p)
    (h1 : p.status = .runnable) (h2 : p.result = none) :
    Frame.WF m (p.stack[p.stack.size - 1]!) := by
  have hsz := runnable_stack_pos hp h1 h2
  have hlt : p.stack.size - 1 < p.stack.size := Nat.sub_one_lt_of_lt hsz
  simp [Process.WF, h1, h2] at hp
  have hf := hp.2.2.1 (p.stack.size - 1) hlt
  rwa [← getElem!_pos p.stack (p.stack.size - 1) hlt] at hf

theorem process_heap_WF {m p} (hp : Process.WF m p) : Heap.WF p.heap := hp.1

theorem setCurrentProcess_WF (s : State) (p : Process)
    (hs : State.WF s) (hp : Process.WF s.module p) :
    State.WF (s.setCurrentProcess p) := by
  have hcur := hs.2.2.1
  dsimp [State.setCurrentProcess]
  simp only [hcur, ↓reduceDIte]
  refine ⟨hs.1, ?_, ?_, ?_⟩
  · simpa [Array.size_set] using hs.2.1
  · simpa [Array.size_set] using hcur
  · intro i hi
    have hsz : (s.processes.set s.current p hcur).size = s.processes.size := Array.size_set _
    have hi0 : i < s.processes.size := by simpa [hsz] using hi
    by_cases heq : i = s.current
    · have hget : (s.processes.set s.current p hcur)[i]'hi = p := by
        simp [heq, Array.getElem_set_self]
      rw [hget]; exact hp
    · have hget : (s.processes.set s.current p hcur)[i]'hi =
          s.processes[i]'hi0 :=
        Array.getElem_set_ne (v := p) hcur hi0 (Ne.symm heq)
      rw [hget]; exact hs.2.2.2 i hi0

theorem setReg!_WF (f : Frame) (r : Reg) (v : Value) (m : Module)
    (hwf : Frame.WF m f) : Frame.WF m (setReg! f r v) := by
  dsimp [setReg!]
  refine ⟨hwf.1, ?_, hwf.2.2.1, hwf.2.2.2⟩
  simpa [Array.size_setIfInBounds] using hwf.2.1

theorem setCurrentFrame_stack_size (p : Process) (f : Frame)
    (hsz : 0 < p.stack.size) :
    (State.setCurrentFrame p f).stack.size = p.stack.size := by
  dsimp [State.setCurrentFrame]
  simp only [hsz, ↓reduceDIte, Array.size_set]

theorem bumpIp_frame (f : Frame) (m : Module) (hwf : Frame.WF m f)
    (h : f.ip + 1 < f.function.code.size) :
    Frame.WF m { f with ip := f.ip + 1 } :=
  ⟨hwf.1, hwf.2.1, h, hwf.2.2.2⟩

theorem setIp_frame (f : Frame) (ip : Nat) (m : Module) (hwf : Frame.WF m f)
    (h : ip < f.function.code.size) :
    Frame.WF m { f with ip := ip } :=
  ⟨hwf.1, hwf.2.1, h, hwf.2.2.2⟩

theorem setCurrentFrame_sameMeta_WF (m : Module) (p : Process) (f : Frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (hsz : 0 < p.stack.size)
    (hp : Process.WF m p)
    (hfwf : Frame.WF m f)
    (hsameFun : f.function = (p.stack[p.stack.size - 1]!).function)
    (hsameRet : f.retDest = (p.stack[p.stack.size - 1]!).retDest) :
    Process.WF m (State.setCurrentFrame p f) := by
  have hres' : (State.setCurrentFrame p f).result = none := by
    dsimp [State.setCurrentFrame]; simp [hsz, hres]
  have hstat' : (State.setCurrentFrame p f).status = .runnable := by
    dsimp [State.setCurrentFrame]; simp [hsz, hstat]
  have hheap : (State.setCurrentFrame p f).heap = p.heap := by
    dsimp [State.setCurrentFrame]; simp [hsz]
  have hp' : p.stack.size > 0 ∧ Process.stackWF m p.stack := by
    simpa [Process.WF, hres, hstat] using hp.2
  refine And.intro (by simpa [hheap] using hp.1) ?_
  simp only [hres', hstat']
  refine And.intro ((setCurrentFrame_stack_size p f hsz) ▸ hp'.1) ?_
  have ⟨hframes, hrets⟩ := hp'.2
  have hlt := Nat.sub_one_lt_of_lt hsz
  have hszset : (p.stack.set (p.stack.size - 1) f hlt).size = p.stack.size := Array.size_set _
  have top! : p.stack[p.stack.size - 1]! = p.stack[p.stack.size - 1]'hlt :=
    getElem!_pos p.stack (p.stack.size - 1) hlt
  refine And.intro ?_ ?_
  · intro i hi
    have hi0 : i < p.stack.size := by
      simpa [setCurrentFrame_stack_size p f hsz] using hi
    dsimp [State.setCurrentFrame]
    simp only [hsz, ↓reduceDIte]
    have hi' : i < (p.stack.set (p.stack.size - 1) f hlt).size := by simpa [hszset] using hi0
    by_cases heq : i = p.stack.size - 1
    · have hget : (p.stack.set (p.stack.size - 1) f hlt)[i]'hi' = f := by
        simp [heq, Array.getElem_set_self]
      rw [hget]; exact hfwf
    · have hget : (p.stack.set (p.stack.size - 1) f hlt)[i]'hi' = p.stack[i]'hi0 :=
        Array.getElem_set_ne (v := f) hlt hi0 (Ne.symm heq)
      rw [hget]; exact hframes i hi0
  · intro i hi hi0
    have hiS : i < p.stack.size := by
      simpa [setCurrentFrame_stack_size p f hsz] using hi
    have hret := hrets i hiS hi0
    dsimp [State.setCurrentFrame]
    simp only [hsz, ↓reduceDIte]
    have hi' : i < (p.stack.set (p.stack.size - 1) f hlt).size := by simpa [hszset] using hiS
    have hpred : i - 1 < p.stack.size := Nat.lt_of_le_of_lt (Nat.pred_le i) hiS
    have hpred' : i - 1 < (p.stack.set (p.stack.size - 1) f hlt).size := by
      simpa [hszset] using hpred
    by_cases heqi : i = p.stack.size - 1
    · have hgeti : (p.stack.set (p.stack.size - 1) f hlt)[i]'hi' = f := by
        simp [heqi, Array.getElem_set_self]
      have hne : p.stack.size - 1 ≠ i - 1 := by omega
      have hgetp := Array.getElem_set_ne (v := f) hlt hpred hne
      rw [hgeti, hgetp]
      have : f.retDest = (p.stack[i]'hiS).retDest := by
        simp [hsameRet, heqi, top!]
      rw [this]
      exact hret
    · by_cases heqp : i - 1 = p.stack.size - 1
      · have hgeti := Array.getElem_set_ne (v := f) hlt hiS (Ne.symm heqi)
        have hgetp : (p.stack.set (p.stack.size - 1) f hlt)[i - 1]'hpred' = f := by
          simp [heqp, Array.getElem_set_self]
        rw [hgeti, hgetp]
        have : f.function.locals = (p.stack[i - 1]'hpred).function.locals := by
          simp [hsameFun, heqp, top!]
        rw [this]
        exact hret
      · have hgeti := Array.getElem_set_ne (v := f) hlt hiS (Ne.symm heqi)
        have hgetp := Array.getElem_set_ne (v := f) hlt hpred (Ne.symm heqp)
        rw [hgeti, hgetp]
        exact hret

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

theorem mkRegs_size (locals : Nat) (args : Array Value) :
    (State.mkRegs locals args).size = locals := by
  simp [State.mkRegs]

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

theorem builtin_error_not_structural {heap : Heap} {name : FunName} {args : Array Value}
    {e : StepError}
    (herr : builtin heap name args = .error e) : isStructuralError e = false := by
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
            try { injection herr with heq; subst heq; rfl }
            try { cases herr }
          )
        )
      )
    )
  )

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
    split at herr
    · cases hb : builtin p.heap funName (readArgs! frame argRegs) with
      | error e' =>
        simp [hb] at herr
        injection herr with heq; subst heq
        exact builtin_error_not_structural hb
      | ok v =>
        simp [hb] at herr; exact nomatch herr
    · split at herr
      · split at herr
        · exact nomatch herr
        · injection herr with heq; subst heq; rfl
      · injection herr with heq; subst heq; rfl
  | return_ reg =>
    simp [stepInstr] at herr
    split at herr
    · split at herr
      · exact nomatch herr
      · simp [scheduleNext_error_is_noRunnable _ _ herr, isStructuralError]
    · exact nomatch herr
  | halt reg =>
    simp [stepInstr] at herr
    split at herr
    · exact nomatch herr
    · simp [scheduleNext_error_is_noRunnable _ _ herr, isStructuralError]
  | jump target =>
    simp [stepInstr] at herr; exact nomatch herr
  | jumpIfEq target reg lit =>
    simp [stepInstr] at herr; exact nomatch herr
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
        split at hstep
        · cases hstep
        · split at hstep
          · simp [scheduleNext_error_is_noRunnable s1 s1.current hstep, isStructuralError]
          · cases hstep

/-! ## Preservation -/

private theorem ip_succ_lt_of_nonterminal {m f ip instr}
    (hwf : Function.WF m f) (hip : ip < f.code.size)
    (hcode : f.code[ip]! = instr) (hnt : Instr.isTerminal instr = false) :
    ip + 1 < f.code.size := by
  have hnt' : Instr.isTerminal (f.code[ip]!) = false := by simpa [hcode] using hnt
  exact Function.WF.nonterminal_ip_lt hwf hip hnt'

theorem findFunction_name {m : Module} {name : FunName} {f : Function}
    (h : m.findFunction name = some f) : f.name = name := by
  simp only [Module.findFunction] at h
  have ⟨hbeq, _⟩ := (List.find?_eq_some_iff_append).1 h
  exact (beq_iff_eq).1 hbeq

theorem exited_process_WF (m : Module) (p : Process) (v : Value)
    (hheap : Heap.WF p.heap) :
    Process.WF m { p with stack := #[], result := some v, status := .exited } :=
  ⟨hheap, rfl, rfl⟩

theorem result_update_preserves (s : State) (v : Term) (hs : State.WF s) :
    State.WF { s with result := some v } :=
  ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩

theorem process_mailbox_WF (m : Module) (p : Process) (mb : Array Value)
    (hp : Process.WF m p) :
    Process.WF m { p with mailbox := mb } := by
  refine And.intro hp.1 ?_
  cases hres : p.result with
  | some _ =>
    simpa [Process.WF, hres] using hp.2
  | none =>
    cases hst : p.status with
    | exited => simp [Process.WF, hres, hst] at hp
    | waiting => simpa [Process.WF, hres, hst] using hp.2
    | runnable => simpa [Process.WF, hres, hst] using hp.2

theorem process_waiting_WF (m : Module) (p : Process)
    (hp : Process.WF m p) (hres : p.result = none) (hstat : p.status = .runnable) :
    Process.WF m { p with status := .waiting } := by
  have hp' : p.stack.size > 0 ∧ Process.stackWF m p.stack := by
    simpa [Process.WF, hres, hstat] using hp.2
  refine And.intro hp.1 ?_
  simpa [Process.WF, hres] using hp'

theorem process_wake_mailbox_WF (m : Module) (p : Process) (msg : Value)
    (hp : Process.WF m p) :
    Process.WF m
      { p with
        mailbox := p.mailbox.push msg
        status :=
          match p.status with
          | .waiting => .runnable
          | s => s } := by
  cases hst : p.status with
  | waiting =>
    cases hres : p.result with
    | some _ => simp [Process.WF, hres, hst] at hp
    | none =>
      have hp' : p.stack.size > 0 ∧ Process.stackWF m p.stack := by
        simpa [Process.WF, hres, hst] using hp.2
      refine And.intro hp.1 ?_
      simpa [Process.WF, hres, hst] using hp'
  | runnable =>
    simpa [hst] using process_mailbox_WF m p (p.mailbox.push msg) hp
  | exited =>
    simpa [hst] using process_mailbox_WF m p (p.mailbox.push msg) hp

theorem findProcessIdx_lt {s : State} {pid idx : Nat}
    (h : s.findProcessIdx pid = some idx) : idx < s.processes.size := by
  simp only [State.findProcessIdx] at h
  exact (Array.findIdx?_eq_some_iff_getElem.mp h).1

theorem setProcess_WF (s : State) (idx : Nat) (p : Process)
    (hs : State.WF s) (hidx : idx < s.processes.size)
    (hp : Process.WF s.module p) :
    State.WF { s with processes := s.processes.setIfInBounds idx p } := by
  have heq : s.processes.setIfInBounds idx p = s.processes.set idx p hidx := by
    simp [Array.setIfInBounds_def, hidx]
  rw [heq]
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

theorem push_frame_process_WF (m : Module) (p : Process) (f : Frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (hsz : 0 < p.stack.size) (hp : Process.WF m p) (hfwf : Frame.WF m f)
    (hret : f.retDest < (p.stack[p.stack.size - 1]!).function.locals) :
    Process.WF m { p with stack := p.stack.push f } := by
  have hp' : p.stack.size > 0 ∧ Process.stackWF m p.stack := by
    simpa [Process.WF, hres, hstat] using hp.2
  have ⟨hframes, hrets⟩ := hp'.2
  have hltTop := Nat.sub_one_lt_of_lt hsz
  have htop : p.stack[p.stack.size - 1]! = p.stack[p.stack.size - 1]'hltTop :=
    getElem!_pos p.stack (p.stack.size - 1) hltTop
  refine And.intro hp.1 ?_
  simp only [hres, hstat]
  refine And.intro ?_ ?_
  · have : (p.stack.push f).size = p.stack.size + 1 := Array.size_push f
    omega
  · refine And.intro ?_ ?_
    · intro i hi
      have hi' : i < p.stack.size + 1 := by simpa [Array.size_push] using hi
      by_cases heq : i = p.stack.size
      · subst heq
        simpa [Array.getElem_push_eq] using hfwf
      · have hi0 : i < p.stack.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi') heq
        have hget : (p.stack.push f)[i]'hi = p.stack[i]'hi0 := Array.getElem_push_lt hi0
        rw [hget]; exact hframes i hi0
    · intro i hi hi0
      have hi' : i < p.stack.size + 1 := by simpa [Array.size_push] using hi
      have hpred : i - 1 < p.stack.size + 1 := Nat.lt_of_le_of_lt (Nat.pred_le i) hi'
      by_cases heq : i = p.stack.size
      · subst heq
        have hgeti : (p.stack.push f)[p.stack.size]'hi = f := Array.getElem_push_eq
        have hgetp :
            (p.stack.push f)[p.stack.size - 1]'(by simpa [Array.size_push] using hpred) =
              p.stack[p.stack.size - 1]'hltTop :=
          Array.getElem_push_lt hltTop
        rw [hgeti, hgetp]
        simpa [htop] using hret
      · have hi0' : i < p.stack.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi') heq
        have hpred0 : i - 1 < p.stack.size := Nat.lt_of_le_of_lt (Nat.pred_le i) hi0'
        have hgeti : (p.stack.push f)[i]'hi = p.stack[i]'hi0' := Array.getElem_push_lt hi0'
        have hgetp : (p.stack.push f)[i - 1]'(by simpa [Array.size_push] using hpred) =
            p.stack[i - 1]'hpred0 :=
          Array.getElem_push_lt hpred0
        rw [hgeti, hgetp]
        exact hrets i hi0' hi0

theorem stackWF_of_pop (m : Module) (stack : Array Frame)
    (hsz : 1 < stack.size) (hwf : Process.stackWF m stack) :
    Process.stackWF m stack.pop := by
  have ⟨hframes, hrets⟩ := hwf
  refine And.intro ?_ ?_
  · intro i hi
    have hi0 : i < stack.size := by simp [Array.size_pop] at hi; omega
    have hget : stack.pop[i]'hi = stack[i]'hi0 := Array.getElem_pop hi
    rw [hget]; exact hframes i hi0
  · intro i hi hi0
    have hiS : i < stack.size := by simp [Array.size_pop] at hi; omega
    have hpred : i - 1 < stack.size := Nat.lt_of_le_of_lt (Nat.pred_le i) hiS
    have hgeti : stack.pop[i]'hi = stack[i]'hiS := Array.getElem_pop hi
    have hgetp :
        stack.pop[i - 1]'(Nat.lt_of_le_of_lt (Nat.pred_le i) hi) = stack[i - 1]'hpred :=
      Array.getElem_pop _
    rw [hgeti, hgetp]
    exact hrets i hiS hi0

/-- Pop then replace the new top frame (same function / retDest). -/
theorem pop_set_top_process_WF (m : Module) (p : Process) (caller : Frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (hsz : 1 < p.stack.size) (hp : Process.WF m p)
    (hcaller : Frame.WF m caller)
    (hsameFun : caller.function = (p.stack.pop[p.stack.pop.size - 1]!).function)
    (hsameRet : caller.retDest = (p.stack.pop[p.stack.pop.size - 1]!).retDest) :
    Process.WF m
      { p with stack := p.stack.pop.setIfInBounds (p.stack.pop.size - 1) caller } := by
  have hp' : p.stack.size > 0 ∧ Process.stackWF m p.stack := by
    simpa [Process.WF, hres, hstat] using hp.2
  have hpoppos : 0 < p.stack.pop.size := by simp [Array.size_pop]; omega
  let pPop : Process := { p with stack := p.stack.pop }
  have hpPop : Process.WF m pPop := by
    refine And.intro hp.1 ?_
    simp only [pPop, hres, hstat]
    exact ⟨hpoppos, stackWF_of_pop m p.stack hsz hp'.2⟩
  have hlt := Nat.sub_one_lt_of_lt hpoppos
  have hsetEq :
      { p with stack := p.stack.pop.setIfInBounds (p.stack.pop.size - 1) caller } =
        State.setCurrentFrame pPop caller := by
    dsimp [State.setCurrentFrame, pPop]
    simp only [hpoppos, ↓reduceDIte]
    congr 1
    rw [Array.setIfInBounds_def]
    have hlt' : p.stack.size - 1 - 1 < p.stack.size - 1 := by omega
    simp [hlt']
  rw [hsetEq]
  exact setCurrentFrame_sameMeta_WF m pPop caller hres hstat hpoppos hpPop hcaller
    (by
      have htop! : pPop.stack[pPop.stack.size - 1]! =
          pPop.stack[pPop.stack.size - 1]'hlt := getElem!_pos _ _ _
      simpa [pPop, htop!] using hsameFun)
    (by
      have htop! : pPop.stack[pPop.stack.size - 1]! =
          pPop.stack[pPop.stack.size - 1]'hlt := getElem!_pos _ _ _
      simpa [pPop, htop!] using hsameRet)

theorem push_process_WF (s : State) (child : Process)
    (hs : State.WF s) (hc : Process.WF s.module child) :
    State.WF { s with processes := s.processes.push child } := by
  have hsz : (s.processes.push child).size = s.processes.size + 1 := Array.size_push child
  refine ⟨hs.1, ?_, ?_, ?_⟩
  · simp [hsz]
  · have hcur := hs.2.2.1
    simpa [hsz] using Nat.lt_succ_of_lt hcur
  · intro i hi
    have hi' : i < s.processes.size + 1 := by simpa [hsz] using hi
    by_cases heq : i = s.processes.size
    · subst heq
      simpa [Array.getElem_push_eq] using hc
    · have hi0 : i < s.processes.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi') heq
      have hget : (s.processes.push child)[i]'(by simpa [hsz] using hi') =
          s.processes[i]'hi0 :=
        Array.getElem_push_lt hi0
      rw [hget]; exact hs.2.2.2 i hi0

/-- `loadLit` preserves state well-formedness. -/
theorem loadLit_preserves (s : State) (p : Process) (frame : Frame) (reg : Reg) (lit : Term)
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hip : frame.ip + 1 < frame.function.code.size) :
    State.WF (loadLit s p frame reg lit) := by
  unfold loadLit
  let p0 := State.setCurrentFrame p frame
  have hp0 : Process.WF s.module p0 :=
    setCurrentFrame_sameMeta_WF _ _ _ hres hstat htop hp hfwf
      (by simp [hframe]) (by simp [hframe])
  have hsz0 : 0 < p0.stack.size := by
    simpa [p0, setCurrentFrame_stack_size p frame htop] using htop
  have hres0 : p0.result = none := by
    dsimp [p0, State.setCurrentFrame]; simp [htop, hres]
  have hstat0 : p0.status = .runnable := by
    dsimp [p0, State.setCurrentFrame]; simp [htop, hstat]
  let pv := Process.allocTerm p0 lit
  have hp1 : Process.WF s.module pv.1 := Process.allocTerm_preserves_WF _ _ _ hp0
  have hmeta := Process.allocTerm_meta p0 lit hres0
  have hstat1 : pv.1.status = .runnable := by simpa [pv, hstat0] using hmeta.1
  have hres1 : pv.1.result = none := by simpa [pv] using hmeta.2.1
  have hszEq : pv.1.stack.size = p0.stack.size := by simpa [pv] using hmeta.2.2
  have hsz1 : 0 < pv.1.stack.size := by simpa [hszEq] using hsz0
  have htop0 : p0.stack[p0.stack.size - 1]! = frame := by
    dsimp [p0, State.setCurrentFrame]
    simp only [htop, ↓reduceDIte]
    have hlt := Nat.sub_one_lt_of_lt htop
    simp [Array.getElem_set_self, getElem!_pos, hlt]
  have hmetaF := Process.allocTerm_top_frame_meta p0 lit hres0 hsz0
  have htopFun :
      (pv.1.stack[pv.1.stack.size - 1]!).function = frame.function := by
    have := hmetaF.1
    simpa [pv, getElem!_pos, htop0] using this
  have htopIp : (pv.1.stack[pv.1.stack.size - 1]!).ip = frame.ip := by
    have := hmetaF.2
    simpa [pv, getElem!_pos, htop0] using this
  have hfwf1 : Frame.WF s.module (pv.1.stack[pv.1.stack.size - 1]!) := by
    have hsw : Process.stackWF s.module pv.1.stack := by
      have h := hp1
      simp [Process.WF, hres1, hstat1] at h
      exact h.2.2
    have hi : pv.1.stack.size - 1 < pv.1.stack.size := Nat.sub_one_lt_of_lt hsz1
    rw [getElem!_pos pv.1.stack (pv.1.stack.size - 1) hi]
    exact hsw.1 (pv.1.stack.size - 1) hi
  have hip1 : (pv.1.stack[pv.1.stack.size - 1]!).ip + 1 <
      (pv.1.stack[pv.1.stack.size - 1]!).function.code.size := by
    simpa [htopFun, htopIp] using hip
  let frame1 := setReg! (pv.1.stack[pv.1.stack.size - 1]!) reg pv.2
  let frame2 := { frame1 with ip := frame1.ip + 1 }
  have hfwf2 : Frame.WF s.module frame2 :=
    bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf1) (by
      simpa [frame2, frame1, setReg!] using hip1)
  exact setCurrentProcess_WF s _ hs
    (setCurrentFrame_sameMeta_WF s.module pv.1 frame2 hres1 hstat1 hsz1 hp1 hfwf2
      (by simp [frame2, frame1, setReg!])
      (by simp [frame2, frame1, setReg!]))

/-- Successful `stepInstr` preserves well-formedness under the usual stepper hypotheses. -/
theorem stepInstr_preserves
    (s : State) (p : Process) (frame : Frame) (instr : Instr) {s'}
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hcode : frame.function.code[frame.ip]! = instr)
    (h : stepInstr s p frame instr = .ok s') :
    State.WF s' := by
  have hio : Function.instrOk s.module frame.function instr := by
    have h := Frame.current_instrOk hfwf
    have : frame.function.code[frame.ip]'hfwf.2.2.1 = instr := by
      simpa [getElem!_pos frame.function.code frame.ip hfwf.2.2.1] using hcode
    simpa [this] using h
  cases instr with
  | loadLit reg lit =>
    simp [stepInstr] at h; cases h
    have hnt : Instr.isTerminal (.loadLit reg lit) = false := rfl
    have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
    exact loadLit_preserves s p frame reg lit hs hp hfwf hres hstat htop hframe hip
  | move dest src =>
    simp [stepInstr] at h; cases h
    have hnt : Instr.isTerminal (.move dest src) = false := rfl
    have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
    let frame1 := setReg! frame dest (getReg! frame src)
    let frame2 := { frame1 with ip := frame1.ip + 1 }
    have hfwf2 : Frame.WF s.module frame2 :=
      bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
    exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
      (by simp [frame2, frame1, setReg!, hframe]) (by simp [frame2, frame1, setReg!, hframe])
  | isTag dest reg tag =>
    simp [stepInstr] at h; cases h
    have hnt : Instr.isTerminal (.isTag dest reg tag) = false := rfl
    have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
    let frame1 := setReg! frame dest (.bool (tagOf p.heap (getReg! frame reg) == tag))
    let frame2 := { frame1 with ip := frame1.ip + 1 }
    have hfwf2 : Frame.WF s.module frame2 :=
      bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
    exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
      (by simp [frame2, frame1, setReg!, hframe]) (by simp [frame2, frame1, setReg!, hframe])
  | jump target =>
    simp [stepInstr] at h; cases h
    have htgt : target < frame.function.code.size := by
      simpa [Function.instrOk, Instr.jumpTargetOk, hcode] using hio.2.1
    let frame2 := { frame with ip := target }
    have hfwf2 : Frame.WF s.module frame2 := setIp_frame _ _ _ hfwf htgt
    exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
      (by simp [frame2, hframe]) (by simp [frame2, hframe])
  | jumpIfEq target reg lit =>
    simp [stepInstr] at h; cases h
    have htgt : target < frame.function.code.size := by
      simpa [Function.instrOk, Instr.jumpTargetOk] using hio.2.1
    have hnt : Instr.isTerminal (.jumpIfEq target reg lit) = false := rfl
    have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
    by_cases hb : Heap.beqTerm p.heap (getReg! frame reg) lit = true
    · simp [hb]
      let frame2 := { frame with ip := target }
      have hfwf2 : Frame.WF s.module frame2 := setIp_frame _ _ _ hfwf htgt
      exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
        (by simp [frame2, hframe]) (by simp [frame2, hframe])
    · simp [hb]
      let frame2 := { frame with ip := frame.ip + 1 }
      have hfwf2 : Frame.WF s.module frame2 := bumpIp_frame _ _ hfwf hip
      exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
        (by simp [frame2, hframe]) (by simp [frame2, hframe])
  | getTupleElem dest tupleReg index =>
    simp [stepInstr] at h
    split at h
    · split at h
      · split at h
        · exact nomatch h
        · cases h
          rename_i elems htu hge
          have hnt : Instr.isTerminal (.getTupleElem dest tupleReg index) = false := rfl
          have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
          let frame1 := setReg! frame dest elems[index]!
          let frame2 := { frame1 with ip := frame1.ip + 1 }
          have hfwf2 : Frame.WF s.module frame2 :=
            bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
          exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
            (by simp [frame2, frame1, setReg!, hframe]) (by simp [frame2, frame1, setReg!, hframe])
      · exact nomatch h
    · exact nomatch h
  | call dest funName argRegs =>
    simp [stepInstr] at h
    split at h
    · cases hb : builtin p.heap funName (readArgs! frame argRegs) with
      | error _ => simp [hb] at h; exact nomatch h
      | ok v =>
        simp [hb] at h; cases h
        have hnt : Instr.isTerminal (.call dest funName argRegs) = false := rfl
        have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
        let frame1 := setReg! frame dest v
        let frame2 := { frame1 with ip := frame1.ip + 1 }
        have hfwf2 : Frame.WF s.module frame2 :=
          bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
        exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
          (by simp [frame2, frame1, setReg!, hframe]) (by simp [frame2, frame1, setReg!, hframe])
    · split at h
      · split at h
        · cases h
          rename_i callee hfnd harity
          have hnt : Instr.isTerminal (.call dest funName argRegs) = false := rfl
          have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
          have hcallee : Function.WF s.module callee := Module.findFunction_WF hs.1 hfnd
          have hdest : dest < frame.function.locals := by
            have hregs := hio.1
            simp [Instr.regsOk] at hregs
            exact hregs.1
          let caller := { frame with ip := frame.ip + 1 }
          have hcaller : Frame.WF s.module caller := bumpIp_frame _ _ hfwf hip
          let p1 := State.setCurrentFrame p caller
          have hp1 : Process.WF s.module p1 :=
            setCurrentFrame_sameMeta_WF _ _ _ hres hstat htop hp hcaller
              (by simp [caller, hframe]) (by simp [caller, hframe])
          let newFrame : Frame := {
            function := callee
            regs := State.mkRegs callee.locals (readArgs! frame argRegs)
            ip := 0
            retDest := dest
          }
          have hnew : Frame.WF s.module newFrame := by
            refine ⟨hcallee, ?_, ?_, ?_⟩
            · simp [newFrame, mkRegs_size]
            · exact hcallee.2.1
            · have hname := findFunction_name hfnd
              simpa [newFrame, hname] using Option.isSome_of_eq_some hfnd
          have hsz1 : 0 < p1.stack.size := by
            simpa [p1, setCurrentFrame_stack_size p caller htop] using htop
          have hret : newFrame.retDest < (p1.stack[p1.stack.size - 1]!).function.locals := by
            have htop1 : p1.stack[p1.stack.size - 1]! = caller := by
              dsimp [p1, State.setCurrentFrame]
              simp only [htop, ↓reduceDIte]
              have hlt := Nat.sub_one_lt_of_lt htop
              simp [Array.getElem_set_self, getElem!_pos, hlt, caller]
            simpa [newFrame, htop1, caller] using hdest
          have hp2 : Process.WF s.module { p1 with stack := p1.stack.push newFrame } :=
            push_frame_process_WF _ _ _ (by
              dsimp [p1, State.setCurrentFrame]; simp [htop, hres])
              (by dsimp [p1, State.setCurrentFrame]; simp [htop, hstat])
              hsz1 hp1 hnew hret
          exact setCurrentProcess_WF s _ hs hp2
        · exact nomatch h
      · exact nomatch h
  | return_ reg =>
    simp [stepInstr] at h
    split at h
    · rename_i hsz1
      have hpE := exited_process_WF s.module p (getReg! frame reg) hp.1
      have hsE := setCurrentProcess_WF s _ hs hpE
      split at h
      · cases h
        exact result_update_preserves _ _ hsE
      · exact scheduleNext_preserves _ _ hsE h
    · rename_i hszne
      cases h
      have hsz2 : 1 < p.stack.size := by
        have : ¬(p.stack.size = 1) := by
          intro heq; simp [heq] at hszne
        omega
      have hp' : p.stack.size > 0 ∧ Process.stackWF s.module p.stack := by
        simpa [Process.WF, hres, hstat] using hp.2
      have ⟨hframes, _hrets⟩ := hp'.2
      have hpoppos : 0 < p.stack.pop.size := by simp [Array.size_pop]; omega
      have hltPop := Nat.sub_one_lt_of_lt hpoppos
      have hcaller_idx : p.stack.pop.size - 1 < p.stack.size := by
        simp [Array.size_pop]; omega
      let caller0 := p.stack.pop[p.stack.pop.size - 1]!
      have hcaller0WF : Frame.WF s.module caller0 := by
        have h1 := getElem!_pos p.stack.pop (p.stack.pop.size - 1) hltPop
        have h2 : p.stack.pop[p.stack.pop.size - 1]'hltPop =
            p.stack[p.stack.pop.size - 1]'hcaller_idx := Array.getElem_pop hltPop
        simpa [caller0, h1, h2] using hframes _ hcaller_idx
      let caller1 := setReg! caller0 frame.retDest (getReg! frame reg)
      have hcaller1 : Frame.WF s.module caller1 := setReg!_WF _ _ _ _ hcaller0WF
      have hp2 :=
        pop_set_top_process_WF s.module p caller1 hres hstat hsz2 hp hcaller1
          (by simp [caller1, setReg!, caller0])
          (by simp [caller1, setReg!, caller0])
      simpa [Array.size_pop, caller1, setReg!, caller0] using
        setCurrentProcess_WF s _ hs hp2
  | halt reg =>
    simp [stepInstr] at h
    have hpE := exited_process_WF s.module p (getReg! frame reg) hp.1
    have hsE := setCurrentProcess_WF s _ hs hpE
    split at h
    · cases h
      exact result_update_preserves _ _ hsE
    · exact scheduleNext_preserves _ _ hsE h
  | spawn dest funName argRegs =>
    simp [stepInstr] at h
    split at h
    · split at h
      · cases h
        rename_i callee hfnd harity
        have hnt : Instr.isTerminal (.spawn dest funName argRegs) = false := rfl
        have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
        have hcallee : Function.WF s.module callee := Module.findFunction_WF hs.1 hfnd
        let args := readArgs! frame argRegs
        let child0 : Process := {
          pid := s.nextPid
          stack := #[]
          mailbox := #[]
          status := .runnable
          result := none
          heap := Heap.empty
        }
        let childCopied := child0.copyArrayFrom p.heap args
        have hheapC : Heap.WF childCopied.1.heap :=
          Process.copyArrayFrom_heap_WF child0 p.heap args Heap.empty_default_WF
        let newFrame : Frame := {
          function := callee
          regs := State.mkRegs callee.locals childCopied.2
          ip := 0
          retDest := 0
        }
        have hnew : Frame.WF s.module newFrame := by
          refine ⟨hcallee, ?_, ?_, ?_⟩
          · simp [newFrame, mkRegs_size]
          · exact hcallee.2.1
          · have hname := findFunction_name hfnd
            simpa [newFrame, hname] using Option.isSome_of_eq_some hfnd
        let child : Process := { childCopied.1 with stack := #[newFrame] }
        have hcopy_meta :
            ∀ (q : Process) (i : Nat) (acc : Array Value),
              (Process.copyArrayFrom.go q p.heap args i acc).1.status = q.status ∧
              (Process.copyArrayFrom.go q p.heap args i acc).1.result = q.result ∧
              (Process.copyArrayFrom.go q p.heap args i acc).1.stack = q.stack := by
          intro q i acc
          induction hdiff : args.size - i generalizing q i acc with
          | zero =>
            unfold Process.copyArrayFrom.go
            have hge : args.size ≤ i := Nat.le_of_sub_eq_zero hdiff
            simp [Nat.not_lt.mpr hge]
          | succ d ih =>
            unfold Process.copyArrayFrom.go
            split
            · rename_i hlt
              have hdi : args.size - (i + 1) = d := by omega
              have hcf :
                  (Process.copyFrom q p.heap (args[i]'hlt)).1.status = q.status ∧
                  (Process.copyFrom q p.heap (args[i]'hlt)).1.result = q.result ∧
                  (Process.copyFrom q p.heap (args[i]'hlt)).1.stack = q.stack := by
                simp [Process.copyFrom]
              have hrest :=
                ih (Process.copyFrom q p.heap (args[i]'hlt)).1 (i + 1)
                  (acc.push (Process.copyFrom q p.heap (args[i]'hlt)).2) hdi
              exact ⟨hrest.1.trans hcf.1, hrest.2.1.trans hcf.2.1, hrest.2.2.trans hcf.2.2⟩
            · exact ⟨rfl, rfl, rfl⟩
        have hchild : Process.WF s.module child := by
          have hst : childCopied.1.status = .runnable := by
            change (Process.copyArrayFrom.go child0 p.heap args 0
              (Array.mkEmpty args.size)).1.status = .runnable
            exact (hcopy_meta child0 0 (Array.mkEmpty args.size)).1
          have hresC : childCopied.1.result = none := by
            change (Process.copyArrayFrom.go child0 p.heap args 0
              (Array.mkEmpty args.size)).1.result = none
            exact (hcopy_meta child0 0 (Array.mkEmpty args.size)).2.1
          refine And.intro hheapC ?_
          change
            match child.result with
            | some _ => _
            | none => _
          have hresChild : child.result = none := by simpa [child] using hresC
          have hstChild : child.status = .runnable := by simpa [child] using hst
          simp only [hresChild, hstChild]
          refine And.intro (by simp [child]) ?_
          refine And.intro ?_ ?_
          · intro i hi
            have hi0 : i < 1 := by simpa [child] using hi
            have : i = 0 := Nat.lt_one_iff.mp hi0
            subst this
            simpa [child] using hnew
          · intro i hi hi0
            have : i < 1 := by simpa [child] using hi
            omega
        let frame1 := setReg! frame dest (.pid s.nextPid)
        let frame2 := { frame1 with ip := frame1.ip + 1 }
        have hfwf2 : Frame.WF s.module frame2 :=
          bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
        let s1 := s.setCurrentProcess (State.setCurrentFrame p frame2)
        have hs1 : State.WF s1 :=
          apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
            (by simp [frame2, frame1, setReg!, hframe]) (by simp [frame2, frame1, setReg!, hframe])
        have hmod : s1.module = s.module := by
          dsimp [s1, State.setCurrentProcess, State.setCurrentFrame]
          split <;> simp
        have hchild1 : Process.WF s1.module child := by simpa [hmod] using hchild
        have hsPush := push_process_WF s1 child hs1 hchild1
        -- `stepInstr` also bumps `nextPid`; State.WF ignores that field.
        change State.WF
          { s1 with processes := s1.processes.push child, nextPid := s1.nextPid + 1 }
        exact hsPush
      · exact nomatch h
    · exact nomatch h
  | send pidReg msgReg =>
    simp [stepInstr] at h
    split at h
    · rename_i pid hpid
      split at h
      · cases h
        rename_i idx hfnd
        have hnt : Instr.isTerminal (.send pidReg msgReg) = false := rfl
        have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
        let frame2 := { frame with ip := frame.ip + 1 }
        have hfwf2 : Frame.WF s.module frame2 := bumpIp_frame _ _ hfwf hip
        let s1 := s.setCurrentProcess (State.setCurrentFrame p frame2)
        have hs1 : State.WF s1 :=
          apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
            (by simp [frame2, hframe]) (by simp [frame2, hframe])
        have hidx0 := findProcessIdx_lt hfnd
        have hidx : idx < s1.processes.size := by
          simpa [s1, State.setCurrentProcess, hs.2.2.1, Array.size_set] using hidx0
        let target0 := s1.processes[idx]!
        have htarget0 : Process.WF s1.module target0 := by
          have := hs1.2.2.2 idx hidx
          simpa [target0, getElem!_pos s1.processes idx hidx] using this
        have hsrcHeap :
            (State.setCurrentFrame p frame2).heap = p.heap := by
          dsimp [State.setCurrentFrame]; simp [htop]
        let msg := getReg! frame msgReg
        let copied := target0.copyFrom (State.setCurrentFrame p frame2).heap msg
        have htargetC : Process.WF s1.module copied.1 := by
          have h := Process.copyFrom_preserves_WF s1.module target0 p.heap msg htarget0
          rw [show copied = target0.copyFrom p.heap msg by simp [copied, hsrcHeap]]
          exact h
        have htarget1 : Process.WF s1.module
            { copied.1 with
              mailbox := copied.1.mailbox.push copied.2
              status :=
                match copied.1.status with
                | .waiting => ProcStatus.runnable
                | st => st } :=
          process_wake_mailbox_WF s1.module copied.1 copied.2 htargetC
        exact setProcess_WF s1 idx _ hs1 hidx htarget1
      · exact nomatch h
    · exact nomatch h
  | recv dest =>
    simp [stepInstr] at h
    split at h
    · cases h
      rename_i hmb
      have hnt : Instr.isTerminal (.recv dest) = false := rfl
      have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
      let pMb := { p with mailbox := p.mailbox.eraseIdx! 0 }
      have hpMb : Process.WF s.module pMb := process_mailbox_WF _ p _ hp
      let frame1 := setReg! frame dest p.mailbox[0]!
      let frame2 := { frame1 with ip := frame1.ip + 1 }
      have hfwf2 : Frame.WF s.module frame2 :=
        bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
      exact apply_top_frame_preserves s pMb frame2 hs hpMb hres hstat htop hfwf2
        (by simp [frame2, frame1, setReg!, pMb, hframe])
        (by simp [frame2, frame1, setReg!, pMb, hframe])
    · rename_i hmb
      have hpW := process_waiting_WF _ p hp hres hstat
      have hsW := setCurrentProcess_WF s _ hs hpW
      exact scheduleNext_preserves _ _ hsW h

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
        split at h
        · cases h; exact hs1
        · split at h
          · exact scheduleNext_preserves s1 s1.current hs1 h
          · cases h
            exact reductions_preserves s1 (s1.reductions - 1) hs1

theorem addMain_has_entry :
    (addMainModule.findFunction addMainModule.entry).isSome := by
  native_decide

#eval Step.runModule addMainModule (fuel := 100)

end Step
end Autumn
