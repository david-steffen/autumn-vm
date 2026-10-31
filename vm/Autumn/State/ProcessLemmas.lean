import Autumn.WellFormed
import Autumn.Heap.Lemmas
import Autumn.Process.Lemmas
import Autumn.State

namespace Autumn

/-! # Process / frame helpers and mutators -/

theorem runnable_WF_parts {m p} (hp : Process.WF m p)
    (hstat : p.status = .runnable ∨ p.status = .waiting) (hres : p.result = none) :
    0 < p.stack.size ∧ Process.stackWF m p.stack ∧
      Process.handlersWF p.stack p.handlers := by
  cases hstat with
  | inl h => simp [Process.WF, h, hres] at hp; exact hp.2
  | inr h => simp [Process.WF, h, hres] at hp; exact hp.2

theorem runnable_stack_pos {m p} (hp : Process.WF m p)
    (h1 : p.status = .runnable) (h2 : p.result = none) :
    0 < p.stack.size :=
  (runnable_WF_parts hp (Or.inl h1) h2).1

theorem runnable_top_WF {m p} (hp : Process.WF m p)
    (h1 : p.status = .runnable) (h2 : p.result = none) :
    Frame.WF m (p.stack[p.stack.size - 1]!) := by
  have hsz := runnable_stack_pos hp h1 h2
  have hlt : p.stack.size - 1 < p.stack.size := Nat.sub_one_lt_of_lt hsz
  have hsw := (runnable_WF_parts hp (Or.inl h1) h2).2.1
  have hf := hsw.1 (p.stack.size - 1) hlt
  rwa [← getElem!_pos p.stack (p.stack.size - 1) hlt] at hf

theorem clearWait_WF (m : Module) (p : Process) (hp : Process.WF m p) :
    Process.WF m (State.clearWait p) := by
  simpa [State.clearWait, Process.WF] using hp

theorem wakeOnTimeout_WF (m : Module) (p : Process) (hp : Process.WF m p) :
    Process.WF m (State.wakeOnTimeout p) := by
  dsimp [State.wakeOnTimeout]
  cases hst : p.status with
  | waiting =>
    cases hres : p.result with
    | some _ =>
      have h := hp
      simp [Process.WF, hres, hst] at h
    | none =>
      have hp' := runnable_WF_parts hp (Or.inr hst) hres
      exact ⟨hp.1, by simpa [Process.WF, hres] using hp'⟩
  | runnable => simpa [hst] using hp
  | exited => simpa [hst] using hp

theorem wakeOnMessage_WF (m : Module) (p : Process) (hp : Process.WF m p) :
    Process.WF m (State.wakeOnMessage p) := by
  dsimp [State.wakeOnMessage]
  cases hst : p.status with
  | waiting =>
    have hpC := clearWait_WF m p hp
    cases hres : p.result with
    | some _ =>
      have h := hpC
      simp [State.clearWait, Process.WF, hres, hst] at h
    | none =>
      have hresC : (State.clearWait p).result = none := by simpa [State.clearWait] using hres
      have hstC : (State.clearWait p).status = .waiting := by simpa [State.clearWait] using hst
      have hp' := runnable_WF_parts hpC (Or.inr hstC) hresC
      exact ⟨hpC.1, by simpa [State.clearWait, Process.WF, hres] using hp'⟩
  | runnable => exact clearWait_WF m p hp
  | exited => exact clearWait_WF m p hp

theorem wakeExpired_preserves_procs (m : Module) (procs : Array Process) (clock : Nat)
    (h : ∀ i, (hi : i < procs.size) → Process.WF m (procs[i]'hi)) :
    ∀ i, (hi : i < (State.wakeExpired procs clock).size) →
      Process.WF m ((State.wakeExpired procs clock)[i]'hi) := by
  intro i hi
  simp only [State.wakeExpired, Array.size_map] at hi
  have hi0 : i < procs.size := hi
  have hp := h i hi0
  simp only [State.wakeExpired, Array.getElem_map]
  cases hst : (procs[i]'hi0).status with
  | waiting =>
    cases hd : (procs[i]'hi0).waitDeadline with
    | none => simpa [hst, hd] using hp
    | some d =>
      by_cases hle : d ≤ clock
      · simp [hst, hd, hle]
        exact wakeOnTimeout_WF m (procs[i]'hi0) hp
      · simp [hst, hd, hle]
        exact hp
  | runnable => simpa [hst] using hp
  | exited => simpa [hst] using hp

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

theorem setCurrentFrame_stack_size (p : Process) (f : Frame)
    (hsz : 0 < p.stack.size) :
    (State.setCurrentFrame p f).stack.size = p.stack.size := by
  dsimp [State.setCurrentFrame]
  simp only [hsz, ↓reduceDIte, Array.size_set]

/-- `handlersWF` only depends on stack size and each frame's `function`. -/
theorem handlersWF_of_sameFun (stack stack' : Array Frame) (handlers : Array Handler)
    (hsz : stack'.size = stack.size)
    (hfun : ∀ i, (hi : i < stack.size) → (stack'[i]!).function = (stack[i]!).function)
    (h : Process.handlersWF stack handlers) :
    Process.handlersWF stack' handlers := by
  intro i hi
  have ⟨hd0, hdle, hip, hexc⟩ := h i hi
  refine ⟨hd0, by rw [hsz]; exact hdle, ?_, ?_⟩
  · let depth := (handlers[i]'hi).stackDepth
    have hdi : depth - 1 < stack.size := by omega
    have hf := hfun (depth - 1) hdi
    simpa [depth, hf, getElem!_pos] using hip
  · let depth := (handlers[i]'hi).stackDepth
    have hdi : depth - 1 < stack.size := by omega
    have hf := hfun (depth - 1) hdi
    simpa [depth, hf, getElem!_pos] using hexc

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
  have hp' := runnable_WF_parts hp (Or.inl hstat) hres
  refine And.intro (by simpa [hheap] using hp.1) ?_
  simp only [hres', hstat']
  refine And.intro ((setCurrentFrame_stack_size p f hsz) ▸ hp'.1) ?_
  have ⟨hframes, hrets⟩ := hp'.2.1
  have hlt := Nat.sub_one_lt_of_lt hsz
  have hszset : (p.stack.set (p.stack.size - 1) f hlt).size = p.stack.size := Array.size_set _
  have top! : p.stack[p.stack.size - 1]! = p.stack[p.stack.size - 1]'hlt :=
    getElem!_pos p.stack (p.stack.size - 1) hlt
  refine And.intro ?_ ?_
  · -- stackWF
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
  · -- handlersWF: function unchanged on top ⇒ rescue/exc bounds still hold
    have hszEq := setCurrentFrame_stack_size p f hsz
    have hhandEq : (State.setCurrentFrame p f).handlers = p.handlers := by
      dsimp [State.setCurrentFrame]; simp [hsz]
    have hfun :
        ∀ i, (hi : i < p.stack.size) →
          ((State.setCurrentFrame p f).stack[i]!).function = (p.stack[i]!).function := by
      intro i hi
      have hi' : i < (State.setCurrentFrame p f).stack.size := by simpa [hszEq] using hi
      dsimp [State.setCurrentFrame]
      simp only [hsz, ↓reduceDIte]
      by_cases heq : i = p.stack.size - 1
      · subst heq
        have hget :
            (p.stack.set (p.stack.size - 1) f hlt)[p.stack.size - 1]! = f := by
          have this :
              p.stack.size - 1 < (p.stack.set (p.stack.size - 1) f hlt).size := by
            simpa [hszset] using hlt
          rw [getElem!_pos (p.stack.set (p.stack.size - 1) f hlt) (p.stack.size - 1) this,
            Array.getElem_set_self]
        rw [hget]
        exact hsameFun
      · have hne : i ≠ p.stack.size - 1 := heq
        have hget :
            (p.stack.set (p.stack.size - 1) f hlt)[i]! = p.stack[i]! := by
          have hiS : i < (p.stack.set (p.stack.size - 1) f hlt).size := by
            simpa [hszset] using hi
          rw [getElem!_pos (p.stack.set (p.stack.size - 1) f hlt) i hiS,
            getElem!_pos p.stack i hi]
          exact Array.getElem_set_ne (v := f) hlt hi (Ne.symm hne)
        rw [hget]
    exact hhandEq ▸
      handlersWF_of_sameFun p.stack (State.setCurrentFrame p f).stack p.handlers hszEq hfun
        hp'.2.2

theorem mkRegs_size (locals : Nat) (args : Array Value) :
    (State.mkRegs locals args).size = locals := by
  simp [State.mkRegs]


/-! ## Process mutators -/

theorem exited_process_WF (m : Module) (p : Process) (v : Value)
    (hheap : Heap.WF p.heap) :
    Process.WF m
      { p with stack := #[], result := some v, status := .exited, handlers := #[] } :=
  ⟨hheap, rfl, rfl, rfl⟩

theorem result_update_preserves (s : State) (v : Term) (hs : State.WF s) :
    State.WF { s with result := some v } :=
  ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩

/-- Updating `processes` does not touch the machine result. -/
theorem processes_update_result (s : State) (ps : Array Process) :
    ({ s with processes := ps } : State).result = s.result :=
  rfl

/-- `setCurrentProcess` does not touch the machine result. -/
theorem setCurrentProcess_result (s : State) (p : Process) :
    (State.setCurrentProcess s p).result = s.result := by
  simp [State.setCurrentProcess]
  split <;> rfl

/-- `setCurrentProcess` does not change `current`. -/
theorem setCurrentProcess_current (s : State) (p : Process) :
    (State.setCurrentProcess s p).current = s.current := by
  simp [State.setCurrentProcess]
  split <;> rfl

/-- Clock update does not touch the machine result. -/
theorem clock_result (s : State) (n : Nat) :
    ({ s with clock := n } : State).result = s.result :=
  rfl

/-- Reductions update does not touch the machine result. -/
theorem reductions_result (s : State) (n : Nat) :
    ({ s with reductions := n } : State).result = s.result :=
  rfl

/-- Module / nextRef updates do not touch the machine result. -/
theorem nextRef_result (s : State) (n : Nat) :
    ({ s with nextRef := n } : State).result = s.result :=
  rfl

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
    | waiting =>
      have hp' := runnable_WF_parts hp (Or.inr hst) hres
      simpa [Process.WF, hres, hst] using hp'
    | runnable =>
      have hp' := runnable_WF_parts hp (Or.inl hst) hres
      simpa [Process.WF, hres, hst] using hp'

/-- Replace handlers when the new stack satisfies `handlersWF`. -/
theorem process_handlers_WF (m : Module) (p : Process) (hs : Array Handler)
    (hp : Process.WF m p) (hres : p.result = none)
    (hhs : Process.handlersWF p.stack hs) :
    Process.WF m { p with handlers := hs } := by
  refine And.intro hp.1 ?_
  cases hst : p.status with
  | exited => simp [Process.WF, hres, hst] at hp
  | waiting =>
      have hp' := runnable_WF_parts hp (Or.inr hst) hres
      simpa [Process.WF, hres, hst] using And.intro hp'.1 (And.intro hp'.2.1 hhs)
  | runnable =>
      have hp' := runnable_WF_parts hp (Or.inl hst) hres
      simpa [Process.WF, hres, hst] using And.intro hp'.1 (And.intro hp'.2.1 hhs)

theorem stackWF_of_extract (m : Module) (stack : Array Frame) (depth : Nat)
    (hdepth : depth ≤ stack.size) (hwf : Process.stackWF m stack) :
    Process.stackWF m (stack.extract 0 depth) := by
  have ⟨hframes, hrets⟩ := hwf
  have hsz : (stack.extract 0 depth).size = depth := by
    simp [Array.size_extract, Nat.min_eq_left hdepth]
  refine And.intro ?_ ?_
  · intro i hi
    have hi0 : i < stack.size := by omega
    have hget : (stack.extract 0 depth)[i]'hi = stack[i]'hi0 := by
      simpa [Nat.zero_add] using Array.getElem_extract (xs := stack) (start := 0) (stop := depth) hi
    rw [hget]; exact hframes i hi0
  · intro i hi hi0
    have hiS : i < stack.size := by omega
    have hpred : i - 1 < stack.size := Nat.lt_of_le_of_lt (Nat.pred_le i) hiS
    have hgeti : (stack.extract 0 depth)[i]'hi = stack[i]'hiS := by
      simpa [Nat.zero_add] using Array.getElem_extract (xs := stack) (start := 0) (stop := depth) hi
    have hgetp :
        (stack.extract 0 depth)[i - 1]'(Nat.lt_of_le_of_lt (Nat.pred_le i) hi) =
          stack[i - 1]'hpred := by
      simpa [Nat.zero_add] using
        Array.getElem_extract (xs := stack) (start := 0) (stop := depth)
          (Nat.lt_of_le_of_lt (Nat.pred_le i) hi)
    rw [hgeti, hgetp]
    exact hrets i hiS hi0

/-- Truncate stack to `depth`, then replace the top frame (same function).
`handlers` must already satisfy `handlersWF` on the truncated stack. -/
theorem extract_set_top_process_WF (m : Module) (p : Process) (depth : Nat) (top : Frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (hdepth0 : 0 < depth) (hdepth : depth ≤ p.stack.size) (hp : Process.WF m p)
    (htop : Frame.WF m top)
    (hsameFun :
      top.function =
        (p.stack.extract 0 depth)[(p.stack.extract 0 depth).size - 1]!.function)
    (hsameRet :
      top.retDest =
        (p.stack.extract 0 depth)[(p.stack.extract 0 depth).size - 1]!.retDest)
    (handlers : Array Handler)
    (hhs : Process.handlersWF (p.stack.extract 0 depth) handlers) :
    Process.WF m
      { p with
        stack :=
          let stack := p.stack.extract 0 depth
          stack.setIfInBounds (stack.size - 1) top
        handlers } := by
  have hp' := runnable_WF_parts hp (Or.inl hstat) hres
  have hszExt : (p.stack.extract 0 depth).size = depth := by
    simp [Array.size_extract, Nat.min_eq_left hdepth]
  let stack := p.stack.extract 0 depth
  let pExt : Process := { p with stack, handlers }
  have hpExt : Process.WF m pExt := by
    refine And.intro hp.1 ?_
    simp only [pExt, stack, hres, hstat]
    exact ⟨by simpa [Array.size_extract, Nat.min_eq_left hdepth] using hdepth0,
      stackWF_of_extract m p.stack depth hdepth hp'.2.1, hhs⟩
  have hpos : 0 < stack.size := by simpa [stack, hszExt] using hdepth0
  have hsetEq :
      { p with stack := stack.setIfInBounds (stack.size - 1) top, handlers } =
        State.setCurrentFrame pExt top := by
    dsimp [State.setCurrentFrame, pExt]
    simp only [hpos, ↓reduceDIte]
    congr 1
    have hlt : stack.size - 1 < stack.size := Nat.sub_one_lt_of_lt hpos
    rw [Array.setIfInBounds_def]
    simp [hlt]
  rw [hsetEq]
  exact setCurrentFrame_sameMeta_WF m pExt top hres hstat hpos hpExt htop
    (by simpa [pExt, stack] using hsameFun)
    (by simpa [pExt, stack] using hsameRet)

theorem process_waiting_WF (m : Module) (p : Process)
    (hp : Process.WF m p) (hres : p.result = none) (hstat : p.status = .runnable) :
    Process.WF m { p with status := .waiting } := by
  have hp' := runnable_WF_parts hp (Or.inl hstat) hres
  refine And.intro hp.1 ?_
  simpa [Process.WF, hres] using hp'

theorem process_wake_mailbox_WF (m : Module) (p : Process) (msg : Value)
    (hp : Process.WF m p) :
    Process.WF m
      (let p1 := { p with mailbox := p.mailbox.push msg }
        if p.status == .waiting then State.wakeOnMessage p1 else p1) := by
  have hp1 : Process.WF m { p with mailbox := p.mailbox.push msg } :=
    process_mailbox_WF m p _ hp
  dsimp only
  split
  · exact wakeOnMessage_WF m _ hp1
  · exact hp1

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
  have hp' := runnable_WF_parts hp (Or.inl hstat) hres
  have ⟨hframes, hrets⟩ := hp'.2.1
  have hltTop := Nat.sub_one_lt_of_lt hsz
  have htop : p.stack[p.stack.size - 1]! = p.stack[p.stack.size - 1]'hltTop :=
    getElem!_pos p.stack (p.stack.size - 1) hltTop
  refine And.intro hp.1 ?_
  simp only [hres, hstat]
  refine And.intro ?_ ?_
  · have : (p.stack.push f).size = p.stack.size + 1 := Array.size_push f
    omega
  · refine And.intro ?_ ?_
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
          have hgetp :
              (p.stack.push f)[i - 1]'(by simpa [Array.size_push] using hpred) =
                p.stack[i - 1]'hpred0 :=
            Array.getElem_push_lt hpred0
          rw [hgeti, hgetp]
          exact hrets i hi0' hi0
    · -- handlersWF: depths ≤ old size, so frames at depth-1 are unchanged
      intro i hi
      have ⟨hd0, hdle, hip, hexc⟩ := hp'.2.2 i hi
      refine ⟨hd0, ?_, ?_, ?_⟩
      · have : (p.stack.push f).size = p.stack.size + 1 := Array.size_push f
        omega
      · let depth := (p.handlers[i]'hi).stackDepth
        have hdi : depth - 1 < p.stack.size := by omega
        have hget : (p.stack.push f)[depth - 1]! = p.stack[depth - 1]! := by
          have hiS : depth - 1 < (p.stack.push f).size := by
            simp [Array.size_push]; omega
          rw [getElem!_pos (p.stack.push f) (depth - 1) hiS,
            getElem!_pos p.stack (depth - 1) hdi]
          exact Array.getElem_push_lt hdi
        simpa [depth, hget] using hip
      · let depth := (p.handlers[i]'hi).stackDepth
        have hdi : depth - 1 < p.stack.size := by omega
        have hget : (p.stack.push f)[depth - 1]! = p.stack[depth - 1]! := by
          have hiS : depth - 1 < (p.stack.push f).size := by
            simp [Array.size_push]; omega
          rw [getElem!_pos (p.stack.push f) (depth - 1) hiS,
            getElem!_pos p.stack (depth - 1) hdi]
          exact Array.getElem_push_lt hdi
        simpa [depth, hget] using hexc

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

/-- Pop then replace the new top frame (same function / retDest).
Requires no handler with `stackDepth > pop.size` (as enforced by return-through-try). -/
theorem pop_set_top_process_WF (m : Module) (p : Process) (caller : Frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (hsz : 1 < p.stack.size) (hp : Process.WF m p)
    (hcaller : Frame.WF m caller)
    (hsameFun : caller.function = (p.stack.pop[p.stack.pop.size - 1]!).function)
    (hsameRet : caller.retDest = (p.stack.pop[p.stack.pop.size - 1]!).retDest)
    (hhandLe : ∀ i, (hi : i < p.handlers.size) →
      (p.handlers[i]'hi).stackDepth ≤ p.stack.pop.size) :
    Process.WF m
      { p with stack := p.stack.pop.setIfInBounds (p.stack.pop.size - 1) caller } := by
  have hp' := runnable_WF_parts hp (Or.inl hstat) hres
  have hpoppos : 0 < p.stack.pop.size := by simp [Array.size_pop]; omega
  have hhs : Process.handlersWF p.stack.pop p.handlers := by
    intro i hi
    have ⟨hd0, _hdle, hip, hexc⟩ := hp'.2.2 i hi
    have hdle' := hhandLe i hi
    refine ⟨hd0, hdle', ?_, ?_⟩
    · let depth := (p.handlers[i]'hi).stackDepth
      have hdi : depth - 1 < p.stack.pop.size := by omega
      have hdi0 : depth - 1 < p.stack.size := by omega
      have hget : p.stack.pop[depth - 1]! = p.stack[depth - 1]! := by
        rw [getElem!_pos p.stack.pop (depth - 1) hdi,
          getElem!_pos p.stack (depth - 1) hdi0]
        exact Array.getElem_pop hdi
      simpa [depth, hget] using hip
    · let depth := (p.handlers[i]'hi).stackDepth
      have hdi : depth - 1 < p.stack.pop.size := by omega
      have hdi0 : depth - 1 < p.stack.size := by omega
      have hget : p.stack.pop[depth - 1]! = p.stack[depth - 1]! := by
        rw [getElem!_pos p.stack.pop (depth - 1) hdi,
          getElem!_pos p.stack (depth - 1) hdi0]
        exact Array.getElem_pop hdi
      simpa [depth, hget] using hexc
  let pPop : Process := { p with stack := p.stack.pop }
  have hpPop : Process.WF m pPop := by
    refine And.intro hp.1 ?_
    simp only [pPop, hres, hstat]
    exact ⟨hpoppos, stackWF_of_pop m p.stack hsz hp'.2.1, hhs⟩
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

/-! ## `State.initial` well-formedness -/

/-- Successful `initial` yields a well-formed state (needs positive heap capacity). -/
theorem initial_WF (m : Module) (cap : Nat)
    (hm : Module.WF m) (hcap : 0 < cap)
    {s : State} (h : State.initial m cap = .ok s) :
    State.WF s := by
  unfold State.initial at h
  cases hf : m.findFunction m.entry with
  | none => simp only [hf] at h; exact nomatch h
  | some f =>
    simp only [hf] at h
    split at h
    · -- arity ≠ 0 → throw
      exact nomatch h
    · cases h
      have hfwf : Function.WF m f := Module.findFunction_WF hm hf
      have hip : (0 : Nat) < f.code.size := hfwf.2.1
      have hfname : f.name = m.entry := Module.findFunction_name hf
      have hframe : Frame.WF m
          { function := f, regs := State.mkRegs f.locals #[], ip := 0, retDest := 0 } := by
        refine ⟨hfwf, mkRegs_size f.locals #[], hip, ?_⟩
        simpa [hfname] using hm.2.2.1
      have hstack : Process.stackWF m
          #[{ function := f, regs := State.mkRegs f.locals #[], ip := 0, retDest := 0 }] := by
        refine ⟨?_, ?_⟩
        · intro i hi
          have : i = 0 := Nat.lt_one_iff.1 (by simpa using hi)
          subst this; simpa using hframe
        · intro i hi hi0
          have : i = 0 := Nat.lt_one_iff.1 (by simpa using hi)
          subst this; exact (Nat.lt_irrefl 0 hi0).elim
      have hhand : Process.handlersWF
          #[{ function := f, regs := State.mkRegs f.locals #[], ip := 0, retDest := 0 }] #[] := by
        intro i hi; exact (Nat.not_lt_zero _ hi).elim
      have hheap : Heap.WF (Heap.empty cap) := Heap.empty_WF cap hcap
      have hproc : Process.WF m
          { pid := 0
            stack := #[{ function := f, regs := State.mkRegs f.locals #[], ip := 0, retDest := 0 }]
            mailbox := #[]
            status := .runnable
            result := none
            heap := Heap.empty cap
            handlers := #[] } :=
        ⟨hheap, Nat.succ_pos _, hstack, hhand⟩
      refine ⟨hm, Nat.succ_pos _, Nat.zero_lt_one, ?_⟩
      intro i hi
      have : i = 0 := Nat.lt_one_iff.1 (by simpa using hi)
      subst this; simpa using hproc

end Autumn
