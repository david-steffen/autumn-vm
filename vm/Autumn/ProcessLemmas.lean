import Autumn.HeapLemmas
import Autumn.WellFormed
import Autumn.State
import Autumn.Process

namespace Autumn

namespace Process

theorem process_set_heap_WF (m : Module) (p : Process) (h' : Heap)
    (hp : Process.WF m p) (hh : Heap.WF h') :
    Process.WF m { p with heap := h' } := by
  refine And.intro hh ?_
  cases hres : p.result with
  | some _ => simpa [Process.WF, hres] using hp.2
  | none =>
    cases hst : p.status with
    | exited => simp [Process.WF, hres, hst] at hp
    | waiting => simpa [Process.WF, hres, hst] using hp.2
    | runnable => simpa [Process.WF, hres, hst] using hp.2

theorem copyFrom_heap_WF (p : Process) (src : Heap) (v : Value)
    (hh : Heap.WF p.heap) : Heap.WF (copyFrom p src v).1.heap := by
  simp only [copyFrom]
  exact Heap.sanitized_copy_WF src p.heap v hh.2.1

theorem copyFrom_preserves_WF (m : Module) (p : Process) (src : Heap) (v : Value)
    (hp : Process.WF m p) : Process.WF m (copyFrom p src v).1 := by
  simp only [copyFrom]
  exact process_set_heap_WF m p _ hp (Heap.sanitized_copy_WF src p.heap v hp.1.2.1)

theorem copyArrayFrom.go_heap_WF (p : Process) (src : Heap) (vs : Array Value)
    (i : Nat) (acc : Array Value) (hh : Heap.WF p.heap) :
    Heap.WF (copyArrayFrom.go p src vs i acc).1.heap := by
  induction hdiff : vs.size - i generalizing p i acc with
  | zero =>
    unfold copyArrayFrom.go
    have hge : vs.size ≤ i := Nat.le_of_sub_eq_zero hdiff
    simp [Nat.not_lt.mpr hge]
    exact hh
  | succ d ih =>
    unfold copyArrayFrom.go
    split
    · rename_i hlt
      have hh1 := copyFrom_heap_WF p src (vs[i]'hlt) hh
      have hdi : vs.size - (i + 1) = d := by omega
      exact ih _ _ _ hh1 hdi
    · exact hh

theorem copyArrayFrom_heap_WF (p : Process) (src : Heap) (vs : Array Value)
    (hh : Heap.WF p.heap) : Heap.WF (copyArrayFrom p src vs).1.heap :=
  copyArrayFrom.go_heap_WF p src vs 0 _ hh

theorem copyArrayFrom.go_preserves_WF (m : Module) (p : Process) (src : Heap)
    (vs : Array Value) (i : Nat) (acc : Array Value) (hp : Process.WF m p) :
    Process.WF m (copyArrayFrom.go p src vs i acc).1 := by
  induction hdiff : vs.size - i generalizing p i acc with
  | zero =>
    unfold copyArrayFrom.go
    have hge : vs.size ≤ i := Nat.le_of_sub_eq_zero hdiff
    simp [Nat.not_lt.mpr hge]
    exact hp
  | succ d ih =>
    unfold copyArrayFrom.go
    split
    · rename_i hlt
      have hp1 := copyFrom_preserves_WF m p src (vs[i]'hlt) hp
      have hdi : vs.size - (i + 1) = d := by omega
      exact ih _ _ _ hp1 hdi
    · exact hp

theorem copyArrayFrom_preserves_WF (m : Module) (p : Process) (src : Heap)
    (vs : Array Value) (hp : Process.WF m p) :
    Process.WF m (copyArrayFrom p src vs).1 :=
  copyArrayFrom.go_preserves_WF m p src vs 0 _ hp

theorem process_set_mailbox_WF (m : Module) (p : Process) (mb : Array Value)
    (hp : Process.WF m p) : Process.WF m { p with mailbox := mb } := by
  refine And.intro hp.1 ?_
  cases hres : p.result with
  | some _ => simpa [Process.WF, hres] using hp.2
  | none =>
    cases hst : p.status with
    | exited => simp [Process.WF, hres, hst] at hp
    | waiting => simpa [Process.WF, hres, hst] using hp.2
    | runnable => simpa [Process.WF, hres, hst] using hp.2

theorem installHeap_preserves_WF (m : Module) (p : Process) (h0 : Heap)
    (hp : Process.WF m p) (hy : 0 < h0.youngCapacity) :
    Process.WF m (installHeap p h0) :=
  process_set_heap_WF m p _ hp
    (Heap.sanitized_heap_WF_tight _ _ _ _ _ hy _ (Nat.min_le_right _ _))

/-- Evacuators that leave non-ref values (and the to-space / forward table) untouched. -/
def Evac.FixesImm (ev : Evac) : Prop :=
  ∀ fwd neu v, (¬ ∃ r, v = .ref r) → ev fwd neu v = (fwd, neu, v)

theorem evacuateValue_fixesImm (fuel : Nat) (old : Heap) :
    Evac.FixesImm (Heap.evacuateValue fuel old) :=
  fun fwd neu v hne => Heap.evacuateValue_of_not_ref fuel old fwd neu v hne

theorem evacuateYoungValue_fixesImm (fuel : Nat) (old : Heap) :
    Evac.FixesImm (Heap.evacuateYoungValue fuel old) :=
  fun fwd neu v hne => Heap.evacuateYoungValue_of_not_ref fuel old fwd neu v hne

/-- Frames agree on function / ip / retDest / regs.size. -/
def Frame.SameMeta (f g : Frame) : Prop :=
  f.function = g.function ∧ f.ip = g.ip ∧ f.retDest = g.retDest ∧
    f.regs.size = g.regs.size

theorem Frame.SameMeta.trans {f g h : Frame} (h1 : Frame.SameMeta f g)
    (h2 : Frame.SameMeta g h) : Frame.SameMeta f h :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

theorem evacuateVals.go_size (ev : Evac) (vals : Array Value)
    (i : Nat) (fwd : Heap.Fwd) (neu : Array Node) (acc : Array Value) :
    (evacuateVals.go ev vals i fwd neu acc).2.2.size =
      acc.size + (vals.size - i) := by
  revert fwd neu acc
  induction hdiff : vals.size - i generalizing i with
  | zero =>
    intro fwd neu acc
    have hge : vals.size ≤ i := Nat.le_of_sub_eq_zero hdiff
    unfold evacuateVals.go
    simp [Nat.not_lt.mpr hge]
  | succ d ih =>
    intro fwd neu acc
    unfold evacuateVals.go
    split
    · rename_i hlt
      have hdi : vals.size - (i + 1) = d := by omega
      have := ih (i + 1) hdi
      simp only [this _ _ _, Array.size_push]; omega
    · omega

theorem evacuateVals_size (ev : Evac) (fwd : Heap.Fwd)
    (neu : Array Node) (vals : Array Value) :
    (evacuateVals ev fwd neu vals).2.2.size = vals.size := by
  simpa [evacuateVals] using evacuateVals.go_size ev vals 0 fwd neu #[]

theorem evacuateFrame_meta (ev : Evac) (fwd : Heap.Fwd)
    (neu : Array Node) (frame : Frame) :
    (evacuateFrame ev fwd neu frame).2.2.function = frame.function ∧
    (evacuateFrame ev fwd neu frame).2.2.ip = frame.ip ∧
    (evacuateFrame ev fwd neu frame).2.2.retDest = frame.retDest ∧
    (evacuateFrame ev fwd neu frame).2.2.regs.size = frame.regs.size := by
  dsimp [evacuateFrame]
  refine ⟨rfl, rfl, rfl, ?_⟩
  simpa using evacuateVals_size ev fwd neu frame.regs

theorem evacuateFrame_preserves_WF (m : Module) (ev : Evac)
    (fwd : Heap.Fwd) (neu : Array Node) (frame : Frame)
    (hwf : Frame.WF m frame) :
    Frame.WF m (evacuateFrame ev fwd neu frame).2.2 := by
  have hm := evacuateFrame_meta ev fwd neu frame
  refine ⟨hwf.1, ?_, ?_, ?_⟩
  · simpa [hm.2.2.2, hm.1] using hwf.2.1
  · simpa [hm.2.1, hm.1] using hwf.2.2.1
  · simpa [hm.1] using hwf.2.2.2

theorem evacuateStack.go_size (ev : Evac) (stack : Array Frame)
    (i : Nat) (fwd : Heap.Fwd) (neu : Array Node) (acc : Array Frame) :
    (evacuateStack.go ev stack i fwd neu acc).2.2.size =
      acc.size + (stack.size - i) := by
  revert fwd neu acc
  induction hdiff : stack.size - i generalizing i with
  | zero =>
    intro fwd neu acc
    have hge : stack.size ≤ i := Nat.le_of_sub_eq_zero hdiff
    unfold evacuateStack.go
    simp [Nat.not_lt.mpr hge]
  | succ d ih =>
    intro fwd neu acc
    unfold evacuateStack.go
    split
    · rename_i hlt
      have hdi : stack.size - (i + 1) = d := by omega
      have := ih (i + 1) hdi
      simp only [this _ _ _, Array.size_push]; omega
    · omega

theorem map_sanitize_frame_WF (m : Module) (f : Frame) (bound : Nat)
    (hwf : Frame.WF m f) :
    Frame.WF m { f with regs := f.regs.map (Heap.sanitizeValue bound) } :=
  ⟨hwf.1, by simpa [Array.size_map] using hwf.2.1, hwf.2.2.1, hwf.2.2.2⟩

theorem map_sanitize_stackWF (m : Module) (stack : Array Frame) (bound : Nat)
    (hwf : Process.stackWF m stack) :
    Process.stackWF m
      (stack.map fun f => { f with regs := f.regs.map (Heap.sanitizeValue bound) }) := by
  have ⟨hframes, hrets⟩ := hwf
  have hsz :
      (stack.map fun f =>
        { f with regs := f.regs.map (Heap.sanitizeValue bound) }).size = stack.size :=
    Array.size_map
  refine And.intro ?_ ?_
  · intro i hi
    have hi0 : i < stack.size := by simpa [hsz] using hi
    rw [Array.getElem_map]
    exact map_sanitize_frame_WF m _ bound (hframes i hi0)
  · intro i hi hi0
    have hiS : i < stack.size := by simpa [hsz] using hi
    have hpred : i - 1 < stack.size := Nat.lt_of_le_of_lt (Nat.pred_le i) hiS
    rw [Array.getElem_map, Array.getElem_map]
    exact hrets i hiS hi0

/-- Evacuated stack (before sanitize) preserves `stackWF` from index 0. -/
theorem evacuateStack_preserves_stackWF (m : Module) (ev : Evac)
    (fwd0 : Heap.Fwd) (neu0 : Array Node) (stack : Array Frame) (hsw : Process.stackWF m stack) :
    Process.stackWF m
      (evacuateStack.go ev stack 0 fwd0 neu0 #[]).2.2 := by
  have go (i : Nat) (fwd : Heap.Fwd) (neu : Array Node) (acc : Array Frame)
      (haccSz : acc.size = i) (hle : i ≤ stack.size)
      (haccF : ∀ j, (hj : j < acc.size) → Frame.WF m (acc[j]'hj))
      (haccM : ∀ j, (hj : j < acc.size) →
        (acc[j]'hj).function =
          (stack[j]'(Nat.lt_of_lt_of_le hj (by omega))).function ∧
        (acc[j]'hj).retDest =
          (stack[j]'(Nat.lt_of_lt_of_le hj (by omega))).retDest) :
      Process.stackWF m (evacuateStack.go ev stack i fwd neu acc).2.2 := by
    have ⟨hframes, hrets⟩ := hsw
    revert fwd neu acc haccSz hle haccF haccM
    induction hdiff : stack.size - i generalizing i with
    | zero =>
      intro fwd neu acc haccSz hle haccF haccM
      have hge : stack.size ≤ i := Nat.le_of_sub_eq_zero hdiff
      have hiEq : i = stack.size := Nat.le_antisymm hle hge
      unfold evacuateStack.go
      split
      · rename_i hlt; exact absurd hlt (Nat.not_lt.mpr hge)
      · refine And.intro ?_ ?_
        · intro j hj; exact haccF j hj
        · intro j hj hj0
          have hjA : j < acc.size := hj
          have hjS : j < stack.size := by omega
          have hmJ := haccM j hjA
          have hmP := haccM (j - 1) (by omega)
          simpa [hmJ.2, hmP.1] using hrets j hjS hj0
    | succ d ih =>
      intro fwd neu acc haccSz hle haccF haccM
      unfold evacuateStack.go
      split
      · rename_i hlt
        let f' := (evacuateFrame ev fwd neu (stack[i]'hlt)).2.2
        have hfw : Frame.WF m f' :=
          evacuateFrame_preserves_WF m ev fwd neu (stack[i]'hlt) (hframes i hlt)
        have hm := evacuateFrame_meta ev fwd neu (stack[i]'hlt)
        have hdi : stack.size - (i + 1) = d := by omega
        refine ih (i + 1) hdi _ _ (acc.push f') ?_ (by omega) ?_ ?_
        · simp [Array.size_push, haccSz]
        · intro j hj
          have hj' : j < acc.size + 1 := by simpa [Array.size_push] using hj
          by_cases heq : j = acc.size
          · subst heq; simpa [Array.getElem_push_eq] using hfw
          · have hltj : j < acc.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj') heq
            simpa [Array.getElem_push_lt hltj] using haccF j hltj
        · intro j hj
          have hj' : j < acc.size + 1 := by simpa [Array.size_push] using hj
          by_cases heq : j = acc.size
          · subst heq
            simp only [Array.getElem_push_eq]
            simpa [haccSz] using And.intro hm.1 hm.2.2.1
          · have hltj : j < acc.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj') heq
            simpa [Array.getElem_push_lt hltj] using haccM j hltj
      · omega
  exact go 0 _ _ #[] rfl (Nat.zero_le _)
    (by intro j hj; cases hj) (by intro j hj; cases hj)


/-- Evacuated stack frames keep function / ip / retDest / regs.size. -/
theorem evacuateStack.go_frame_meta (ev : Evac) (stack : Array Frame)
    (i0 : Nat) (fwd : Heap.Fwd) (neu : Array Node) (acc : Array Frame)
    (hle : i0 ≤ stack.size) (haccSz : acc.size = i0)
    (haccMeta : ∀ j, j < acc.size → Frame.SameMeta (acc[j]!) (stack[j]!))
    (j : Nat) (hjS : j < stack.size) :
    Frame.SameMeta ((evacuateStack.go ev stack i0 fwd neu acc).2.2[j]!)
      (stack[j]!) := by
  revert fwd neu acc hle haccSz haccMeta
  induction hdiff : stack.size - i0 generalizing i0 with
  | zero =>
    intro fwd neu acc hle haccSz haccMeta
    have hge : stack.size ≤ i0 := Nat.le_of_sub_eq_zero hdiff
    unfold evacuateStack.go
    have hnlt : ¬ i0 < stack.size := Nat.not_lt.mpr hge
    rw [dite_eq_right hnlt]
    exact haccMeta j (by omega)
  | succ d ih =>
    intro fwd neu acc hle haccSz haccMeta
    have hlt : i0 < stack.size := by omega
    unfold evacuateStack.go
    rw [dite_eq_left hlt]
    have hdi : stack.size - (i0 + 1) = d := by omega
    have hmF := evacuateFrame_meta ev fwd neu (stack[i0]'hlt)
    refine ih (i0 + 1) hdi _ _ (acc.push (evacuateFrame ev fwd neu
        (stack[i0]'hlt)).2.2) (by omega) (by simp [Array.size_push, haccSz]) ?_
    intro k hk
    have hk1 : k < acc.size + 1 := by simpa [Array.size_push] using hk
    have hkS : k < stack.size := by omega
    rw [getElem!_pos _ k hk, getElem!_pos stack k hkS]
    by_cases heq : k = acc.size
    · subst heq
      have hi0 : acc.size = i0 := haccSz
      simp only [Array.getElem_push_eq]
      simpa [Frame.SameMeta, hi0] using hmF
    · have hltk : k < acc.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk1) heq
      rw [Array.getElem_push_lt hltk]
      have := haccMeta k hltk
      rwa [getElem!_pos _ k hltk, getElem!_pos stack k hkS] at this


theorem evacuateVals.go_immediate (ev : Evac) (hev : Evac.FixesImm ev) (vals : Array Value)
    (i : Nat) (fwd : Heap.Fwd) (neu : Array Node) (acc : Array Value)
    (hle : i ≤ vals.size) (haccSz : acc.size = i)
    (haccImm : ∀ k, k < acc.size → (¬ ∃ r, vals[k]! = .ref r) → acc[k]! = vals[k]!)
    (j : Nat) (hjS : j < vals.size) (hne : ¬ ∃ r, vals[j]! = .ref r) :
    (evacuateVals.go ev vals i fwd neu acc).2.2[j]! = vals[j]! := by
  revert fwd neu acc hle haccSz haccImm
  induction hdiff : vals.size - i generalizing i with
  | zero =>
    intro fwd neu acc hle haccSz haccImm
    have hge : vals.size ≤ i := Nat.le_of_sub_eq_zero hdiff
    unfold evacuateVals.go
    rw [dite_eq_right (Nat.not_lt.mpr hge)]
    exact haccImm j (by omega) hne
  | succ d ih =>
    intro fwd neu acc hle haccSz haccImm
    have hlt : i < vals.size := by omega
    unfold evacuateVals.go
    rw [dite_eq_left hlt]
    have hdi : vals.size - (i + 1) = d := by omega
    refine ih (i + 1) hdi _ _ _ (by omega) (by simp [Array.size_push, haccSz]) ?_
    intro k hk hnek
    have hk1 : k < acc.size + 1 := by simpa [Array.size_push] using hk
    have hkS : k < vals.size := by omega
    by_cases heq : k = acc.size
    · subst heq
      have hi0 : acc.size = i := haccSz
      have hne' : ¬ ∃ r, vals[i]'hlt = .ref r := by
        intro h
        apply hnek
        rcases h with ⟨r, hr⟩
        refine ⟨r, ?_⟩
        rw [getElem!_pos vals acc.size hkS]
        simpa [hi0] using hr
      rw [hev _ _ _ hne']
      dsimp only
      have hk' : acc.size < (acc.push (vals[i]'hlt)).size := by simp
      rw [getElem!_pos (acc.push (vals[i]'hlt)) acc.size hk',
        getElem!_pos vals acc.size hkS]
      rw [Array.getElem_push_eq]
      simp [hi0]
    · have hltk : k < acc.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk1) heq
      rw [getElem!_pos _ k hk, Array.getElem_push_lt hltk]
      have := haccImm k hltk hnek
      rwa [getElem!_pos _ k hltk] at this

theorem evacuateVals_immediate (ev : Evac) (hev : Evac.FixesImm ev) (fwd : Heap.Fwd)
    (neu : Array Node) (vals : Array Value) (j : Nat) (hj : j < vals.size)
    (hne : ¬ ∃ r, vals[j]! = .ref r) :
    (evacuateVals ev fwd neu vals).2.2[j]! = vals[j]! :=
  evacuateVals.go_immediate ev hev vals 0 fwd neu #[] (Nat.zero_le _) rfl
    (by intro k hk; simp at hk) j hj hne

theorem evacuateFrame_reg_immediate (ev : Evac) (hev : Evac.FixesImm ev) (fwd : Heap.Fwd)
    (neu : Array Node) (frame : Frame) (k : Nat) (hk : k < frame.regs.size)
    (hne : ¬ ∃ r, frame.regs[k]! = .ref r) :
    ((evacuateFrame ev fwd neu frame).2.2.regs)[k]! = frame.regs[k]! := by
  dsimp [evacuateFrame]
  exact evacuateVals_immediate ev hev fwd neu frame.regs k hk hne


theorem evacuateStack.go_reg_immediate (ev : Evac) (hev : Evac.FixesImm ev) (stack : Array Frame)
    (i0 : Nat) (fwd : Heap.Fwd) (neu : Array Node) (acc : Array Frame)
    (hle : i0 ≤ stack.size) (haccSz : acc.size = i0)
    (haccImm : ∀ j, j < acc.size → ∀ k, k < (stack[j]!).regs.size →
      (¬ ∃ r, (stack[j]!).regs[k]! = .ref r) →
      ((acc[j]!).regs)[k]! = (stack[j]!).regs[k]!)
    (j : Nat) (hjS : j < stack.size) (k : Nat) (hk : k < (stack[j]!).regs.size)
    (hne : ¬ ∃ r, (stack[j]!).regs[k]! = .ref r) :
    (((evacuateStack.go ev stack i0 fwd neu acc).2.2[j]!).regs)[k]! =
      (stack[j]!).regs[k]! := by
  revert fwd neu acc hle haccSz haccImm
  induction hdiff : stack.size - i0 generalizing i0 with
  | zero =>
    intro fwd neu acc hle haccSz haccImm
    have hge : stack.size ≤ i0 := Nat.le_of_sub_eq_zero hdiff
    unfold evacuateStack.go
    rw [dite_eq_right (Nat.not_lt.mpr hge)]
    exact haccImm j (by omega) k hk hne
  | succ d ih =>
    intro fwd neu acc hle haccSz haccImm
    have hlt : i0 < stack.size := by omega
    unfold evacuateStack.go
    rw [dite_eq_left hlt]
    have hdi : stack.size - (i0 + 1) = d := by omega
    refine ih (i0 + 1) hdi _ _ _ (by omega) (by simp [Array.size_push, haccSz]) ?_
    intro j' hj' k' hk' hne'
    have hj1 : j' < acc.size + 1 := by simpa [Array.size_push] using hj'
    have hjS' : j' < stack.size := by omega
    by_cases heq : j' = acc.size
    · subst heq
      have hi0 : acc.size = i0 := haccSz
      have hfr : ((evacuateFrame ev fwd neu (stack[i0]'hlt)).2.2.regs)[k']! =
          (stack[i0]'hlt).regs[k']! := by
        apply evacuateFrame_reg_immediate ev hev
        · simpa [getElem!_pos stack i0 hlt, hi0] using hk'
        · simpa [getElem!_pos stack i0 hlt, hi0] using hne'
      have hpush : (acc.push (evacuateFrame ev fwd neu (stack[i0]'hlt)).2.2)[acc.size]! =
          (evacuateFrame ev fwd neu (stack[i0]'hlt)).2.2 := by
        rw [getElem!_pos _ acc.size (by simp), Array.getElem_push_eq]
      have hst : stack[acc.size]! = stack[i0]'hlt := by
        rw [hi0, getElem!_pos stack i0 hlt]
      change (((acc.push (evacuateFrame ev fwd neu (stack[i0]'hlt)).2.2)[acc.size]!).regs)[k']! =
        ((stack[acc.size]!).regs)[k']!
      rw [hpush, hst]
      exact hfr
    · have hltj : j' < acc.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj1) heq
      rw [getElem!_pos _ j' hj', Array.getElem_push_lt hltj]
      have := haccImm j' hltj k' hk' hne'
      rwa [getElem!_pos _ j' hltj] at this



/-! ### Root rewriting: `collectWith` (shared by minor / major GC) -/

section Collect

variable (ev : Evac) (fwd0 : Heap.Fwd) (neu0 : Array Node) (p : Process)

theorem collectWith_stack_size :
    (collectWith ev fwd0 neu0 p).2.1.size = p.stack.size := by
  simp only [collectWith, Array.size_map]
  simpa using evacuateStack.go_size ev p.stack 0 fwd0 neu0 #[]

theorem collectWith_mailbox_size :
    (collectWith ev fwd0 neu0 p).2.2.1.size = p.mailbox.size := by
  simp only [collectWith, Array.size_map]
  exact evacuateVals_size ev _ _ p.mailbox

theorem collectWith_result_none :
    (collectWith ev fwd0 neu0 p).2.2.2 = none ↔ p.result = none := by
  unfold collectWith
  cases hr : p.result <;> simp

theorem collectWith_stackWF (m : Module) (hsw : Process.stackWF m p.stack) :
    Process.stackWF m (collectWith ev fwd0 neu0 p).2.1 := by
  simp only [collectWith]
  exact map_sanitize_stackWF m _ _ (evacuateStack_preserves_stackWF m ev fwd0 neu0 _ hsw)

theorem collectWith_frame_meta (i : Nat) (hi : i < p.stack.size) :
    Frame.SameMeta ((collectWith ev fwd0 neu0 p).2.1[i]!) (p.stack[i]!) := by
  have hi' : i < (collectWith ev fwd0 neu0 p).2.1.size := by
    simpa [collectWith_stack_size] using hi
  have hszGo := evacuateStack.go_size ev p.stack 0 fwd0 neu0 #[]
  have hm := evacuateStack.go_frame_meta ev p.stack 0 fwd0 neu0 #[]
    (Nat.zero_le _) rfl (by intro j hj; simp at hj) i hi
  have hgoLt : i < (evacuateStack.go ev p.stack 0 fwd0 neu0 #[]).2.2.size := by
    simpa [hszGo] using hi
  rw [getElem!_pos _ i hgoLt] at hm
  rw [getElem!_pos _ i hi']
  rw [getElem!_pos _ i hi] at hm ⊢
  simp only [collectWith]
  rw [Array.getElem_map]
  obtain ⟨h1, h2, h3, h4⟩ := hm
  exact ⟨h1, h2, h3, by simpa [Array.size_map] using h4⟩

theorem collectWith_reg_immediate (hev : Evac.FixesImm ev) (i : Nat)
    (hi : i < p.stack.size) (k : Nat) (hk : k < (p.stack[i]!).regs.size)
    (hne : ¬ ∃ r, (p.stack[i]!).regs[k]! = .ref r) :
    ((((collectWith ev fwd0 neu0 p).2.1[i]!).regs))[k]! = (p.stack[i]!).regs[k]! := by
  have hszGo := evacuateStack.go_size ev p.stack 0 fwd0 neu0 #[]
  have hm := evacuateStack.go_reg_immediate ev hev p.stack 0 fwd0 neu0 #[]
    (Nat.zero_le _) rfl (by intro j hj; simp at hj) i hi k hk hne
  have hgoLt : i < (evacuateStack.go ev p.stack 0 fwd0 neu0 #[]).2.2.size := by
    simpa [hszGo] using hi
  have hi' : i < (collectWith ev fwd0 neu0 p).2.1.size := by
    simpa [collectWith_stack_size] using hi
  rw [getElem!_pos _ i hgoLt] at hm
  rw [getElem!_pos _ i hi']
  have hm2 := evacuateStack.go_frame_meta ev p.stack 0 fwd0 neu0 #[]
    (Nat.zero_le _) rfl (by intro j hj; simp at hj) i hi
  rw [getElem!_pos _ i hgoLt, getElem!_pos _ i hi] at hm2
  have hkG : k < ((evacuateStack.go ev p.stack 0 fwd0 neu0 #[]).2.2[i]'hgoLt).regs.size := by
    rw [hm2.2.2.2, ← getElem!_pos p.stack i hi]; exact hk
  simp only [collectWith]
  rw [Array.getElem_map]
  show (((evacuateStack.go ev p.stack 0 fwd0 neu0 #[]).2.2[i]'hgoLt).regs.map
      (Heap.sanitizeValue _))[k]! = _
  rw [getElem!_pos _ k (by simpa [Array.size_map] using hkG), Array.getElem_map,
    ← getElem!_pos _ k hkG, hm]
  exact Heap.sanitizeValue_eq_of_not_ref _ _ hne

theorem collectWith_mailbox_immediate (hev : Evac.FixesImm ev) (j : Nat)
    (hj : j < p.mailbox.size) (hne : ¬ ∃ r, p.mailbox[j]! = .ref r) :
    (collectWith ev fwd0 neu0 p).2.2.1[j]! = p.mailbox[j]! := by
  have hev' := evacuateVals_immediate ev hev
    (evacuateStack.go ev p.stack 0 fwd0 neu0 #[]).1
    (evacuateStack.go ev p.stack 0 fwd0 neu0 #[]).2.1 p.mailbox j hj hne
  have hsz := evacuateVals_size ev (evacuateStack.go ev p.stack 0 fwd0 neu0 #[]).1
    (evacuateStack.go ev p.stack 0 fwd0 neu0 #[]).2.1 p.mailbox
  have hlt : j < (evacuateVals ev (evacuateStack.go ev p.stack 0 fwd0 neu0 #[]).1
      (evacuateStack.go ev p.stack 0 fwd0 neu0 #[]).2.1 p.mailbox).2.2.size := by
    simpa [hsz] using hj
  rw [getElem!_pos _ j hlt] at hev'
  have hlt' : j < (collectWith ev fwd0 neu0 p).2.2.1.size := by
    simpa [collectWith_mailbox_size] using hj
  rw [getElem!_pos _ j hlt', getElem!_pos _ j hj]
  rw [getElem!_pos _ j hj] at hev'
  simp only [collectWith]
  rw [Array.getElem_map, hev']
  exact Heap.sanitizeValue_eq_of_not_ref _ _ (by
    intro h; apply hne; rcases h with ⟨r, hr⟩
    exact ⟨r, by rw [getElem!_pos _ j hj]; exact hr⟩)

theorem collectWith_result_immediate (hev : Evac.FixesImm ev) (v : Value)
    (hv : p.result = some v) (hne : ¬ ∃ r, v = .ref r) :
    (collectWith ev fwd0 neu0 p).2.2.2 = some v := by
  simp only [collectWith, hv]
  rw [hev _ _ _ hne]
  simp [Heap.sanitizeValue_eq_of_not_ref _ _ hne]

theorem collectWith_regs_bound (i : Nat) (hi : i < (collectWith ev fwd0 neu0 p).2.1.size)
    (j : Nat) (hj : j < ((collectWith ev fwd0 neu0 p).2.1[i]'hi).regs.size) :
    Heap.valueBound (collectWith ev fwd0 neu0 p).1.size
      (((collectWith ev fwd0 neu0 p).2.1[i]'hi).regs[j]'hj) := by
  simp only [collectWith, Array.getElem_map]
  exact Heap.sanitizeValue_valueBound _ _

theorem collectWith_mailbox_bound (i : Nat)
    (hi : i < (collectWith ev fwd0 neu0 p).2.2.1.size) :
    Heap.valueBound (collectWith ev fwd0 neu0 p).1.size
      ((collectWith ev fwd0 neu0 p).2.2.1[i]'hi) := by
  simp only [collectWith, Array.getElem_map]
  exact Heap.sanitizeValue_valueBound _ _

theorem collectWith_result_bound (v : Value)
    (hv : (collectWith ev fwd0 neu0 p).2.2.2 = some v) :
    Heap.valueBound (collectWith ev fwd0 neu0 p).1.size v := by
  simp only [collectWith] at hv ⊢
  cases hr : p.result with
  | none => simp [hr] at hv
  | some v0 =>
    simp only [hr] at hv
    injection hv with heq
    subst heq
    exact Heap.sanitizeValue_valueBound _ _

theorem collectWith_nodes_sanitized :
    ∃ X, (collectWith ev fwd0 neu0 p).1 = Heap.sanitizeNodes X := ⟨_, rfl⟩

end Collect

/-! ### `GcRel`: what any root-rewriting collection `p ⟶ q` guarantees -/

structure GcRel (p q : Process) : Prop where
  pid : q.pid = p.pid
  status : q.status = p.status
  stack_size : q.stack.size = p.stack.size
  mailbox_size : q.mailbox.size = p.mailbox.size
  handlers : q.handlers = p.handlers
  result_none : q.result = none ↔ p.result = none
  youngCapacity : q.heap.youngCapacity = p.heap.youngCapacity
  heap_WF : 0 < p.heap.youngCapacity → Heap.WF q.heap
  rootsWF : 0 < p.heap.youngCapacity → Process.rootsWF q.heap q
  stackWF : ∀ m, Process.stackWF m p.stack → Process.stackWF m q.stack
  frame_meta : ∀ i, i < p.stack.size → Frame.SameMeta (q.stack[i]!) (p.stack[i]!)
  reg_immediate : ∀ i, i < p.stack.size → ∀ k, k < (p.stack[i]!).regs.size →
    (¬ ∃ r, (p.stack[i]!).regs[k]! = .ref r) →
    ((q.stack[i]!).regs)[k]! = (p.stack[i]!).regs[k]!
  mailbox_immediate : ∀ j, j < p.mailbox.size → (¬ ∃ r, p.mailbox[j]! = .ref r) →
    q.mailbox[j]! = p.mailbox[j]!
  result_immediate : ∀ v, p.result = some v → (¬ ∃ r, v = .ref r) → q.result = some v

theorem handlersWF_of_SameMeta (stack stack' : Array Frame) (handlers : Array Handler)
    (hsz : stack'.size = stack.size)
    (hmeta : ∀ i, i < stack.size → Frame.SameMeta (stack'[i]!) (stack[i]!))
    (h : Process.handlersWF stack handlers) :
    Process.handlersWF stack' handlers := by
  intro i hi
  have ⟨hd0, hdle, hip, hexc⟩ := h i hi
  let depth := (handlers[i]'hi).stackDepth
  have hdi : depth - 1 < stack.size := by omega
  have hm := hmeta (depth - 1) hdi
  refine ⟨hd0, by rw [hsz]; exact hdle, ?_, ?_⟩
  · have hfun : (stack'[depth - 1]!).function = (stack[depth - 1]!).function := hm.1
    simpa [depth, hfun, getElem!_pos] using hip
  · have hfun : (stack'[depth - 1]!).function = (stack[depth - 1]!).function := hm.1
    simpa [depth, hfun, getElem!_pos] using hexc

theorem GcRel.trans {p q r : Process} (h1 : GcRel p q) (h2 : GcRel q r) : GcRel p r where
  pid := h2.pid.trans h1.pid
  status := h2.status.trans h1.status
  stack_size := h2.stack_size.trans h1.stack_size
  mailbox_size := h2.mailbox_size.trans h1.mailbox_size
  handlers := h2.handlers.trans h1.handlers
  result_none := ⟨fun h => h1.result_none.1 (h2.result_none.1 h),
    fun h => h2.result_none.2 (h1.result_none.2 h)⟩
  youngCapacity := h2.youngCapacity.trans h1.youngCapacity
  heap_WF := fun hy => h2.heap_WF (by rw [h1.youngCapacity]; exact hy)
  rootsWF := fun hy => h2.rootsWF (by rw [h1.youngCapacity]; exact hy)
  stackWF := fun m hs => h2.stackWF m (h1.stackWF m hs)
  frame_meta := fun i hi =>
    (h2.frame_meta i (by rw [h1.stack_size]; exact hi)).trans (h1.frame_meta i hi)
  reg_immediate := fun i hi k hk hne => by
    have hm := h1.frame_meta i hi
    have e1 := h1.reg_immediate i hi k hk hne
    have hiq : i < q.stack.size := by rw [h1.stack_size]; exact hi
    have hkq : k < (q.stack[i]!).regs.size := by rw [hm.2.2.2]; exact hk
    have hneq : ¬ ∃ s, (q.stack[i]!).regs[k]! = .ref s := by rw [e1]; exact hne
    rw [h2.reg_immediate i hiq k hkq hneq, e1]
  mailbox_immediate := fun j hj hne => by
    have e1 := h1.mailbox_immediate j hj hne
    have hjq : j < q.mailbox.size := by rw [h1.mailbox_size]; exact hj
    have hneq : ¬ ∃ s, q.mailbox[j]! = .ref s := by rw [e1]; exact hne
    rw [h2.mailbox_immediate j hjq hneq, e1]
  result_immediate := fun v hv hne =>
    h2.result_immediate v (h1.result_immediate v hv hne) hne

theorem commitCollect_rel (ev : Evac) (hev : Evac.FixesImm ev) (fwd0 : Heap.Fwd)
    (neu0 : Array Node) (p : Process) (g mn : Nat) (want : Nat → Nat) :
    GcRel p (commitCollect p (collectWith ev fwd0 neu0 p) g mn want) := by
  have hheap : 0 < p.heap.youngCapacity →
      Heap.WF (commitCollect p (collectWith ev fwd0 neu0 p) g mn want).heap := by
    intro hy
    obtain ⟨X, hX⟩ := collectWith_nodes_sanitized ev fwd0 neu0 p
    simp only [commitCollect]
    rw [hX]
    refine Heap.sanitized_heap_WF_cap X _ _ _ _ _ ?_ ?_ hy (Nat.le_refl _)
    · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_max_right _ _))
    · exact Nat.lt_of_lt_of_le (Nat.succ_pos 0)
        (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
          (Nat.le_max_right _ _))
  refine
    { pid := rfl, status := rfl
      stack_size := collectWith_stack_size ev fwd0 neu0 p
      mailbox_size := collectWith_mailbox_size ev fwd0 neu0 p
      handlers := rfl
      result_none := collectWith_result_none ev fwd0 neu0 p
      youngCapacity := rfl
      heap_WF := hheap
      rootsWF := ?_
      stackWF := fun m hs => collectWith_stackWF ev fwd0 neu0 p m hs
      frame_meta := fun i hi => collectWith_frame_meta ev fwd0 neu0 p i hi
      reg_immediate := fun i hi k hk hne =>
        collectWith_reg_immediate ev fwd0 neu0 p hev i hi k hk hne
      mailbox_immediate := fun j hj hne =>
        collectWith_mailbox_immediate ev fwd0 neu0 p hev j hj hne
      result_immediate := fun v hv hne =>
        collectWith_result_immediate ev fwd0 neu0 p hev v hv hne }
  intro hy
  have hH := hheap hy
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro i hi j hj
    exact Heap.valueWF_of_valueBound _ hH _
      (collectWith_regs_bound ev fwd0 neu0 p i hi j hj)
  · intro i hi
    exact Heap.valueWF_of_valueBound _ hH _
      (collectWith_mailbox_bound ev fwd0 neu0 p i hi)
  · cases hres : (commitCollect p (collectWith ev fwd0 neu0 p) g mn want).result with
    | none => trivial
    | some v =>
      exact Heap.valueWF_of_valueBound _ hH _
        (collectWith_result_bound ev fwd0 neu0 p v hres)

theorem minorGc_rel (p : Process) : GcRel p (minorGc p) :=
  commitCollect_rel (Heap.evacuateYoungValue (Heap.evacuateFuel p.heap.nodes.size) p.heap)
    (evacuateYoungValue_fixesImm _ _) (Array.replicate p.heap.nodes.size none)
    (p.heap.nodes.extract 0 p.heap.oldSize) p p.heap.gcCount (p.heap.minorCount + 1)
    (fun _ => 0)

theorem majorGc_rel (p : Process) : GcRel p (majorGc p) :=
  commitCollect_rel (Heap.evacuateValue (Heap.evacuateFuel p.heap.nodes.size) p.heap)
    (evacuateValue_fixesImm _ _) (Array.replicate p.heap.nodes.size none) #[] p
    (p.heap.gcCount + 1) p.heap.minorCount
    (fun n => max (n * 2) (n + p.heap.youngCapacity))

theorem gc_rel (p : Process) : GcRel p (gc p) := by
  unfold gc
  dsimp only
  split
  · exact (minorGc_rel p).trans (majorGc_rel _)
  · exact minorGc_rel p

/-- A `GcRel` collection preserves process well-formedness. -/
theorem GcRel.preserves_WF {m : Module} {p q : Process} (hr : GcRel p q)
    (hp : Process.WF m p) : Process.WF m q := by
  refine And.intro (hr.heap_WF hp.1.2.1) ?_
  have hsz := hr.stack_size
  cases hqres : q.result with
  | some v =>
    have hpres : p.result ≠ none := fun h => by
      have := hr.result_none.2 h
      rw [hqres] at this; exact nomatch this
    cases hpr : p.result with
    | none => exact absurd hpr hpres
    | some v0 =>
      have hp' : p.stack.size = 0 ∧ p.status = .exited ∧ p.handlers = #[] := by
        have h := hp
        simp [Process.WF, hpr] at h
        exact ⟨(Array.size_eq_zero_iff).2 h.2.1, h.2.2.1, h.2.2.2⟩
      exact ⟨by rw [hsz]; exact hp'.1, by rw [hr.status]; exact hp'.2.1,
        by rw [hr.handlers]; exact hp'.2.2⟩
  | none =>
    have hpres : p.result = none := hr.result_none.1 hqres
    simp only [hr.status]
    cases hst : p.status with
    | exited =>
      have h := hp
      simp [Process.WF, hpres, hst] at h
    | waiting =>
      have hp' : p.stack.size > 0 ∧ Process.stackWF m p.stack ∧
          Process.handlersWF p.stack p.handlers := by
        have h := hp
        simp [Process.WF, hpres, hst] at h
        exact h.2
      refine ⟨by rw [hsz]; exact hp'.1, hr.stackWF m hp'.2.1, ?_⟩
      have hhand : q.handlers = p.handlers := hr.handlers
      simpa [hhand] using
        handlersWF_of_SameMeta p.stack q.stack p.handlers hsz
          (fun i hi => hr.frame_meta i hi) hp'.2.2
    | runnable =>
      have hp' : p.stack.size > 0 ∧ Process.stackWF m p.stack ∧
          Process.handlersWF p.stack p.handlers := by
        have h := hp
        simp [Process.WF, hpres, hst] at h
        exact h.2
      refine ⟨by rw [hsz]; exact hp'.1, hr.stackWF m hp'.2.1, ?_⟩
      have hhand : q.handlers = p.handlers := hr.handlers
      simpa [hhand] using
        handlersWF_of_SameMeta p.stack q.stack p.handlers hsz
          (fun i hi => hr.frame_meta i hi) hp'.2.2

/-! ### GC preserves WF / observational substrate (minor, major, combined) -/

theorem minor_gc_preserves_process_WF (m : Module) (p : Process)
    (hp : Process.WF m p) : Process.WF m (minorGc p) :=
  (minorGc_rel p).preserves_WF hp

theorem majorGc_preserves_process_WF (m : Module) (p : Process)
    (hp : Process.WF m p) : Process.WF m (majorGc p) :=
  (majorGc_rel p).preserves_WF hp

/-- GC (minor, then major if needed) preserves process well-formedness. -/
theorem gc_preserves_process_WF (m : Module) (p : Process)
    (hp : Process.WF m p) : Process.WF m (gc p) :=
  (gc_rel p).preserves_WF hp

theorem gc_preserves_WF (m : Module) (p : Process)
    (hp : Process.WF m p) : Process.WF m (gc p) :=
  gc_preserves_process_WF m p hp

theorem minorGc_heap_WF (p : Process) (hy : 0 < p.heap.youngCapacity) :
    Heap.WF (minorGc p).heap := (minorGc_rel p).heap_WF hy

theorem majorGc_heap_WF (p : Process) (hy : 0 < p.heap.youngCapacity) :
    Heap.WF (majorGc p).heap := (majorGc_rel p).heap_WF hy

theorem gc_heap_WF (p : Process) (hy : 0 < p.heap.youngCapacity) :
    Heap.WF (gc p).heap := (gc_rel p).heap_WF hy

theorem gc_stack_size (p : Process) : (gc p).stack.size = p.stack.size :=
  (gc_rel p).stack_size

theorem gc_rootsWF (p : Process) (hy : 0 < p.heap.youngCapacity) :
    Process.rootsWF (gc p).heap (gc p) := (gc_rel p).rootsWF hy

/-- Minor GC preserves heap WF and root `valueWF` (observational substrate). -/
theorem minor_gc_preserves_obs (p : Process) (hy : 0 < p.heap.youngCapacity) :
    Heap.WF (minorGc p).heap ∧ Process.rootsWF (minorGc p).heap (minorGc p) :=
  ⟨(minorGc_rel p).heap_WF hy, (minorGc_rel p).rootsWF hy⟩

theorem majorGc_preserves_obs (p : Process) (hy : 0 < p.heap.youngCapacity) :
    Heap.WF (majorGc p).heap ∧ Process.rootsWF (majorGc p).heap (majorGc p) :=
  ⟨(majorGc_rel p).heap_WF hy, (majorGc_rel p).rootsWF hy⟩

/-- GC preserves heap WF and root `valueWF` (observational substrate). -/
theorem gc_preserves_obs (p : Process) (hy : 0 < p.heap.youngCapacity) :
    Heap.WF (gc p).heap ∧ Process.rootsWF (gc p).heap (gc p) :=
  ⟨gc_heap_WF p hy, gc_rootsWF p hy⟩

theorem gc_preserves_obs_immediate (bound : Nat) (v : Value)
    (hne : ¬ ∃ r, v = .ref r) :
    Heap.sanitizeValue bound v = v :=
  Heap.sanitizeValue_eq_of_not_ref bound v hne

/-! ### Observational preservation of GC roots

Immediates in registers / mailbox / result are fixed points of every collection
(`GcRel.*_immediate`). Fueled materialization (`Heap.toTermFuel` / `toTerm'`) therefore
agrees on those roots (`*_toTermFuel_immediate`). Flat compounds agree across heaps
with the same immediate payload (`Heap.toTermFuel_flatCompound_congr`). Nested compound
roots are checked by `#guard` in `GCDemo`. -/

theorem minor_gc_frame_meta (p : Process) (i : Nat) (hi : i < p.stack.size) :
    Frame.SameMeta ((minorGc p).stack[i]!) (p.stack[i]!) :=
  (minorGc_rel p).frame_meta i hi

theorem majorGc_frame_meta (p : Process) (i : Nat) (hi : i < p.stack.size) :
    Frame.SameMeta ((majorGc p).stack[i]!) (p.stack[i]!) :=
  (majorGc_rel p).frame_meta i hi

theorem gc_frame_meta (p : Process) (i : Nat) (hi : i < p.stack.size) :
    Frame.SameMeta ((gc p).stack[i]!) (p.stack[i]!) :=
  (gc_rel p).frame_meta i hi

/-- Immediate mailbox entries are fixed by minor GC. -/
theorem minor_gc_mailbox_immediate (p : Process) (j : Nat) (hj : j < p.mailbox.size)
    (hne : ¬ ∃ r, p.mailbox[j]! = .ref r) :
    (minorGc p).mailbox[j]! = p.mailbox[j]! :=
  (minorGc_rel p).mailbox_immediate j hj hne

theorem majorGc_mailbox_immediate (p : Process) (j : Nat) (hj : j < p.mailbox.size)
    (hne : ¬ ∃ r, p.mailbox[j]! = .ref r) :
    (majorGc p).mailbox[j]! = p.mailbox[j]! :=
  (majorGc_rel p).mailbox_immediate j hj hne

/-- Immediate mailbox entries are fixed by `gc`. -/
theorem gc_mailbox_immediate (p : Process) (j : Nat) (hj : j < p.mailbox.size)
    (hne : ¬ ∃ r, p.mailbox[j]! = .ref r) :
    (gc p).mailbox[j]! = p.mailbox[j]! :=
  (gc_rel p).mailbox_immediate j hj hne

/-- An immediate process result is fixed by minor GC. -/
theorem minor_gc_result_immediate (p : Process) (v : Value) (hv : p.result = some v)
    (hne : ¬ ∃ r, v = .ref r) : (minorGc p).result = some v :=
  (minorGc_rel p).result_immediate v hv hne

theorem majorGc_result_immediate (p : Process) (v : Value) (hv : p.result = some v)
    (hne : ¬ ∃ r, v = .ref r) : (majorGc p).result = some v :=
  (majorGc_rel p).result_immediate v hv hne

/-- An immediate process result is fixed by `gc`. -/
theorem gc_result_immediate (p : Process) (v : Value) (hv : p.result = some v)
    (hne : ¬ ∃ r, v = .ref r) : (gc p).result = some v :=
  (gc_rel p).result_immediate v hv hne

/-- Immediate registers of every frame are fixed by minor GC. -/
theorem minor_gc_frame_reg_immediate (p : Process) (i : Nat) (hi : i < p.stack.size)
    (k : Nat) (hk : k < (p.stack[i]!).regs.size)
    (hne : ¬ ∃ r, (p.stack[i]!).regs[k]! = .ref r) :
    (((minorGc p).stack[i]!).regs)[k]! = (p.stack[i]!).regs[k]! :=
  (minorGc_rel p).reg_immediate i hi k hk hne

theorem majorGc_frame_reg_immediate (p : Process) (i : Nat) (hi : i < p.stack.size)
    (k : Nat) (hk : k < (p.stack[i]!).regs.size)
    (hne : ¬ ∃ r, (p.stack[i]!).regs[k]! = .ref r) :
    (((majorGc p).stack[i]!).regs)[k]! = (p.stack[i]!).regs[k]! :=
  (majorGc_rel p).reg_immediate i hi k hk hne

/-- Immediate registers of every frame are fixed by `gc`. -/
theorem gc_frame_reg_immediate (p : Process) (i : Nat) (hi : i < p.stack.size)
    (k : Nat) (hk : k < (p.stack[i]!).regs.size)
    (hne : ¬ ∃ r, (p.stack[i]!).regs[k]! = .ref r) :
    (((gc p).stack[i]!).regs)[k]! = (p.stack[i]!).regs[k]! :=
  (gc_rel p).reg_immediate i hi k hk hne

/-! ### Fueled `toTerm` observational equality under GC -/

theorem GcRel.toTermFuel_mailbox_immediate {p q : Process} (hr : GcRel p q)
    (j : Nat) (hj : j < p.mailbox.size) (fuel₁ fuel₂ : Nat)
    (hne : ¬ ∃ r, p.mailbox[j]! = .ref r) (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    Heap.toTermFuel fuel₁ q.heap (q.mailbox[j]!) =
      Heap.toTermFuel fuel₂ p.heap (p.mailbox[j]!) := by
  have heq := hr.mailbox_immediate j hj hne
  rw [heq]
  exact Heap.toTermFuel_immediate_eq fuel₁ fuel₂ q.heap p.heap _ hne h1 h2

theorem GcRel.toTermFuel_result_immediate {p q : Process} (hr : GcRel p q)
    (v : Value) (hv : p.result = some v) (fuel₁ fuel₂ : Nat)
    (hne : ¬ ∃ r, v = .ref r) (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    (match q.result with
      | some v' => Heap.toTermFuel fuel₁ q.heap v'
      | none => Heap.toTermSentinel) =
      Heap.toTermFuel fuel₂ p.heap v := by
  have hq := hr.result_immediate v hv hne
  simp [hq]
  exact Heap.toTermFuel_immediate_eq fuel₁ fuel₂ q.heap p.heap v hne h1 h2

theorem GcRel.toTermFuel_reg_immediate {p q : Process} (hr : GcRel p q)
    (i : Nat) (hi : i < p.stack.size) (k : Nat)
    (hk : k < (p.stack[i]!).regs.size) (fuel₁ fuel₂ : Nat)
    (hne : ¬ ∃ r, (p.stack[i]!).regs[k]! = .ref r)
    (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    Heap.toTermFuel fuel₁ q.heap (((q.stack[i]!).regs)[k]!) =
      Heap.toTermFuel fuel₂ p.heap (((p.stack[i]!).regs)[k]!) := by
  have heq := hr.reg_immediate i hi k hk hne
  rw [heq]
  exact Heap.toTermFuel_immediate_eq fuel₁ fuel₂ q.heap p.heap _ hne h1 h2

theorem minorGc_mailbox_toTermFuel_immediate (p : Process) (j : Nat)
    (hj : j < p.mailbox.size) (fuel₁ fuel₂ : Nat)
    (hne : ¬ ∃ r, p.mailbox[j]! = .ref r) (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    Heap.toTermFuel fuel₁ (minorGc p).heap ((minorGc p).mailbox[j]!) =
      Heap.toTermFuel fuel₂ p.heap (p.mailbox[j]!) :=
  (minorGc_rel p).toTermFuel_mailbox_immediate j hj fuel₁ fuel₂ hne h1 h2

theorem majorGc_mailbox_toTermFuel_immediate (p : Process) (j : Nat)
    (hj : j < p.mailbox.size) (fuel₁ fuel₂ : Nat)
    (hne : ¬ ∃ r, p.mailbox[j]! = .ref r) (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    Heap.toTermFuel fuel₁ (majorGc p).heap ((majorGc p).mailbox[j]!) =
      Heap.toTermFuel fuel₂ p.heap (p.mailbox[j]!) :=
  (majorGc_rel p).toTermFuel_mailbox_immediate j hj fuel₁ fuel₂ hne h1 h2

theorem gc_mailbox_toTermFuel_immediate (p : Process) (j : Nat)
    (hj : j < p.mailbox.size) (fuel₁ fuel₂ : Nat)
    (hne : ¬ ∃ r, p.mailbox[j]! = .ref r) (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    Heap.toTermFuel fuel₁ (gc p).heap ((gc p).mailbox[j]!) =
      Heap.toTermFuel fuel₂ p.heap (p.mailbox[j]!) :=
  (gc_rel p).toTermFuel_mailbox_immediate j hj fuel₁ fuel₂ hne h1 h2

theorem minorGc_result_toTermFuel_immediate (p : Process) (v : Value)
    (hv : p.result = some v) (fuel₁ fuel₂ : Nat)
    (hne : ¬ ∃ r, v = .ref r) (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    (match (minorGc p).result with
      | some v' => Heap.toTermFuel fuel₁ (minorGc p).heap v'
      | none => Heap.toTermSentinel) =
      Heap.toTermFuel fuel₂ p.heap v :=
  (minorGc_rel p).toTermFuel_result_immediate v hv fuel₁ fuel₂ hne h1 h2

theorem majorGc_result_toTermFuel_immediate (p : Process) (v : Value)
    (hv : p.result = some v) (fuel₁ fuel₂ : Nat)
    (hne : ¬ ∃ r, v = .ref r) (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    (match (majorGc p).result with
      | some v' => Heap.toTermFuel fuel₁ (majorGc p).heap v'
      | none => Heap.toTermSentinel) =
      Heap.toTermFuel fuel₂ p.heap v :=
  (majorGc_rel p).toTermFuel_result_immediate v hv fuel₁ fuel₂ hne h1 h2

theorem gc_result_toTermFuel_immediate (p : Process) (v : Value)
    (hv : p.result = some v) (fuel₁ fuel₂ : Nat)
    (hne : ¬ ∃ r, v = .ref r) (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    (match (gc p).result with
      | some v' => Heap.toTermFuel fuel₁ (gc p).heap v'
      | none => Heap.toTermSentinel) =
      Heap.toTermFuel fuel₂ p.heap v :=
  (gc_rel p).toTermFuel_result_immediate v hv fuel₁ fuel₂ hne h1 h2

theorem minorGc_reg_toTermFuel_immediate (p : Process) (i : Nat)
    (hi : i < p.stack.size) (k : Nat) (hk : k < (p.stack[i]!).regs.size)
    (fuel₁ fuel₂ : Nat) (hne : ¬ ∃ r, (p.stack[i]!).regs[k]! = .ref r)
    (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    Heap.toTermFuel fuel₁ (minorGc p).heap ((((minorGc p).stack[i]!).regs)[k]!) =
      Heap.toTermFuel fuel₂ p.heap (((p.stack[i]!).regs)[k]!) :=
  (minorGc_rel p).toTermFuel_reg_immediate i hi k hk fuel₁ fuel₂ hne h1 h2

theorem majorGc_reg_toTermFuel_immediate (p : Process) (i : Nat)
    (hi : i < p.stack.size) (k : Nat) (hk : k < (p.stack[i]!).regs.size)
    (fuel₁ fuel₂ : Nat) (hne : ¬ ∃ r, (p.stack[i]!).regs[k]! = .ref r)
    (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    Heap.toTermFuel fuel₁ (majorGc p).heap ((((majorGc p).stack[i]!).regs)[k]!) =
      Heap.toTermFuel fuel₂ p.heap (((p.stack[i]!).regs)[k]!) :=
  (majorGc_rel p).toTermFuel_reg_immediate i hi k hk fuel₁ fuel₂ hne h1 h2

theorem gc_reg_toTermFuel_immediate (p : Process) (i : Nat)
    (hi : i < p.stack.size) (k : Nat) (hk : k < (p.stack[i]!).regs.size)
    (fuel₁ fuel₂ : Nat) (hne : ¬ ∃ r, (p.stack[i]!).regs[k]! = .ref r)
    (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    Heap.toTermFuel fuel₁ (gc p).heap ((((gc p).stack[i]!).regs)[k]!) =
      Heap.toTermFuel fuel₂ p.heap (((p.stack[i]!).regs)[k]!) :=
  (gc_rel p).toTermFuel_reg_immediate i hi k hk fuel₁ fuel₂ hne h1 h2

/-- Top-frame register immediate roots: fueled materialization is preserved by GC. -/
theorem gc_top_reg_toTermFuel_immediate (p : Process) (htop : 0 < p.stack.size)
    (k : Nat) (hk : k < (p.stack[p.stack.size - 1]!).regs.size)
    (fuel₁ fuel₂ : Nat) (hne : ¬ ∃ r, (p.stack[p.stack.size - 1]!).regs[k]! = .ref r)
    (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    Heap.toTermFuel fuel₁ (gc p).heap
        ((((gc p).stack[(gc p).stack.size - 1]!).regs)[k]!) =
      Heap.toTermFuel fuel₂ p.heap (((p.stack[p.stack.size - 1]!).regs)[k]!) := by
  have hi : p.stack.size - 1 < p.stack.size := Nat.sub_one_lt_of_lt htop
  have hsz : (gc p).stack.size = p.stack.size := (gc_rel p).stack_size
  have hk' : k < (p.stack[p.stack.size - 1]!).regs.size := hk
  have := gc_reg_toTermFuel_immediate p (p.stack.size - 1) hi k hk' fuel₁ fuel₂ hne h1 h2
  -- rewrite index on the left via stack_size
  have hi' : (gc p).stack.size - 1 < (gc p).stack.size := by
    rw [hsz]; exact hi
  simpa [hsz, getElem!_pos] using this

theorem growAlloc_youngCapacity_pos (p : Process) (n : Node) :
    0 < (growAlloc p n).1.heap.youngCapacity :=
  Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_max_right _ _)

theorem growAlloc_preserves_WF (m : Module) (p : Process) (n : Node)
    (hp : Process.WF m p) (hn : ∀ b, Heap.nodeBound b n) :
    Process.WF m (growAlloc p n).1 := by
  let cap := max (p.heap.capacity * 2) (p.heap.nodes.size + 1)
  let ycap := max p.heap.youngCapacity (p.heap.youngSize + 1)
  have hpos : 0 < cap :=
    Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_max_right _ _)
  have hle : p.heap.nodes.size ≤ cap :=
    Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _)
  have hroom : p.heap.nodes.size < cap :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  have hypos : 0 < ycap :=
    Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_max_right _ _)
  have hwf' := Heap.grow_capacity_WF p.heap cap hp.1 hpos hle
  have hwf'' := Heap.grow_young_capacity_WF { p.heap with capacity := cap } ycap hwf' hypos
  have hh := Heap.allocForce_WF { p.heap with capacity := cap, youngCapacity := ycap } n
    hwf'' hroom (hn _)
  exact process_set_heap_WF m p _ hp hh

theorem allocCompound_preserves_WF (m : Module) (p : Process)
    (mk : Array Value → Node) (vs : Array Value)
    (hp : Process.WF m p) : Process.WF m (allocCompound p mk vs).1 := by
  dsimp [allocCompound]
  have hpPush : Process.WF m { p with mailbox := p.mailbox ++ vs } :=
    process_set_mailbox_WF m p _ hp
  cases halloc :
      ({ p with mailbox := p.mailbox ++ vs }).heap.alloc?
        (mk (({ p with mailbox := p.mailbox ++ vs }).mailbox.extract
          p.mailbox.size)) with
  | some pr =>
    simp only
    have hy : 0 < pr.1.youngCapacity := by
      rw [Heap.alloc?_some_youngCapacity _ _ halloc]; exact hp.1.2.1
    have hp1 := installHeap_preserves_WF m _ pr.1 hpPush hy
    exact process_set_mailbox_WF m _ _ hp1
  | none =>
    simp only
    have hpGc : Process.WF m (gc { p with mailbox := p.mailbox ++ vs }) :=
      gc_preserves_process_WF m _ hpPush
    cases halloc2 :
        (gc { p with mailbox := p.mailbox ++ vs }).heap.alloc?
          (mk ((gc { p with mailbox := p.mailbox ++ vs }).mailbox.extract
            p.mailbox.size)) with
    | some pr =>
      simp only
      have hy : 0 < pr.1.youngCapacity := by
        rw [Heap.alloc?_some_youngCapacity _ _ halloc2]; exact hpGc.1.2.1
      have hp1 := installHeap_preserves_WF m _ pr.1 hpGc hy
      exact process_set_mailbox_WF m _ _ hp1
    | none =>
      simp only
      have hp1 := installHeap_preserves_WF m _
        (growAlloc (gc { p with mailbox := p.mailbox ++ vs })
          (mk ((gc { p with mailbox := p.mailbox ++ vs }).mailbox.extract
            p.mailbox.size))).1.heap
        hpGc (growAlloc_youngCapacity_pos _ _)
      exact process_set_mailbox_WF m _ _ hp1

theorem allocMap_preserves_WF (m : Module) (p : Process)
    (entries : Array (Value × Value))
    (hp : Process.WF m p) : Process.WF m (allocMap p entries).1 := by
  dsimp [allocMap]
  have hpPush :
      Process.WF m { p with mailbox := p.mailbox ++ flattenMapEntries entries } :=
    process_set_mailbox_WF m p _ hp
  cases halloc :
      ({ p with mailbox := p.mailbox ++ flattenMapEntries entries }).heap.alloc?
        (Node.map (pairsFromFlat
          (({ p with mailbox := p.mailbox ++ flattenMapEntries entries }).mailbox.extract
            p.mailbox.size))) with
  | some pr =>
    simp only
    have hy : 0 < pr.1.youngCapacity := by
      rw [Heap.alloc?_some_youngCapacity _ _ halloc]; exact hp.1.2.1
    have hp1 := installHeap_preserves_WF m _ pr.1 hpPush hy
    exact process_set_mailbox_WF m _ _ hp1
  | none =>
    simp only
    have hpGc :
        Process.WF m (gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }) :=
      gc_preserves_process_WF m _ hpPush
    cases halloc2 :
        (gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }).heap.alloc?
          (Node.map (pairsFromFlat
            ((gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }).mailbox.extract
              p.mailbox.size))) with
    | some pr =>
      simp only
      have hy : 0 < pr.1.youngCapacity := by
        rw [Heap.alloc?_some_youngCapacity _ _ halloc2]; exact hpGc.1.2.1
      have hp1 := installHeap_preserves_WF m _ pr.1 hpGc hy
      exact process_set_mailbox_WF m _ _ hp1
    | none =>
      simp only
      have hp1 := installHeap_preserves_WF m _
        (growAlloc (gc { p with mailbox := p.mailbox ++ flattenMapEntries entries })
          (Node.map (pairsFromFlat
            ((gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }).mailbox.extract
              p.mailbox.size)))).1.heap
        hpGc (growAlloc_youngCapacity_pos _ _)
      exact process_set_mailbox_WF m _ _ hp1

theorem allocMap_meta (p : Process) (entries : Array (Value × Value)) :
    (allocMap p entries).1.status = p.status ∧
    (p.result = none → (allocMap p entries).1.result = none) ∧
    (allocMap p entries).1.pid = p.pid ∧
    (allocMap p entries).1.stack.size = p.stack.size := by
  dsimp [allocMap]
  have hr := gc_rel { p with mailbox := p.mailbox ++ flattenMapEntries entries }
  have hstat :
      (gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }).status = p.status :=
    hr.status
  have hresNone :
      p.result = none →
        (gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }).result = none :=
    fun h => hr.result_none.2 h
  have hpid :
      (gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }).pid = p.pid := hr.pid
  have hsz :
      (gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }).stack.size =
        p.stack.size := hr.stack_size
  cases halloc :
      ({ p with mailbox := p.mailbox ++ flattenMapEntries entries }).heap.alloc?
        (Node.map (pairsFromFlat
          (({ p with mailbox := p.mailbox ++ flattenMapEntries entries }).mailbox.extract
            p.mailbox.size))) with
  | some pr => simp [installHeap]
  | none =>
    simp only
    cases halloc2 :
        (gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }).heap.alloc?
          (Node.map (pairsFromFlat
            ((gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }).mailbox.extract
              p.mailbox.size))) with
    | some pr =>
      simp [installHeap, hstat, hpid, hsz]
      exact hresNone
    | none =>
      simp [installHeap, growAlloc, hstat, hpid, hsz]
      exact hresNone

theorem allocCompound_meta (p : Process) (mk : Array Value → Node) (vs : Array Value) :
    (allocCompound p mk vs).1.status = p.status ∧
    (p.result = none → (allocCompound p mk vs).1.result = none) ∧
    (allocCompound p mk vs).1.pid = p.pid ∧
    (allocCompound p mk vs).1.stack.size = p.stack.size := by
  dsimp [allocCompound]
  have hr := gc_rel { p with mailbox := p.mailbox ++ vs }
  have hstat : (gc { p with mailbox := p.mailbox ++ vs }).status = p.status := hr.status
  have hresNone :
      p.result = none → (gc { p with mailbox := p.mailbox ++ vs }).result = none :=
    fun h => hr.result_none.2 h
  have hpid : (gc { p with mailbox := p.mailbox ++ vs }).pid = p.pid := hr.pid
  have hsz : (gc { p with mailbox := p.mailbox ++ vs }).stack.size = p.stack.size :=
    hr.stack_size
  cases halloc :
      ({ p with mailbox := p.mailbox ++ vs }).heap.alloc?
        (mk (({ p with mailbox := p.mailbox ++ vs }).mailbox.extract
          p.mailbox.size)) with
  | some pr =>
    simp [installHeap]
  | none =>
    simp only
    cases halloc2 :
        (gc { p with mailbox := p.mailbox ++ vs }).heap.alloc?
          (mk ((gc { p with mailbox := p.mailbox ++ vs }).mailbox.extract
            p.mailbox.size)) with
    | some pr =>
      simp [installHeap, hstat, hpid, hsz]
      exact hresNone
    | none =>
      simp [installHeap, growAlloc, hstat, hpid, hsz]
      exact hresNone

mutual
  theorem allocTermFuel_preserves_WF (m : Module) (fuel : Nat) (p : Process) (t : Term)
      (hp : Process.WF m p) : Process.WF m (allocTermFuel fuel p t).1 := by
    match fuel with
    | 0 => simpa [allocTermFuel] using hp
    | fuel + 1 =>
      cases t with
      | nil => simpa [allocTermFuel] using hp
      | bool _ => simpa [allocTermFuel] using hp
      | int _ => simpa [allocTermFuel] using hp
      | atom _ => simpa [allocTermFuel] using hp
      | pid _ => simpa [allocTermFuel] using hp
      | tuple elems =>
        have hp' := allocTermArrayFuel_preserves_WF m fuel p elems 0 #[] hp
        simpa [allocTermFuel] using allocCompound_preserves_WF m _ Node.tuple _ hp'
      | list elems =>
        have hp' := allocTermArrayFuel_preserves_WF m fuel p elems 0 #[] hp
        simpa [allocTermFuel] using allocCompound_preserves_WF m _ Node.list _ hp'
      | map entries =>
        have hp' :=
          allocTermEntriesFuel_preserves_WF m fuel p (Term.sortMapEntries entries) 0 #[] hp
        simpa [allocTermFuel] using allocMap_preserves_WF m _ _ hp'
  termination_by (fuel, 0, 0)

  theorem allocTermArrayFuel_preserves_WF (m : Module) (fuel : Nat) (p : Process)
      (elems : Array Term) (i : Nat) (acc : Array Value)
      (hp : Process.WF m p) :
      Process.WF m (allocTermArrayFuel fuel p elems i acc).1 := by
    match fuel with
    | 0 => simpa [allocTermArrayFuel] using hp
    | fuel + 1 =>
      simp only [allocTermArrayFuel]
      split
      · rename_i hlt
        have hpPush := process_set_mailbox_WF m p (p.mailbox ++ acc) hp
        have hp1 :=
          allocTermFuel_preserves_WF m fuel { p with mailbox := p.mailbox ++ acc }
            (elems[i]'hlt) hpPush
        have hp2 := process_set_mailbox_WF m
          (allocTermFuel fuel { p with mailbox := p.mailbox ++ acc }
            (elems[i]'hlt)).1
          ((allocTermFuel fuel { p with mailbox := p.mailbox ++ acc }
            (elems[i]'hlt)).1.mailbox.extract 0 p.mailbox.size)
          hp1
        exact allocTermArrayFuel_preserves_WF m fuel _ elems (i + 1) _ hp2
      · exact hp
  termination_by (fuel, 1, elems.size - i)

  theorem allocTermEntriesFuel_preserves_WF (m : Module) (fuel : Nat) (p : Process)
      (entries : Array (Term × Term)) (i : Nat) (acc : Array (Value × Value))
      (hp : Process.WF m p) :
      Process.WF m (allocTermEntriesFuel fuel p entries i acc).1 := by
    match fuel with
    | 0 => simpa [allocTermEntriesFuel] using hp
    | fuel + 1 =>
      simp only [allocTermEntriesFuel]
      split
      · rename_i hlt
        let flat := flattenMapEntries acc
        have hpPush := process_set_mailbox_WF m p (p.mailbox ++ flat) hp
        let p1 := { p with mailbox := p.mailbox ++ flat }
        have hpK := allocTermFuel_preserves_WF m fuel p1 (entries[i]'hlt).1 hpPush
        let pk := allocTermFuel fuel p1 (entries[i]'hlt).1
        have hpV := allocTermFuel_preserves_WF m fuel pk.1 (entries[i]'hlt).2 hpK
        let pv := allocTermFuel fuel pk.1 (entries[i]'hlt).2
        have hpPop := process_set_mailbox_WF m pv.1
          (pv.1.mailbox.extract 0 p.mailbox.size) hpV
        exact allocTermEntriesFuel_preserves_WF m fuel _ entries (i + 1) _ hpPop
      · exact hp
  termination_by (fuel, 1, entries.size - i)
end

theorem allocTerm_preserves_WF (m : Module) (p : Process) (t : Term)
    (hp : Process.WF m p) : Process.WF m (allocTerm p t).1 :=
  allocTermFuel_preserves_WF m _ p t hp

mutual
  theorem allocTermFuel_meta (fuel : Nat) (p : Process) (t : Term)
      (hres : p.result = none) :
      (allocTermFuel fuel p t).1.status = p.status ∧
      (allocTermFuel fuel p t).1.result = none ∧
      (allocTermFuel fuel p t).1.pid = p.pid ∧
      (allocTermFuel fuel p t).1.stack.size = p.stack.size := by
    match fuel with
    | 0 => simp [allocTermFuel, hres]
    | fuel + 1 =>
      cases t with
      | nil | bool _ | int _ | atom _ | pid _ => simp [allocTermFuel, hres]
      | tuple elems =>
        have ha := allocTermArrayFuel_meta fuel p elems 0 #[] hres
        have hc := allocCompound_meta (allocTermArrayFuel fuel p elems 0 #[]).1
          Node.tuple (allocTermArrayFuel fuel p elems 0 #[]).2
        simp only [allocTermFuel]
        refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
        · exact hc.1.trans ha.1
        · exact hc.2.1 ha.2.1
        · exact hc.2.2.1.trans ha.2.2.1
        · exact hc.2.2.2.trans ha.2.2.2
      | list elems =>
        have ha := allocTermArrayFuel_meta fuel p elems 0 #[] hres
        have hc := allocCompound_meta (allocTermArrayFuel fuel p elems 0 #[]).1
          Node.list (allocTermArrayFuel fuel p elems 0 #[]).2
        simp only [allocTermFuel]
        refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
        · exact hc.1.trans ha.1
        · exact hc.2.1 ha.2.1
        · exact hc.2.2.1.trans ha.2.2.1
        · exact hc.2.2.2.trans ha.2.2.2
      | map entries =>
        have ha :=
          allocTermEntriesFuel_meta fuel p (Term.sortMapEntries entries) 0 #[] hres
        have hc :=
          allocMap_meta (allocTermEntriesFuel fuel p (Term.sortMapEntries entries) 0 #[]).1
            (allocTermEntriesFuel fuel p (Term.sortMapEntries entries) 0 #[]).2
        simp only [allocTermFuel]
        refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
        · exact hc.1.trans ha.1
        · exact hc.2.1 ha.2.1
        · exact hc.2.2.1.trans ha.2.2.1
        · exact hc.2.2.2.trans ha.2.2.2
  termination_by (fuel, 0, 0)

  theorem allocTermArrayFuel_meta (fuel : Nat) (p : Process) (elems : Array Term)
      (i : Nat) (acc : Array Value) (hres : p.result = none) :
      (allocTermArrayFuel fuel p elems i acc).1.status = p.status ∧
      (allocTermArrayFuel fuel p elems i acc).1.result = none ∧
      (allocTermArrayFuel fuel p elems i acc).1.pid = p.pid ∧
      (allocTermArrayFuel fuel p elems i acc).1.stack.size = p.stack.size := by
    match fuel with
    | 0 => simp [allocTermArrayFuel, hres]
    | fuel + 1 =>
      simp only [allocTermArrayFuel]
      split
      · rename_i hlt
        have h1 := allocTermFuel_meta fuel { p with mailbox := p.mailbox ++ acc }
          (elems[i]'hlt) (by simpa using hres)
        have h3 := allocTermArrayFuel_meta fuel
          { (allocTermFuel fuel { p with mailbox := p.mailbox ++ acc }
              (elems[i]'hlt)).1 with
            mailbox :=
              (allocTermFuel fuel { p with mailbox := p.mailbox ++ acc }
                (elems[i]'hlt)).1.mailbox.extract 0 p.mailbox.size }
          elems (i + 1)
          (((allocTermFuel fuel { p with mailbox := p.mailbox ++ acc }
              (elems[i]'hlt)).1.mailbox.extract p.mailbox.size).push
            (allocTermFuel fuel { p with mailbox := p.mailbox ++ acc }
              (elems[i]'hlt)).2)
          h1.2.1
        refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
        · exact h3.1.trans h1.1
        · exact h3.2.1
        · exact h3.2.2.1.trans h1.2.2.1
        · exact h3.2.2.2.trans h1.2.2.2
      · simp [hres]
  termination_by (fuel, 1, elems.size - i)

  theorem allocTermEntriesFuel_meta (fuel : Nat) (p : Process)
      (entries : Array (Term × Term)) (i : Nat) (acc : Array (Value × Value))
      (hres : p.result = none) :
      (allocTermEntriesFuel fuel p entries i acc).1.status = p.status ∧
      (allocTermEntriesFuel fuel p entries i acc).1.result = none ∧
      (allocTermEntriesFuel fuel p entries i acc).1.pid = p.pid ∧
      (allocTermEntriesFuel fuel p entries i acc).1.stack.size = p.stack.size := by
    match fuel with
    | 0 => simp [allocTermEntriesFuel, hres]
    | fuel + 1 =>
      simp only [allocTermEntriesFuel]
      split
      · rename_i hlt
        let flat := flattenMapEntries acc
        have h1 := allocTermFuel_meta fuel { p with mailbox := p.mailbox ++ flat }
          (entries[i]'hlt).1 (by simpa using hres)
        have h2 := allocTermFuel_meta fuel
          (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
            (entries[i]'hlt).1).1
          (entries[i]'hlt).2 h1.2.1
        have h3 := allocTermEntriesFuel_meta fuel
          { (allocTermFuel fuel
                (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
                  (entries[i]'hlt).1).1
                (entries[i]'hlt).2).1 with
            mailbox :=
              (allocTermFuel fuel
                  (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
                    (entries[i]'hlt).1).1
                  (entries[i]'hlt).2).1.mailbox.extract 0 p.mailbox.size }
          entries (i + 1)
          ((pairsFromFlat
              ((allocTermFuel fuel
                  (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
                    (entries[i]'hlt).1).1
                  (entries[i]'hlt).2).1.mailbox.extract p.mailbox.size)).push
            ((allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
                (entries[i]'hlt).1).2,
              (allocTermFuel fuel
                  (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
                    (entries[i]'hlt).1).1
                  (entries[i]'hlt).2).2))
          h2.2.1
        refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
        · exact h3.1.trans (h2.1.trans h1.1)
        · exact h3.2.1
        · exact h3.2.2.1.trans (h2.2.2.1.trans h1.2.2.1)
        · exact h3.2.2.2.trans (h2.2.2.2.trans h1.2.2.2)
      · simp [hres]
  termination_by (fuel, 1, entries.size - i)
end

theorem allocTerm_meta (p : Process) (t : Term) (hres : p.result = none) :
    (allocTerm p t).1.status = p.status ∧
    (allocTerm p t).1.result = none ∧
    (allocTerm p t).1.stack.size = p.stack.size := by
  simpa [allocTerm] using
    And.intro (allocTermFuel_meta _ p t hres).1
      (And.intro (allocTermFuel_meta _ p t hres).2.1
        (allocTermFuel_meta _ p t hres).2.2.2)

/-- Top frame of `q` agrees with the top frame of `p` on function and ip. -/
def TopMeta (p q : Process) : Prop :=
  (q.stack[q.stack.size - 1]!).function = (p.stack[p.stack.size - 1]!).function ∧
  (q.stack[q.stack.size - 1]!).ip = (p.stack[p.stack.size - 1]!).ip

theorem TopMeta.refl (p : Process) : TopMeta p p := ⟨rfl, rfl⟩

theorem TopMeta.trans {p q r : Process} (h1 : TopMeta p q) (h2 : TopMeta q r) :
    TopMeta p r :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem gc_top_frame_meta (p : Process) (hsz : 0 < p.stack.size) :
    TopMeta p (gc p) := by
  have hm := gc_frame_meta p (p.stack.size - 1) (Nat.sub_one_lt_of_lt hsz)
  have hs := gc_stack_size p
  unfold TopMeta
  rw [hs]
  exact ⟨hm.1, hm.2.1⟩

theorem allocCompound_stack (p : Process) (mk : Array Value → Node)
    (vs : Array Value) :
    (allocCompound p mk vs).1.stack = p.stack ∨
    (allocCompound p mk vs).1.stack = (gc { p with mailbox := p.mailbox ++ vs }).stack := by
  dsimp [allocCompound]
  cases halloc :
      ({ p with mailbox := p.mailbox ++ vs }).heap.alloc?
        (mk (({ p with mailbox := p.mailbox ++ vs }).mailbox.extract
          p.mailbox.size)) with
  | some pr =>
    left; simp [installHeap]
  | none =>
    simp only
    right
    cases halloc2 :
        (gc { p with mailbox := p.mailbox ++ vs }).heap.alloc?
          (mk ((gc { p with mailbox := p.mailbox ++ vs }).mailbox.extract
            p.mailbox.size)) with
    | some pr => simp [installHeap]
    | none => simp [installHeap, growAlloc]

theorem allocCompound_top_frame_meta (p : Process) (mk : Array Value → Node)
    (vs : Array Value) (hsz : 0 < p.stack.size) :
    TopMeta p (allocCompound p mk vs).1 := by
  rcases allocCompound_stack p mk vs with h | h
  · unfold TopMeta; rw [h]; exact ⟨rfl, rfl⟩
  · have hg := gc_top_frame_meta { p with mailbox := p.mailbox ++ vs } hsz
    unfold TopMeta at hg ⊢
    rw [h]; exact hg

theorem allocMap_stack (p : Process) (entries : Array (Value × Value)) :
    (allocMap p entries).1.stack = p.stack ∨
    (allocMap p entries).1.stack =
      (gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }).stack := by
  dsimp [allocMap]
  cases halloc :
      ({ p with mailbox := p.mailbox ++ flattenMapEntries entries }).heap.alloc?
        (Node.map (pairsFromFlat
          (({ p with mailbox := p.mailbox ++ flattenMapEntries entries }).mailbox.extract
            p.mailbox.size))) with
  | some pr => left; simp [installHeap]
  | none =>
    simp only
    right
    cases halloc2 :
        (gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }).heap.alloc?
          (Node.map (pairsFromFlat
            ((gc { p with mailbox := p.mailbox ++ flattenMapEntries entries }).mailbox.extract
              p.mailbox.size))) with
    | some pr => simp [installHeap]
    | none => simp [installHeap, growAlloc]

theorem allocMap_top_frame_meta (p : Process) (entries : Array (Value × Value))
    (hsz : 0 < p.stack.size) :
    TopMeta p (allocMap p entries).1 := by
  rcases allocMap_stack p entries with h | h
  · unfold TopMeta; rw [h]; exact ⟨rfl, rfl⟩
  · have hg := gc_top_frame_meta
      { p with mailbox := p.mailbox ++ flattenMapEntries entries } hsz
    unfold TopMeta at hg ⊢
    rw [h]; exact hg

mutual
  theorem allocTermFuel_top_frame_meta (fuel : Nat) (p : Process) (t : Term)
      (hres : p.result = none) (hsz : 0 < p.stack.size) :
      TopMeta p (allocTermFuel fuel p t).1 := by
    match fuel with
    | 0 => simp only [allocTermFuel]; exact TopMeta.refl _
    | fuel + 1 =>
      cases t with
      | nil | bool _ | int _ | atom _ | pid _ =>
        simp only [allocTermFuel]; exact TopMeta.refl _
      | tuple elems =>
        have ha := allocTermArrayFuel_top_frame_meta fuel p elems 0 #[] hres hsz
        have hszA : 0 < (allocTermArrayFuel fuel p elems 0 #[]).1.stack.size := by
          have := (allocTermArrayFuel_meta fuel p elems 0 #[] hres).2.2.2; omega
        have hc := allocCompound_top_frame_meta
          (allocTermArrayFuel fuel p elems 0 #[]).1 Node.tuple
          (allocTermArrayFuel fuel p elems 0 #[]).2 hszA
        simp only [allocTermFuel]
        exact ha.trans hc
      | list elems =>
        have ha := allocTermArrayFuel_top_frame_meta fuel p elems 0 #[] hres hsz
        have hszA : 0 < (allocTermArrayFuel fuel p elems 0 #[]).1.stack.size := by
          have := (allocTermArrayFuel_meta fuel p elems 0 #[] hres).2.2.2; omega
        have hc := allocCompound_top_frame_meta
          (allocTermArrayFuel fuel p elems 0 #[]).1 Node.list
          (allocTermArrayFuel fuel p elems 0 #[]).2 hszA
        simp only [allocTermFuel]
        exact ha.trans hc
      | map entries =>
        have ha :=
          allocTermEntriesFuel_top_frame_meta fuel p (Term.sortMapEntries entries) 0 #[]
            hres hsz
        have hszA :
            0 <
              (allocTermEntriesFuel fuel p (Term.sortMapEntries entries) 0 #[]).1.stack.size := by
          have :=
            (allocTermEntriesFuel_meta fuel p (Term.sortMapEntries entries) 0 #[] hres).2.2.2
          omega
        have hc :=
          allocMap_top_frame_meta
            (allocTermEntriesFuel fuel p (Term.sortMapEntries entries) 0 #[]).1
            (allocTermEntriesFuel fuel p (Term.sortMapEntries entries) 0 #[]).2 hszA
        simp only [allocTermFuel]
        exact ha.trans hc
  termination_by (fuel, 0, 0)

  theorem allocTermArrayFuel_top_frame_meta (fuel : Nat) (p : Process)
      (elems : Array Term) (i : Nat) (acc : Array Value)
      (hres : p.result = none) (hsz : 0 < p.stack.size) :
      TopMeta p (allocTermArrayFuel fuel p elems i acc).1 := by
    match fuel with
    | 0 => simp only [allocTermArrayFuel]; exact TopMeta.refl _
    | fuel + 1 =>
      simp only [allocTermArrayFuel]
      split
      · rename_i hlt
        have h1 := allocTermFuel_top_frame_meta fuel
          { p with mailbox := p.mailbox ++ acc } (elems[i]'hlt)
          (by simpa using hres) hsz
        have hm1 := allocTermFuel_meta fuel { p with mailbox := p.mailbox ++ acc }
          (elems[i]'hlt) (by simpa using hres)
        have hsz1 : 0 < (allocTermFuel fuel { p with mailbox := p.mailbox ++ acc }
            (elems[i]'hlt)).1.stack.size := by
          have : (allocTermFuel fuel { p with mailbox := p.mailbox ++ acc }
              (elems[i]'hlt)).1.stack.size = p.stack.size := hm1.2.2.2
          omega
        have h3 := allocTermArrayFuel_top_frame_meta fuel
          { (allocTermFuel fuel { p with mailbox := p.mailbox ++ acc }
              (elems[i]'hlt)).1 with
            mailbox :=
              (allocTermFuel fuel { p with mailbox := p.mailbox ++ acc }
                (elems[i]'hlt)).1.mailbox.extract 0 p.mailbox.size }
          elems (i + 1)
          (((allocTermFuel fuel { p with mailbox := p.mailbox ++ acc }
              (elems[i]'hlt)).1.mailbox.extract p.mailbox.size).push
            (allocTermFuel fuel { p with mailbox := p.mailbox ++ acc }
              (elems[i]'hlt)).2)
          hm1.2.1 hsz1
        exact h1.trans h3
      · exact TopMeta.refl _
  termination_by (fuel, 1, elems.size - i)

  theorem allocTermEntriesFuel_top_frame_meta (fuel : Nat) (p : Process)
      (entries : Array (Term × Term)) (i : Nat) (acc : Array (Value × Value))
      (hres : p.result = none) (hsz : 0 < p.stack.size) :
      TopMeta p (allocTermEntriesFuel fuel p entries i acc).1 := by
    match fuel with
    | 0 => simp only [allocTermEntriesFuel]; exact TopMeta.refl _
    | fuel + 1 =>
      simp only [allocTermEntriesFuel]
      split
      · rename_i hlt
        let flat := flattenMapEntries acc
        have h1 := allocTermFuel_top_frame_meta fuel
          { p with mailbox := p.mailbox ++ flat } (entries[i]'hlt).1
          (by simpa using hres) hsz
        have hm1 := allocTermFuel_meta fuel { p with mailbox := p.mailbox ++ flat }
          (entries[i]'hlt).1 (by simpa using hres)
        have h2 := allocTermFuel_top_frame_meta fuel
          (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
            (entries[i]'hlt).1).1
          (entries[i]'hlt).2 hm1.2.1
          (by
            have : (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
                (entries[i]'hlt).1).1.stack.size = p.stack.size := hm1.2.2.2
            omega)
        have hm2 := allocTermFuel_meta fuel
          (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
            (entries[i]'hlt).1).1
          (entries[i]'hlt).2 hm1.2.1
        have h3 := allocTermEntriesFuel_top_frame_meta fuel
          { (allocTermFuel fuel
                (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
                  (entries[i]'hlt).1).1
                (entries[i]'hlt).2).1 with
            mailbox :=
              (allocTermFuel fuel
                  (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
                    (entries[i]'hlt).1).1
                  (entries[i]'hlt).2).1.mailbox.extract 0 p.mailbox.size }
          entries (i + 1)
          ((pairsFromFlat
              ((allocTermFuel fuel
                  (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
                    (entries[i]'hlt).1).1
                  (entries[i]'hlt).2).1.mailbox.extract p.mailbox.size)).push
            ((allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
                (entries[i]'hlt).1).2,
              (allocTermFuel fuel
                  (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
                    (entries[i]'hlt).1).1
                  (entries[i]'hlt).2).2))
          hm2.2.1
          (by
            have hszEq :
                (allocTermFuel fuel
                    (allocTermFuel fuel { p with mailbox := p.mailbox ++ flat }
                      (entries[i]'hlt).1).1
                    (entries[i]'hlt).2).1.stack.size =
                  p.stack.size := by
              simpa [hm1.2.2.2] using hm2.2.2.2
            simpa [hszEq] using hsz)
        exact h1.trans (h2.trans h3)
      · exact TopMeta.refl _
  termination_by (fuel, 1, entries.size - i)
end

theorem allocTerm_top_frame_meta (p : Process) (t : Term)
    (hres : p.result = none) (hsz : 0 < p.stack.size) :
    TopMeta p (allocTerm p t).1 :=
  allocTermFuel_top_frame_meta _ p t hres hsz

theorem allocNode_preserves_WF (m : Module) (p : Process) (n : Node)
    (hp : Process.WF m p)
    (hn : ∀ b, Heap.nodeBound b n) :
    Process.WF m (allocNode p n).1 := by
  unfold allocNode
  cases halloc : p.heap.alloc? n with
  | some pr =>
    simp
    exact process_set_heap_WF m p pr.1 hp
      (Heap.alloc?_some_WF p.heap n hp.1 (hn _) halloc)
  | none =>
    simp only
    have hp1 := gc_preserves_process_WF m p hp
    cases halloc2 : (gc p).heap.alloc? n with
    | some pr =>
      simp only
      exact process_set_heap_WF m (gc p) pr.1 hp1
        (Heap.alloc?_some_WF (gc p).heap n hp1.1 (hn _) halloc2)
    | none =>
      simp only
      exact growAlloc_preserves_WF m (gc p) n hp1 hn

end Process

end Autumn
