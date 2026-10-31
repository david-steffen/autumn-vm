import Autumn.WellFormed
import Autumn.State

namespace Autumn
namespace Heap

/-! # Heap / GC lemmas -/

theorem sanitizeValue_valueBound (bound : Nat) (v : Value) :
    valueBound bound (sanitizeValue bound v) := by
  cases v with
  | ref r => dsimp [sanitizeValue]; split <;> rename_i h <;> first | exact h | trivial
  | nil => trivial
  | bool _ => trivial
  | int _ => trivial
  | atom _ => trivial
  | pid _ => trivial

theorem sanitizeNode_nodeBound (bound : Nat) (n : Node) :
    nodeBound bound (sanitizeNode bound n) := by
  cases n with
  | tuple elems =>
    intro i hi
    have hsz : (elems.map (sanitizeValue bound)).size = elems.size := Array.size_map
    have hi0 : i < elems.size := by simpa [sanitizeNode, hsz] using hi
    simpa [sanitizeNode, Array.getElem_map] using
      sanitizeValue_valueBound bound (elems[i]'hi0)
  | list elems =>
    intro i hi
    have hsz : (elems.map (sanitizeValue bound)).size = elems.size := Array.size_map
    have hi0 : i < elems.size := by simpa [sanitizeNode, hsz] using hi
    simpa [sanitizeNode, Array.getElem_map] using
      sanitizeValue_valueBound bound (elems[i]'hi0)

theorem sanitizeNodes_WF_nodes (neu : Array Node) :
    ∀ r, (hr : r < (sanitizeNodes neu).size) →
      nodeBound (sanitizeNodes neu).size ((sanitizeNodes neu)[r]'hr) := by
  intro r hr
  have hsz : (sanitizeNodes neu).size = neu.size := Array.size_map
  have hr0 : r < neu.size := by simpa [sanitizeNodes, hsz] using hr
  have hget : (sanitizeNodes neu)[r]'hr =
      sanitizeNode neu.size (neu[r]'hr0) := by
    simp [sanitizeNodes, Array.getElem_map]
  rw [hget]
  simpa [hsz] using sanitizeNode_nodeBound neu.size (neu[r]'hr0)

theorem sanitized_heap_WF (neu0 : Array Node) (oldCap youngCap gcCount minorCount : Nat)
    (hyoung : 0 < youngCap) :
    WF { nodes := sanitizeNodes neu0
         oldSize := (sanitizeNodes neu0).size
         youngCapacity := youngCap
         capacity := max oldCap ((sanitizeNodes neu0).size + 1)
         gcCount
         minorCount } :=
  ⟨Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_max_right _ _),
   hyoung,
   Nat.le_refl _,
   Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _),
   sanitizeNodes_WF_nodes neu0⟩

/-- Like `sanitized_heap_WF`, but capacity only covers `nodes.size` (no spare slot). -/
theorem sanitized_heap_WF_tight (neu0 : Array Node) (oldCap youngCap gcCount minorCount : Nat)
    (hyoung : 0 < youngCap) (hold : Nat) (holdLe : hold ≤ (sanitizeNodes neu0).size) :
    WF { nodes := sanitizeNodes neu0
         oldSize := hold
         youngCapacity := youngCap
         capacity := max oldCap (max (sanitizeNodes neu0).size 1)
         gcCount
         minorCount } :=
  ⟨Nat.lt_of_lt_of_le (Nat.succ_pos 0)
     (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)),
   hyoung,
   holdLe,
   Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
   sanitizeNodes_WF_nodes neu0⟩

/-- General capacity: any `cap` covering the sanitized nodes works. -/
theorem sanitized_heap_WF_cap (neu0 : Array Node) (cap youngCap gcCount minorCount hold : Nat)
    (hcap : (sanitizeNodes neu0).size ≤ cap) (hpos : 0 < cap)
    (hyoung : 0 < youngCap) (holdLe : hold ≤ (sanitizeNodes neu0).size) :
    WF { nodes := sanitizeNodes neu0
         oldSize := hold
         youngCapacity := youngCap
         capacity := cap
         gcCount
         minorCount } :=
  ⟨hpos, hyoung, holdLe, hcap, sanitizeNodes_WF_nodes neu0⟩

theorem valueWF_of_valueBound (h : Heap) (hwf : Heap.WF h) (v : Value)
    (hb : valueBound h.nodes.size v) : valueWF h v := by
  cases v with
  | ref r => exact ⟨hb, ⟨hb, hwf.2.2.2.2 r hb⟩⟩
  | nil => exact ⟨hb, trivial⟩
  | bool _ => exact ⟨hb, trivial⟩
  | int _ => exact ⟨hb, trivial⟩
  | atom _ => exact ⟨hb, trivial⟩
  | pid _ => exact ⟨hb, trivial⟩

theorem sanitizeValue_eq_of_not_ref (bound : Nat) (v : Value)
    (hne : ¬ ∃ r, v = .ref r) : sanitizeValue bound v = v := by
  cases v with
  | ref r => exact False.elim (hne ⟨r, rfl⟩)
  | nil => rfl
  | bool _ => rfl
  | int _ => rfl
  | atom _ => rfl
  | pid _ => rfl

/-- Evacuating an immediate leaves it unchanged (any fuel, any to-space). -/
theorem evacuateValue_of_not_ref (fuel : Nat) (old : Heap) (fwd : Fwd)
    (neu : Array Node) (v : Value) (hne : ¬ ∃ r, v = .ref r) :
    evacuateValue fuel old fwd neu v = (fwd, neu, v) := by
  cases fuel with
  | zero =>
    cases v with
    | ref r => exact False.elim (hne ⟨r, rfl⟩)
    | nil => simp [evacuateValue]
    | bool _ => simp [evacuateValue]
    | int _ => simp [evacuateValue]
    | atom _ => simp [evacuateValue]
    | pid _ => simp [evacuateValue]
  | succ fuel =>
    cases v with
    | ref r => exact False.elim (hne ⟨r, rfl⟩)
    | nil => simp [evacuateValue]
    | bool _ => simp [evacuateValue]
    | int _ => simp [evacuateValue]
    | atom _ => simp [evacuateValue]
    | pid _ => simp [evacuateValue]

/-- Evacuating an immediate (minor GC) leaves it unchanged. -/
theorem evacuateYoungValue_of_not_ref (fuel : Nat) (old : Heap) (fwd : Fwd)
    (neu : Array Node) (v : Value) (hne : ¬ ∃ r, v = .ref r) :
    evacuateYoungValue fuel old fwd neu v = (fwd, neu, v) := by
  cases fuel with
  | zero =>
    cases v with
    | ref r => exact False.elim (hne ⟨r, rfl⟩)
    | nil => simp [evacuateYoungValue]
    | bool _ => simp [evacuateYoungValue]
    | int _ => simp [evacuateYoungValue]
    | atom _ => simp [evacuateYoungValue]
    | pid _ => simp [evacuateYoungValue]
  | succ fuel =>
    cases v with
    | ref r => exact False.elim (hne ⟨r, rfl⟩)
    | nil => simp [evacuateYoungValue]
    | bool _ => simp [evacuateYoungValue]
    | int _ => simp [evacuateYoungValue]
    | atom _ => simp [evacuateYoungValue]
    | pid _ => simp [evacuateYoungValue]

theorem evacuateRoots_heap_WF (h : Heap) (roots : Array Value)
    (hy : 0 < h.youngCapacity) : WF (evacuateRoots h roots).1 := by
  simp only [evacuateRoots]
  exact sanitized_heap_WF_tight _ _ h.youngCapacity _ _ hy _ (Nat.le_refl _)

theorem grow_capacity_WF (h : Heap) (cap' : Nat) (hwf : WF h)
    (hpos : 0 < cap') (hle : h.nodes.size ≤ cap') :
    WF { h with capacity := cap' } :=
  ⟨hpos, hwf.2.1, hwf.2.2.1, hle, hwf.2.2.2.2⟩

theorem grow_young_capacity_WF (h : Heap) (ycap' : Nat) (hwf : WF h)
    (hpos : 0 < ycap') :
    WF { h with youngCapacity := ycap' } :=
  ⟨hwf.1, hpos, hwf.2.2.1, hwf.2.2.2.1, hwf.2.2.2.2⟩

theorem allocForce_WF (h : Heap) (n : Node) (hwf : WF h)
    (hroom : h.nodes.size < h.capacity)
    (hn : nodeBound (h.nodes.size + 1) n) : WF (allocForce h n).1 := by
  have hsz : (h.nodes.push n).size = h.nodes.size + 1 := Array.size_push _
  refine ⟨hwf.1, hwf.2.1, ?_, ?_, ?_⟩
  · simp [allocForce, hsz]; exact Nat.le_succ_of_le hwf.2.2.1
  · simpa [allocForce, hsz] using Nat.succ_le_of_lt hroom
  · intro r hr
    simp only [allocForce] at hr ⊢
    have hr' : r < h.nodes.size + 1 := by simpa [hsz] using hr
    by_cases heq : r = h.nodes.size
    · subst heq
      simpa [Array.getElem_push_eq] using hn
    · have hlt : r < h.nodes.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hr') heq
      have hget := Array.getElem_push_lt (xs := h.nodes) (x := n) hlt
      have bold := hwf.2.2.2.2 r hlt
      simpa [hget] using nodeBound_mono (Nat.le_succ _) _ bold

theorem ensureCapacity_nodes (h : Heap) : (ensureCapacity h).nodes = h.nodes := by
  unfold ensureCapacity; split <;> rfl

theorem ensureCapacity_youngCapacity (h : Heap) :
    (ensureCapacity h).youngCapacity = h.youngCapacity := by
  unfold ensureCapacity; split <;> rfl

theorem ensureYoung_nodes (h : Heap) : (ensureYoung h).nodes = h.nodes := by
  unfold ensureYoung; split <;> rfl

theorem ensureYoung_capacity (h : Heap) : (ensureYoung h).capacity = h.capacity := by
  unfold ensureYoung; split <;> rfl

theorem ensureYoung_youngCapacity_ge (h : Heap) :
    h.youngCapacity ≤ (ensureYoung h).youngCapacity := by
  unfold ensureYoung
  split
  · exact Nat.le_trans (Nat.le_mul_of_pos_right _ (by decide)) (Nat.le_max_left _ _)
  · exact Nat.le_refl _

theorem ensureCapacity_WF (h : Heap) (hwf : WF h) :
    WF (ensureCapacity h) ∧ h.nodes.size < (ensureCapacity h).capacity := by
  unfold ensureCapacity
  split
  · exact ⟨grow_capacity_WF h _ hwf
        (Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_max_right _ _))
        (Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _)),
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)⟩
  · rename_i hc
    exact ⟨hwf, Nat.lt_of_not_ge hc⟩

theorem ensureYoung_WF (h : Heap) (hwf : WF h) : WF (ensureYoung h) := by
  unfold ensureYoung
  split
  · exact grow_young_capacity_WF h _ hwf
      (Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_max_right _ _))
  · exact hwf

theorem allocGrow_WF (h : Heap) (n : Node) (hwf : WF h)
    (hn : nodeBound (h.nodes.size + 1) n) : WF (allocGrow h n).1 := by
  unfold allocGrow
  obtain ⟨hw1, hr1⟩ := ensureCapacity_WF h hwf
  have hw2 := ensureYoung_WF _ hw1
  refine allocForce_WF _ n hw2 ?_ ?_
  · rw [ensureYoung_nodes, ensureYoung_capacity, ensureCapacity_nodes]
    exact hr1
  · rw [ensureYoung_nodes, ensureCapacity_nodes]; exact hn

theorem allocGrow_size (h : Heap) (n : Node) :
    (allocGrow h n).1.nodes.size = h.nodes.size + 1 ∧
    (allocGrow h n).2 = h.nodes.size := by
  simp [allocGrow, allocForce, ensureYoung_nodes, ensureCapacity_nodes]

theorem allocGrow_youngCapacity_ge (h : Heap) (n : Node) :
    h.youngCapacity ≤ (allocGrow h n).1.youngCapacity := by
  have h1 := ensureYoung_youngCapacity_ge (ensureCapacity h)
  rw [ensureCapacity_youngCapacity] at h1
  exact h1

theorem allocGrow_ref_bound (h : Heap) (n : Node) (hwf : WF h)
    (hn : nodeBound (h.nodes.size + 1) n) :
    WF (allocGrow h n).1 ∧
      valueBound (allocGrow h n).1.nodes.size (.ref (allocGrow h n).2) := by
  refine ⟨allocGrow_WF h n hwf hn, ?_⟩
  have ⟨hsz, hr⟩ := allocGrow_size h n
  dsimp [valueBound]
  rw [hsz, hr]
  exact Nat.lt_succ_self _

theorem alloc?_some_room (h : Heap) (n : Node) {h' : Heap} {r : Ref}
    (hok : alloc? h n = some (h', r)) : h.nodes.size < h.capacity := by
  simp only [alloc?] at hok
  split at hok
  · exact nomatch hok
  · rename_i hroom
    simp at hroom
    omega

theorem alloc?_some_youngCapacity (h : Heap) (n : Node) {h' : Heap} {r : Ref}
    (hok : alloc? h n = some (h', r)) : h'.youngCapacity = h.youngCapacity := by
  simp only [alloc?] at hok
  split at hok
  · exact nomatch hok
  · injection hok with heq
    have hh : h' = { h with nodes := h.nodes.push n } :=
      (congrArg Prod.fst heq).symm
    subst hh
    rfl

theorem alloc?_some_WF (h : Heap) (n : Node) (hwf : WF h)
    (hn : nodeBound (h.nodes.size + 1) n) {h' : Heap} {r : Ref}
    (hok : alloc? h n = some (h', r)) : WF h' := by
  have hroom := alloc?_some_room h n hok
  simp only [alloc?] at hok
  split at hok
  · exact nomatch hok
  · injection hok with heq
    have hh : h' = { h with nodes := h.nodes.push n } :=
      (congrArg Prod.fst heq).symm
    subst hh
    exact allocForce_WF h n hwf hroom hn

mutual
  theorem copyValueFuel_youngCapacity_ge (fuel : Nat) (src dst : Heap) (v : Value) :
      dst.youngCapacity ≤ (copyValueFuel fuel src dst v).1.youngCapacity := by
    match fuel with
    | 0 => cases v <;> simp [copyValueFuel]
    | fuel + 1 =>
      cases v with
      | nil => simp [copyValueFuel]
      | bool _ => simp [copyValueFuel]
      | int _ => simp [copyValueFuel]
      | atom _ => simp [copyValueFuel]
      | pid _ => simp [copyValueFuel]
      | ref r =>
        simp only [copyValueFuel]
        split
        · exact Nat.le_refl _
        · rename_i elems _
          have h1 := copyArrayFuel_youngCapacity_ge fuel src dst elems 0 #[]
          exact Nat.le_trans h1
            (allocGrow_youngCapacity_ge (copyArrayFuel fuel src dst elems 0 #[]).1 _)
        · rename_i elems _
          have h1 := copyArrayFuel_youngCapacity_ge fuel src dst elems 0 #[]
          exact Nat.le_trans h1
            (allocGrow_youngCapacity_ge (copyArrayFuel fuel src dst elems 0 #[]).1 _)
  termination_by (fuel, 0, 0)

  theorem copyArrayFuel_youngCapacity_ge (fuel : Nat) (src dst : Heap)
      (elems : Array Value) (i : Nat) (acc : Array Value) :
      dst.youngCapacity ≤ (copyArrayFuel fuel src dst elems i acc).1.youngCapacity := by
    match fuel with
    | 0 => simp [copyArrayFuel]
    | fuel + 1 =>
      simp only [copyArrayFuel]
      split
      · rename_i hlt
        have h1 := copyValueFuel_youngCapacity_ge fuel src dst (elems[i]'hlt)
        have h2 := copyArrayFuel_youngCapacity_ge fuel src
          (copyValueFuel fuel src dst (elems[i]'hlt)).1 elems (i + 1)
          (acc.push (copyValueFuel fuel src dst (elems[i]'hlt)).2)
        exact Nat.le_trans h1 h2
      · exact Nat.le_refl _
  termination_by (fuel, 1, elems.size - i)
end

theorem copyValue_youngCapacity_ge (src dst : Heap) (v : Value) :
    dst.youngCapacity ≤ (copyValue src dst v).1.youngCapacity :=
  copyValueFuel_youngCapacity_ge _ src dst v

/-- After sanitize (as in `Process.copyFrom`), the destination is WF. -/
theorem sanitized_copy_WF (src dst : Heap) (v : Value)
    (hyoung : 0 < dst.youngCapacity) :
    WF { nodes := sanitizeNodes (copyValue src dst v).1.nodes
         oldSize := min (copyValue src dst v).1.oldSize
           (sanitizeNodes (copyValue src dst v).1.nodes).size
         youngCapacity := (copyValue src dst v).1.youngCapacity
         capacity := max (copyValue src dst v).1.capacity
           (max (sanitizeNodes (copyValue src dst v).1.nodes).size 1)
         gcCount := (copyValue src dst v).1.gcCount
         minorCount := (copyValue src dst v).1.minorCount } := by
  refine sanitized_heap_WF_tight _ _ _ _ _ ?_ _ ?_
  · exact Nat.lt_of_lt_of_le hyoung (copyValue_youngCapacity_ge src dst v)
  · exact Nat.min_le_right _ _

end Heap


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

theorem GcRel.trans {p q r : Process} (h1 : GcRel p q) (h2 : GcRel q r) : GcRel p r where
  pid := h2.pid.trans h1.pid
  status := h2.status.trans h1.status
  stack_size := h2.stack_size.trans h1.stack_size
  mailbox_size := h2.mailbox_size.trans h1.mailbox_size
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
      have hp' : p.stack.size = 0 ∧ p.status = .exited := by
        have h := hp
        simp [Process.WF, hpr] at h
        exact ⟨(Array.size_eq_zero_iff).2 h.2.1, h.2.2⟩
      exact ⟨by rw [hsz]; exact hp'.1, by rw [hr.status]; exact hp'.2⟩
  | none =>
    have hpres : p.result = none := hr.result_none.1 hqres
    simp only [hr.status]
    cases hst : p.status with
    | exited =>
      have h := hp
      simp [Process.WF, hpres, hst] at h
    | waiting =>
      have hp' : p.stack.size > 0 ∧ Process.stackWF m p.stack := by
        have h := hp
        simp [Process.WF, hpres, hst] at h
        exact h.2
      exact ⟨by rw [hsz]; exact hp'.1, hr.stackWF m hp'.2⟩
    | runnable =>
      have hp' : p.stack.size > 0 ∧ Process.stackWF m p.stack := by
        have h := hp
        simp [Process.WF, hpres, hst] at h
        exact h.2
      exact ⟨by rw [hsz]; exact hp'.1, hr.stackWF m hp'.2⟩

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

`Heap.toTerm` is `partial` (opaque to the kernel), so we state preservation at the
`Value` level: immediates in registers / mailbox / result are fixed points of every
collection, hence anything that reads them (including `toTerm`, which never consults
the heap for immediates) is unchanged. Compound roots are covered by `*_rootsWF`
(well-formed refs) and by the runtime check in `GCDemo`. -/

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
