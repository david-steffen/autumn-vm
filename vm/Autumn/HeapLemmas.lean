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
  | map entries =>
    intro i hi
    have hsz :
        (entries.map fun (k, v) => (sanitizeValue bound k, sanitizeValue bound v)).size =
          entries.size := Array.size_map
    have hi0 : i < entries.size := by simpa [sanitizeNode, hsz] using hi
    have hget :
        (entries.map fun (k, v) => (sanitizeValue bound k, sanitizeValue bound v))[i]'(by
            simpa [hsz] using hi) =
          (sanitizeValue bound (entries[i]'hi0).1,
            sanitizeValue bound (entries[i]'hi0).2) := by
      simpa [Array.getElem_map] using rfl
    simpa [sanitizeNode, hget] using
      And.intro (sanitizeValue_valueBound bound (entries[i]'hi0).1)
        (sanitizeValue_valueBound bound (entries[i]'hi0).2)

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
        · rename_i entries _
          have h1 := copyEntriesFuel_youngCapacity_ge fuel src dst entries 0 #[]
          exact Nat.le_trans h1
            (allocGrow_youngCapacity_ge (copyEntriesFuel fuel src dst entries 0 #[]).1 _)
  termination_by (fuel, 0, 0)

  theorem copyEntriesFuel_youngCapacity_ge (fuel : Nat) (src dst : Heap)
      (entries : Array (Value × Value)) (i : Nat) (acc : Array (Value × Value)) :
      dst.youngCapacity ≤
        (copyEntriesFuel fuel src dst entries i acc).1.youngCapacity := by
    match fuel with
    | 0 => simp [copyEntriesFuel]
    | fuel + 1 =>
      simp only [copyEntriesFuel]
      split
      · rename_i hlt
        let k := (entries[i]'hlt).1
        let v := (entries[i]'hlt).2
        let kv := copyValueFuel fuel src dst k
        have h1 := copyValueFuel_youngCapacity_ge fuel src dst k
        let vv := copyValueFuel fuel src kv.1 v
        have h2 := copyValueFuel_youngCapacity_ge fuel src kv.1 v
        have h3 :=
          copyEntriesFuel_youngCapacity_ge fuel src vv.1 entries (i + 1) (acc.push (kv.2, vv.2))
        exact Nat.le_trans h1 (Nat.le_trans h2 h3)
      · exact Nat.le_refl _
  termination_by (fuel, 1, entries.size - i)

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

/-! ### Fueled `toTerm` -/

/-- Heap view used only for materialization (only `nodes` matter). -/
def heapView (nodes : Array Node) (youngCapacity : Nat := 1) : Heap where
  nodes := nodes
  oldSize := nodes.size
  youngCapacity := max youngCapacity 1
  capacity := max nodes.size 1
  gcCount := 0
  minorCount := 0

mutual
  theorem toTermFuel_congr_nodes (fuel : Nat) (h₁ h₂ : Heap) (v : Value)
      (hn : h₁.nodes = h₂.nodes) :
      toTermFuel fuel h₁ v = toTermFuel fuel h₂ v := by
    cases fuel with
    | zero => simp [toTermFuel]
    | succ fuel =>
      cases v with
      | nil | bool _ | int _ | atom _ | pid _ => simp [toTermFuel]
      | ref r =>
        have hg : get? h₁ r = get? h₂ r := by simp [get?, hn]
        simp only [toTermFuel]
        rw [hg]
        cases get? h₂ r with
        | none => rfl
        | some n =>
          cases n with
          | tuple elems =>
            simpa using toTermArrayFuel_congr_nodes fuel h₁ h₂ elems 0 #[] hn
          | list elems =>
            simpa using toTermArrayFuel_congr_nodes fuel h₁ h₂ elems 0 #[] hn
          | map entries =>
            simpa using toTermEntriesFuel_congr_nodes fuel h₁ h₂ entries 0 #[] hn
  termination_by fuel

  theorem toTermArrayFuel_congr_nodes (fuel : Nat) (h₁ h₂ : Heap)
      (elems : Array Value) (i : Nat) (acc : Array Term)
      (hn : h₁.nodes = h₂.nodes) :
      toTermArrayFuel fuel h₁ elems i acc = toTermArrayFuel fuel h₂ elems i acc := by
    cases fuel with
    | zero => simp [toTermArrayFuel]
    | succ fuel =>
      simp only [toTermArrayFuel]
      split
      · next hlt =>
        rw [toTermFuel_congr_nodes fuel h₁ h₂ (elems[i]!) hn]
        exact toTermArrayFuel_congr_nodes fuel h₁ h₂ elems (i + 1) _ hn
      · rfl
  termination_by fuel

  theorem toTermEntriesFuel_congr_nodes (fuel : Nat) (h₁ h₂ : Heap)
      (entries : Array (Value × Value)) (i : Nat) (acc : Array (Term × Term))
      (hn : h₁.nodes = h₂.nodes) :
      toTermEntriesFuel fuel h₁ entries i acc =
        toTermEntriesFuel fuel h₂ entries i acc := by
    cases fuel with
    | zero => simp [toTermEntriesFuel]
    | succ fuel =>
      simp only [toTermEntriesFuel]
      split
      · next hlt =>
        rw [toTermFuel_congr_nodes fuel h₁ h₂ (entries[i]!).1 hn,
            toTermFuel_congr_nodes fuel h₁ h₂ (entries[i]!).2 hn]
        exact toTermEntriesFuel_congr_nodes fuel h₁ h₂ entries (i + 1) _ hn
      · rfl
  termination_by fuel
end

theorem toTermFuel_immediate_eq (fuel₁ fuel₂ : Nat) (h₁ h₂ : Heap) (v : Value)
    (hne : ¬ ∃ r, v = .ref r) (h1 : 0 < fuel₁) (h2 : 0 < fuel₂) :
    toTermFuel fuel₁ h₁ v = toTermFuel fuel₂ h₂ v := by
  cases fuel₁ with | zero => cases h1 | succ f1 =>
  cases fuel₂ with | zero => cases h2 | succ f2 =>
  cases v with
  | ref r => exact False.elim (hne ⟨r, rfl⟩)
  | nil => simp [toTermFuel]
  | bool b => simp [toTermFuel]
  | int n => simp [toTermFuel]
  | atom s => simp [toTermFuel]
  | pid id => simp [toTermFuel]

/-- Flat compound: a ref whose node children are all immediates. -/
def flatCompound (h : Heap) (v : Value) : Prop :=
  match v with
  | .ref r =>
    match get? h r with
    | some (.tuple elems) => ∀ i, (hi : i < elems.size) → ¬ ∃ r, (elems[i]'hi) = .ref r
    | some (.list elems) => ∀ i, (hi : i < elems.size) → ¬ ∃ r, (elems[i]'hi) = .ref r
    | some (.map entries) =>
      ∀ i, (hi : i < entries.size) →
        (¬ ∃ r, (entries[i]'hi).1 = .ref r) ∧ (¬ ∃ r, (entries[i]'hi).2 = .ref r)
    | _ => False
  | _ => False

/-- Flat tuple materializes as a tuple of its children. -/
theorem toTermFuel_flat_tuple (fuel : Nat) (h : Heap) (r : Ref)
    (elems : Array Value)
    (hget : get? h r = some (.tuple elems)) :
    toTermFuel (fuel + 1) h (.ref r) =
      .tuple (toTermArrayFuel fuel h elems 0 #[]) := by
  simp [toTermFuel, hget]

/-- Same for a flat list. -/
theorem toTermFuel_flat_list (fuel : Nat) (h : Heap) (r : Ref)
    (elems : Array Value)
    (hget : get? h r = some (.list elems)) :
    toTermFuel (fuel + 1) h (.ref r) =
      .list (toTermArrayFuel fuel h elems 0 #[]) := by
  simp [toTermFuel, hget]

/-- Same for a flat map. -/
theorem toTermFuel_flat_map (fuel : Nat) (h : Heap) (r : Ref)
    (entries : Array (Value × Value))
    (hget : get? h r = some (.map entries)) :
    toTermFuel (fuel + 1) h (.ref r) =
      .map (toTermEntriesFuel fuel h entries 0 #[]) := by
  simp [toTermFuel, hget]

/-- Array of immediates: fueled materialization ignores the heap. -/
theorem toTermArrayFuel_immediates (fuel : Nat) (h₁ h₂ : Heap)
    (elems : Array Value) (i : Nat) (acc : Array Term)
    (himm : ∀ j, (hj : j < elems.size) → ¬ ∃ s, (elems[j]'hj) = .ref s) :
    toTermArrayFuel fuel h₁ elems i acc = toTermArrayFuel fuel h₂ elems i acc := by
  revert i acc
  induction fuel with
  | zero => intro i acc; simp [toTermArrayFuel]
  | succ fuel ih =>
    intro i acc
    simp only [toTermArrayFuel]
    split
    · next hlt =>
      have hne : ¬ ∃ s, elems[i]! = .ref s := by
        simpa [getElem!_pos elems i hlt] using himm i hlt
      have hv : toTermFuel fuel h₁ (elems[i]!) = toTermFuel fuel h₂ (elems[i]!) := by
        cases fuel with
        | zero => simp [toTermFuel]
        | succ f =>
          exact toTermFuel_immediate_eq (f + 1) (f + 1) h₁ h₂ _ hne (Nat.succ_pos _) (Nat.succ_pos _)
      rw [hv]
      exact ih (i + 1) _
    · rfl

theorem toTermEntriesFuel_immediates (fuel : Nat) (h₁ h₂ : Heap)
    (entries : Array (Value × Value)) (i : Nat) (acc : Array (Term × Term))
    (himm : ∀ j, (hj : j < entries.size) →
      (¬ ∃ s, (entries[j]'hj).1 = .ref s) ∧ (¬ ∃ s, (entries[j]'hj).2 = .ref s)) :
    toTermEntriesFuel fuel h₁ entries i acc =
      toTermEntriesFuel fuel h₂ entries i acc := by
  revert i acc
  induction fuel with
  | zero => intro i acc; simp [toTermEntriesFuel]
  | succ fuel ih =>
    intro i acc
    simp only [toTermEntriesFuel]
    split
    · next hlt =>
      have hk : ¬ ∃ s, (entries[i]!).1 = .ref s := by
        simpa [getElem!_pos entries i hlt] using (himm i hlt).1
      have hv : ¬ ∃ s, (entries[i]!).2 = .ref s := by
        simpa [getElem!_pos entries i hlt] using (himm i hlt).2
      have hk' : toTermFuel fuel h₁ (entries[i]!).1 =
          toTermFuel fuel h₂ (entries[i]!).1 := by
        cases fuel with
        | zero => simp [toTermFuel]
        | succ f =>
          exact toTermFuel_immediate_eq (f + 1) (f + 1) h₁ h₂ _ hk (Nat.succ_pos _) (Nat.succ_pos _)
      have hv' : toTermFuel fuel h₁ (entries[i]!).2 =
          toTermFuel fuel h₂ (entries[i]!).2 := by
        cases fuel with
        | zero => simp [toTermFuel]
        | succ f =>
          exact toTermFuel_immediate_eq (f + 1) (f + 1) h₁ h₂ _ hv (Nat.succ_pos _) (Nat.succ_pos _)
      simp only [hk', hv']
      exact ih (i + 1) _
    · rfl

/-- Flat compounds with identical node payloads agree under fueled materialization. -/
theorem toTermFuel_flatCompound_congr (fuel : Nat) (h₁ h₂ : Heap) (r : Ref)
    (hflat : flatCompound h₁ (.ref r))
    (hnode : get? h₁ r = get? h₂ r)
    (hpos : 0 < fuel) :
    toTermFuel fuel h₁ (.ref r) = toTermFuel fuel h₂ (.ref r) := by
  cases fuel with
  | zero => cases hpos
  | succ fuel =>
    dsimp [flatCompound] at hflat
    cases h1 : get? h₁ r with
    | none => simp [h1] at hflat
    | some n =>
      have h2 : get? h₂ r = some n := by
        rw [← hnode, h1]
      cases n with
      | tuple elems =>
        simp [toTermFuel, h1, h2]
        exact toTermArrayFuel_immediates fuel h₁ h₂ elems 0 #[] (by
          simpa [h1] using hflat)
      | list elems =>
        simp [toTermFuel, h1, h2]
        exact toTermArrayFuel_immediates fuel h₁ h₂ elems 0 #[] (by
          simpa [h1] using hflat)
      | map entries =>
        simp [toTermFuel, h1, h2]
        exact toTermEntriesFuel_immediates fuel h₁ h₂ entries 0 #[] (by
          simpa [h1] using hflat)

end Heap

end Autumn
