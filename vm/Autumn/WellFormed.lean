import Autumn.Instr
import Autumn.State

namespace Autumn

def FunName.resolvable (m : Module) (name : FunName) : Prop :=
  isBuiltinName name = true ∨ (m.findFunction name).isSome

/-- Decidable resolvability (builtins or MFA present). -/
def FunName.resolvableB (m : Module) (name : FunName) : Bool :=
  isBuiltinName name || (m.findFunction name).isSome

theorem FunName.resolvableB_sound (m : Module) (name : FunName)
    (h : FunName.resolvableB m name = true) : FunName.resolvable m name := by
  simp only [FunName.resolvableB, FunName.resolvable, Bool.or_eq_true] at h ⊢
  exact h

theorem FunName.resolvableB_complete (m : Module) (name : FunName)
    (h : FunName.resolvable m name) : FunName.resolvableB m name = true := by
  simp only [FunName.resolvable, FunName.resolvableB, Bool.or_eq_true] at h ⊢
  exact h

namespace Instr

def regsOk (locals : Nat) : Instr → Bool
  | .loadLit r _ => r < locals
  | .move d s => d < locals && s < locals
  | .call d _ args => d < locals && args.all (· < locals)
  | .return_ r => r < locals
  | .halt r => r < locals
  | .jump _ => true
  | .jumpIfEq _ r _ => r < locals
  | .getTupleElem d t _ => d < locals && t < locals
  | .getListElem d t _ => d < locals && t < locals
  | .getListRest d t _ => d < locals && t < locals
  | .isTag d r _ => d < locals && r < locals
  | .spawn d _ args => d < locals && args.all (· < locals)
  | .send p m => p < locals && m < locals
  | .recv d => d < locals
  | .recvPeek d i _ => d < locals && i < locals
  | .recvDrop i => i < locals
  | .wait _ _ (.reg r) => r < locals
  | .wait _ _ _ => true
  | .enterTry _ exc => exc < locals
  | .leaveTry => true
  | .raise r => r < locals
  | .link p => p < locals
  | .monitor d p => d < locals && p < locals
  | .demonitor r => r < locals
  | .makeFun d _ caps => d < locals && caps.all (· < locals)
  | .apply d f args => d < locals && f < locals && args.all (· < locals)
  | .loadFile d p => d < locals && p < locals
  | .applyMfa d m f args => d < locals && m < locals && f < locals && args.all (· < locals)

def jumpTargetOk (codeSize : Nat) : Instr → Bool
  | .jump t => t < codeSize
  | .jumpIfEq t _ _ => t < codeSize
  | .enterTry t _ => t < codeSize
  | .recvPeek _ _ empty => empty < codeSize
  | .wait retry after _ => retry < codeSize && after < codeSize
  | _ => true

def isTerminal : Instr → Bool
  | .return_ _ | .halt _ | .raise _ => true
  | _ => false

end Instr

namespace Function

def instrOk (m : Module) (f : Function) (i : Instr) : Prop :=
  Instr.regsOk f.locals i = true ∧
  Instr.jumpTargetOk f.code.size i = true ∧
  match i with
  | .call _ name _ => FunName.resolvable m name
  | .spawn _ name _ => (m.findFunction name).isSome
  | .makeFun _ name _ => FunName.resolvable m name
  | _ => True

/-- Decidable instruction well-formedness under `m`. -/
def instrOkB (m : Module) (f : Function) (i : Instr) : Bool :=
  Instr.regsOk f.locals i && Instr.jumpTargetOk f.code.size i &&
  match i with
  | .call _ name _ => FunName.resolvableB m name
  | .spawn _ name _ => (m.findFunction name).isSome
  | .makeFun _ name _ => FunName.resolvableB m name
  | _ => true

theorem instrOkB_sound (m : Module) (f : Function) (i : Instr)
    (h : instrOkB m f i = true) : instrOk m f i := by
  simp only [instrOkB, Bool.and_eq_true] at h
  refine ⟨h.1.1, h.1.2, ?_⟩
  cases i with
  | call _ name _ => exact FunName.resolvableB_sound _ _ h.2
  | spawn _ name _ => exact h.2
  | makeFun _ name _ => exact FunName.resolvableB_sound _ _ h.2
  | _ => trivial

theorem instrOkB_complete (m : Module) (f : Function) (i : Instr)
    (h : instrOk m f i) : instrOkB m f i = true := by
  simp only [instrOk, instrOkB, Bool.and_eq_true] at h ⊢
  refine ⟨⟨h.1, h.2.1⟩, ?_⟩
  cases i with
  | call _ name _ => exact FunName.resolvableB_complete _ _ h.2.2
  | spawn _ name _ => exact h.2.2
  | makeFun _ name _ => exact FunName.resolvableB_complete _ _ h.2.2
  | _ => rfl

def WF (m : Module) (f : Function) : Prop :=
  f.locals ≥ f.arity ∧
  0 < f.code.size ∧
  Instr.isTerminal (f.code[f.code.size - 1]!) = true ∧
  ∀ i : Fin f.code.size, instrOk m f f.code[i]

/-- Decidable function well-formedness under `m`. -/
def checkWF (m : Module) (f : Function) : Bool :=
  (f.locals ≥ f.arity) &&
  (0 < f.code.size) &&
  (if hsz : 0 < f.code.size then
      Instr.isTerminal (f.code[f.code.size - 1]'(Nat.sub_one_lt_of_lt hsz)) &&
      (List.range f.code.size).all fun i =>
        if hi : i < f.code.size then instrOkB m f (f.code[i]) else false
    else
      false)

theorem checkWF_sound (m : Module) (f : Function) (h : checkWF m f = true) : WF m f := by
  simp only [checkWF, Bool.and_eq_true, decide_eq_true_eq] at h
  have hloc : f.locals ≥ f.arity := h.1.1
  have hsz : 0 < f.code.size := h.1.2
  simp only [hsz, ↓reduceDIte, Bool.and_eq_true] at h
  have hterm : Instr.isTerminal (f.code[f.code.size - 1]'(Nat.sub_one_lt_of_lt hsz)) = true :=
    h.2.1
  have hterm' : Instr.isTerminal (f.code[f.code.size - 1]!) = true := by
    simpa [getElem!_pos f.code (f.code.size - 1) (Nat.sub_one_lt_of_lt hsz)] using hterm
  refine ⟨hloc, hsz, hterm', ?_⟩
  intro i
  have hall := (List.all_eq_true).1 h.2.2
  have hi : i.val < f.code.size := i.isLt
  have hb : instrOkB m f (f.code[i.val]) = true := by
    have := hall i.val (List.mem_range.2 hi)
    simpa [hi, ↓reduceDIte] using this
  exact instrOkB_sound m f _ hb

theorem checkWF_complete (m : Module) (f : Function) (h : WF m f) : checkWF m f = true := by
  simp only [checkWF, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨h.1, h.2.1⟩, ?_⟩
  simp only [h.2.1, ↓reduceDIte, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · have hterm := h.2.2.1
    simpa [getElem!_pos f.code (f.code.size - 1) (Nat.sub_one_lt_of_lt h.2.1)] using hterm
  · apply (List.all_eq_true).2
    intro i hi
    have hi' : i < f.code.size := List.mem_range.1 hi
    simp only [hi', ↓reduceDIte]
    exact instrOkB_complete m f _ (h.2.2.2 ⟨i, hi'⟩)

theorem nonterminal_ip_lt {f : Function} {ip : Nat}
    (hsz : 0 < f.code.size)
    (hterm : Instr.isTerminal (f.code[f.code.size - 1]!) = true)
    (hip : ip < f.code.size)
    (hnt : Instr.isTerminal (f.code[ip]!) = false) :
    ip + 1 < f.code.size := by
  match Nat.lt_or_ge (ip + 1) f.code.size with
  | .inl h => exact h
  | .inr h =>
    have hip' : ip = f.code.size - 1 := by omega
    rw [hip'] at hnt
    simp [hterm] at hnt

theorem WF.nonterminal_ip_lt {_m : Module} {f : Function} {ip : Nat}
    (hwf : WF _m f) (hip : ip < f.code.size)
    (hnt : Instr.isTerminal (f.code[ip]!) = false) :
    ip + 1 < f.code.size :=
  Function.nonterminal_ip_lt (f := f) (ip := ip) hwf.2.1 hwf.2.2.1 hip hnt

end Function

namespace Module

def uniqueFunNames (m : Module) : Prop :=
  ∀ i j : Fin m.allFunctions.size,
    i ≠ j → m.allFunctions[i].name ≠ m.allFunctions[j].name

def uniqueModuleNames (m : Module) : Prop :=
  ∀ i j : Fin m.modules.size,
    i ≠ j → m.modules[i].name ≠ m.modules[j].name

def versionOk (v : Nat) : Prop :=
  v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨
    v = 10 ∨ v = 11 ∨ v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 ∨ v = 16 ∨ v = 17 ∨
    v = 18 ∨ v = 19

def versionOkB (v : Nat) : Bool :=
  (1 ≤ v) && (v ≤ 19)

theorem versionOkB_sound (v : Nat) (h : versionOkB v = true) : versionOk v := by
  simp only [versionOkB, Bool.and_eq_true, decide_eq_true_eq] at h
  match v with
  | 0 => omega
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 =>
    simp [versionOk]
  | n + 20 => omega

theorem versionOkB_complete (v : Nat) (h : versionOk v) : versionOkB v = true := by
  simp only [versionOk] at h
  simp only [versionOkB, Bool.and_eq_true, decide_eq_true_eq]
  rcases h with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

def uniqueFunNamesB (m : Module) : Bool :=
  (List.range m.allFunctions.size).all fun i =>
    (List.range m.allFunctions.size).all fun j =>
      if hi : i < m.allFunctions.size then
        if hj : j < m.allFunctions.size then
          i == j || m.allFunctions[i].name != m.allFunctions[j].name
        else false
      else false

def uniqueModuleNamesB (m : Module) : Bool :=
  (List.range m.modules.size).all fun i =>
    (List.range m.modules.size).all fun j =>
      if hi : i < m.modules.size then
        if hj : j < m.modules.size then
          i == j || m.modules[i].name != m.modules[j].name
        else false
      else false

theorem uniqueFunNamesB_sound (m : Module) (h : uniqueFunNamesB m = true) :
    uniqueFunNames m := by
  intro i j hne
  have hall := (List.all_eq_true).1 h
  have hi := hall i.val (List.mem_range.2 i.isLt)
  have hallj := (List.all_eq_true).1 hi
  have hj := hallj j.val (List.mem_range.2 j.isLt)
  simp only [i.isLt, j.isLt, ↓reduceDIte, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hj
  exact hj.resolve_left (Fin.val_ne_of_ne hne)

theorem uniqueFunNamesB_complete (m : Module) (h : uniqueFunNames m) :
    uniqueFunNamesB m = true := by
  simp only [uniqueFunNamesB]
  apply (List.all_eq_true).2
  intro i hi
  have hi' : i < m.allFunctions.size := List.mem_range.1 hi
  apply (List.all_eq_true).2
  intro j hj
  have hj' : j < m.allFunctions.size := List.mem_range.1 hj
  simp only [hi', hj', ↓reduceDIte, Bool.or_eq_true, bne_iff_ne, beq_iff_eq]
  by_cases heq : i = j
  · left; exact heq
  · right
    exact h ⟨i, hi'⟩ ⟨j, hj'⟩ (Fin.ne_of_val_ne heq)

theorem uniqueModuleNamesB_sound (m : Module) (h : uniqueModuleNamesB m = true) :
    uniqueModuleNames m := by
  intro i j hne
  have hall := (List.all_eq_true).1 h
  have hi := hall i.val (List.mem_range.2 i.isLt)
  have hallj := (List.all_eq_true).1 hi
  have hj := hallj j.val (List.mem_range.2 j.isLt)
  simp only [i.isLt, j.isLt, ↓reduceDIte, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hj
  exact hj.resolve_left (Fin.val_ne_of_ne hne)

theorem uniqueModuleNamesB_complete (m : Module) (h : uniqueModuleNames m) :
    uniqueModuleNamesB m = true := by
  simp only [uniqueModuleNamesB]
  apply (List.all_eq_true).2
  intro i hi
  have hi' : i < m.modules.size := List.mem_range.1 hi
  apply (List.all_eq_true).2
  intro j hj
  have hj' : j < m.modules.size := List.mem_range.1 hj
  simp only [hi', hj', ↓reduceDIte, Bool.or_eq_true, bne_iff_ne, beq_iff_eq]
  by_cases heq : i = j
  · left; exact heq
  · right
    exact h ⟨i, hi'⟩ ⟨j, hj'⟩ (Fin.ne_of_val_ne heq)

def WF (m : Module) : Prop :=
  versionOk m.version ∧
  0 < m.modules.size ∧
  (m.findFunction m.entry).isSome ∧
  uniqueModuleNames m ∧
  uniqueFunNames m ∧
  ∀ i : Fin m.allFunctions.size, Function.WF m m.allFunctions[i]

/-- Decidable module well-formedness (used to reject bad `load_file` installs). -/
def checkWF (m : Module) : Bool :=
  versionOkB m.version &&
  (0 < m.modules.size) &&
  (m.findFunction m.entry).isSome &&
  uniqueModuleNamesB m &&
  uniqueFunNamesB m &&
  (List.range m.allFunctions.size).all fun i =>
    if hi : i < m.allFunctions.size then Function.checkWF m (m.allFunctions[i]) else false

theorem checkWF_sound (m : Module) (h : checkWF m = true) : WF m := by
  simp only [checkWF, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨versionOkB_sound _ h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2,
    uniqueModuleNamesB_sound _ h.1.1.2, uniqueFunNamesB_sound _ h.1.2, ?_⟩
  intro i
  have hall := (List.all_eq_true).1 h.2
  have hb := hall i.val (List.mem_range.2 i.isLt)
  have hb' : Function.checkWF m (m.allFunctions[i.val]) = true := by
    simpa [i.isLt, ↓reduceDIte] using hb
  exact Function.checkWF_sound m _ hb'

theorem checkWF_complete (m : Module) (h : WF m) : checkWF m = true := by
  simp only [checkWF, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨versionOkB_complete _ h.1, h.2.1⟩, h.2.2.1⟩,
    uniqueModuleNamesB_complete _ h.2.2.2.1⟩, uniqueFunNamesB_complete _ h.2.2.2.2.1⟩, ?_⟩
  apply (List.all_eq_true).2
  intro i hi
  have hi' : i < m.allFunctions.size := List.mem_range.1 hi
  simp only [hi', ↓reduceDIte]
  exact Function.checkWF_complete m _ (h.2.2.2.2.2 ⟨i, hi'⟩)

theorem findFunction_mem {m : Module} {name : FunName} {f : Function}
    (h : m.findFunction name = some f) : f ∈ m.allFunctions.toList := by
  simp only [Module.findFunction] at h
  rcases (List.find?_eq_some_iff_append).1 h with ⟨_, as, bs, heq, _⟩
  have : f ∈ as ++ f :: bs := List.mem_append.2 (Or.inr (List.mem_cons_self))
  exact heq ▸ this

theorem findFunction_name {m : Module} {name : FunName} {f : Function}
    (h : m.findFunction name = some f) : f.name = name := by
  simp only [Module.findFunction] at h
  have ⟨hbeq, _⟩ := (List.find?_eq_some_iff_append).1 h
  exact (beq_iff_eq).1 hbeq

theorem findFunction_WF {m : Module} {name : FunName} {f : Function}
    (hwf : Module.WF m) (h : m.findFunction name = some f) : Function.WF m f := by
  have hmem := findFunction_mem h
  have hmemA : f ∈ m.allFunctions := (Array.mem_def).2 hmem
  obtain ⟨i, hi, heq⟩ := Array.getElem_of_mem hmemA
  simpa [heq] using hwf.2.2.2.2.2 ⟨i, hi⟩

end Module

namespace Heap

/-- Every ref stored in a node is within `bound`. -/
def valueBound (bound : Nat) : Value → Prop
  | .ref r => r < bound
  | _ => True

def nodeBound (bound : Nat) : Node → Prop
  | .tuple elems => ∀ i, (hi : i < elems.size) → valueBound bound (elems[i]'hi)
  | .list elems => ∀ i, (hi : i < elems.size) → valueBound bound (elems[i]'hi)
  | .map entries =>
    ∀ i, (hi : i < entries.size) →
      valueBound bound (entries[i]'hi).1 ∧ valueBound bound (entries[i]'hi).2
  | .closure _ env => ∀ i, (hi : i < env.size) → valueBound bound (env[i]'hi)

/-- Heap well-formedness: frontier in range, capacities positive, child refs in-range. -/
def WF (h : Heap) : Prop :=
  0 < h.capacity ∧
  0 < h.youngCapacity ∧
  h.oldSize ≤ h.nodes.size ∧
  h.nodes.size ≤ h.capacity ∧
  ∀ r, (hr : r < h.nodes.size) → nodeBound h.nodes.size (h.nodes[r]'hr)

def valueWF (h : Heap) (v : Value) : Prop :=
  valueBound h.nodes.size v ∧
  match v with
  | .ref r =>
      ∃ hr : r < h.nodes.size, nodeBound h.nodes.size (h.nodes[r]'hr)
  | _ => True

theorem valueBound_nil (bound : Nat) : valueBound bound .nil := trivial
theorem valueBound_bool (bound : Nat) (b : Bool) : valueBound bound (.bool b) := trivial
theorem valueBound_int (bound : Nat) (n : Int) : valueBound bound (.int n) := trivial
theorem valueBound_atom (bound : Nat) (s : String) : valueBound bound (.atom s) := trivial
theorem valueBound_pid (bound : Nat) (id : Nat) : valueBound bound (.pid id) := trivial
theorem valueBound_reference (bound : Nat) (id : Nat) : valueBound bound (.reference id) := trivial
theorem valueBound_float (bound : Nat) (f : Term.FiniteFloat) : valueBound bound (.float f) := trivial
theorem valueBound_string (bound : Nat) (s : String) : valueBound bound (.string s) := trivial
theorem valueBound_bitstring (bound : Nat) (b : Term.Bitstring) : valueBound bound (.bitstring b) := trivial

theorem valueWF_nil (h : Heap) : valueWF h .nil := ⟨trivial, trivial⟩
theorem valueWF_bool (h : Heap) (b : Bool) : valueWF h (.bool b) := ⟨trivial, trivial⟩
theorem valueWF_int (h : Heap) (n : Int) : valueWF h (.int n) := ⟨trivial, trivial⟩
theorem valueWF_atom (h : Heap) (s : String) : valueWF h (.atom s) := ⟨trivial, trivial⟩
theorem valueWF_pid (h : Heap) (id : Nat) : valueWF h (.pid id) := ⟨trivial, trivial⟩
theorem valueWF_reference (h : Heap) (id : Nat) : valueWF h (.reference id) := ⟨trivial, trivial⟩
theorem valueWF_float (h : Heap) (f : Term.FiniteFloat) : valueWF h (.float f) := ⟨trivial, trivial⟩
theorem valueWF_string (h : Heap) (s : String) : valueWF h (.string s) := ⟨trivial, trivial⟩
theorem valueWF_bitstring (h : Heap) (b : Term.Bitstring) : valueWF h (.bitstring b) := ⟨trivial, trivial⟩

theorem valueBound_mono {b₁ b₂ : Nat} (h : b₁ ≤ b₂) :
    ∀ v, valueBound b₁ v → valueBound b₂ v
  | .ref _, hr => Nat.lt_of_lt_of_le hr h
  | .nil, _ => trivial
  | .bool _b, _ => trivial
  | .int _n, _ => trivial
  | .float _f, _ => trivial
  | .atom _s, _ => trivial
  | .string _s, _ => trivial
  | .bitstring _b, _ => trivial
  | .pid _id, _ => trivial
  | .reference _id, _ => trivial

theorem nodeBound_mono {b₁ b₂ : Nat} (hle : b₁ ≤ b₂) (n : Node)
    (hb : nodeBound b₁ n) : nodeBound b₂ n := by
  cases n with
  | tuple elems =>
    intro i hi
    exact valueBound_mono hle _ (hb i hi)
  | list elems =>
    intro i hi
    exact valueBound_mono hle _ (hb i hi)
  | map entries =>
    intro i hi
    exact ⟨valueBound_mono hle _ (hb i hi).1, valueBound_mono hle _ (hb i hi).2⟩
  | closure _ env =>
    intro i hi
    exact valueBound_mono hle _ (hb i hi)

theorem empty_WF (cap : Nat) (hcap : 0 < cap) : WF (empty cap) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [empty]; exact Nat.lt_of_lt_of_le hcap (Nat.le_max_left _ _)
  · simp [empty]
    exact (Nat.lt_min).2 ⟨Nat.succ_pos _, Nat.lt_of_lt_of_le hcap (Nat.le_max_left _ _)⟩
  · simp [empty]
  · simp [empty]
  · intro r hr; simp [empty] at hr

theorem empty_default_WF : WF (empty) := empty_WF defaultCapacity (by decide)

end Heap

namespace Frame

def WF (m : Module) (f : Frame) : Prop :=
  Function.WF m f.function ∧
  f.regs.size = f.function.locals ∧
  f.ip < f.function.code.size ∧
  (m.findFunction f.function.name).isSome

/-- Decidable frame well-formedness under `m`. -/
def checkWF (m : Module) (f : Frame) : Bool :=
  Function.checkWF m f.function &&
  (f.regs.size == f.function.locals) &&
  (f.ip < f.function.code.size) &&
  (m.findFunction f.function.name).isSome

theorem checkWF_sound (m : Module) (f : Frame) (h : checkWF m f = true) : WF m f := by
  simp only [checkWF, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨Function.checkWF_sound m _ h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem checkWF_complete (m : Module) (f : Frame) (h : WF m f) : checkWF m f = true := by
  simp only [checkWF, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨⟨Function.checkWF_complete m _ h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩

/-- Frame registers are valid in `h`. -/
def regsWF (h : Heap) (f : Frame) : Prop :=
  ∀ i, (hi : i < f.regs.size) → Heap.valueWF h (f.regs[i]'hi)

theorem current_instrOk {m : Module} {f : Frame} (hwf : WF m f) :
    Function.instrOk m f.function (f.function.code[f.ip]'hwf.2.2.1) :=
  hwf.1.2.2.2 ⟨f.ip, hwf.2.2.1⟩

end Frame

namespace Process

def stackWF (m : Module) (stack : Array Frame) : Prop :=
  (∀ i, (hi : i < stack.size) → Frame.WF m (stack[i]'hi)) ∧
  (∀ i, (hi : i < stack.size) → i > 0 →
    (stack[i]'hi).retDest <
      (stack[i - 1]'(Nat.lt_of_le_of_lt (Nat.pred_le i) hi)).function.locals)

/-- Decidable stack well-formedness under `m`. -/
def stackWF_B (m : Module) (stack : Array Frame) : Bool :=
  (List.range stack.size).all (fun i =>
    if hi : i < stack.size then Frame.checkWF m (stack[i]) else false) &&
  (List.range stack.size).all (fun i =>
    if hi : i < stack.size then
      (i == 0) ||
        decide (stack[i].retDest <
          (stack[i - 1]'(Nat.lt_of_le_of_lt (Nat.pred_le i) hi)).function.locals)
    else false)

theorem stackWF_B_sound (m : Module) (stack : Array Frame) (h : stackWF_B m stack = true) :
    stackWF m stack := by
  simp only [stackWF_B, Bool.and_eq_true] at h
  refine ⟨?_, ?_⟩
  · intro i hi
    have hall := (List.all_eq_true).1 h.1
    have hb := hall i (List.mem_range.2 hi)
    have hb' : Frame.checkWF m (stack[i]) = true := by
      simpa [hi, ↓reduceDIte] using hb
    exact Frame.checkWF_sound m _ hb'
  · intro i hi hi0
    have hall := (List.all_eq_true).1 h.2
    have hb := hall i (List.mem_range.2 hi)
    have hne : (i == 0) = false := beq_eq_false_iff_ne.2 (Nat.ne_of_gt hi0)
    have hb' :
        decide (stack[i].retDest <
          (stack[i - 1]'(Nat.lt_of_le_of_lt (Nat.pred_le i) hi)).function.locals) = true := by
      simpa [hi, ↓reduceDIte, hne, Bool.or_false] using hb
    exact of_decide_eq_true hb'

theorem stackWF_B_complete (m : Module) (stack : Array Frame) (h : stackWF m stack) :
    stackWF_B m stack = true := by
  simp only [stackWF_B, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · apply (List.all_eq_true).2
    intro i hi
    have hi' : i < stack.size := List.mem_range.1 hi
    simp only [hi', ↓reduceDIte]
    exact Frame.checkWF_complete m _ (h.1 i hi')
  · apply (List.all_eq_true).2
    intro i hi
    have hi' : i < stack.size := List.mem_range.1 hi
    simp only [hi', ↓reduceDIte, Bool.or_eq_true, beq_iff_eq]
    by_cases hi0 : i = 0
    · left; exact hi0
    · right
      exact decide_eq_true (h.2 i hi' (Nat.pos_of_ne_zero hi0))

/-- Module-dependent conjunct of `Process.WF` (stack frames under a new image). -/
def moduleOkB (m : Module) (p : Process) : Bool :=
  match p.result with
  | some _ => true
  | none =>
    match p.status with
    | .exited => true
    | .runnable | .waiting => stackWF_B m p.stack

def rootsWF (h : Heap) (p : Process) : Prop :=
  (∀ i, (hi : i < p.stack.size) → Frame.regsWF h (p.stack[i]'hi)) ∧
  (∀ i, (hi : i < p.mailbox.size) → Heap.valueWF h (p.mailbox[i]'hi)) ∧
  match p.result with
  | some v => Heap.valueWF h v
  | none => True

/-- Handler indices are in range for the given stack (used by step lemmas, not `Process.WF`). -/
def handlersWF (stack : Array Frame) (handlers : Array Handler) : Prop :=
  ∀ i, (hi : i < handlers.size) →
    let h := handlers[i]'hi
    0 < h.stackDepth ∧ h.stackDepth ≤ stack.size ∧
      h.rescueIp < (stack[h.stackDepth - 1]!).function.code.size ∧
      h.excReg < (stack[h.stackDepth - 1]!).function.locals

/--
Process well-formedness: heap in-bounds, plus the classic stack/status rules.
Root `valueWF` (`rootsWF`) is maintained by GC (`Process.gc_preserves_*`) and
is available as a separate conjunct for observational theorems.
Runnable/waiting processes also satisfy `handlersWF` (handler stack bounds).
Exited processes must have an empty handler stack.
-/
def WF (m : Module) (p : Process) : Prop :=
  Heap.WF p.heap ∧
  match p.result with
  | some _ => p.stack.size = 0 ∧ p.status = .exited ∧ p.handlers = #[]
  | none =>
      match p.status with
      | .exited => False
      | .waiting | .runnable =>
          p.stack.size > 0 ∧ stackWF m p.stack ∧ handlersWF p.stack p.handlers

/-- Re-check module-dependent stack WF under `m'`; heap/status/handlers unchanged. -/
theorem WF_of_moduleOkB (m m' : Module) (p : Process)
    (hp : WF m p) (hok : moduleOkB m' p = true) : WF m' p := by
  refine ⟨hp.1, ?_⟩
  cases hr : p.result with
  | some _ =>
    have hrest : p.stack.size = 0 ∧ p.status = .exited ∧ p.handlers = #[] := by
      simpa [hr] using hp.2
    simpa [hr] using hrest
  | none =>
    cases hs : p.status with
    | exited =>
      have hfalse : False := by simpa [hr, hs] using hp.2
      exact hfalse.elim
    | runnable =>
      simp only [moduleOkB, hr, hs] at hok
      have hp' : p.stack.size > 0 ∧ stackWF m p.stack ∧ handlersWF p.stack p.handlers := by
        simpa [hr, hs] using hp.2
      exact ⟨hp'.1, stackWF_B_sound m' p.stack hok, hp'.2.2⟩
    | waiting =>
      simp only [moduleOkB, hr, hs] at hok
      have hp' : p.stack.size > 0 ∧ stackWF m p.stack ∧ handlersWF p.stack p.handlers := by
        simpa [hr, hs] using hp.2
      exact ⟨hp'.1, stackWF_B_sound m' p.stack hok, hp'.2.2⟩

/-- Under `Process.WF m p`, the module-dependent Bool check succeeds. -/
theorem moduleOkB_complete (m : Module) (p : Process) (hp : WF m p) :
    moduleOkB m p = true := by
  simp only [moduleOkB]
  cases hr : p.result with
  | some _ => rfl
  | none =>
    cases hs : p.status with
    | exited =>
      have hfalse : False := by simpa [hr, hs] using hp.2
      exact hfalse.elim
    | runnable =>
      have hp' : p.stack.size > 0 ∧ stackWF m p.stack ∧ handlersWF p.stack p.handlers := by
        simpa [hr, hs] using hp.2
      exact stackWF_B_complete m p.stack hp'.2.1
    | waiting =>
      have hp' : p.stack.size > 0 ∧ stackWF m p.stack ∧ handlersWF p.stack p.handlers := by
        simpa [hr, hs] using hp.2
      exact stackWF_B_complete m p.stack hp'.2.1

end Process

namespace State

def WF (s : State) : Prop :=
  Module.WF s.module ∧
  0 < s.processes.size ∧
  s.current < s.processes.size ∧
  (∀ i, (hi : i < s.processes.size) → Process.WF s.module (s.processes[i]'hi))

theorem current_process_WF (s : State) (hs : WF s) :
    Process.WF s.module (s.processes[s.current]'hs.2.2.1) :=
  hs.2.2.2 s.current hs.2.2.1

/-- All processes remain module-OK under a candidate image (for `load_file`). -/
def processesModuleOkB (m : Module) (s : State) : Bool :=
  (List.range s.processes.size).all fun i =>
    if hi : i < s.processes.size then Process.moduleOkB m (s.processes[i]) else false

theorem WF_with_module (s : State) (m' : Module)
    (hs : WF s) (hm' : Module.WF m')
    (hok : processesModuleOkB m' s = true) :
    WF { s with module := m' } := by
  refine ⟨hm', hs.2.1, hs.2.2.1, ?_⟩
  intro i hi
  have hall := (List.all_eq_true).1 hok
  have hb := hall i (List.mem_range.2 hi)
  have hokᵢ : Process.moduleOkB m' (s.processes[i]) = true := by
    simpa [hi, ↓reduceDIte] using hb
  exact Process.WF_of_moduleOkB s.module m' _ (hs.2.2.2 i hi) hokᵢ

theorem processesModuleOkB_complete (m : Module) (s : State)
    (h : ∀ i, (hi : i < s.processes.size) → Process.WF m (s.processes[i]'hi)) :
    processesModuleOkB m s = true := by
  simp only [processesModuleOkB]
  apply (List.all_eq_true).2
  intro i hi
  have hi' : i < s.processes.size := List.mem_range.1 hi
  simp only [hi', ↓reduceDIte]
  exact Process.moduleOkB_complete m _ (h i hi')

end State

def isStructuralError : StepError → Bool
  | .emptyStack | .badRegister _ _ | .badIp _ _ => true
  | _ => false

end Autumn
