import Autumn.Instr
import Autumn.State

namespace Autumn

def FunName.resolvable (m : Module) (name : FunName) : Prop :=
  isBuiltinName name = true ∨ (m.findFunction name).isSome

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
  | .wait _ _ _ => true
  | .enterTry _ exc => exc < locals
  | .leaveTry => true
  | .raise r => r < locals
  | .link p => p < locals

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
  | _ => True

def WF (m : Module) (f : Function) : Prop :=
  f.locals ≥ f.arity ∧
  0 < f.code.size ∧
  Instr.isTerminal (f.code[f.code.size - 1]!) = true ∧
  ∀ i : Fin f.code.size, instrOk m f f.code[i]

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

def uniqueNames (m : Module) : Prop :=
  ∀ i j : Fin m.functions.size,
    i ≠ j → m.functions[i].name ≠ m.functions[j].name

def WF (m : Module) : Prop :=
  (m.version = 1 ∨ m.version = 2 ∨ m.version = 3 ∨ m.version = 4 ∨ m.version = 5 ∨
    m.version = 6 ∨ m.version = 7) ∧
  (m.findFunction m.entry).isSome ∧
  uniqueNames m ∧
  ∀ i : Fin m.functions.size, Function.WF m m.functions[i]

theorem findFunction_mem {m : Module} {name : FunName} {f : Function}
    (h : m.findFunction name = some f) : f ∈ m.functions.toList := by
  simp only [Module.findFunction] at h
  rcases (List.find?_eq_some_iff_append).1 h with ⟨_, as, bs, heq, _⟩
  have : f ∈ as ++ f :: bs := List.mem_append.2 (Or.inr (List.mem_cons_self))
  exact heq ▸ this

theorem findFunction_WF {m : Module} {name : FunName} {f : Function}
    (hwf : Module.WF m) (h : m.findFunction name = some f) : Function.WF m f := by
  have hmem := findFunction_mem h
  have hmemA : f ∈ m.functions := (Array.mem_def).2 hmem
  obtain ⟨i, hi, heq⟩ := Array.getElem_of_mem hmemA
  simpa [heq] using hwf.2.2.2 ⟨i, hi⟩

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

theorem valueWF_nil (h : Heap) : valueWF h .nil := ⟨trivial, trivial⟩
theorem valueWF_bool (h : Heap) (b : Bool) : valueWF h (.bool b) := ⟨trivial, trivial⟩
theorem valueWF_int (h : Heap) (n : Int) : valueWF h (.int n) := ⟨trivial, trivial⟩
theorem valueWF_atom (h : Heap) (s : String) : valueWF h (.atom s) := ⟨trivial, trivial⟩
theorem valueWF_pid (h : Heap) (id : Nat) : valueWF h (.pid id) := ⟨trivial, trivial⟩

theorem valueBound_mono {b₁ b₂ : Nat} (h : b₁ ≤ b₂) :
    ∀ v, valueBound b₁ v → valueBound b₂ v
  | .ref _, hr => Nat.lt_of_lt_of_le hr h
  | .nil, _ => trivial
  | .bool _b, _ => trivial
  | .int _n, _ => trivial
  | .atom _s, _ => trivial
  | .pid _id, _ => trivial

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

end State

def isStructuralError : StepError → Bool
  | .emptyStack | .badRegister _ _ | .badIp _ _ => true
  | _ => false

end Autumn
