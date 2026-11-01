import Autumn.Instr
import Autumn.Heap

namespace Autumn

structure Frame where
  function : Function
  regs : Array Value
  ip : Nat
  retDest : Reg
  deriving Repr, Inhabited

inductive ProcStatus where
  | runnable
  | waiting
  | exited
  deriving Repr, BEq, Inhabited

/-- Exception handler pushed by `enter_try` (no heap roots — only indices). -/
structure Handler where
  /-- `stack.size` when the try was entered (frame that owns the try). -/
  stackDepth : Nat
  rescueIp : Nat
  excReg : Reg
  deriving Repr, Inhabited

structure Process where
  pid : Nat
  stack : Array Frame
  mailbox : Array Value
  status : ProcStatus
  /-- Set when this process's root frame returns/halts. -/
  result : Option Value
  heap : Heap
  /-- Innermost try handler is the last element. -/
  handlers : Array Handler
  /-- Absolute machine clock deadline for selective `wait` (`none` = infinity / not waiting on a timer). -/
  waitDeadline : Option Nat := none
  /-- Linked peer pids (IR v8). EXIT signals go here on exit. -/
  links : Array Nat := #[]
  /-- Outbound monitors (IR v9): `(targetPid, refId)`. -/
  monitors : Array (Nat × Nat) := #[]
  /-- Inbound monitors (IR v9): `(fromPid, refId)`. DOWN signals go here on exit. -/
  monitoredBy : Array (Nat × Nat) := #[]
  /-- IR v14: when true, linked EXIT is delivered as `{:EXIT, …}` (OTP `trap_exit`).
  Default false — linked EXIT kills the peer. -/
  trapExit : Bool := false
  deriving Repr, Inhabited

/-- ETS table kind (IR v17/v18 teaching subset). -/
inductive EtsKind where
  | set
  | bag
  | duplicateBag
  | orderedSet
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Public ETS table: `{key, val}` objects stored as `Term` pairs (copied on insert). -/
structure EtsTable where
  /-- Atom name when created with `ets_new/2`; `none` = anonymous. -/
  name : Option String := none
  kind : EtsKind := .set
  entries : Array (Term × Term) := #[]
  /-- Creator process pid (IR v18). -/
  owner : Option Nat := none
  /-- Heir pid + opaque data delivered on owner exit (IR v18). -/
  heir : Option (Nat × Term) := none
  /-- False after owner exit without heir; tid slot kept (IR v18). -/
  alive : Bool := true
  deriving Repr, Inhabited

/-- Whole-machine state: reduction-preemptive multi-process VM. -/
structure State where
  module : Module
  processes : Array Process
  /-- Index into `processes` of the currently running process (if any). -/
  current : Nat
  /-- Reductions left in the current quantum before forced yield. -/
  reductions : Nat
  /-- Entry process pid (machine result comes from this process). -/
  entryPid : Nat
  /-- Machine-level result once the machine is idle and the entry process has exited.
  Entry exit alone does not halt the machine (IR v14 durable drain). -/
  result : Option Term
  nextPid : Nat
  /-- Next unique reference id (IR v9). -/
  nextRef : Nat := 0
  /-- Logical clock for `wait` timeouts (advanced each step / idle jump). -/
  clock : Nat := 0
  /-- Public ETS tables (IR v17); tid = index into this array. -/
  etsTables : Array EtsTable := #[]
  deriving Repr, Inhabited

inductive StepError where
  | emptyStack
  | unknownFunction (name : FunName)
  | badArity (name : FunName) (expected got : Nat)
  | badRegister (reg : Reg) (locals : Nat)
  | badIp (ip : Nat) (size : Nat)
  | typeError (msg : String)
  | decodeError (msg : String)
  | badPid (id : Nat)
  | noRunnable
  deriving Repr, Inhabited

namespace StepError

def toString : StepError → String
  | .emptyStack => "empty call stack"
  | .unknownFunction name => s!"unknown function: {name}"
  | .badArity name expected got =>
      s!"bad arity for {name}: expected {expected}, got {got}"
  | .badRegister reg locals =>
      s!"register r{reg} out of range (locals={locals})"
  | .badIp ip size => s!"instruction pointer {ip} out of range (size={size})"
  | .typeError msg => s!"type error: {msg}"
  | .decodeError msg => s!"decode error: {msg}"
  | .badPid id => s!"bad pid: {id}"
  | .noRunnable => "no runnable process"

instance : ToString StepError where
  toString := StepError.toString

end StepError

end Autumn
