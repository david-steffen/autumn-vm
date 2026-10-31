import Autumn.State

namespace Autumn

namespace Step

/-- Builtins operate on materialized views where needed; arithmetic uses immediates. -/
def builtin (h : Heap) (name : FunName) (args : Array Value) :
    Except StepError Value :=
  match name with
  | "+/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .int a, .int b => .ok (.int (a + b))
      | _, _ => .error (.typeError "+/2 expects two integers")
  | "-/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .int a, .int b => .ok (.int (a - b))
      | _, _ => .error (.typeError "-/2 expects two integers")
  | "*/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .int a, .int b => .ok (.int (a * b))
      | _, _ => .error (.typeError "*/2 expects two integers")
  | "==/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else .ok (.bool (Heap.beq h args[0]! args[1]!))
  | "tuple_size/1" =>
    if args.size != 1 then .error (.badArity name 1 args.size)
    else match args[0]! with
      | .ref r =>
        match h.get? r with
        | some (.tuple elems) => .ok (.int elems.size)
        | _ => .error (.typeError "tuple_size/1 expects a tuple")
      | _ => .error (.typeError "tuple_size/1 expects a tuple")
  | "elem/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .ref r, .int i =>
        match h.get? r with
        | some (.tuple elems) =>
          if i < 0 || i >= elems.size then
            .error (.typeError "elem/2 index out of range")
          else
            .ok elems[i.toNat]!
        | _ => .error (.typeError "elem/2 expects (tuple, int)")
      | _, _ => .error (.typeError "elem/2 expects (tuple, int)")
  | _ => .error (.unknownFunction name)

def getReg! (f : Frame) (r : Reg) : Value := f.regs[r]!

def setReg! (f : Frame) (r : Reg) (v : Value) : Frame :=
  { f with regs := f.regs.setIfInBounds r v }

def readArgs! (f : Frame) (regs : Array Reg) : Array Value :=
  regs.map (getReg! f)

def tagOf (h : Heap) (v : Value) : Tag := Value.tagOf h v

/-- `loadLit` installs the frame before alloc so GC sees current regs as roots. -/
def loadLit (s : State) (p : Process) (frame : Frame) (reg : Reg) (lit : Term) : State :=
  let p := State.setCurrentFrame p frame
  let (p, v) := Process.allocTerm p lit
  let frame := p.stack[p.stack.size - 1]!
  let frame := setReg! frame reg v
  let frame := { frame with ip := frame.ip + 1 }
  s.setCurrentProcess (State.setCurrentFrame p frame)

/--
Execute one instruction. Register indexing is unchecked (safe for well-formed
code). Remaining errors are non-structural: `typeError`, `badArity`,
`unknownFunction`, `badPid`, `noRunnable`.
-/
def stepInstr (s : State) (p : Process) (frame : Frame) (instr : Instr) :
    Except StepError State := do
  match instr with
  | .loadLit reg lit =>
    pure (loadLit s p frame reg lit)
  | .move dest src =>
    let frame := setReg! frame dest (getReg! frame src)
    let frame := { frame with ip := frame.ip + 1 }
    pure (s.setCurrentProcess (State.setCurrentFrame p frame))
  | .call dest funName argRegs =>
    let args := readArgs! frame argRegs
    if isBuiltinName funName then
      let v ← builtin p.heap funName args
      let frame := setReg! frame dest v
      let frame := { frame with ip := frame.ip + 1 }
      pure (s.setCurrentProcess (State.setCurrentFrame p frame))
    else
      let some callee := s.module.findFunction funName
        | throw (.unknownFunction funName)
      if callee.arity != args.size then
        throw (.badArity funName callee.arity args.size)
      let caller := { frame with ip := frame.ip + 1 }
      let p := State.setCurrentFrame p caller
      let newFrame : Frame := {
        function := callee
        regs := State.mkRegs callee.locals args
        ip := 0
        retDest := dest
      }
      pure (s.setCurrentProcess { p with stack := p.stack.push newFrame })
  | .return_ reg =>
    let v := getReg! frame reg
    if p.stack.size == 1 then
      let p := { p with stack := #[], result := some v, status := .exited }
      let s := s.setCurrentProcess p
      if p.pid == s.entryPid then
        pure { s with result := some (Heap.toTerm p.heap v) }
      else
        State.scheduleNext s s.current
    else
      let stack := p.stack.pop
      let caller := stack[stack.size - 1]!
      let caller := setReg! caller frame.retDest v
      pure (s.setCurrentProcess { p with stack := stack.setIfInBounds (stack.size - 1) caller })
  | .halt reg =>
    let v := getReg! frame reg
    let p := { p with stack := #[], result := some v, status := .exited }
    let s := s.setCurrentProcess p
    if p.pid == s.entryPid then
      pure { s with result := some (Heap.toTerm p.heap v) }
    else
      State.scheduleNext s s.current
  | .jump target =>
    let frame := { frame with ip := target }
    pure (s.setCurrentProcess (State.setCurrentFrame p frame))
  | .jumpIfEq target reg lit =>
    let v := getReg! frame reg
    let frame :=
      if Heap.beqTerm p.heap v lit then { frame with ip := target }
      else { frame with ip := frame.ip + 1 }
    pure (s.setCurrentProcess (State.setCurrentFrame p frame))
  | .getTupleElem dest tupleReg index =>
    let v := getReg! frame tupleReg
    match v with
    | .ref r =>
      match p.heap.get? r with
      | some (.tuple elems) =>
        if index ≥ elems.size then
          throw (.typeError "get_tuple_elem index out of range")
        else
          let frame := setReg! frame dest elems[index]!
          let frame := { frame with ip := frame.ip + 1 }
          pure (s.setCurrentProcess (State.setCurrentFrame p frame))
      | _ => throw (.typeError "get_tuple_elem expects a tuple")
    | _ => throw (.typeError "get_tuple_elem expects a tuple")
  | .isTag dest reg tag =>
    let v := getReg! frame reg
    let frame := setReg! frame dest (.bool (tagOf p.heap v == tag))
    let frame := { frame with ip := frame.ip + 1 }
    pure (s.setCurrentProcess (State.setCurrentFrame p frame))
  | .spawn dest funName argRegs =>
    let args := readArgs! frame argRegs
    let some callee := s.module.findFunction funName
      | throw (.unknownFunction funName)
    if callee.arity != args.size then
      throw (.badArity funName callee.arity args.size)
    let child0 : Process := {
      pid := s.nextPid
      stack := #[]
      mailbox := #[]
      status := .runnable
      result := none
      heap := Heap.empty
    }
    let (child0, args') := child0.copyArrayFrom p.heap args
    let newFrame : Frame := {
      function := callee
      regs := State.mkRegs callee.locals args'
      ip := 0
      retDest := 0
    }
    let child := { child0 with stack := #[newFrame] }
    let frame := setReg! frame dest (.pid s.nextPid)
    let frame := { frame with ip := frame.ip + 1 }
    let p := State.setCurrentFrame p frame
    let s := s.setCurrentProcess p
    pure { s with processes := s.processes.push child, nextPid := s.nextPid + 1 }
  | .send pidReg msgReg =>
    let pidT := getReg! frame pidReg
    let msg := getReg! frame msgReg
    let pid ← match pidT with
      | .pid id => pure id
      | _ => throw (.typeError "send expects a pid")
    let some idx := s.findProcessIdx pid
      | throw (.badPid pid)
    let frame := { frame with ip := frame.ip + 1 }
    let p := State.setCurrentFrame p frame
    let s := s.setCurrentProcess p
    let target0 := s.processes[idx]!
    let (target0, msg') := target0.copyFrom p.heap msg
    let status :=
      match target0.status with
      | .waiting => ProcStatus.runnable
      | st => st
    let target := { target0 with mailbox := target0.mailbox.push msg', status }
    pure { s with processes := s.processes.setIfInBounds idx target }
  | .recv dest =>
    if p.mailbox.size > 0 then
      let msg := p.mailbox[0]!
      let mailbox := p.mailbox.eraseIdx! 0
      let frame := setReg! frame dest msg
      let frame := { frame with ip := frame.ip + 1 }
      pure (s.setCurrentProcess (State.setCurrentFrame { p with mailbox } frame))
    else
      let p := { p with status := .waiting }
      let s := s.setCurrentProcess p
      State.scheduleNext s s.current

def step (s : State) : Except StepError State :=
  if s.result.isSome then
    .ok s
  else if hcur : s.current < s.processes.size then
    let p := s.processes[s.current]
    if p.status != .runnable || p.result.isSome then
      State.scheduleNext s s.current
    else if p.stack.isEmpty then
      .error .emptyStack
    else
      let frame := p.stack[p.stack.size - 1]!
      let code := frame.function.code
      if frame.ip ≥ code.size then
        .error (.badIp frame.ip code.size)
      else
        match stepInstr s p frame code[frame.ip]! with
        | .error e => .error e
        | .ok s =>
          if s.result.isSome then
            .ok s
          else if s.reductions ≤ 1 then
            State.scheduleNext s s.current
          else
            .ok { s with reductions := s.reductions - 1 }
  else
    .error .noRunnable

def run (fuel : Nat) (s : State) : Except StepError Term :=
  match fuel with
  | 0 => throw (.typeError "out of fuel")
  | fuel + 1 =>
    match s.result with
    | some v => pure v
    | none => do
      let s ← step s
      run fuel s

def runModule (m : Module) (fuel : Nat := 100000)
    (heapCapacity : Nat := State.defaultHeapCapacity) : Except StepError Term := do
  let s ← State.initial m heapCapacity
  run fuel s

end Step

end Autumn
