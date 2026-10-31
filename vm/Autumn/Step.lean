import Autumn.State
import Autumn.Process
import Autumn.Json.Decode
import Autumn.WellFormed

namespace Autumn

namespace Step

/-- Outcome of a pure builtin: value, catchable `:badarg`, or stepper error. -/
inductive BuiltinResult where
  | ok (v : Value)
  | badarg
  | error (e : StepError)
  deriving Repr

/-- Builtins operate on materialized views where needed; arithmetic uses immediates.
`selfPid` is the calling process id (used by `self/0`).
Language-shaped type mismatches yield `.badarg` (IR v14); IR corruption stays `.error`. -/
def builtin (h : Heap) (selfPid : Nat) (name : FunName) (args : Array Value) :
    BuiltinResult :=
  match name with
  | "+/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .int a, .int b => .ok (.int (a + b))
      | .float a, .float b => .ok (.float (a + b))
      | _, _ => .badarg
  | "-/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .int a, .int b => .ok (.int (a - b))
      | .float a, .float b => .ok (.float (a - b))
      | _, _ => .badarg
  | "*/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .int a, .int b => .ok (.int (a * b))
      | .float a, .float b => .ok (.float (a * b))
      | _, _ => .badarg
  | "==/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else .ok (.bool (Heap.beq h args[0]! args[1]!))
  | "</2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .int a, .int b => .ok (.bool (decide (a < b)))
      | .float a, .float b => .ok (.bool (Float.lt a b))
      | _, _ => .badarg
  | ">/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .int a, .int b => .ok (.bool (decide (a > b)))
      | .float a, .float b => .ok (.bool (Float.lt b a))
      | _, _ => .badarg
  | "<=/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .int a, .int b => .ok (.bool (decide (a ≤ b)))
      | .float a, .float b => .ok (.bool (!(Float.lt b a)))
      | _, _ => .badarg
  | ">=/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .int a, .int b => .ok (.bool (decide (a ≥ b)))
      | .float a, .float b => .ok (.bool (!(Float.lt a b)))
      | _, _ => .badarg
  | "<>/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .string a, .string b => .ok (.string (a ++ b))
      | _, _ => .badarg
  | "tuple_size/1" =>
    if args.size != 1 then .error (.badArity name 1 args.size)
    else match args[0]! with
      | .ref r =>
        match h.get? r with
        | some (.tuple elems) => .ok (.int elems.size)
        | _ => .badarg
      | _ => .badarg
  | "list_size/1" =>
    if args.size != 1 then .error (.badArity name 1 args.size)
    else match args[0]! with
      | .ref r =>
        match h.get? r with
        | some (.list elems) => .ok (.int elems.size)
        | _ => .badarg
      | _ => .badarg
  | "map_size/1" =>
    if args.size != 1 then .error (.badArity name 1 args.size)
    else match args[0]! with
      | .ref r =>
        match h.get? r with
        | some (.map entries) => .ok (.int entries.size)
        | _ => .badarg
      | _ => .badarg
  | "map_get/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]! with
      | .ref r =>
        match h.get? r with
        | some (.map entries) =>
          let key := args[1]!
          .ok <|
            Id.run do
              let mut i := 0
              while hlt : i < entries.size do
                let (k, v) := entries[i]
                if Heap.beq h k key then return v
                i := i + 1
              return .nil
        | _ => .badarg
      | _ => .badarg
  | "elem/2" =>
    if args.size != 2 then .error (.badArity name 2 args.size)
    else match args[0]!, args[1]! with
      | .ref r, .int i =>
        match h.get? r with
        | some (.tuple elems) =>
          if i < 0 || i >= elems.size then
            .badarg
          else
            .ok elems[i.toNat]!
        | _ => .badarg
      | _, _ => .badarg
  | "self/0" =>
    if args.size != 0 then .error (.badArity name 0 args.size)
    else .ok (.pid selfPid)
  | _ => .error (.unknownFunction name)

def getReg! (f : Frame) (r : Reg) : Value := f.regs[r]!

def setReg! (f : Frame) (r : Reg) (v : Value) : Frame :=
  { f with regs := f.regs.setIfInBounds r v }

/-- Catchable language exception (same control as the `raise` opcode).
Uncaught: exit the process and schedule next (IR v14: entry exit does not halt the machine). -/
def raiseValue (s : State) (p : Process) (_frame : Frame) (v : Value) :
    Except StepError State :=
  if p.handlers.isEmpty then
    let p := { p with stack := #[], result := some v, status := .exited, handlers := #[] }
    let s := s.setCurrentProcess p
    let s := State.propagateExit s s.current v
    State.scheduleNext s s.current
  else
    let h := p.handlers[p.handlers.size - 1]!
    if h.stackDepth == 0 || p.stack.size < h.stackDepth then
      .error (.typeError "raise: bad handler stackDepth")
    else
      let stack := p.stack.extract 0 h.stackDepth
      let top0 := stack[stack.size - 1]!
      if h.rescueIp >= top0.function.code.size || h.excReg >= top0.function.locals then
        .error (.typeError "raise: bad handler rescue/exc")
      else
        let handlers := p.handlers.pop
        let handlers := handlers.filter (fun hh => hh.stackDepth ≤ stack.size)
        let top := setReg! top0 h.excReg v
        let top := { top with ip := h.rescueIp }
        let stack := stack.setIfInBounds (stack.size - 1) top
        .ok (s.setCurrentProcess { p with stack, handlers })

def readArgs! (f : Frame) (regs : Array Reg) : Array Value :=
  regs.map (getReg! f)

def tagOf (h : Heap) (v : Value) : Tag := Value.tagOf h v

/-- Build updated map entries (overwrite key; sort by materialized key). -/
def mapPutEntries (h : Heap) (entries : Array (Value × Value)) (key val : Value) :
    Array (Value × Value) :=
  let kept := entries.filter fun (k, _) => !(Heap.beq h k key)
  let entries := kept.push (key, val)
  entries.qsort fun (k1, _) (k2, _) =>
    Term.lt (Heap.toTerm h k1) (Heap.toTerm h k2)

/-- `map_put/3` allocates a new map (GC-safe). `none` → catchable `:badarg`. -/
def mapPut (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (mapV key val : Value) : Option State :=
  match mapV with
  | .ref r =>
    match p.heap.get? r with
    | some (.map entries) =>
      let entries := mapPutEntries p.heap entries key val
      let p := State.setCurrentFrame p frame
      let (p, v) := Process.allocMap p entries
      let frame := p.stack[p.stack.size - 1]!
      let frame := setReg! frame dest v
      let frame := { frame with ip := frame.ip + 1 }
      some (s.setCurrentProcess (State.setCurrentFrame p frame))
    | _ => none
  | _ => none

/-- `cons/2` allocates `[head | tail]` (GC-safe). `none` → catchable `:badarg`. -/
def cons (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (head tail : Value) : Option State :=
  match tail with
  | .ref r =>
    match p.heap.get? r with
    | some (.list elems) =>
      let p := State.setCurrentFrame p frame
      let (p, v) := Process.allocCompound p Node.list (#[head] ++ elems)
      let frame := p.stack[p.stack.size - 1]!
      let frame := setReg! frame dest v
      let frame := { frame with ip := frame.ip + 1 }
      some (s.setCurrentProcess (State.setCurrentFrame p frame))
    | _ => none
  | _ => none

/-- `Process.flag/2` — currently only `:trap_exit`. Returns previous flag value. -/
def processFlag (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (flagV valV : Value) : Except StepError State :=
  match flagV, valV with
  | .atom "trap_exit", .bool b =>
    let prev := p.trapExit
    let p := { p with trapExit := b }
    let frame := setReg! frame dest (.bool prev)
    let frame := { frame with ip := frame.ip + 1 }
    .ok (s.setCurrentProcess (State.setCurrentFrame p frame))
  | _, _ => raiseValue s p frame (.atom "badarg")

/-- `Process.exit/2` — self: `raiseValue`; other: force-exit (ignores trap) then yield. -/
def processExit (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (pidV reason : Value) : Except StepError State :=
  match pidV with
  | .pid pid =>
    if pid == p.pid then
      raiseValue s p frame reason
    else
      let frame := setReg! frame dest (.atom "true")
      let frame := { frame with ip := frame.ip + 1 }
      let s := s.setCurrentProcess (State.setCurrentFrame p frame)
      let s := State.forceExitPid s pid reason
      State.scheduleNext s s.current
  | _ => raiseValue s p frame (.atom "badarg")

/-- `make_tuple/N` allocates a tuple from argument registers (GC-safe). -/
def makeTuple (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (elems : Array Value) : State :=
  let p := State.setCurrentFrame p frame
  let (p, v) := Process.allocCompound p Node.tuple elems
  let frame := p.stack[p.stack.size - 1]!
  let frame := setReg! frame dest v
  let frame := { frame with ip := frame.ip + 1 }
  s.setCurrentProcess (State.setCurrentFrame p frame)

/-- `make_fun` allocates a closure heap node (GC-safe). -/
def makeFun (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (funName : FunName) (caps : Array Value) : State :=
  let p := State.setCurrentFrame p frame
  let (p, v) := Process.allocCompound p (fun env => Node.closure funName env) caps
  let frame := p.stack[p.stack.size - 1]!
  let frame := setReg! frame dest v
  let frame := { frame with ip := frame.ip + 1 }
  s.setCurrentProcess (State.setCurrentFrame p frame)

/-- `loadLit` installs the frame before alloc so GC sees current regs as roots. -/
def loadLit (s : State) (p : Process) (frame : Frame) (reg : Reg) (lit : Term) : State :=
  let p := State.setCurrentFrame p frame
  let (p, v) := Process.allocTerm p lit
  let frame := p.stack[p.stack.size - 1]!
  let frame := setReg! frame reg v
  let frame := { frame with ip := frame.ip + 1 }
  s.setCurrentProcess (State.setCurrentFrame p frame)

/-- Allocate list suffix after `index` into `dest` (GC-safe via `allocCompound`). -/
def getListRest (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (elems : Array Value) (index : Nat) : State :=
  let suffix := elems.extract (index + 1) elems.size
  let p := State.setCurrentFrame p frame
  let (p, v) := Process.allocCompound p Node.list suffix
  let frame := p.stack[p.stack.size - 1]!
  let frame := setReg! frame dest v
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
    if funName == "map_put/3" then
      if args.size != 3 then
        throw (.badArity funName 3 args.size)
      else
        match mapPut s p frame dest args[0]! args[1]! args[2]! with
        | some s => pure s
        | none => raiseValue s p frame (.atom "badarg")
    else if funName == "cons/2" then
      if args.size != 2 then
        throw (.badArity funName 2 args.size)
      else
        match cons s p frame dest args[0]! args[1]! with
        | some s => pure s
        | none => raiseValue s p frame (.atom "badarg")
    else if funName == "Process.flag/2" then
      if args.size != 2 then
        throw (.badArity funName 2 args.size)
      else
        processFlag s p frame dest args[0]! args[1]!
    else if funName == "Process.exit/2" then
      if args.size != 2 then
        throw (.badArity funName 2 args.size)
      else
        processExit s p frame dest args[0]! args[1]!
    else if funName == "make_ref/0" then
      if args.size != 0 then
        throw (.badArity funName 0 args.size)
      else
        let frame := setReg! frame dest (.reference s.nextRef)
        let frame := { frame with ip := frame.ip + 1 }
        pure {
          s.setCurrentProcess (State.setCurrentFrame p frame) with
          nextRef := s.nextRef + 1
        }
    else if isMakeTupleName funName then
      pure (makeTuple s p frame dest args)
    else if isBuiltinName funName then
      match builtin p.heap p.pid funName args with
      | .ok v =>
        let frame := setReg! frame dest v
        let frame := { frame with ip := frame.ip + 1 }
        pure (s.setCurrentProcess (State.setCurrentFrame p frame))
      | .badarg => raiseValue s p frame (.atom "badarg")
      | .error e => throw e
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
      let p := { p with stack := #[], result := some v, status := .exited, handlers := #[] }
      let s := s.setCurrentProcess p
      let s := State.propagateExit s s.current v
      State.scheduleNext s s.current
    else
      let stack := p.stack.pop
      -- Must `leave_try` before returning out of a try frame.
      if p.handlers.any (fun h => decide (h.stackDepth > stack.size)) then
        throw (.typeError "return through active try")
      else
        let caller := stack[stack.size - 1]!
        let caller := setReg! caller frame.retDest v
        pure (s.setCurrentProcess
          { p with stack := stack.setIfInBounds (stack.size - 1) caller })
  | .halt reg =>
    let v := getReg! frame reg
    let p := { p with stack := #[], result := some v, status := .exited, handlers := #[] }
    let s := s.setCurrentProcess p
    let s := State.propagateExit s s.current v
    State.scheduleNext s s.current
  | .enterTry rescueIp excReg =>
    let h : Handler := {
      stackDepth := p.stack.size
      rescueIp
      excReg
    }
    let frame := { frame with ip := frame.ip + 1 }
    let p := State.setCurrentFrame { p with handlers := p.handlers.push h } frame
    pure (s.setCurrentProcess p)
  | .leaveTry =>
    if p.handlers.isEmpty then
      throw (.typeError "leave_try with empty handler stack")
    else
      let frame := { frame with ip := frame.ip + 1 }
      let p := State.setCurrentFrame { p with handlers := p.handlers.pop } frame
      pure (s.setCurrentProcess p)
  | .raise reg =>
    raiseValue s p frame (getReg! frame reg)
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
  | .getListElem dest listReg index =>
    let v := getReg! frame listReg
    match v with
    | .ref r =>
      match p.heap.get? r with
      | some (.list elems) =>
        if index ≥ elems.size then
          throw (.typeError "get_list_elem index out of range")
        else
          let frame := setReg! frame dest elems[index]!
          let frame := { frame with ip := frame.ip + 1 }
          pure (s.setCurrentProcess (State.setCurrentFrame p frame))
      | _ => throw (.typeError "get_list_elem expects a list")
    | _ => throw (.typeError "get_list_elem expects a list")
  | .getListRest dest listReg index =>
    let v := getReg! frame listReg
    match v with
    | .ref r =>
      match p.heap.get? r with
      | some (.list elems) =>
        if index ≥ elems.size then
          throw (.typeError "get_list_rest index out of range")
        else
          pure (getListRest s p frame dest elems index)
      | _ => throw (.typeError "get_list_rest expects a list")
    | _ => throw (.typeError "get_list_rest expects a list")
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
      handlers := #[]
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
    let target1 := { target0 with mailbox := target0.mailbox.push msg' }
    let target :=
      if target0.status == .waiting then State.wakeOnMessage target1 else target1
    pure { s with processes := s.processes.setIfInBounds idx target }
  | .recv dest =>
    if p.mailbox.size > 0 then
      let msg := p.mailbox[0]!
      let mailbox := p.mailbox.eraseIdx! 0
      let frame := setReg! frame dest msg
      let frame := { frame with ip := frame.ip + 1 }
      pure (s.setCurrentProcess (State.setCurrentFrame { p with mailbox } frame))
    else
      let p := State.clearWait { p with status := .waiting }
      let s := s.setCurrentProcess p
      State.scheduleNext s s.current
  | .recvPeek dest indexReg empty =>
    match getReg! frame indexReg with
    | .int i =>
      if i < 0 then
        throw (.typeError "recv_peek index must be ≥ 0")
      else
        let idx := i.toNat
        if idx < p.mailbox.size then
          let frame := setReg! frame dest p.mailbox[idx]!
          let frame := { frame with ip := frame.ip + 1 }
          pure (s.setCurrentProcess (State.setCurrentFrame p frame))
        else
          let frame := { frame with ip := empty }
          pure (s.setCurrentProcess (State.setCurrentFrame p frame))
    | _ => throw (.typeError "recv_peek expects an int index")
  | .recvDrop indexReg =>
    match getReg! frame indexReg with
    | .int i =>
      if i < 0 then
        throw (.typeError "recv_drop index must be ≥ 0")
      else
        let idx := i.toNat
        if idx ≥ p.mailbox.size then
          throw (.typeError "recv_drop index out of range")
        else
          let mailbox := p.mailbox.eraseIdx! idx
          let frame := { frame with ip := frame.ip + 1 }
          pure (s.setCurrentProcess (State.setCurrentFrame { p with mailbox } frame))
    | _ => throw (.typeError "recv_drop expects an int index")
  | .wait retry after timeout =>
    -- Message present (including after `send` woke us): restart the receive scan.
    if p.mailbox.size > 0 then
      let frame := { frame with ip := retry }
      pure (s.setCurrentProcess (State.setCurrentFrame (State.clearWait p) frame))
    else
      -- Timed out while parked: scheduler made us runnable with deadline still set.
      match p.waitDeadline with
      | some d =>
        if d ≤ s.clock then
          let frame := { frame with ip := after }
          pure (s.setCurrentProcess (State.setCurrentFrame (State.clearWait p) frame))
        else
          let p := { p with status := .waiting }
          let s := s.setCurrentProcess p
          State.scheduleNext s s.current
      | none =>
        match timeout with
        | some 0 =>
          let frame := { frame with ip := after }
          pure (s.setCurrentProcess (State.setCurrentFrame p frame))
        | some n =>
          let p := {
            p with
            status := .waiting
            waitDeadline := some (s.clock + n)
          }
          let s := s.setCurrentProcess p
          State.scheduleNext s s.current
        | none =>
          let p := State.clearWait { p with status := .waiting }
          let s := s.setCurrentProcess p
          State.scheduleNext s s.current
  | .link pidReg =>
    let pidT := getReg! frame pidReg
    let other ← match pidT with
      | .pid id => pure id
      | _ => throw (.typeError "link expects a pid")
    let frame := { frame with ip := frame.ip + 1 }
    let p := State.setCurrentFrame p frame
    let s := s.setCurrentProcess p
    State.linkWith s other
  | .monitor dest pidReg =>
    let pidT := getReg! frame pidReg
    let other ← match pidT with
      | .pid id => pure id
      | _ => throw (.typeError "monitor expects a pid")
    let refId := s.nextRef
    let frame := setReg! frame dest (.reference refId)
    let frame := { frame with ip := frame.ip + 1 }
    let p := State.setCurrentFrame p frame
    let s := { s.setCurrentProcess p with nextRef := refId + 1 }
    State.monitorWith s other refId
  | .demonitor refReg =>
    let refId ← match getReg! frame refReg with
      | .reference id => pure id
      | _ => throw (.typeError "demonitor expects a ref")
    let frame := { frame with ip := frame.ip + 1 }
    let p := State.setCurrentFrame p frame
    let s := s.setCurrentProcess p
    State.demonitorWith s refId
  | .makeFun dest funName capRegs =>
    let caps := readArgs! frame capRegs
    pure (makeFun s p frame dest funName caps)
  | .apply dest funReg argRegs =>
    match getReg! frame funReg with
    | .ref r =>
      match p.heap.get? r with
      | some (.closure funName env) =>
        let args := readArgs! frame argRegs
        let allArgs := env ++ args
        match s.module.findFunction funName with
        | none => throw (.unknownFunction funName)
        | some callee =>
          if callee.arity == allArgs.size then
            let caller := { frame with ip := frame.ip + 1 }
            let p := State.setCurrentFrame p caller
            let newFrame : Frame := {
              function := callee
              regs := State.mkRegs callee.locals allArgs
              ip := 0
              retDest := dest
            }
            pure (s.setCurrentProcess { p with stack := p.stack.push newFrame })
          else
            throw (.badArity funName callee.arity allArgs.size)
      | _ => throw (.typeError "apply expects a fun")
    | _ => throw (.typeError "apply expects a fun")
  | .loadFile dest pathReg =>
    -- Pure stepper: no filesystem. Real loads are handled by `runIO`.
    match getReg! frame pathReg with
    | .string _ => raiseValue s p frame (.atom "enoent")
    | _ => raiseValue s p frame (.atom "badarg")

/-- After a successful instruction, bump clock and maybe yield. -/
def afterInstr (s : State) : Except StepError State :=
  let s := { s with clock := s.clock + 1 }
  if s.result.isSome then
    .ok s
  else if s.reductions ≤ 1 then
    State.scheduleNext s s.current
  else
    .ok { s with reductions := s.reductions - 1 }

/-- If the current instruction is `load_file` with a string path, return `(dest, path)`. -/
def peekLoadFile (s : State) : Option (Reg × String) :=
  if s.result.isSome then none
  else if hcur : s.current < s.processes.size then
    let p := s.processes[s.current]
    if p.status != .runnable || p.result.isSome || p.stack.isEmpty then none
    else
      let frame := p.stack[p.stack.size - 1]!
      let code := frame.function.code
      if frame.ip ≥ code.size then none
      else
        match code[frame.ip]! with
        | .loadFile dest pathReg =>
          match getReg! frame pathReg with
          | .string path => some (dest, path)
          | _ => none
        | _ => none
  else none

/-- Finish `load_file` after bytes are read (or raise `:bad_bytecode`). -/
def finishLoadFile (s : State) (dest : Reg) (contents : String) :
    Except StepError State :=
  if hcur : s.current < s.processes.size then
    let p := s.processes[s.current]
    if hsz : 0 < p.stack.size then
      let frame := p.stack[p.stack.size - 1]!
      match Json.Decode.fromString contents with
      | .error _ => raiseValue s p frame (.atom "bad_bytecode")
      | .ok incoming =>
        let m' := Module.installModules s.module incoming
        if hok : Module.checkWF m' && State.processesModuleOkB m' s then
          let s := { s with module := m' }
          let frame := setReg! frame dest (.atom "ok")
          let frame := { frame with ip := frame.ip + 1 }
          .ok (s.setCurrentProcess (State.setCurrentFrame p frame))
        else
          raiseValue s p frame (.atom "bad_bytecode")
    else
      .error .emptyStack
  else
    .error .noRunnable

/-- Raise a load failure from the current frame (`:enoent` / `:badarg`). -/
def raiseLoadAtCurrent (s : State) (reason : String) : Except StepError State :=
  if hcur : s.current < s.processes.size then
    let p := s.processes[s.current]
    if hsz : 0 < p.stack.size then
      let frame := p.stack[p.stack.size - 1]!
      raiseValue s p frame (.atom reason)
    else
      .error .emptyStack
  else
    .error .noRunnable

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
        | .ok s => afterInstr s
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

/-- IO runner: services `load_file` via `IO.FS.readFile`, then pure `step`.
Returns the final state so callers (REPL) can keep hot-loaded modules. -/
partial def runIOState (fuel : Nat) (s : State) : IO (Except StepError (State × Term)) := do
  match fuel with
  | 0 => pure (.error (.typeError "out of fuel"))
  | fuel + 1 =>
    match s.result with
    | some v => pure (.ok (s, v))
    | none =>
      match peekLoadFile s with
      | some (dest, path) =>
        let loaded ←
          try
            let contents ← IO.FS.readFile path
            pure (finishLoadFile s dest contents)
          catch _ =>
            pure (raiseLoadAtCurrent s "enoent")
        match loaded with
        | .error e => pure (.error e)
        | .ok s =>
          match afterInstr s with
          | .error e => pure (.error e)
          | .ok s => runIOState fuel s
      | none =>
        -- Non-string path on load_file: pure step raises `:badarg`.
        match step s with
        | .error e => pure (.error e)
        | .ok s => runIOState fuel s

/-- IO runner: services `load_file` via `IO.FS.readFile`, then pure `step`. -/
def runIO (fuel : Nat) (s : State) : IO (Except StepError Term) := do
  match ← runIOState fuel s with
  | .error e => pure (.error e)
  | .ok (_, v) => pure (.ok v)

def runModuleIO (m : Module) (fuel : Nat := 100000)
    (heapCapacity : Nat := State.defaultHeapCapacity) : IO (Except StepError Term) := do
  match State.initial m heapCapacity with
  | .error e => pure (.error e)
  | .ok s => runIO fuel s

end Step

end Autumn
