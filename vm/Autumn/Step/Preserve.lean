import Autumn.Step.Progress
import Autumn.State.Lemmas
import Autumn.Step

namespace Autumn
namespace Step

/-! # Preservation helpers (per-opcode `stepInstr` cases in `Step.PreserveInstr`) -/

theorem ip_succ_lt_of_nonterminal {m f ip instr}
    (hwf : Function.WF m f) (hip : ip < f.code.size)
    (hcode : f.code[ip]! = instr) (hnt : Instr.isTerminal instr = false) :
    ip + 1 < f.code.size := by
  have hnt' : Instr.isTerminal (f.code[ip]!) = false := by simpa [hcode] using hnt
  exact Function.WF.nonterminal_ip_lt hwf hip hnt'

/-- Shared hypotheses for one `stepInstr` preservation case. -/
structure StepInstrHyp (s : State) (p : Process) (frame : Frame) : Prop where
  hs : State.WF s
  hp : Process.WF s.module p
  hfwf : Frame.WF s.module frame
  hres : p.result = none
  hstat : p.status = .runnable
  htop : p.stack.size > 0
  hframe : p.stack[p.stack.size - 1]! = frame

theorem StepInstrHyp.instrOk {s p frame} (H : StepInstrHyp s p frame) (instr : Instr)
    (hcode : frame.function.code[frame.ip]! = instr) :
    Function.instrOk s.module frame.function instr := by
  have h := Frame.current_instrOk H.hfwf
  have : frame.function.code[frame.ip]'H.hfwf.2.2.1 = instr := by
    simpa [getElem!_pos frame.function.code frame.ip H.hfwf.2.2.1] using hcode
  simpa [this] using h

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
      exact h.2.2.1
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

/-- `getListRest` (allocating suffix) preserves state well-formedness. -/
theorem getListRest_preserves (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (elems : Array Value) (index : Nat)
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hip : frame.ip + 1 < frame.function.code.size) :
    State.WF (getListRest s p frame dest elems index) := by
  unfold getListRest
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
  let suffix := elems.extract (index + 1) elems.size
  let pv := Process.allocCompound p0 Node.list suffix
  have hp1 : Process.WF s.module pv.1 :=
    Process.allocCompound_preserves_WF _ _ Node.list _ hp0
  have hmeta := Process.allocCompound_meta p0 Node.list suffix
  have hstat1 : pv.1.status = .runnable := by simpa [pv, hstat0] using hmeta.1
  have hres1 : pv.1.result = none := by simpa [pv] using hmeta.2.1 hres0
  have hszEq : pv.1.stack.size = p0.stack.size := by simpa [pv] using hmeta.2.2.2
  have hsz1 : 0 < pv.1.stack.size := by simpa [hszEq] using hsz0
  have htop0 : p0.stack[p0.stack.size - 1]! = frame := by
    dsimp [p0, State.setCurrentFrame]
    simp only [htop, ↓reduceDIte]
    have hlt := Nat.sub_one_lt_of_lt htop
    simp [Array.getElem_set_self, getElem!_pos, hlt]
  have hmetaF := Process.allocCompound_top_frame_meta p0 Node.list suffix hsz0
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
      exact h.2.2.1
    have hi : pv.1.stack.size - 1 < pv.1.stack.size := Nat.sub_one_lt_of_lt hsz1
    rw [getElem!_pos pv.1.stack (pv.1.stack.size - 1) hi]
    exact hsw.1 (pv.1.stack.size - 1) hi
  have hip1 : (pv.1.stack[pv.1.stack.size - 1]!).ip + 1 <
      (pv.1.stack[pv.1.stack.size - 1]!).function.code.size := by
    simpa [htopFun, htopIp] using hip
  let frame1 := setReg! (pv.1.stack[pv.1.stack.size - 1]!) dest pv.2
  let frame2 := { frame1 with ip := frame1.ip + 1 }
  have hfwf2 : Frame.WF s.module frame2 :=
    bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf1) (by
      simpa [frame2, frame1, setReg!] using hip1)
  exact setCurrentProcess_WF s _ hs
    (setCurrentFrame_sameMeta_WF s.module pv.1 frame2 hres1 hstat1 hsz1 hp1 hfwf2
      (by simp [frame2, frame1, setReg!])
      (by simp [frame2, frame1, setReg!]))

/-- Successful allocating map-put (after resolving the map node) preserves WF. -/
theorem mapPutAlloc_preserves (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (entries : Array (Value × Value)) (key val : Value)
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hip : frame.ip + 1 < frame.function.code.size) :
    let entries' := mapPutEntries p.heap entries key val
    let p0 := State.setCurrentFrame p frame
    let pv := Process.allocMap p0 entries'
    let frame1 := setReg! (pv.1.stack[pv.1.stack.size - 1]!) dest pv.2
    let frame2 := { frame1 with ip := frame1.ip + 1 }
    State.WF (s.setCurrentProcess (State.setCurrentFrame pv.1 frame2)) := by
  let entries' := mapPutEntries p.heap entries key val
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
  let pv := Process.allocMap p0 entries'
  have hp1 : Process.WF s.module pv.1 := Process.allocMap_preserves_WF _ _ _ hp0
  have hmeta := Process.allocMap_meta p0 entries'
  have hstat1 : pv.1.status = .runnable := by simpa [pv, hstat0] using hmeta.1
  have hres1 : pv.1.result = none := by simpa [pv] using hmeta.2.1 hres0
  have hszEq : pv.1.stack.size = p0.stack.size := by simpa [pv] using hmeta.2.2.2
  have hsz1 : 0 < pv.1.stack.size := by simpa [hszEq] using hsz0
  have htop0 : p0.stack[p0.stack.size - 1]! = frame := by
    dsimp [p0, State.setCurrentFrame]
    simp only [htop, ↓reduceDIte]
    have hlt := Nat.sub_one_lt_of_lt htop
    simp [Array.getElem_set_self, getElem!_pos, hlt]
  have hmetaF := Process.allocMap_top_frame_meta p0 entries' hsz0
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
      exact h.2.2.1
    have hi : pv.1.stack.size - 1 < pv.1.stack.size := Nat.sub_one_lt_of_lt hsz1
    rw [getElem!_pos pv.1.stack (pv.1.stack.size - 1) hi]
    exact hsw.1 (pv.1.stack.size - 1) hi
  have hip1 : (pv.1.stack[pv.1.stack.size - 1]!).ip + 1 <
      (pv.1.stack[pv.1.stack.size - 1]!).function.code.size := by
    simpa [htopFun, htopIp] using hip
  let frame1 := setReg! (pv.1.stack[pv.1.stack.size - 1]!) dest pv.2
  let frame2 := { frame1 with ip := frame1.ip + 1 }
  have hfwf2 : Frame.WF s.module frame2 :=
    bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf1) (by
      simpa [frame2, frame1, setReg!] using hip1)
  exact setCurrentProcess_WF s _ hs
    (setCurrentFrame_sameMeta_WF s.module pv.1 frame2 hres1 hstat1 hsz1 hp1 hfwf2
      (by simp [frame2, frame1, setReg!])
      (by simp [frame2, frame1, setReg!]))

/-- Direct cons allocation WF (same shape as `getListRest_preserves`). -/
theorem cons_alloc_preserves (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (head : Value) (elems : Array Value)
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hip : frame.ip + 1 < frame.function.code.size) :
    let p0 := State.setCurrentFrame p frame
    let pv := Process.allocCompound p0 Node.list (#[head] ++ elems)
    let frame1 := setReg! (pv.1.stack[pv.1.stack.size - 1]!) dest pv.2
    let frame2 := { frame1 with ip := frame1.ip + 1 }
    State.WF (s.setCurrentProcess (State.setCurrentFrame pv.1 frame2)) := by
  -- Mirror getListRest_preserves with Node.list (#[head] ++ elems)
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
  let vs := #[head] ++ elems
  let pv := Process.allocCompound p0 Node.list vs
  have hp1 : Process.WF s.module pv.1 :=
    Process.allocCompound_preserves_WF _ _ Node.list _ hp0
  have hmeta := Process.allocCompound_meta p0 Node.list vs
  have hstat1 : pv.1.status = .runnable := by simpa [pv, hstat0] using hmeta.1
  have hres1 : pv.1.result = none := by simpa [pv] using hmeta.2.1 hres0
  have hszEq : pv.1.stack.size = p0.stack.size := by simpa [pv] using hmeta.2.2.2
  have hsz1 : 0 < pv.1.stack.size := by simpa [hszEq] using hsz0
  have htop0 : p0.stack[p0.stack.size - 1]! = frame := by
    dsimp [p0, State.setCurrentFrame]
    simp only [htop, ↓reduceDIte]
    have hlt := Nat.sub_one_lt_of_lt htop
    simp [Array.getElem_set_self, getElem!_pos, hlt]
  have hmetaF := Process.allocCompound_top_frame_meta p0 Node.list vs hsz0
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
      exact h.2.2.1
    have hi : pv.1.stack.size - 1 < pv.1.stack.size := Nat.sub_one_lt_of_lt hsz1
    rw [getElem!_pos pv.1.stack (pv.1.stack.size - 1) hi]
    exact hsw.1 (pv.1.stack.size - 1) hi
  have hip1 : (pv.1.stack[pv.1.stack.size - 1]!).ip + 1 <
      (pv.1.stack[pv.1.stack.size - 1]!).function.code.size := by
    simpa [htopFun, htopIp] using hip
  let frame1 := setReg! (pv.1.stack[pv.1.stack.size - 1]!) dest pv.2
  let frame2 := { frame1 with ip := frame1.ip + 1 }
  have hfwf2 : Frame.WF s.module frame2 :=
    bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf1) (by
      simpa [frame2, frame1, setReg!] using hip1)
  exact setCurrentProcess_WF s _ hs
    (setCurrentFrame_sameMeta_WF s.module pv.1 frame2 hres1 hstat1 hsz1 hp1 hfwf2
      (by simp [frame2, frame1, setReg!])
      (by simp [frame2, frame1, setReg!]))

theorem makeTuple_preserves (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (elems : Array Value)
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hip : frame.ip + 1 < frame.function.code.size) :
    State.WF (makeTuple s p frame dest elems) := by
  unfold makeTuple
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
  let pv := Process.allocCompound p0 Node.tuple elems
  have hp1 : Process.WF s.module pv.1 :=
    Process.allocCompound_preserves_WF _ _ Node.tuple _ hp0
  have hmeta := Process.allocCompound_meta p0 Node.tuple elems
  have hstat1 : pv.1.status = .runnable := by simpa [pv, hstat0] using hmeta.1
  have hres1 : pv.1.result = none := by simpa [pv] using hmeta.2.1 hres0
  have hszEq : pv.1.stack.size = p0.stack.size := by simpa [pv] using hmeta.2.2.2
  have hsz1 : 0 < pv.1.stack.size := by simpa [hszEq] using hsz0
  have htop0 : p0.stack[p0.stack.size - 1]! = frame := by
    dsimp [p0, State.setCurrentFrame]
    simp only [htop, ↓reduceDIte]
    have hlt := Nat.sub_one_lt_of_lt htop
    simp [Array.getElem_set_self, getElem!_pos, hlt]
  have hmetaF := Process.allocCompound_top_frame_meta p0 Node.tuple elems hsz0
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
      exact h.2.2.1
    have hi : pv.1.stack.size - 1 < pv.1.stack.size := Nat.sub_one_lt_of_lt hsz1
    rw [getElem!_pos pv.1.stack (pv.1.stack.size - 1) hi]
    exact hsw.1 (pv.1.stack.size - 1) hi
  have hip1 : (pv.1.stack[pv.1.stack.size - 1]!).ip + 1 <
      (pv.1.stack[pv.1.stack.size - 1]!).function.code.size := by
    simpa [htopFun, htopIp] using hip
  let frame1 := setReg! (pv.1.stack[pv.1.stack.size - 1]!) dest pv.2
  let frame2 := { frame1 with ip := frame1.ip + 1 }
  have hfwf2 : Frame.WF s.module frame2 :=
    bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf1) (by
      simpa [frame2, frame1, setReg!] using hip1)
  exact setCurrentProcess_WF s _ hs
    (setCurrentFrame_sameMeta_WF s.module pv.1 frame2 hres1 hstat1 hsz1 hp1 hfwf2
      (by simp [frame2, frame1, setReg!])
      (by simp [frame2, frame1, setReg!]))

/-- Successful `mapPut` preserves WF. -/
theorem mapPut_preserves (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (mapV key val : Value) {s'}
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hip : frame.ip + 1 < frame.function.code.size)
    (h : mapPut s p frame dest mapV key val = some s') :
    State.WF s' := by
  unfold mapPut at h
  split at h
  · split at h
    · cases h
      rename_i entries _
      exact mapPutAlloc_preserves s p frame dest entries key val
        hs hp hfwf hres hstat htop hframe hip
    · exact nomatch h
  · exact nomatch h

/-- Successful `cons` preserves WF. -/
theorem cons_preserves (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (head tail : Value) {s'}
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hip : frame.ip + 1 < frame.function.code.size)
    (h : cons s p frame dest head tail = some s') :
    State.WF s' := by
  unfold cons at h
  split at h
  · split at h
    · cases h
      rename_i elems _
      exact cons_alloc_preserves s p frame dest head elems
        hs hp hfwf hres hstat htop hframe hip
    · exact nomatch h
  · exact nomatch h

/-- `raiseValue` preserves WF (shared by `raise` and pure `load_file`). -/
theorem raiseValue_preserves
    (s : State) (p : Process) (frame : Frame) (v : Value) {s'}
    (hs : State.WF s) (hp : Process.WF s.module p)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0)
    (h : raiseValue s p frame v = .ok s') :
    State.WF s' := by
    cases hEmp : p.handlers.isEmpty with
    | true =>
      simp [raiseValue, hEmp] at h
      let pEx :=
        { p with
          stack := #[]
          result := some v
          status := .exited
          handlers := #[] }
      have hs2 : State.WF
          (State.propagateExit (s.setCurrentProcess pEx) (s.setCurrentProcess pEx).current
            v) :=
        propagateExit_preserves _ _ _
          (setCurrentProcess_WF s pEx hs (exited_process_WF _ p _ hp.1))
      exact scheduleNext_preserves _ _ hs2 h
    | false =>
      simp [raiseValue, hEmp] at h
      have hempty : p.handlers ≠ #[] := by
        intro heq; simp [heq, Array.isEmpty] at hEmp
      have hp' := runnable_WF_parts hp (Or.inl hstat) hres
      have hszH : 0 < p.handlers.size := by
        cases hsz : p.handlers.size with
        | zero =>
          exact absurd (Array.eq_empty_of_size_eq_zero hsz) hempty
        | succ n => omega
      let hand := p.handlers[p.handlers.size - 1]!
      have hhandIdx : p.handlers.size - 1 < p.handlers.size := Nat.sub_one_lt_of_lt hszH
      have hhandEq : hand = p.handlers[p.handlers.size - 1]'hhandIdx :=
        getElem!_pos p.handlers (p.handlers.size - 1) hhandIdx
      have ⟨hd0, hdle, hresIp, hexc⟩ := hp'.2.2 (p.handlers.size - 1) hhandIdx
      have hdepth0 : 0 < hand.stackDepth := by simpa [hhandEq] using hd0
      have hdepthLe : hand.stackDepth ≤ p.stack.size := by simpa [hhandEq] using hdle
      have hbad1 : ¬(hand.stackDepth = 0 ∨ p.stack.size < hand.stackDepth) := by
        intro hbad
        rcases hbad with h0 | hlt
        · omega
        · omega
      simp [hand, hbad1] at h
      have hmin : min hand.stackDepth p.stack.size = hand.stackDepth :=
        Nat.min_eq_left hdepthLe
      have hszExt : (p.stack.extract 0 hand.stackDepth).size = hand.stackDepth := by
        simp [Array.size_extract, hmin]
      have htopExt :
          (p.stack.extract 0 hand.stackDepth)[(p.stack.extract 0 hand.stackDepth).size - 1]! =
            p.stack[hand.stackDepth - 1]! := by
        have hlt : (p.stack.extract 0 hand.stackDepth).size - 1 <
            (p.stack.extract 0 hand.stackDepth).size := by
          simpa [hszExt] using Nat.sub_one_lt_of_lt hdepth0
        have hlt0 : hand.stackDepth - 1 < p.stack.size := by omega
        rw [hszExt, getElem!_pos (p.stack.extract 0 hand.stackDepth) (hand.stackDepth - 1)
              (by simpa [hszExt] using Nat.sub_one_lt_of_lt hdepth0),
            getElem!_pos p.stack (hand.stackDepth - 1) hlt0]
        simp [Nat.zero_add,
          Array.getElem_extract (xs := p.stack) (start := 0) (stop := hand.stackDepth)
            (by simpa [hszExt] using Nat.sub_one_lt_of_lt hdepth0)]
      have htop' :
          (p.stack.extract 0 hand.stackDepth)[min hand.stackDepth p.stack.size - 1]! =
            p.stack[hand.stackDepth - 1]! := by
        simpa [hmin, hszExt] using htopExt
      have hbad2 :
          ¬((p.stack.extract 0 hand.stackDepth)[min hand.stackDepth p.stack.size - 1]!.function.code.size ≤
              hand.rescueIp ∨
            (p.stack.extract 0 hand.stackDepth)[min hand.stackDepth p.stack.size - 1]!.function.locals ≤
              hand.excReg) := by
        rw [htop']
        intro hbad
        have hrip : hand.rescueIp < p.stack[hand.stackDepth - 1]!.function.code.size := by
          simpa [hhandEq] using hresIp
        have hexc' : hand.excReg < p.stack[hand.stackDepth - 1]!.function.locals := by
          simpa [hhandEq] using hexc
        rcases hbad with hr | he
        · exact Nat.not_le.mpr hrip hr
        · exact Nat.not_le.mpr hexc' he
      simp [hand, hbad2] at h
      cases h
      -- Build WF for the catch process via extract_set_top, then rewrite to the goal.
      let depth := hand.stackDepth
      let stack0 := p.stack.extract 0 depth
      have hsz0 : stack0.size = depth := by simpa [stack0, depth] using hszExt
      let top0 := stack0[min depth p.stack.size - 1]!
      have htop0eq : top0 = p.stack[depth - 1]! := by
        simpa [top0, stack0, depth] using htop'
      let top := { setReg! top0 hand.excReg v with ip := hand.rescueIp }
      have htop0WF : Frame.WF s.module top0 := by
        have hlt : depth - 1 < p.stack.size := by dsimp [depth]; omega
        have ⟨hframes, _⟩ := hp'.2.1
        have hget : p.stack[depth - 1]! = p.stack[depth - 1]'hlt :=
          getElem!_pos p.stack (depth - 1) hlt
        simpa [top0, htop0eq, hget] using hframes (depth - 1) hlt
      have htopWF : Frame.WF s.module top := by
        have h1 := setReg!_WF top0 hand.excReg v s.module htop0WF
        refine ⟨h1.1, h1.2.1, ?_, h1.2.2.2⟩
        have : hand.rescueIp < top0.function.code.size := by
          have hrip : hand.rescueIp < p.stack[depth - 1]!.function.code.size := by
            simpa [hhandEq, depth] using hresIp
          simpa [htop0eq] using hrip
        simpa [top, setReg!] using this
      have htop0sz : top0 = stack0[stack0.size - 1]! := by
        dsimp [top0]
        have : min depth p.stack.size = stack0.size := by
          rw [hsz0, hmin]
        rw [this]
      have hsameFun : top.function =
          (p.stack.extract 0 depth)[(p.stack.extract 0 depth).size - 1]!.function := by
        simp [top, setReg!, htop0sz, stack0]
      have hsameRet : top.retDest =
          (p.stack.extract 0 depth)[(p.stack.extract 0 depth).size - 1]!.retDest := by
        simp [top, setReg!, htop0sz, stack0]
      let handlers' := (p.handlers.pop).filter
        (fun hh => decide (hh.stackDepth ≤ min depth p.stack.size))
      have hhs : Process.handlersWF (p.stack.extract 0 depth) handlers' := by
        intro i hi
        have hmem : handlers'[i] ∈ handlers' := Array.getElem_mem hi
        have ⟨hmemPop, hpredB⟩ := (Array.mem_filter).1 hmem
        have hpred : handlers'[i].stackDepth ≤ min depth p.stack.size := by
          simpa [decide_eq_true_iff] using hpredB
        have hpred' : handlers'[i].stackDepth ≤ (p.stack.extract 0 depth).size := by
          simpa [hszExt, depth, hmin] using hpred
        obtain ⟨j, hj, hgetj⟩ := Array.getElem_of_mem hmemPop
        have hj0 : j < p.handlers.size := by simp [Array.size_pop] at hj; omega
        have hgetPop : p.handlers.pop[j]'hj = p.handlers[j]'hj0 := Array.getElem_pop hj
        have heq : handlers'[i] = p.handlers[j]'hj0 := by rw [← hgetj, hgetPop]
        have ⟨hd0', _hdle0, hip0, hexc0⟩ := hp'.2.2 j hj0
        refine ⟨by simpa [heq] using hd0', hpred', ?_, ?_⟩
        · rw [heq]
          have hdi : (p.handlers[j]'hj0).stackDepth - 1 < (p.stack.extract 0 depth).size := by
            have : (p.handlers[j]'hj0).stackDepth ≤ (p.stack.extract 0 depth).size := by
              simpa [heq] using hpred'
            omega
          have hdi0 : (p.handlers[j]'hj0).stackDepth - 1 < p.stack.size := by omega
          have hgetS :
              (p.stack.extract 0 depth)[(p.handlers[j]'hj0).stackDepth - 1]! =
                p.stack[(p.handlers[j]'hj0).stackDepth - 1]! := by
            rw [getElem!_pos (p.stack.extract 0 depth) _ hdi,
              getElem!_pos p.stack _ hdi0]
            simp [Nat.zero_add,
              Array.getElem_extract (xs := p.stack) (start := 0) (stop := depth) hdi]
          rw [hgetS]; exact hip0
        · rw [heq]
          have hdi : (p.handlers[j]'hj0).stackDepth - 1 < (p.stack.extract 0 depth).size := by
            have : (p.handlers[j]'hj0).stackDepth ≤ (p.stack.extract 0 depth).size := by
              simpa [heq] using hpred'
            omega
          have hdi0 : (p.handlers[j]'hj0).stackDepth - 1 < p.stack.size := by omega
          have hgetS :
              (p.stack.extract 0 depth)[(p.handlers[j]'hj0).stackDepth - 1]! =
                p.stack[(p.handlers[j]'hj0).stackDepth - 1]! := by
            rw [getElem!_pos (p.stack.extract 0 depth) _ hdi,
              getElem!_pos p.stack _ hdi0]
            simp [Nat.zero_add,
              Array.getElem_extract (xs := p.stack) (start := 0) (stop := depth) hdi]
          rw [hgetS]; exact hexc0
      have hp2 :=
        extract_set_top_process_WF s.module p depth top hres hstat
          (by simpa [depth] using hdepth0)
          (by simpa [depth] using hdepthLe) hp htopWF hsameFun hsameRet handlers' hhs
      -- Unfold lets, then align `size`/`min` and filter stop with the goal's shape.
      simp only [hand, depth, stack0, top0, top, handlers'] at hp2 ⊢
      have hszMin :
          (p.stack.extract 0 p.handlers[p.handlers.size - 1]!.stackDepth).size =
            min p.handlers[p.handlers.size - 1]!.stackDepth p.stack.size := by
        simp [Array.size_extract]
      have hszPop : p.handlers.pop.size = p.handlers.size - 1 := by
        simp [Array.size_pop]
      rw [hszMin, hszPop] at hp2
      exact setCurrentProcess_WF s _ hs hp2

theorem makeFun_preserves (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (funName : FunName) (caps : Array Value)
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hip : frame.ip + 1 < frame.function.code.size) :
    State.WF (makeFun s p frame dest funName caps) := by
  unfold makeFun
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
  let mk := fun env => Node.closure funName env
  let pv := Process.allocCompound p0 mk caps
  have hp1 : Process.WF s.module pv.1 :=
    Process.allocCompound_preserves_WF _ _ mk _ hp0
  have hmeta := Process.allocCompound_meta p0 mk caps
  have hstat1 : pv.1.status = .runnable := by simpa [pv, hstat0] using hmeta.1
  have hres1 : pv.1.result = none := by simpa [pv] using hmeta.2.1 hres0
  have hszEq : pv.1.stack.size = p0.stack.size := by simpa [pv] using hmeta.2.2.2
  have hsz1 : 0 < pv.1.stack.size := by simpa [hszEq] using hsz0
  have htop0 : p0.stack[p0.stack.size - 1]! = frame := by
    dsimp [p0, State.setCurrentFrame]
    simp only [htop, ↓reduceDIte]
    have hlt := Nat.sub_one_lt_of_lt htop
    simp [Array.getElem_set_self, getElem!_pos, hlt]
  have hmetaF := Process.allocCompound_top_frame_meta p0 mk caps hsz0
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
      exact h.2.2.1
    have hi : pv.1.stack.size - 1 < pv.1.stack.size := Nat.sub_one_lt_of_lt hsz1
    rw [getElem!_pos pv.1.stack (pv.1.stack.size - 1) hi]
    exact hsw.1 (pv.1.stack.size - 1) hi
  have hip1 : (pv.1.stack[pv.1.stack.size - 1]!).ip + 1 <
      (pv.1.stack[pv.1.stack.size - 1]!).function.code.size := by
    simpa [htopFun, htopIp] using hip
  let frame1 := setReg! (pv.1.stack[pv.1.stack.size - 1]!) dest pv.2
  let frame2 := { frame1 with ip := frame1.ip + 1 }
  have hfwf2 : Frame.WF s.module frame2 :=
    bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf1) (by
      simpa [frame2, frame1, setReg!] using hip1)
  exact setCurrentProcess_WF s _ hs
    (setCurrentFrame_sameMeta_WF s.module pv.1 frame2 hres1 hstat1 hsz1 hp1 hfwf2
      (by simp [frame2, frame1, setReg!])
      (by simp [frame2, frame1, setReg!]))

/-- Successful `Process.flag/2` preserves WF. -/
theorem processFlag_preserves
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (flagV valV : Value) {s'}
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hip : frame.ip + 1 < frame.function.code.size)
    (h : processFlag s p frame dest flagV valV = .ok s') :
    State.WF s' := by
  simp [processFlag] at h
  split at h
  · cases h
    rename_i b
    let p1 := { p with trapExit := b }
    have hp1 : Process.WF s.module p1 := process_set_trapExit_WF _ _ _ hp
    let frame1 := setReg! frame dest (.bool p.trapExit)
    let frame2 := { frame1 with ip := frame1.ip + 1 }
    have hfwf2 : Frame.WF s.module frame2 :=
      bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
    exact apply_top_frame_preserves s p1 frame2 hs hp1
      (by simpa [p1] using hres) (by simpa [p1] using hstat)
      (by simpa [p1] using htop) hfwf2
      (by simp [frame2, frame1, setReg!, hframe, p1])
      (by simp [frame2, frame1, setReg!, hframe, p1])
  · exact raiseValue_preserves _ _ _ _ hs hp hres hstat htop h

/-- Successful `Process.exit/2` preserves WF. -/
theorem processExit_preserves
    (s : State) (p : Process) (frame : Frame) (dest : Reg)
    (pidV reason : Value) {s'}
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hip : frame.ip + 1 < frame.function.code.size)
    (h : processExit s p frame dest pidV reason = .ok s') :
    State.WF s' := by
  simp [processExit] at h
  split at h
  · rename_i pid
    split at h
    · exact raiseValue_preserves _ _ _ _ hs hp hres hstat htop h
    · let frame1 := setReg! frame dest (.atom "true")
      let frame2 := { frame1 with ip := frame1.ip + 1 }
      have hfwf2 : Frame.WF s.module frame2 :=
        bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
      have hs1 : State.WF (s.setCurrentProcess (State.setCurrentFrame p frame2)) :=
        apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
          (by simp [frame2, frame1, setReg!, hframe])
          (by simp [frame2, frame1, setReg!, hframe])
      have hs2 := forceExitPid_preserves
        (s.setCurrentProcess (State.setCurrentFrame p frame2)) pid reason hs1
      exact scheduleNext_preserves _ _ hs2 h
  · exact raiseValue_preserves _ _ _ _ hs hp hres hstat htop h

/-- `raiseLoadAtCurrent` preserves WF (`:enoent` / `:badarg` from the IO runner). -/
theorem raiseLoadAtCurrent_preserves
    (s : State) (reason : String) {s'}
    (hs : State.WF s)
    (hstat0 : (s.processes[s.current]'hs.2.2.1).status = .runnable)
    (hres0 : (s.processes[s.current]'hs.2.2.1).result = none)
    (h : raiseLoadAtCurrent s reason = .ok s') :
    State.WF s' := by
  have hcur := hs.2.2.1
  let p := s.processes[s.current]'hcur
  have hp : Process.WF s.module p := hs.2.2.2 s.current hcur
  have hstat : p.status = .runnable := hstat0
  have hres : p.result = none := hres0
  have hsz : 0 < p.stack.size := runnable_stack_pos hp hstat hres
  simp [raiseLoadAtCurrent, hcur, show 0 < (s.processes[s.current]).stack.size from hsz] at h
  exact raiseValue_preserves s p (p.stack[p.stack.size - 1]!) (.atom reason)
    hs hp hres hstat hsz h

/-- Successful / rejecting `finishLoadFile` preserves WF.
On the install-success path, `hip` must hold (`load_file` is nonterminal). -/
theorem finishLoadFile_preserves
    (s : State) (dest : Reg) (contents : String) {s'}
    (hs : State.WF s)
    (hstat0 : (s.processes[s.current]'hs.2.2.1).status = .runnable)
    (hres0 : (s.processes[s.current]'hs.2.2.1).result = none)
    (hip :
      ((s.processes[s.current]'hs.2.2.1).stack[
        (s.processes[s.current]'hs.2.2.1).stack.size - 1]!).ip + 1 <
      ((s.processes[s.current]'hs.2.2.1).stack[
        (s.processes[s.current]'hs.2.2.1).stack.size - 1]!).function.code.size)
    (h : finishLoadFile s dest contents = .ok s') :
    State.WF s' := by
  have hcur := hs.2.2.1
  let p := s.processes[s.current]'hcur
  have hp : Process.WF s.module p := hs.2.2.2 s.current hcur
  have hstat : p.status = .runnable := hstat0
  have hres : p.result = none := hres0
  have hsz : 0 < p.stack.size := runnable_stack_pos hp hstat hres
  let frame := p.stack[p.stack.size - 1]!
  have hip' : frame.ip + 1 < frame.function.code.size := hip
  simp [finishLoadFile, hcur, show 0 < (s.processes[s.current]).stack.size from hsz] at h
  cases hdec : Json.Decode.fromString contents with
  | error _ =>
    simp [hdec] at h
    exact raiseValue_preserves s p frame (.atom "bad_bytecode") hs hp hres hstat hsz h
  | ok incoming =>
    simp [hdec] at h
    by_cases hok :
        Module.checkWF (Module.installModules s.module incoming) = true ∧
          State.processesModuleOkB (Module.installModules s.module incoming) s = true
    · simp [hok, ↓reduceIte] at h
      let m' := Module.installModules s.module incoming
      have hm'WF : Module.WF m' := Module.checkWF_sound m' hok.1
      have hs1 : State.WF { s with module := m' } :=
        State.WF_with_module s m' hs hm'WF hok.2
      have hp1 : Process.WF m' p := by simpa [p] using hs1.2.2.2 s.current hcur
      have hfwf0 : Frame.WF m' frame := by
        simpa [frame] using runnable_top_WF hp1 hstat hres
      let frame1 := setReg! frame dest (.atom "ok")
      have hfwf1 : Frame.WF m' frame1 := setReg!_WF frame dest (.atom "ok") m' hfwf0
      let frame2 := { frame1 with ip := frame1.ip + 1 }
      have hip2 : frame1.ip + 1 < frame1.function.code.size := by
        simpa [frame1, setReg!] using hip'
      have hfwf2 : Frame.WF m' frame2 := bumpIp_frame frame1 m' hfwf1 hip2
      have hs2 :
          State.WF
            ({ s with module := m' }.setCurrentProcess (State.setCurrentFrame p frame2)) :=
        apply_top_frame_preserves { s with module := m' } p frame2 hs1 hp1 hres hstat
          hsz hfwf2 (by simp [frame2, frame1, setReg!, frame])
          (by simp [frame2, frame1, setReg!, frame])
      cases h
      exact hs2
    · simp [hok, ↓reduceIte] at h
      exact raiseValue_preserves s p frame (.atom "bad_bytecode") hs hp hres hstat hsz h

end Step
end Autumn
