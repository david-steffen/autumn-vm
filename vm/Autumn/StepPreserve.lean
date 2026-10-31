import Autumn.StepProgress
import Autumn.StateLemmas
import Autumn.Step

namespace Autumn
namespace Step

/-! # Preservation helpers and stepInstr_preserves -/

private theorem ip_succ_lt_of_nonterminal {m f ip instr}
    (hwf : Function.WF m f) (hip : ip < f.code.size)
    (hcode : f.code[ip]! = instr) (hnt : Instr.isTerminal instr = false) :
    ip + 1 < f.code.size := by
  have hnt' : Instr.isTerminal (f.code[ip]!) = false := by simpa [hcode] using hnt
  exact Function.WF.nonterminal_ip_lt hwf hip hnt'

theorem findFunction_name {m : Module} {name : FunName} {f : Function}
    (h : m.findFunction name = some f) : f.name = name := by
  simp only [Module.findFunction] at h
  have ⟨hbeq, _⟩ := (List.find?_eq_some_iff_append).1 h
  exact (beq_iff_eq).1 hbeq


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
    (h : mapPut s p frame dest mapV key val = .ok s') :
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
    (h : cons s p frame dest head tail = .ok s') :
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
    simp [raiseValue] at h
    by_cases hempty : p.handlers = #[]
    · simp [hempty] at h
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
      split at h
      · cases h; exact result_update_preserves _ _ hs2
      · exact scheduleNext_preserves _ _ hs2 h
    · simp [hempty] at h
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

/-- Successful `stepInstr` preserves well-formedness under the usual stepper hypotheses. -/
theorem stepInstr_preserves
    (s : State) (p : Process) (frame : Frame) (instr : Instr) {s'}
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hcode : frame.function.code[frame.ip]! = instr)
    (h : stepInstr s p frame instr = .ok s') :
    State.WF s' := by
  have hio : Function.instrOk s.module frame.function instr := by
    have h := Frame.current_instrOk hfwf
    have : frame.function.code[frame.ip]'hfwf.2.2.1 = instr := by
      simpa [getElem!_pos frame.function.code frame.ip hfwf.2.2.1] using hcode
    simpa [this] using h
  cases instr with
  | loadLit reg lit =>
    simp [stepInstr] at h; cases h
    have hnt : Instr.isTerminal (.loadLit reg lit) = false := rfl
    have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
    exact loadLit_preserves s p frame reg lit hs hp hfwf hres hstat htop hframe hip
  | move dest src =>
    simp [stepInstr] at h; cases h
    have hnt : Instr.isTerminal (.move dest src) = false := rfl
    have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
    let frame1 := setReg! frame dest (getReg! frame src)
    let frame2 := { frame1 with ip := frame1.ip + 1 }
    have hfwf2 : Frame.WF s.module frame2 :=
      bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
    exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
      (by simp [frame2, frame1, setReg!, hframe]) (by simp [frame2, frame1, setReg!, hframe])
  | isTag dest reg tag =>
    simp [stepInstr] at h; cases h
    have hnt : Instr.isTerminal (.isTag dest reg tag) = false := rfl
    have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
    let frame1 := setReg! frame dest (.bool (tagOf p.heap (getReg! frame reg) == tag))
    let frame2 := { frame1 with ip := frame1.ip + 1 }
    have hfwf2 : Frame.WF s.module frame2 :=
      bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
    exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
      (by simp [frame2, frame1, setReg!, hframe]) (by simp [frame2, frame1, setReg!, hframe])
  | jump target =>
    simp [stepInstr] at h; cases h
    have htgt : target < frame.function.code.size := by
      simpa [Function.instrOk, Instr.jumpTargetOk, hcode] using hio.2.1
    let frame2 := { frame with ip := target }
    have hfwf2 : Frame.WF s.module frame2 := setIp_frame _ _ _ hfwf htgt
    exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
      (by simp [frame2, hframe]) (by simp [frame2, hframe])
  | jumpIfEq target reg lit =>
    simp [stepInstr] at h; cases h
    have htgt : target < frame.function.code.size := by
      simpa [Function.instrOk, Instr.jumpTargetOk] using hio.2.1
    have hnt : Instr.isTerminal (.jumpIfEq target reg lit) = false := rfl
    have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
    by_cases hb : Heap.beqTerm p.heap (getReg! frame reg) lit = true
    · simp [hb]
      let frame2 := { frame with ip := target }
      have hfwf2 : Frame.WF s.module frame2 := setIp_frame _ _ _ hfwf htgt
      exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
        (by simp [frame2, hframe]) (by simp [frame2, hframe])
    · simp [hb]
      let frame2 := { frame with ip := frame.ip + 1 }
      have hfwf2 : Frame.WF s.module frame2 := bumpIp_frame _ _ hfwf hip
      exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
        (by simp [frame2, hframe]) (by simp [frame2, hframe])
  | enterTry rescueIp excReg =>
    simp [stepInstr] at h; cases h
    have hnt : Instr.isTerminal (.enterTry rescueIp excReg) = false := rfl
    have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
    let hnd : Handler := {
      stackDepth := p.stack.size
      rescueIp
      excReg
    }
    let pH := { p with handlers := p.handlers.push hnd }
    have hpH : Process.WF s.module pH := by
      refine process_handlers_WF _ p _ hp hres ?_
      have hp' := runnable_WF_parts hp (Or.inl hstat) hres
      intro i hi
      have hi' : i < p.handlers.size + 1 := by simpa [Array.size_push] using hi
      by_cases heq : i = p.handlers.size
      · subst heq
        have hget : (p.handlers.push hnd)[p.handlers.size]'hi = hnd := Array.getElem_push_eq
        have hexcOk : excReg < frame.function.locals := by
          simpa [Function.instrOk, Instr.regsOk, hcode] using hio.1
        have hresOk : rescueIp < frame.function.code.size := by
          simpa [Function.instrOk, Instr.jumpTargetOk, hcode] using hio.2.1
        simp only [hget, hnd]
        refine ⟨htop, Nat.le_refl _, ?_, ?_⟩
        · have htop! : p.stack[p.stack.size - 1]! = frame := hframe
          simpa [htop!] using hresOk
        · have htop! : p.stack[p.stack.size - 1]! = frame := hframe
          simpa [htop!] using hexcOk
      · have hi0 : i < p.handlers.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi') heq
        have hget : (p.handlers.push hnd)[i]'hi = p.handlers[i]'hi0 :=
          Array.getElem_push_lt hi0
        have ⟨hd0, hdle, hip0, hexc0⟩ := hp'.2.2 i hi0
        simpa [hget] using And.intro hd0 (And.intro hdle (And.intro hip0 hexc0))
    let frame2 := { frame with ip := frame.ip + 1 }
    have hfwf2 : Frame.WF s.module frame2 := bumpIp_frame _ _ hfwf hip
    exact apply_top_frame_preserves s pH frame2 hs hpH
      (by simpa [pH] using hres) (by simpa [pH] using hstat)
      (by simpa [pH] using htop) hfwf2
      (by simp [frame2, pH, hframe]) (by simp [frame2, pH, hframe])
  | leaveTry =>
    simp [stepInstr] at h
    split at h
    · exact nomatch h
    · cases h
      have hnt : Instr.isTerminal (.leaveTry) = false := rfl
      have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
      let pH := { p with handlers := p.handlers.pop }
      have hpH : Process.WF s.module pH := by
        refine process_handlers_WF _ p _ hp hres ?_
        have hp' := runnable_WF_parts hp (Or.inl hstat) hres
        intro i hi
        have hi0 : i < p.handlers.size := by
          simp [Array.size_pop] at hi; omega
        have hget : p.handlers.pop[i]'hi = p.handlers[i]'hi0 := Array.getElem_pop hi
        have ⟨hd0, hdle, hip0, hexc0⟩ := hp'.2.2 i hi0
        simpa [hget] using And.intro hd0 (And.intro hdle (And.intro hip0 hexc0))
      let frame2 := { frame with ip := frame.ip + 1 }
      have hfwf2 : Frame.WF s.module frame2 := bumpIp_frame _ _ hfwf hip
      exact apply_top_frame_preserves s pH frame2 hs hpH
        (by simpa [pH] using hres) (by simpa [pH] using hstat)
        (by simpa [pH] using htop) hfwf2
        (by simp [frame2, pH, hframe]) (by simp [frame2, pH, hframe])
  | raise reg =>
    simp [stepInstr] at h
    exact raiseValue_preserves s p frame (getReg! frame reg) hs hp hres hstat htop h
  | link pidReg =>
    simp [stepInstr] at h
    split at h
    · rename_i other hpid
      have hnt : Instr.isTerminal (.link pidReg) = false := rfl
      have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
      let frame2 := { frame with ip := frame.ip + 1 }
      have hfwf2 : Frame.WF s.module frame2 := bumpIp_frame _ _ hfwf hip
      have hs1 : State.WF (s.setCurrentProcess (State.setCurrentFrame p frame2)) :=
        apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
          (by simp [frame2, hframe]) (by simp [frame2, hframe])
      exact linkWith_preserves _ other hs1 h
    · exact nomatch h
  | getTupleElem dest tupleReg index =>
    simp [stepInstr] at h
    split at h
    · split at h
      · split at h
        · exact nomatch h
        · cases h
          rename_i elems htu hge
          have hnt : Instr.isTerminal (.getTupleElem dest tupleReg index) = false := rfl
          have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
          let frame1 := setReg! frame dest elems[index]!
          let frame2 := { frame1 with ip := frame1.ip + 1 }
          have hfwf2 : Frame.WF s.module frame2 :=
            bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
          exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
            (by simp [frame2, frame1, setReg!, hframe]) (by simp [frame2, frame1, setReg!, hframe])
      · exact nomatch h
    · exact nomatch h
  | getListElem dest listReg index =>
    simp [stepInstr] at h
    split at h
    · split at h
      · split at h
        · exact nomatch h
        · cases h
          rename_i elems hls hge
          have hnt : Instr.isTerminal (.getListElem dest listReg index) = false := rfl
          have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
          let frame1 := setReg! frame dest elems[index]!
          let frame2 := { frame1 with ip := frame1.ip + 1 }
          have hfwf2 : Frame.WF s.module frame2 :=
            bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
          exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
            (by simp [frame2, frame1, setReg!, hframe]) (by simp [frame2, frame1, setReg!, hframe])
      · exact nomatch h
    · exact nomatch h
  | getListRest dest listReg index =>
    simp [stepInstr] at h
    split at h
    · split at h
      · split at h
        · exact nomatch h
        · cases h
          rename_i elems hls hge
          have hnt : Instr.isTerminal (.getListRest dest listReg index) = false := rfl
          have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
          exact getListRest_preserves s p frame dest elems index hs hp hfwf hres hstat htop
            hframe hip
      · exact nomatch h
    · exact nomatch h
  | call dest funName argRegs =>
    simp [stepInstr] at h
    have hip :=
      ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode rfl
    by_cases hmp : funName = "map_put/3"
    · simp [hmp] at h
      by_cases har : (readArgs! frame argRegs).size = 3
      · simp [har] at h
        exact mapPut_preserves _ _ _ _ _ _ _
          hs hp hfwf hres hstat htop hframe hip h
      · simp [har] at h
    · simp [hmp] at h
      by_cases hc : funName = "cons/2"
      · simp [hc] at h
        by_cases har : (readArgs! frame argRegs).size = 2
        · simp [har] at h
          exact cons_preserves _ _ _ _ _ _
            hs hp hfwf hres hstat htop hframe hip h
        · simp [har] at h
      · simp [hc] at h
        by_cases hmref : funName = "make_ref/0"
        · simp [hmref] at h
          split at h
          · cases h
            let frame1 := setReg! frame dest (.reference s.nextRef)
            let frame2 := { frame1 with ip := frame1.ip + 1 }
            have hfwf2 : Frame.WF s.module frame2 :=
              bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
            have hs1 : State.WF (s.setCurrentProcess (State.setCurrentFrame p frame2)) :=
              apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
                (by simp [frame2, frame1, setReg!, hframe])
                (by simp [frame2, frame1, setReg!, hframe])
            exact nextRef_preserves _ (s.nextRef + 1) hs1
          · exact nomatch h
        · simp [hmref] at h
          by_cases htu : isMakeTupleName funName = true
          · simp [htu] at h; cases h
            exact makeTuple_preserves _ _ _ _ _
              hs hp hfwf hres hstat htop hframe hip
          · simp [htu] at h
            by_cases hbi : isBuiltinName funName = true
            · simp [hbi] at h
              cases hb : builtin p.heap p.pid funName (readArgs! frame argRegs) with
              | error _ => simp [hb] at h; cases h
              | ok v =>
                simp [hb] at h; cases h
                exact apply_top_frame_preserves s p
                  { setReg! frame dest v with ip := (setReg! frame dest v).ip + 1 }
                  hs hp hres hstat htop
                  (bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [setReg!] using hip))
                  (by simp [setReg!, hframe]) (by simp [setReg!, hframe])
            · simp [hbi] at h
              have hresv : FunName.resolvable s.module funName := by
                simpa [Function.instrOk, hcode] using hio.2.2
              have hfndSome : (s.module.findFunction funName).isSome := by
                cases hresv with
                | inl hb => exact absurd hb hbi
                | inr hs => exact hs
              cases hff : s.module.findFunction funName with
              | none =>
                simp [hff, Option.isSome] at hfndSome
              | some callee =>
                simp [hff] at h
                by_cases har : callee.arity = (readArgs! frame argRegs).size
                · simp [har] at h
                  cases h
                  have hcallee : Function.WF s.module callee :=
                    Module.findFunction_WF hs.1 hff
                  let caller : Frame :=
                    { frame with ip := frame.ip + 1 }
                  have hcaller : Frame.WF s.module caller := bumpIp_frame _ _ hfwf hip
                  have hs1 : State.WF (s.setCurrentProcess (State.setCurrentFrame p caller)) :=
                    apply_top_frame_preserves s p caller hs hp hres hstat htop hcaller
                      (by simp [caller, hframe]) (by simp [caller, hframe])
                  let p1 := State.setCurrentFrame p caller
                  have hp1 : Process.WF s.module p1 :=
                    setCurrentFrame_sameMeta_WF _ _ _ hres hstat htop hp hcaller
                      (by simp [caller, hframe]) (by simp [caller, hframe])
                  have hres1 : p1.result = none := by
                    dsimp [p1, State.setCurrentFrame]; simp [htop, hres]
                  have hstat1 : p1.status = .runnable := by
                    dsimp [p1, State.setCurrentFrame]; simp [htop, hstat]
                  have hsz1 : 0 < p1.stack.size := by
                    simpa [p1, setCurrentFrame_stack_size p caller htop] using htop
                  let args := readArgs! frame argRegs
                  let newFrame : Frame := {
                    function := callee
                    regs := State.mkRegs callee.locals args
                    ip := 0
                    retDest := dest
                  }
                  have hnew : Frame.WF s.module newFrame := by
                    refine ⟨hcallee, ?_, ?_, ?_⟩
                    · simp [newFrame, mkRegs_size]
                    · exact hcallee.2.1
                    · have hname := findFunction_name hff
                      simpa [newFrame, hname] using Option.isSome_of_eq_some hff
                  have hdest : dest < frame.function.locals := by
                    have hr : Instr.regsOk frame.function.locals
                        (Instr.call dest funName argRegs) = true := by
                      simpa [Function.instrOk] using hio.1
                    simp [Instr.regsOk] at hr
                    exact hr.1
                  have hret : newFrame.retDest < (p1.stack[p1.stack.size - 1]!).function.locals := by
                    have htop1 : p1.stack[p1.stack.size - 1]! = caller := by
                      dsimp [p1, State.setCurrentFrame]
                      simp only [htop, ↓reduceDIte]
                      have hszs : (p.stack.set (p.stack.size - 1) caller).size = p.stack.size :=
                        Array.size_set _
                      have hlt : p.stack.size - 1 < (p.stack.set (p.stack.size - 1) caller).size := by
                        simpa [hszs] using Nat.sub_one_lt_of_lt htop
                      rw [hszs, getElem!_pos (p.stack.set (p.stack.size - 1) caller)
                        (p.stack.size - 1) hlt, Array.getElem_set_self]
                    simpa [newFrame, htop1, caller, hframe] using hdest
                  have hp2 : Process.WF s.module { p1 with stack := p1.stack.push newFrame } :=
                    push_frame_process_WF s.module p1 newFrame hres1 hstat1 hsz1 hp1 hnew hret
                  exact setCurrentProcess_WF s _ hs hp2
                · simp [har] at h
                  cases h
  | return_ reg =>
    simp [stepInstr] at h
    by_cases hsz : p.stack.size = 1
    · simp [hsz] at h
      let pEx :=
        { p with
          stack := #[]
          result := some (getReg! frame reg)
          status := .exited
          handlers := #[] }
      have hs2 : State.WF
          (State.propagateExit (s.setCurrentProcess pEx) (s.setCurrentProcess pEx).current
            (getReg! frame reg)) :=
        propagateExit_preserves _ _ _
          (setCurrentProcess_WF s pEx hs (exited_process_WF _ p _ hp.1))
      split at h
      · cases h; exact result_update_preserves _ _ hs2
      · exact scheduleNext_preserves _ _ hs2 h
    · simp [hsz] at h
      split at h
      · exact nomatch h
      · cases h
        rename_i hhand
        have hsz1 : 1 < p.stack.size := by omega
        let stack := p.stack.pop
        let v := getReg! frame reg
        let caller0 := stack[stack.size - 1]!
        let caller := setReg! caller0 frame.retDest v
        have hcaller0 : Frame.WF s.module caller0 := by
          have hp' := runnable_WF_parts hp (Or.inl hstat) hres
          have hpoppos : 0 < stack.size := by simp [stack, Array.size_pop]; omega
          have hi : stack.size - 1 < stack.size := Nat.sub_one_lt_of_lt hpoppos
          have hi0 : stack.size - 1 < p.stack.size := by
            simp [stack, Array.size_pop] at hi ⊢; omega
          have hget : stack[stack.size - 1]'hi = p.stack[stack.size - 1]'hi0 :=
            Array.getElem_pop hi
          have hf := hp'.2.1.1 (stack.size - 1) hi0
          simpa [caller0, getElem!_pos stack (stack.size - 1) hi, hget] using hf
        have hcaller : Frame.WF s.module caller := setReg!_WF _ _ _ _ hcaller0
        have hhandLe : ∀ i, (hi : i < p.handlers.size) →
            (p.handlers[i]'hi).stackDepth ≤ p.stack.pop.size := by
          intro i hi
          have : ¬(p.stack.size - 1 < (p.handlers[i]'hi).stackDepth) := by
            intro hlt; exact hhand ⟨i, hi, hlt⟩
          simpa [Array.size_pop] using Nat.le_of_not_gt this
        have hsameFun :
            caller.function = (p.stack.pop[p.stack.pop.size - 1]!).function := by
          simp [caller, setReg!, caller0, stack]
        have hsameRet :
            caller.retDest = (p.stack.pop[p.stack.pop.size - 1]!).retDest := by
          simp [caller, setReg!, caller0, stack]
        have hpPop :=
          pop_set_top_process_WF s.module p caller hres hstat hsz1 hp hcaller
            hsameFun hsameRet hhandLe
        have heq :
            { p with
                stack :=
                  p.stack.pop.setIfInBounds (p.stack.size - 1 - 1)
                    (setReg! p.stack.pop[p.stack.size - 1 - 1]! frame.retDest
                      (getReg! frame reg)) } =
              { p with stack := p.stack.pop.setIfInBounds (p.stack.pop.size - 1) caller } := by
          simp [caller, caller0, stack, setReg!, Array.size_pop, v]
        rw [heq]
        exact setCurrentProcess_WF s _ hs hpPop
  | halt reg =>
    simp [stepInstr] at h
    let pEx :=
      { p with
        stack := #[]
        result := some (getReg! frame reg)
        status := .exited
        handlers := #[] }
    have hs2 : State.WF
        (State.propagateExit (s.setCurrentProcess pEx) (s.setCurrentProcess pEx).current
          (getReg! frame reg)) :=
      propagateExit_preserves _ _ _
        (setCurrentProcess_WF s pEx hs (exited_process_WF _ p _ hp.1))
    split at h
    · cases h; exact result_update_preserves _ _ hs2
    · exact scheduleNext_preserves _ _ hs2 h
  | spawn dest funName argRegs =>
    simp [stepInstr] at h
    split at h
    · split at h
      · cases h
        rename_i callee hfnd harity
        have hnt : Instr.isTerminal (.spawn dest funName argRegs) = false := rfl
        have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
        have hcallee : Function.WF s.module callee := Module.findFunction_WF hs.1 hfnd
        let args := readArgs! frame argRegs
        let child0 : Process := {
          pid := s.nextPid
          stack := #[]
          mailbox := #[]
          status := .runnable
          result := none
          heap := Heap.empty
          handlers := #[]
        }
        let childCopied := child0.copyArrayFrom p.heap args
        have hheapC : Heap.WF childCopied.1.heap :=
          Process.copyArrayFrom_heap_WF child0 p.heap args Heap.empty_default_WF
        let newFrame : Frame := {
          function := callee
          regs := State.mkRegs callee.locals childCopied.2
          ip := 0
          retDest := 0
        }
        have hnew : Frame.WF s.module newFrame := by
          refine ⟨hcallee, ?_, ?_, ?_⟩
          · simp [newFrame, mkRegs_size]
          · exact hcallee.2.1
          · have hname := findFunction_name hfnd
            simpa [newFrame, hname] using Option.isSome_of_eq_some hfnd
        let child : Process := { childCopied.1 with stack := #[newFrame] }
        have hcopy_meta :
            ∀ (q : Process) (i : Nat) (acc : Array Value),
              (Process.copyArrayFrom.go q p.heap args i acc).1.status = q.status ∧
              (Process.copyArrayFrom.go q p.heap args i acc).1.result = q.result ∧
              (Process.copyArrayFrom.go q p.heap args i acc).1.stack = q.stack := by
          intro q i acc
          induction hdiff : args.size - i generalizing q i acc with
          | zero =>
            unfold Process.copyArrayFrom.go
            have hge : args.size ≤ i := Nat.le_of_sub_eq_zero hdiff
            simp [Nat.not_lt.mpr hge]
          | succ d ih =>
            unfold Process.copyArrayFrom.go
            split
            · rename_i hlt
              have hdi : args.size - (i + 1) = d := by omega
              have hcf :
                  (Process.copyFrom q p.heap (args[i]'hlt)).1.status = q.status ∧
                  (Process.copyFrom q p.heap (args[i]'hlt)).1.result = q.result ∧
                  (Process.copyFrom q p.heap (args[i]'hlt)).1.stack = q.stack := by
                simp [Process.copyFrom]
              have hrest :=
                ih (Process.copyFrom q p.heap (args[i]'hlt)).1 (i + 1)
                  (acc.push (Process.copyFrom q p.heap (args[i]'hlt)).2) hdi
              exact ⟨hrest.1.trans hcf.1, hrest.2.1.trans hcf.2.1, hrest.2.2.trans hcf.2.2⟩
            · exact ⟨rfl, rfl, rfl⟩
        have hchild : Process.WF s.module child := by
          have hst : childCopied.1.status = .runnable := by
            change (Process.copyArrayFrom.go child0 p.heap args 0
              (Array.mkEmpty args.size)).1.status = .runnable
            exact (hcopy_meta child0 0 (Array.mkEmpty args.size)).1
          have hresC : childCopied.1.result = none := by
            change (Process.copyArrayFrom.go child0 p.heap args 0
              (Array.mkEmpty args.size)).1.result = none
            exact (hcopy_meta child0 0 (Array.mkEmpty args.size)).2.1
          refine And.intro hheapC ?_
          change
            match child.result with
            | some _ => _
            | none => _
          have hresChild : child.result = none := by simpa [child] using hresC
          have hstChild : child.status = .runnable := by simpa [child] using hst
          simp only [hresChild, hstChild]
          refine And.intro (by simp [child]) ?_
          refine And.intro ?_ ?_
          · -- stackWF
            refine And.intro ?_ ?_
            · intro i hi
              have hi0 : i < 1 := by simpa [child] using hi
              have : i = 0 := Nat.lt_one_iff.mp hi0
              subst this
              simpa [child] using hnew
            · intro i hi hi0
              have : i < 1 := by simpa [child] using hi
              omega
          · -- handlersWF (spawned child has empty handlers)
            have hhandlers : child.handlers = #[] := by
              have hpres : ∀ (q : Process) (i : Nat) (acc : Array Value),
                  (Process.copyArrayFrom.go q p.heap args i acc).1.handlers = q.handlers := by
                intro q i acc
                induction hdiff : args.size - i generalizing q i acc with
                | zero =>
                  unfold Process.copyArrayFrom.go
                  have hge : args.size ≤ i := Nat.le_of_sub_eq_zero hdiff
                  simp [Nat.not_lt.mpr hge]
                | succ d ih =>
                  unfold Process.copyArrayFrom.go
                  split
                  · rename_i hlt
                    have hdi : args.size - (i + 1) = d := by omega
                    have hcf : (Process.copyFrom q p.heap (args[i]'hlt)).1.handlers =
                        q.handlers := by simp [Process.copyFrom]
                    have hrest :=
                      ih (Process.copyFrom q p.heap (args[i]'hlt)).1 (i + 1)
                        (acc.push (Process.copyFrom q p.heap (args[i]'hlt)).2) hdi
                    exact hrest.trans hcf
                  · rfl
              have hgo : childCopied.1.handlers = child0.handlers := by
                change (Process.copyArrayFrom.go child0 p.heap args 0
                  (Array.mkEmpty args.size)).1.handlers = child0.handlers
                exact hpres child0 0 (Array.mkEmpty args.size)
              simpa [child, child0] using hgo
            intro i hi
            simp [hhandlers] at hi
        let frame1 := setReg! frame dest (.pid s.nextPid)
        let frame2 := { frame1 with ip := frame1.ip + 1 }
        have hfwf2 : Frame.WF s.module frame2 :=
          bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
        let s1 := s.setCurrentProcess (State.setCurrentFrame p frame2)
        have hs1 : State.WF s1 :=
          apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
            (by simp [frame2, frame1, setReg!, hframe]) (by simp [frame2, frame1, setReg!, hframe])
        have hmod : s1.module = s.module := by
          dsimp [s1, State.setCurrentProcess, State.setCurrentFrame]
          split <;> simp
        have hchild1 : Process.WF s1.module child := by simpa [hmod] using hchild
        have hsPush := push_process_WF s1 child hs1 hchild1
        -- `stepInstr` also bumps `nextPid`; State.WF ignores that field.
        change State.WF
          { s1 with processes := s1.processes.push child, nextPid := s1.nextPid + 1 }
        exact hsPush
      · exact nomatch h
    · exact nomatch h
  | send pidReg msgReg =>
    simp [stepInstr] at h
    split at h
    · rename_i pid hpid
      split at h
      · cases h
        rename_i idx hfnd
        have hnt : Instr.isTerminal (.send pidReg msgReg) = false := rfl
        have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
        let frame2 := { frame with ip := frame.ip + 1 }
        have hfwf2 : Frame.WF s.module frame2 := bumpIp_frame _ _ hfwf hip
        let s1 := s.setCurrentProcess (State.setCurrentFrame p frame2)
        have hs1 : State.WF s1 :=
          apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
            (by simp [frame2, hframe]) (by simp [frame2, hframe])
        have hidx0 := findProcessIdx_lt hfnd
        have hidx : idx < s1.processes.size := by
          simpa [s1, State.setCurrentProcess, hs.2.2.1, Array.size_set] using hidx0
        let target0 := s1.processes[idx]!
        have htarget0 : Process.WF s1.module target0 := by
          have := hs1.2.2.2 idx hidx
          simpa [target0, getElem!_pos s1.processes idx hidx] using this
        have hsrcHeap :
            (State.setCurrentFrame p frame2).heap = p.heap := by
          dsimp [State.setCurrentFrame]; simp [htop]
        let msg := getReg! frame msgReg
        let copied := target0.copyFrom (State.setCurrentFrame p frame2).heap msg
        have htargetC : Process.WF s1.module copied.1 := by
          have h := Process.copyFrom_preserves_WF s1.module target0 p.heap msg htarget0
          rw [show copied = target0.copyFrom p.heap msg by simp [copied, hsrcHeap]]
          exact h
        have htarget1 : Process.WF s1.module
            (let p1 := { copied.1 with mailbox := copied.1.mailbox.push copied.2 }
              if copied.1.status == .waiting then State.wakeOnMessage p1 else p1) :=
          process_wake_mailbox_WF s1.module copied.1 copied.2 htargetC
        exact setProcess_WF s1 idx _ hs1 hidx htarget1
      · exact nomatch h
    · exact nomatch h
  | recv dest =>
    simp [stepInstr] at h
    split at h
    · cases h
      rename_i hmb
      have hnt : Instr.isTerminal (.recv dest) = false := rfl
      have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
      let pMb := { p with mailbox := p.mailbox.eraseIdx! 0 }
      have hpMb : Process.WF s.module pMb := process_mailbox_WF _ p _ hp
      let frame1 := setReg! frame dest p.mailbox[0]!
      let frame2 := { frame1 with ip := frame1.ip + 1 }
      have hfwf2 : Frame.WF s.module frame2 :=
        bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
      exact apply_top_frame_preserves s pMb frame2 hs hpMb hres hstat htop hfwf2
        (by simp [frame2, frame1, setReg!, pMb, hframe])
        (by simp [frame2, frame1, setReg!, pMb, hframe])
    · rename_i hmb
      have hpW0 := process_waiting_WF _ p hp hres hstat
      have hpW := clearWait_WF _ _ hpW0
      have hsW := setCurrentProcess_WF s _ hs hpW
      exact scheduleNext_preserves _ _ hsW h
  | recvPeek dest indexReg empty =>
    simp [stepInstr] at h
    split at h
    · rename_i i hi
      split at h
      · exact nomatch h
      · rename_i hge
        split at h
        · cases h
          rename_i hlt
          have hnt : Instr.isTerminal (.recvPeek dest indexReg empty) = false := rfl
          have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
          let frame1 := setReg! frame dest p.mailbox[i.toNat]!
          let frame2 := { frame1 with ip := frame1.ip + 1 }
          have hfwf2 : Frame.WF s.module frame2 :=
            bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
          exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
            (by simp [frame2, frame1, setReg!, hframe])
            (by simp [frame2, frame1, setReg!, hframe])
        · cases h
          have hempty : empty < frame.function.code.size := by
            simpa [Function.instrOk, Instr.jumpTargetOk, hcode] using hio.2.1
          let frame2 := { frame with ip := empty }
          have hfwf2 : Frame.WF s.module frame2 := setIp_frame _ _ _ hfwf hempty
          exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
            (by simp [frame2, hframe]) (by simp [frame2, hframe])
    · exact nomatch h
  | recvDrop indexReg =>
    simp [stepInstr] at h
    split at h
    · rename_i i hi
      split at h
      · exact nomatch h
      · rename_i hge
        split at h
        · exact nomatch h
        · cases h
          rename_i hlt
          have hnt : Instr.isTerminal (.recvDrop indexReg) = false := rfl
          have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
          let pMb := { p with mailbox := p.mailbox.eraseIdx! i.toNat }
          have hpMb : Process.WF s.module pMb := process_mailbox_WF _ p _ hp
          let frame2 := { frame with ip := frame.ip + 1 }
          have hfwf2 : Frame.WF s.module frame2 := bumpIp_frame _ _ hfwf hip
          exact apply_top_frame_preserves s pMb frame2 hs hpMb hres hstat htop hfwf2
            (by simp [frame2, pMb, hframe]) (by simp [frame2, pMb, hframe])
    · exact nomatch h
  | wait retry after timeout =>
    simp [stepInstr] at h
    have hretry : retry < frame.function.code.size := by
      have := hio.2.1
      simp [Instr.jumpTargetOk] at this
      exact this.1
    have hafter : after < frame.function.code.size := by
      have := hio.2.1
      simp [Instr.jumpTargetOk] at this
      exact this.2
    by_cases hmb : 0 < p.mailbox.size
    · simp [hmb] at h; cases h
      let frame2 := { frame with ip := retry }
      have hfwf2 : Frame.WF s.module frame2 := setIp_frame _ _ _ hfwf hretry
      have hpC := clearWait_WF _ p hp
      exact apply_top_frame_preserves s (State.clearWait p) frame2 hs hpC
        (by simpa [State.clearWait] using hres)
        (by simpa [State.clearWait] using hstat)
        (by simpa [State.clearWait] using htop) hfwf2
        (by simp [frame2, State.clearWait, hframe])
        (by simp [frame2, State.clearWait, hframe])
    · simp [hmb] at h
      cases hd : p.waitDeadline with
      | some d =>
        simp [hd] at h
        by_cases hle : d ≤ s.clock
        · simp [hle] at h; cases h
          let frame2 := { frame with ip := after }
          have hfwf2 : Frame.WF s.module frame2 := setIp_frame _ _ _ hfwf hafter
          have hpC := clearWait_WF _ p hp
          exact apply_top_frame_preserves s (State.clearWait p) frame2 hs hpC
            (by simpa [State.clearWait] using hres)
            (by simpa [State.clearWait] using hstat)
            (by simpa [State.clearWait] using htop) hfwf2
            (by simp [frame2, State.clearWait, hframe])
            (by simp [frame2, State.clearWait, hframe])
        · simp [hle] at h
          let pW := { p with status := .waiting }
          have hpW : Process.WF s.module pW := process_waiting_WF _ p hp hres hstat
          have hsW : State.WF (s.setCurrentProcess pW) := setCurrentProcess_WF s pW hs hpW
          exact scheduleNext_preserves _ _ hsW (by simpa [pW, hd] using h)
      | none =>
        simp [hd] at h
        cases hto : timeout with
        | some n =>
          cases n with
          | zero =>
            simp [hto] at h; cases h
            let frame2 := { frame with ip := after }
            have hfwf2 : Frame.WF s.module frame2 := setIp_frame _ _ _ hfwf hafter
            exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
              (by simp [frame2, hframe]) (by simp [frame2, hframe])
          | succ n =>
            simp [hto] at h
            let pW :=
              { p with status := .waiting, waitDeadline := some (s.clock + (n + 1)) }
            have hpW0 := process_waiting_WF _ p hp hres hstat
            have hpW : Process.WF s.module pW :=
              process_set_waitDeadline_WF _ _ (some (s.clock + (n + 1))) hpW0
            have hsW := setCurrentProcess_WF s pW hs hpW
            exact scheduleNext_preserves _ _ hsW (by simpa [pW] using h)
        | none =>
          simp [hto] at h
          let pW := State.clearWait { p with status := .waiting }
          have hpW0 := process_waiting_WF _ p hp hres hstat
          have hpW : Process.WF s.module pW := clearWait_WF _ _ hpW0
          have hsW := setCurrentProcess_WF s pW hs hpW
          exact scheduleNext_preserves _ _ hsW (by simpa [pW, State.clearWait] using h)


  | monitor dest pidReg =>
    simp [stepInstr] at h
    split at h
    · rename_i other hpid
      have hnt : Instr.isTerminal (.monitor dest pidReg) = false := rfl
      have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
      let frame1 := setReg! frame dest (.reference s.nextRef)
      let frame2 := { frame1 with ip := frame1.ip + 1 }
      have hfwf2 : Frame.WF s.module frame2 :=
        bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
      have hs1 : State.WF (s.setCurrentProcess (State.setCurrentFrame p frame2)) :=
        apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
          (by simp [frame2, frame1, setReg!, hframe])
          (by simp [frame2, frame1, setReg!, hframe])
      have hs2 : State.WF
          { s.setCurrentProcess (State.setCurrentFrame p frame2) with
            nextRef := s.nextRef + 1 } :=
        nextRef_preserves _ (s.nextRef + 1) hs1
      exact monitorWith_preserves _ other s.nextRef hs2 h
    · exact nomatch h
  | demonitor refReg =>
    simp [stepInstr] at h
    split at h
    · rename_i refId href
      have hnt : Instr.isTerminal (.demonitor refReg) = false := rfl
      have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
      let frame2 := { frame with ip := frame.ip + 1 }
      have hfwf2 : Frame.WF s.module frame2 := bumpIp_frame _ _ hfwf hip
      have hs1 : State.WF (s.setCurrentProcess (State.setCurrentFrame p frame2)) :=
        apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
          (by simp [frame2, hframe]) (by simp [frame2, hframe])
      exact demonitorWith_preserves _ refId hs1 h
    · exact nomatch h
  | makeFun dest funName capRegs =>
    simp [stepInstr] at h; cases h
    have hnt : Instr.isTerminal (.makeFun dest funName capRegs) = false := rfl
    have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
    exact makeFun_preserves _ _ _ _ _ _
      hs hp hfwf hres hstat htop hframe hip
  | apply dest funReg argRegs =>
    simp [stepInstr] at h
    cases hreg : getReg! frame funReg with
    | ref r =>
      simp [hreg] at h
      cases hnode : p.heap.get? r with
      | none =>
        simp [hnode] at h; try cases h
      | some node =>
        cases node with
        | closure funName env =>
          simp [hnode] at h
          cases hff : s.module.findFunction funName with
          | none =>
            simp [hff] at h; try cases h
          | some callee =>
            simp [hff] at h
            split at h
            · cases h
              have hip :=
                ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode rfl
              have hcallee : Function.WF s.module callee :=
                Module.findFunction_WF hs.1 hff
              let caller : Frame := { frame with ip := frame.ip + 1 }
              have hcaller : Frame.WF s.module caller := bumpIp_frame _ _ hfwf hip
              let p1 := State.setCurrentFrame p caller
              have hp1 : Process.WF s.module p1 :=
                setCurrentFrame_sameMeta_WF _ _ _ hres hstat htop hp hcaller
                  (by simp [caller, hframe]) (by simp [caller, hframe])
              have hres1 : p1.result = none := by
                dsimp [p1, State.setCurrentFrame]; simp [htop, hres]
              have hstat1 : p1.status = .runnable := by
                dsimp [p1, State.setCurrentFrame]; simp [htop, hstat]
              have hsz1 : 0 < p1.stack.size := by
                simpa [p1, setCurrentFrame_stack_size p caller htop] using htop
              let allArgs := env ++ readArgs! frame argRegs
              let newFrame : Frame := {
                function := callee
                regs := State.mkRegs callee.locals allArgs
                ip := 0
                retDest := dest
              }
              have hnew : Frame.WF s.module newFrame := by
                refine ⟨hcallee, ?_, ?_, ?_⟩
                · simp [newFrame, mkRegs_size]
                · exact hcallee.2.1
                · have hname := findFunction_name hff
                  simpa [newFrame, hname] using Option.isSome_of_eq_some hff
              have hdest : dest < frame.function.locals := by
                have hr : Instr.regsOk frame.function.locals
                    (Instr.apply dest funReg argRegs) = true := by
                  simpa [Function.instrOk] using hio.1
                simp [Instr.regsOk] at hr
                exact hr.1.1
              have hret : newFrame.retDest < (p1.stack[p1.stack.size - 1]!).function.locals := by
                have htop1 : p1.stack[p1.stack.size - 1]! = caller := by
                  dsimp [p1, State.setCurrentFrame]
                  simp only [htop, ↓reduceDIte]
                  have hszs : (p.stack.set (p.stack.size - 1) caller).size = p.stack.size :=
                    Array.size_set _
                  have hlt : p.stack.size - 1 < (p.stack.set (p.stack.size - 1) caller).size := by
                    simpa [hszs] using Nat.sub_one_lt_of_lt htop
                  rw [hszs, getElem!_pos (p.stack.set (p.stack.size - 1) caller)
                    (p.stack.size - 1) hlt, Array.getElem_set_self]
                simpa [newFrame, htop1, caller, hframe] using hdest
              have hp2 : Process.WF s.module { p1 with stack := p1.stack.push newFrame } :=
                push_frame_process_WF s.module p1 newFrame hres1 hstat1 hsz1 hp1 hnew hret
              exact setCurrentProcess_WF s _ hs hp2
            · cases h
        | tuple _ | list _ | map _ =>
          simp [hnode] at h; try cases h
    | nil | bool _ | int _ | float _ | atom _ | string _ | pid _ | reference _ =>
      simp [hreg] at h; try cases h
  | loadFile dest pathReg =>
    simp [stepInstr] at h
    cases hpath : getReg! frame pathReg with
    | string _ =>
      simp [hpath] at h
      exact raiseValue_preserves s p frame (.atom "enoent") hs hp hres hstat htop h
    | nil | bool _ | int _ | float _ | atom _ | pid _ | reference _ | ref _ =>
      simp [hpath] at h
      exact raiseValue_preserves s p frame (.atom "badarg") hs hp hres hstat htop h


end Step
end Autumn
