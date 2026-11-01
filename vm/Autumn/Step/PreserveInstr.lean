import Autumn.Step.Preserve

namespace Autumn
namespace Step

/-! # Per-opcode `stepInstr` preservation (public proof surface)

Thin `stepInstr_preserves` dispatcher. **External proofs** should call these
`*_preserves` / `*_step_preserves` lemmas (or `stepInstr_preserves` /
`step_preserves`) rather than unfolding `stepInstr`.

## Audit (Phase 26)

Every `Instr` constructor has a preserve case (mirrored by
`*_error_not_structural` in `ProgressInstr`):

`loadLit`, `move`, `call`, `return_`, `halt`, `jump`, `jumpIfEq`,
`getTupleElem`, `isTag`, `spawn`, `send`, `recv`, `getListElem`, `getListRest`,
`enterTry`, `leaveTry`, `raise`, `recvPeek`, `recvDrop`, `wait`, `link`,
`monitor`, `demonitor`, `makeFun`, `apply`, `loadFile`, `applyMfa`.

Call-specials via `call_preserves` → helpers in `Step.Preserve`: `map_put/3`,
`cons/2`, `Process.flag/2`, `Process.exit/2`, `Process.hibernate/0`, `ets_new/0`, `ets_new/2`,
`ets_insert/3`, `ets_lookup/2`, `ets_delete/2`, `ets_delete_object/2`,
`ets_match_object/2`, `ets_select/2`, `ets_heir/2`, `ets_first/1`, `ets_next/2`,
`ets_give_away/3`, `make_ref/0`; other MFAs use `builtin` +
`builtin_error_not_structural` / `floatBinop_ne_error`.

See `AGENTS.md` (“Public proof surface”).
-/

/-- `loadLit` case of `stepInstr_preserves`. -/
theorem loadLit_step_preserves {s p frame} (H : StepInstrHyp s p frame)
    (reg : Reg) (lit : Term) {s'}
    (hcode : frame.function.code[frame.ip]! = .loadLit reg lit)
    (h : stepInstr s p frame (.loadLit reg lit) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
  simp [stepInstr] at h; cases h
  have hnt : Instr.isTerminal (.loadLit reg lit) = false := rfl
  have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
  exact loadLit_preserves s p frame reg lit hs hp hfwf hres hstat htop hframe hip

/-- `move` case of `stepInstr_preserves`. -/
theorem move_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest src : Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .move dest src)
    (h : stepInstr s p frame (.move dest src) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
  simp [stepInstr] at h; cases h
  have hnt : Instr.isTerminal (.move dest src) = false := rfl
  have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
  let frame1 := setReg! frame dest (getReg! frame src)
  let frame2 := { frame1 with ip := frame1.ip + 1 }
  have hfwf2 : Frame.WF s.module frame2 :=
    bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
  exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
    (by simp [frame2, frame1, setReg!, hframe]) (by simp [frame2, frame1, setReg!, hframe])

/-- `call` case of `stepInstr_preserves`. -/
theorem call_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest : Reg) (funName : FunName) (argRegs : Array Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .call dest funName argRegs)
    (h : stepInstr s p frame (.call dest funName argRegs) = .ok s') :
    State.WF s' := by
  have hio := H.instrOk (.call dest funName argRegs) hcode
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
  simp [stepInstr] at h
  have hip :=
    ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode rfl
  by_cases hmp : funName = "map_put/3"
  · simp [hmp] at h
    by_cases har : (readArgs! frame argRegs).size = 3
    · simp only [har, ↓reduceIte, ite_false] at h
      cases hmpu : mapPut s p frame dest (readArgs! frame argRegs)[0]!
          (readArgs! frame argRegs)[1]! (readArgs! frame argRegs)[2]! with
      | some s1 =>
        simp [hmpu] at h; cases h
        exact mapPut_preserves s p frame dest
          (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
          (readArgs! frame argRegs)[2]!
          hs hp hfwf hres hstat htop hframe hip hmpu
      | none =>
        simp [hmpu] at h
        exact raiseValue_preserves _ _ _ _ hs hp hres hstat htop h
    · simp only [har, ↓reduceIte, ite_true] at h; cases h
  · simp [hmp] at h
    by_cases hc : funName = "cons/2"
    · simp [hc] at h
      by_cases har : (readArgs! frame argRegs).size = 2
      · simp only [har, ↓reduceIte, ite_false] at h
        cases hco : cons s p frame dest (readArgs! frame argRegs)[0]!
            (readArgs! frame argRegs)[1]! with
        | some s1 =>
          simp [hco] at h; cases h
          exact cons_preserves s p frame dest
            (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
            hs hp hfwf hres hstat htop hframe hip hco
        | none =>
          simp [hco] at h
          exact raiseValue_preserves _ _ _ _ hs hp hres hstat htop h
      · simp only [har, ↓reduceIte, ite_true] at h; cases h
    · simp [hc] at h
      by_cases hflag : funName = "Process.flag/2"
      · simp [hflag] at h
        by_cases har : (readArgs! frame argRegs).size = 2
        · simp only [har, ↓reduceIte, ite_false] at h
          exact processFlag_preserves s p frame dest
            (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
            hs hp hfwf hres hstat htop hframe hip h
        · simp only [har, ↓reduceIte, ite_true] at h; cases h
      · simp [hflag] at h
        by_cases hex : funName = "Process.exit/2"
        · simp [hex] at h
          by_cases har : (readArgs! frame argRegs).size = 2
          · simp only [har, ↓reduceIte, ite_false] at h
            exact processExit_preserves s p frame dest
              (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
              hs hp hfwf hres hstat htop hframe hip h
          · simp only [har, ↓reduceIte, ite_true] at h; cases h
        · simp [hex] at h
          by_cases hhib : funName = "Process.hibernate/0"
          · simp [hhib] at h
            split at h
            · exact processHibernate_preserves s p frame dest
                hs hp hfwf hres hstat htop hframe hip h
            · cases h
          · simp [hhib] at h
            by_cases hetsn : funName = "ets_new/0"
            · simp [hetsn] at h
              split at h
              · exact etsNew_preserves s p frame dest
                  hs hp hfwf hres hstat htop hframe hip h
              · cases h
            · simp [hetsn] at h
              by_cases hetsn2 : funName = "ets_new/2"
              · simp [hetsn2] at h
                by_cases har : (readArgs! frame argRegs).size = 2
                · simp only [har, ↓reduceIte, ite_false] at h
                  exact etsNew2_preserves s p frame dest
                    (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                    hs hp hfwf hres hstat htop hframe hip h
                · simp only [har, ↓reduceIte, ite_true] at h; cases h
              · simp [hetsn2] at h
                by_cases hetsi : funName = "ets_insert/3"
                · simp [hetsi] at h
                  by_cases har : (readArgs! frame argRegs).size = 3
                  · simp only [har, ↓reduceIte, ite_false] at h
                    exact etsInsert_preserves s p frame dest
                      (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                      (readArgs! frame argRegs)[2]!
                      hs hp hfwf hres hstat htop hframe hip h
                  · simp only [har, ↓reduceIte, ite_true] at h; cases h
                · simp [hetsi] at h
                  by_cases hetsl : funName = "ets_lookup/2"
                  · simp [hetsl] at h
                    by_cases har : (readArgs! frame argRegs).size = 2
                    · simp only [har, ↓reduceIte, ite_false] at h
                      exact etsLookup_preserves s p frame dest
                        (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                        hs hp hfwf hres hstat htop hframe hip h
                    · simp only [har, ↓reduceIte, ite_true] at h; cases h
                  · simp [hetsl] at h
                    by_cases hetsd : funName = "ets_delete/2"
                    · simp [hetsd] at h
                      by_cases har : (readArgs! frame argRegs).size = 2
                      · simp only [har, ↓reduceIte, ite_false] at h
                        exact etsDelete_preserves s p frame dest
                          (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                          hs hp hfwf hres hstat htop hframe hip h
                      · simp only [har, ↓reduceIte, ite_true] at h; cases h
                    · simp [hetsd] at h
                      by_cases hetsdo : funName = "ets_delete_object/2"
                      · simp [hetsdo] at h
                        by_cases har : (readArgs! frame argRegs).size = 2
                        · simp only [har, ↓reduceIte, ite_false] at h
                          exact etsDeleteObject_preserves s p frame dest
                            (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                            hs hp hfwf hres hstat htop hframe hip h
                        · simp only [har, ↓reduceIte, ite_true] at h; cases h
                      · simp [hetsdo] at h
                        by_cases hetsm : funName = "ets_match_object/2"
                        · simp [hetsm] at h
                          by_cases har : (readArgs! frame argRegs).size = 2
                          · simp only [har, ↓reduceIte, ite_false] at h
                            exact etsMatchObject_preserves s p frame dest
                              (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                              hs hp hfwf hres hstat htop hframe hip h
                          · simp only [har, ↓reduceIte, ite_true] at h; cases h
                        · simp [hetsm] at h
                          by_cases hetss : funName = "ets_select/2"
                          · simp [hetss] at h
                            by_cases har : (readArgs! frame argRegs).size = 2
                            · simp only [har, ↓reduceIte, ite_false] at h
                              exact etsSelect_preserves s p frame dest
                                (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                                hs hp hfwf hres hstat htop hframe hip h
                            · simp only [har, ↓reduceIte, ite_true] at h; cases h
                          · simp [hetss] at h
                            by_cases hetsh : funName = "ets_heir/2"
                            · simp [hetsh] at h
                              by_cases har : (readArgs! frame argRegs).size = 2
                              · simp only [har, ↓reduceIte, ite_false] at h
                                exact etsHeir_preserves s p frame dest
                                  (readArgs! frame argRegs)[0]! (readArgs! frame argRegs)[1]!
                                  hs hp hfwf hres hstat htop hframe hip h
                              · simp only [har, ↓reduceIte, ite_true] at h; cases h
                            · simp [hetsh] at h
                              by_cases hetsf : funName = "ets_first/1"
                              · simp [hetsf] at h
                                by_cases har : (readArgs! frame argRegs).size = 1
                                · simp only [har, ↓reduceIte, ite_false] at h
                                  exact etsFirst_preserves s p frame dest
                                    (readArgs! frame argRegs)[0]!
                                    hs hp hfwf hres hstat htop hframe hip h
                                · simp only [har, ↓reduceIte, ite_true] at h; cases h
                              · simp [hetsf] at h
                                by_cases hetsn : funName = "ets_next/2"
                                · simp [hetsn] at h
                                  by_cases har : (readArgs! frame argRegs).size = 2
                                  · simp only [har, ↓reduceIte, ite_false] at h
                                    exact etsNext_preserves s p frame dest
                                      (readArgs! frame argRegs)[0]!
                                      (readArgs! frame argRegs)[1]!
                                      hs hp hfwf hres hstat htop hframe hip h
                                  · simp only [har, ↓reduceIte, ite_true] at h; cases h
                                · simp [hetsn] at h
                                  by_cases hetsg : funName = "ets_give_away/3"
                                  · simp [hetsg] at h
                                    by_cases har : (readArgs! frame argRegs).size = 3
                                    · simp only [har, ↓reduceIte, ite_false] at h
                                      exact etsGiveAway_preserves s p frame dest
                                        (readArgs! frame argRegs)[0]!
                                        (readArgs! frame argRegs)[1]!
                                        (readArgs! frame argRegs)[2]!
                                        hs hp hfwf hres hstat htop hframe hip h
                                    · simp only [har, ↓reduceIte, ite_true] at h; cases h
                                  · simp [hetsg] at h
                                    by_cases hmref : funName = "make_ref/0"
                                    · simp [hmref] at h
                                      split at h
                                      · cases h
                                        let frame1 := setReg! frame dest (.reference s.nextRef)
                                        let frame2 := { frame1 with ip := frame1.ip + 1 }
                                        have hfwf2 : Frame.WF s.module frame2 :=
                                          bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf)
                                            (by simpa [frame1, setReg!] using hip)
                                        have hs1 : State.WF (s.setCurrentProcess (State.setCurrentFrame p frame2)) :=
                                          apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
                                            (by simp [frame2, frame1, setReg!, hframe])
                                            (by simp [frame2, frame1, setReg!, hframe])
                                        exact nextRef_preserves _ (s.nextRef + 1) hs1
                                      · exact nomatch h
                                    · simp [hmref] at h
                                      by_cases htu : isMakeTupleName funName = true
                                      · simp [htu] at h; cases h
                                        exact makeTuple_preserves s p frame dest (readArgs! frame argRegs)
                                          hs hp hfwf hres hstat htop hframe hip
                                      · simp [htu] at h
                                        by_cases hbi : isBuiltinName funName = true
                                        · simp [hbi] at h
                                          cases hb : builtin p.heap p.pid funName (readArgs! frame argRegs) with
                                          | error _ =>
                                            simp [hb] at h
                                          | badarg =>
                                            simp [hb] at h
                                            exact raiseValue_preserves _ _ _ _ hs hp hres hstat htop h
                                          | ok v =>
                                            simp [hb] at h; cases h
                                            exact apply_top_frame_preserves s p
                                              { setReg! frame dest v with ip := (setReg! frame dest v).ip + 1 }
                                              hs hp hres hstat htop
                                              (bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf)
                                                (by simpa [setReg!] using hip))
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
                                              have hcaller : Frame.WF s.module caller :=
                                                bumpIp_frame _ _ hfwf hip
                                              have hs1 : State.WF
                                                  (s.setCurrentProcess (State.setCurrentFrame p caller)) :=
                                                apply_top_frame_preserves s p caller
                                                  hs hp hres hstat htop hcaller
                                                  (by simp [caller, hframe]) (by simp [caller, hframe])
                                              let p1 := State.setCurrentFrame p caller
                                              have hp1 : Process.WF s.module p1 := by
                                                simpa [p1] using
                                                  setCurrentFrame_sameMeta_WF s.module p caller
                                                    hres hstat htop hp hcaller
                                                    (by simp [caller, hframe]) (by simp [caller, hframe])
                                              have hres1 : p1.result = none := by
                                                simp only [p1, State.setCurrentFrame, htop, ↓reduceDIte, hres]
                                              have hstat1 : p1.status = .runnable := by
                                                simp only [p1, State.setCurrentFrame, htop, ↓reduceDIte, hstat]
                                              have hsz1 : p1.stack.size > 0 := by
                                                simp only [p1, State.setCurrentFrame, htop, ↓reduceDIte]
                                                simpa using htop
                                              let newFrame : Frame := {
                                                function := callee
                                                regs := State.mkRegs callee.locals (readArgs! frame argRegs)
                                                ip := 0
                                                retDest := dest
                                              }
                                              have hnew : Frame.WF s.module newFrame := by
                                                refine ⟨hcallee, ?_, ?_, ?_⟩
                                                · simp [newFrame, mkRegs_size]
                                                · exact hcallee.2.1
                                                · have hname := Module.findFunction_name hff
                                                  simpa [newFrame, hname] using Option.isSome_of_eq_some hff
                                              have hdest : dest < frame.function.locals := by
                                                have hr : Instr.regsOk frame.function.locals
                                                    (Instr.call dest funName argRegs) = true := by
                                                  simpa [Function.instrOk] using hio.1
                                                simp [Instr.regsOk] at hr
                                                exact hr.1
                                              have hret : newFrame.retDest <
                                                  (p1.stack[p1.stack.size - 1]!).function.locals := by
                                                have htop1 : p1.stack[p1.stack.size - 1]! = caller := by
                                                  dsimp [p1, State.setCurrentFrame]
                                                  simp only [htop, ↓reduceDIte]
                                                  have hszs :
                                                      (p.stack.set (p.stack.size - 1) caller).size =
                                                        p.stack.size :=
                                                    Array.size_set _
                                                  have hlt : p.stack.size - 1 <
                                                      (p.stack.set (p.stack.size - 1) caller).size := by
                                                    simpa [hszs] using Nat.sub_one_lt_of_lt htop
                                                  rw [hszs,
                                                    getElem!_pos (p.stack.set (p.stack.size - 1) caller)
                                                      (p.stack.size - 1) hlt, Array.getElem_set_self]
                                                simpa [newFrame, htop1, caller, hframe] using hdest
                                              have hp2 : Process.WF s.module
                                                  { p1 with stack := p1.stack.push newFrame } :=
                                                push_frame_process_WF s.module p1 newFrame
                                                  hres1 hstat1 hsz1 hp1 hnew hret
                                              exact setCurrentProcess_WF s _ hs hp2
                                            · simp [har] at h
                                              cases h

/-- `return_` case of `stepInstr_preserves`. -/
theorem return_preserves {s p frame} (H : StepInstrHyp s p frame)
    (reg : Reg) {s'}
    (_hcode : frame.function.code[frame.ip]! = .return_ reg)
    (h : stepInstr s p frame (.return_ reg) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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
    exact scheduleNext_preserves _ _ hs2 h
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

/-- `halt` case of `stepInstr_preserves`. -/
theorem halt_preserves {s p frame} (H : StepInstrHyp s p frame)
    (reg : Reg) {s'}
    (_hcode : frame.function.code[frame.ip]! = .halt reg)
    (h : stepInstr s p frame (.halt reg) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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
  exact scheduleNext_preserves _ _ hs2 h

/-- `jump` case of `stepInstr_preserves`. -/
theorem jump_preserves {s p frame} (H : StepInstrHyp s p frame)
    (target : Label) {s'}
    (hcode : frame.function.code[frame.ip]! = .jump target)
    (h : stepInstr s p frame (.jump target) = .ok s') :
    State.WF s' := by
  have hio := H.instrOk (.jump target) hcode
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
  simp [stepInstr] at h; cases h
  have htgt : target < frame.function.code.size := by
    simpa [Function.instrOk, Instr.jumpTargetOk, hcode] using hio.2.1
  let frame2 := { frame with ip := target }
  have hfwf2 : Frame.WF s.module frame2 := setIp_frame _ _ _ hfwf htgt
  exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
    (by simp [frame2, hframe]) (by simp [frame2, hframe])

/-- `jumpIfEq` case of `stepInstr_preserves`. -/
theorem jumpIfEq_preserves {s p frame} (H : StepInstrHyp s p frame)
    (target : Label) (reg : Reg) (lit : Term) {s'}
    (hcode : frame.function.code[frame.ip]! = .jumpIfEq target reg lit)
    (h : stepInstr s p frame (.jumpIfEq target reg lit) = .ok s') :
    State.WF s' := by
  have hio := H.instrOk (.jumpIfEq target reg lit) hcode
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `getTupleElem` case of `stepInstr_preserves`. -/
theorem getTupleElem_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest tupleReg : Reg) (index : Nat) {s'}
    (hcode : frame.function.code[frame.ip]! = .getTupleElem dest tupleReg index)
    (h : stepInstr s p frame (.getTupleElem dest tupleReg index) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `isTag` case of `stepInstr_preserves`. -/
theorem isTag_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest reg : Reg) (tag : Tag) {s'}
    (hcode : frame.function.code[frame.ip]! = .isTag dest reg tag)
    (h : stepInstr s p frame (.isTag dest reg tag) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
  simp [stepInstr] at h; cases h
  have hnt : Instr.isTerminal (.isTag dest reg tag) = false := rfl
  have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
  let frame1 := setReg! frame dest (.bool (Value.tagMatches p.heap (getReg! frame reg) tag))
  let frame2 := { frame1 with ip := frame1.ip + 1 }
  have hfwf2 : Frame.WF s.module frame2 :=
    bumpIp_frame _ _ (setReg!_WF _ _ _ _ hfwf) (by simpa [frame1, setReg!] using hip)
  exact apply_top_frame_preserves s p frame2 hs hp hres hstat htop hfwf2
    (by simp [frame2, frame1, setReg!, hframe]) (by simp [frame2, frame1, setReg!, hframe])

/-- `spawn` case of `stepInstr_preserves`. -/
theorem spawn_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest : Reg) (funName : FunName) (argRegs : Array Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .spawn dest funName argRegs)
    (h : stepInstr s p frame (.spawn dest funName argRegs) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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
        · have hname := Module.findFunction_name hfnd
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

/-- `send` case of `stepInstr_preserves`. -/
theorem send_preserves {s p frame} (H : StepInstrHyp s p frame)
    (pidReg msgReg : Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .send pidReg msgReg)
    (h : stepInstr s p frame (.send pidReg msgReg) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `recv` case of `stepInstr_preserves`. -/
theorem recv_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest : Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .recv dest)
    (h : stepInstr s p frame (.recv dest) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `getListElem` case of `stepInstr_preserves`. -/
theorem getListElem_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest listReg : Reg) (index : Nat) {s'}
    (hcode : frame.function.code[frame.ip]! = .getListElem dest listReg index)
    (h : stepInstr s p frame (.getListElem dest listReg index) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `getListRest` case of `stepInstr_preserves`. -/
theorem getListRest_step_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest listReg : Reg) (index : Nat) {s'}
    (hcode : frame.function.code[frame.ip]! = .getListRest dest listReg index)
    (h : stepInstr s p frame (.getListRest dest listReg index) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `enterTry` case of `stepInstr_preserves`. -/
theorem enterTry_preserves {s p frame} (H : StepInstrHyp s p frame)
    (rescueIp : Label) (excReg : Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .enterTry rescueIp excReg)
    (h : stepInstr s p frame (.enterTry rescueIp excReg) = .ok s') :
    State.WF s' := by
  have hio := H.instrOk (.enterTry rescueIp excReg) hcode
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `leaveTry` case of `stepInstr_preserves`. -/
theorem leaveTry_preserves {s p frame} (H : StepInstrHyp s p frame)
    {s'}
    (hcode : frame.function.code[frame.ip]! = .leaveTry)
    (h : stepInstr s p frame (.leaveTry) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `raise` case of `stepInstr_preserves`. -/
theorem raise_preserves {s p frame} (H : StepInstrHyp s p frame)
    (reg : Reg) {s'}
    (_hcode : frame.function.code[frame.ip]! = .raise reg)
    (h : stepInstr s p frame (.raise reg) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
  simp [stepInstr] at h
  exact raiseValue_preserves s p frame (getReg! frame reg) hs hp hres hstat htop h

/-- `recvPeek` case of `stepInstr_preserves`. -/
theorem recvPeek_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest indexReg : Reg) (empty : Label) {s'}
    (hcode : frame.function.code[frame.ip]! = .recvPeek dest indexReg empty)
    (h : stepInstr s p frame (.recvPeek dest indexReg empty) = .ok s') :
    State.WF s' := by
  have hio := H.instrOk (.recvPeek dest indexReg empty) hcode
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `recvDrop` case of `stepInstr_preserves`. -/
theorem recvDrop_preserves {s p frame} (H : StepInstrHyp s p frame)
    (indexReg : Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .recvDrop indexReg)
    (h : stepInstr s p frame (.recvDrop indexReg) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `wait` case of `stepInstr_preserves`. -/
theorem wait_preserves {s p frame} (H : StepInstrHyp s p frame)
    (retry after : Label) (timeout : WaitTimeout) {s'}
    (hcode : frame.function.code[frame.ip]! = .wait retry after timeout)
    (h : stepInstr s p frame (.wait retry after timeout) = .ok s') :
    State.WF s' := by
  have hio := H.instrOk (.wait retry after timeout) hcode
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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
      cases hr : resolveWaitTimeout frame timeout with
      | error _ =>
        simp [hr, Bind.bind, Except.bind] at h
      | ok ticks? =>
        simp [hr, Bind.bind, Except.bind] at h
        cases hto : ticks? with
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

/-- `link` case of `stepInstr_preserves`. -/
theorem link_preserves {s p frame} (H : StepInstrHyp s p frame)
    (pidReg : Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .link pidReg)
    (h : stepInstr s p frame (.link pidReg) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `monitor` case of `stepInstr_preserves`. -/
theorem monitor_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest pidReg : Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .monitor dest pidReg)
    (h : stepInstr s p frame (.monitor dest pidReg) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `demonitor` case of `stepInstr_preserves`. -/
theorem demonitor_preserves {s p frame} (H : StepInstrHyp s p frame)
    (refReg : Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .demonitor refReg)
    (h : stepInstr s p frame (.demonitor refReg) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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

/-- `makeFun` case of `stepInstr_preserves`. -/
theorem makeFun_step_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest : Reg) (funName : FunName) (capRegs : Array Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .makeFun dest funName capRegs)
    (h : stepInstr s p frame (.makeFun dest funName capRegs) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
  simp [stepInstr] at h; cases h
  have hnt : Instr.isTerminal (.makeFun dest funName capRegs) = false := rfl
  have hip := ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode hnt
  exact makeFun_preserves _ _ _ _ _ _
    hs hp hfwf hres hstat htop hframe hip

/-- `apply` case of `stepInstr_preserves`. -/
theorem apply_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest funReg : Reg) (argRegs : Array Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .apply dest funReg argRegs)
    (h : stepInstr s p frame (.apply dest funReg argRegs) = .ok s') :
    State.WF s' := by
  have hio := H.instrOk (.apply dest funReg argRegs) hcode
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
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
              · have hname := Module.findFunction_name hff
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
  | nil | bool _ | int _ | float _ | atom _ | string _ | bitstring _ | pid _ | reference _ =>
    simp [hreg] at h; try cases h

/-- `loadFile` case of `stepInstr_preserves`. -/
theorem loadFile_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest pathReg : Reg) {s'}
    (_hcode : frame.function.code[frame.ip]! = .loadFile dest pathReg)
    (h : stepInstr s p frame (.loadFile dest pathReg) = .ok s') :
    State.WF s' := by
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
  simp [stepInstr] at h
  cases hpath : getReg! frame pathReg with
  | string _ =>
    simp [hpath] at h
    exact raiseValue_preserves s p frame (.atom "enoent") hs hp hres hstat htop h
  | nil | bool _ | int _ | float _ | atom _ | bitstring _ | pid _ | reference _ | ref _ =>
    simp [hpath] at h
    exact raiseValue_preserves s p frame (.atom "badarg") hs hp hres hstat htop h

/-- `applyMfa` case of `stepInstr_preserves`. -/
theorem applyMfa_preserves {s p frame} (H : StepInstrHyp s p frame)
    (dest modReg funReg : Reg) (argRegs : Array Reg) {s'}
    (hcode : frame.function.code[frame.ip]! = .applyMfa dest modReg funReg argRegs)
    (h : stepInstr s p frame (.applyMfa dest modReg funReg argRegs) = .ok s') :
    State.WF s' := by
  have hio := H.instrOk (.applyMfa dest modReg funReg argRegs) hcode
  obtain ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩ := H
  simp [stepInstr] at h
  cases hmod : getReg! frame modReg with
  | atom modName =>
    simp [hmod] at h
    cases hfun : getReg! frame funReg with
    | atom funName =>
      simp [hfun] at h
      generalize hff0 : s.module.findFunction
          (modName ++ "." ++ funName ++ "/" ++
            toString (readArgs! frame argRegs).size) = oFind at h
      cases oFind with
      | none =>
        simp [hff0] at h
        exact raiseValue_preserves _ _ _ _ hs hp hres hstat htop h
      | some callee =>
        simp [hff0] at h
        split at h
        · cases h
          have hip :=
            ip_succ_lt_of_nonterminal hfwf.1 hfwf.2.2.1 hcode rfl
          have hcallee : Function.WF s.module callee :=
            Module.findFunction_WF hs.1 hff0
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
          let newFrame : Frame := {
            function := callee
            regs := State.mkRegs callee.locals (readArgs! frame argRegs)
            ip := 0
            retDest := dest
          }
          have hnew : Frame.WF s.module newFrame := by
            refine ⟨hcallee, ?_, ?_, ?_⟩
            · simp [newFrame, mkRegs_size]
            · exact hcallee.2.1
            · have hname := Module.findFunction_name hff0
              simpa [newFrame, hname] using Option.isSome_of_eq_some hff0
          have hdest : dest < frame.function.locals := by
            have hr : Instr.regsOk frame.function.locals
                (Instr.applyMfa dest modReg funReg argRegs) = true := by
              simpa [Function.instrOk] using hio.1
            simp [Instr.regsOk] at hr
            exact hr.1.1.1
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
        · exact raiseValue_preserves _ _ _ _ hs hp hres hstat htop h
    | nil | bool _ | int _ | float _ | string _ | bitstring _ | pid _ | reference _ | ref _ =>
      simp [hfun] at h
      exact raiseValue_preserves _ _ _ _ hs hp hres hstat htop h
  | nil | bool _ | int _ | float _ | string _ | bitstring _ | pid _ | reference _ | ref _ =>
    simp [hmod] at h
    exact raiseValue_preserves _ _ _ _ hs hp hres hstat htop h

/-- Successful `stepInstr` preserves well-formedness under the usual stepper hypotheses. -/
theorem stepInstr_preserves
    (s : State) (p : Process) (frame : Frame) (instr : Instr) {s'}
    (hs : State.WF s) (hp : Process.WF s.module p) (hfwf : Frame.WF s.module frame)
    (hres : p.result = none) (hstat : p.status = .runnable)
    (htop : p.stack.size > 0) (hframe : p.stack[p.stack.size - 1]! = frame)
    (hcode : frame.function.code[frame.ip]! = instr)
    (h : stepInstr s p frame instr = .ok s') :
    State.WF s' := by
  have H : StepInstrHyp s p frame := ⟨hs, hp, hfwf, hres, hstat, htop, hframe⟩
  cases instr with
  | loadLit reg lit => exact loadLit_step_preserves H reg lit hcode h
  | move dest src => exact move_preserves H dest src hcode h
  | call dest funName argRegs => exact call_preserves H dest funName argRegs hcode h
  | return_ reg => exact return_preserves H reg hcode h
  | halt reg => exact halt_preserves H reg hcode h
  | jump target => exact jump_preserves H target hcode h
  | jumpIfEq target reg lit => exact jumpIfEq_preserves H target reg lit hcode h
  | getTupleElem dest tupleReg index =>
      exact getTupleElem_preserves H dest tupleReg index hcode h
  | isTag dest reg tag => exact isTag_preserves H dest reg tag hcode h
  | spawn dest funName argRegs => exact spawn_preserves H dest funName argRegs hcode h
  | send pidReg msgReg => exact send_preserves H pidReg msgReg hcode h
  | recv dest => exact recv_preserves H dest hcode h
  | getListElem dest listReg index =>
      exact getListElem_preserves H dest listReg index hcode h
  | getListRest dest listReg index =>
      exact getListRest_step_preserves H dest listReg index hcode h
  | enterTry rescueIp excReg => exact enterTry_preserves H rescueIp excReg hcode h
  | leaveTry => exact leaveTry_preserves H hcode h
  | raise reg => exact raise_preserves H reg hcode h
  | recvPeek dest indexReg empty =>
      exact recvPeek_preserves H dest indexReg empty hcode h
  | recvDrop indexReg => exact recvDrop_preserves H indexReg hcode h
  | wait retry after timeout => exact wait_preserves H retry after timeout hcode h
  | link pidReg => exact link_preserves H pidReg hcode h
  | monitor dest pidReg => exact monitor_preserves H dest pidReg hcode h
  | demonitor refReg => exact demonitor_preserves H refReg hcode h
  | makeFun dest funName capRegs =>
      exact makeFun_step_preserves H dest funName capRegs hcode h
  | apply dest funReg argRegs => exact apply_preserves H dest funReg argRegs hcode h
  | loadFile dest pathReg => exact loadFile_preserves H dest pathReg hcode h
  | applyMfa dest modReg funReg argRegs =>
      exact applyMfa_preserves H dest modReg funReg argRegs hcode h

end Step
end Autumn
