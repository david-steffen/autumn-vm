import Autumn.Step.Progress

namespace Autumn
namespace Step

/-! # Per-opcode `stepInstr` progress (public proof surface)

Thin `stepInstr_error_not_structural` dispatcher. **External proofs** should
call these `*_error_not_structural` lemmas (or `step_progress`) rather than
unfolding `stepInstr` / `builtin`.

Every `Instr` constructor has a case here. Pure-builtin structural errors go
through `builtin_error_not_structural` / `floatBinop_ne_error` in `Step.Progress`.
Also hosts `step_progress`. See `AGENTS.md` (“Public proof surface”).
-/

/-- `loadLit` case of `stepInstr_error_not_structural`. -/
theorem loadLit_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (reg : Reg) (lit : Term) {e : StepError}
    (herr : stepInstr s p frame (.loadLit reg lit) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr; exact nomatch herr

/-- `move` case of `stepInstr_error_not_structural`. -/
theorem move_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest src : Reg) {e : StepError}
    (herr : stepInstr s p frame (.move dest src) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr; exact nomatch herr

/-- `call` case of `stepInstr_error_not_structural`. -/
theorem call_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest : Reg) (funName : FunName) (argRegs : Array Reg) {e : StepError}
    (herr : stepInstr s p frame (.call dest funName argRegs) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  by_cases hmp : funName = "map_put/3"
  · simp [hmp] at herr
    by_cases har : (readArgs! frame argRegs).size = 3
    · simp only [har, ↓reduceIte, ite_false] at herr
      cases hmpu : mapPut s p frame dest (readArgs! frame argRegs)[0]!
          (readArgs! frame argRegs)[1]! (readArgs! frame argRegs)[2]! with
      | some _ => simp [hmpu] at herr; exact nomatch herr
      | none =>
        simp [hmpu] at herr
        exact raiseValue_error_not_structural _ _ _ _ herr
    · simp only [har, ↓reduceIte, ite_true] at herr; cases herr; rfl
  · simp [hmp] at herr
    by_cases hc : funName = "cons/2"
    · simp [hc] at herr
      by_cases har : (readArgs! frame argRegs).size = 2
      · simp only [har, ↓reduceIte, ite_false] at herr
        cases hco : cons s p frame dest (readArgs! frame argRegs)[0]!
            (readArgs! frame argRegs)[1]! with
        | some _ => simp [hco] at herr; exact nomatch herr
        | none =>
          simp [hco] at herr
          exact raiseValue_error_not_structural _ _ _ _ herr
      · simp only [har, ↓reduceIte, ite_true] at herr; cases herr; rfl
    · simp [hc] at herr
      by_cases hflag : funName = "Process.flag/2"
      · simp [hflag] at herr
        by_cases har : (readArgs! frame argRegs).size = 2
        · simp only [har, ↓reduceIte, ite_false, processFlag] at herr
          split at herr
          · exact nomatch herr
          · exact raiseValue_error_not_structural _ _ _ _ herr
        · simp only [har, ↓reduceIte, ite_true] at herr; cases herr; rfl
      · simp [hflag] at herr
        by_cases hex : funName = "Process.exit/2"
        · simp [hex] at herr
          by_cases har : (readArgs! frame argRegs).size = 2
          · simp only [har, ↓reduceIte, ite_false, processExit] at herr
            split at herr
            · split at herr
              · exact raiseValue_error_not_structural _ _ _ _ herr
              · exact (scheduleNext_error_is_noRunnable _ _ herr) ▸ rfl
            · exact raiseValue_error_not_structural _ _ _ _ herr
          · simp only [har, ↓reduceIte, ite_true] at herr; cases herr; rfl
        · simp [hex] at herr
          by_cases hetsn : funName = "ets_new/0"
          · simp [hetsn] at herr
            split at herr
            · simp [etsNew, State.etsNew] at herr
            · cases herr; rfl
          · simp [hetsn] at herr
            by_cases hetsn2 : funName = "ets_new/2"
            · simp [hetsn2] at herr
              by_cases har : (readArgs! frame argRegs).size = 2
              · simp only [har, ↓reduceIte, ite_false] at herr
                simp [etsNew2] at herr
                split at herr
                · split at herr
                  · exact raiseValue_error_not_structural _ _ _ _ herr
                  · split at herr
                    · split at herr
                      · exact raiseValue_error_not_structural _ _ _ _ herr
                      · exact nomatch herr
                    · split at herr
                      · exact raiseValue_error_not_structural _ _ _ _ herr
                      · exact nomatch herr
                    · exact raiseValue_error_not_structural _ _ _ _ herr
                · exact raiseValue_error_not_structural _ _ _ _ herr
              · simp only [har, ↓reduceIte, ite_true] at herr; cases herr; rfl
            · simp [hetsn2] at herr
              by_cases hetsi : funName = "ets_insert/3"
              · simp [hetsi] at herr
                by_cases har : (readArgs! frame argRegs).size = 3
                · simp only [har, ↓reduceIte, ite_false] at herr
                  simp [etsInsert] at herr
                  split at herr
                  · exact raiseValue_error_not_structural _ _ _ _ herr
                  · split at herr
                    · exact raiseValue_error_not_structural _ _ _ _ herr
                    · exact nomatch herr
                · simp only [har, ↓reduceIte, ite_true] at herr; cases herr; rfl
              · simp [hetsi] at herr
                by_cases hetsl : funName = "ets_lookup/2"
                · simp [hetsl] at herr
                  by_cases har : (readArgs! frame argRegs).size = 2
                  · simp only [har, ↓reduceIte, ite_false] at herr
                    simp [etsLookup] at herr
                    split at herr
                    · exact raiseValue_error_not_structural _ _ _ _ herr
                    · split at herr
                      · exact raiseValue_error_not_structural _ _ _ _ herr
                      · exact nomatch herr
                  · simp only [har, ↓reduceIte, ite_true] at herr; cases herr; rfl
                · simp [hetsl] at herr
                  by_cases hetsd : funName = "ets_delete/2"
                  · simp [hetsd] at herr
                    by_cases har : (readArgs! frame argRegs).size = 2
                    · simp only [har, ↓reduceIte, ite_false] at herr
                      simp [etsDelete] at herr
                      split at herr
                      · exact raiseValue_error_not_structural _ _ _ _ herr
                      · split at herr
                        · exact raiseValue_error_not_structural _ _ _ _ herr
                        · exact nomatch herr
                    · simp only [har, ↓reduceIte, ite_true] at herr; cases herr; rfl
                  · simp [hetsd] at herr
                    by_cases hetsm : funName = "ets_match_object/2"
                    · simp [hetsm] at herr
                      by_cases har : (readArgs! frame argRegs).size = 2
                      · simp only [har, ↓reduceIte, ite_false] at herr
                        simp [etsMatchObject] at herr
                        split at herr
                        · exact raiseValue_error_not_structural _ _ _ _ herr
                        · split at herr
                          · exact raiseValue_error_not_structural _ _ _ _ herr
                          · exact nomatch herr
                      · simp only [har, ↓reduceIte, ite_true] at herr; cases herr; rfl
                    · simp [hetsm] at herr
                      by_cases hetss : funName = "ets_select/2"
                      · simp [hetss] at herr
                        by_cases har : (readArgs! frame argRegs).size = 2
                        · simp only [har, ↓reduceIte, ite_false] at herr
                          simp [etsSelect] at herr
                          split at herr
                          · exact raiseValue_error_not_structural _ _ _ _ herr
                          · split at herr
                            · exact raiseValue_error_not_structural _ _ _ _ herr
                            · exact raiseValue_error_not_structural _ _ _ _ herr
                            · exact nomatch herr
                        · simp only [har, ↓reduceIte, ite_true] at herr; cases herr; rfl
                      · simp [hetss] at herr
                        by_cases hmref : funName = "make_ref/0"
                        · simp [hmref] at herr
                          split at herr
                          · exact nomatch herr
                          · cases herr; rfl
                        · simp [hmref] at herr
                          by_cases htu : isMakeTupleName funName = true
                          · simp [htu] at herr; exact nomatch herr
                          · simp [htu] at herr
                            by_cases hbi : isBuiltinName funName = true
                            · simp [hbi] at herr
                              cases hb : builtin p.heap p.pid funName
                                  (readArgs! frame argRegs) with
                              | ok v => simp [hb] at herr; exact nomatch herr
                              | badarg =>
                                simp [hb] at herr
                                exact raiseValue_error_not_structural _ _ _ _ herr
                              | error e' =>
                                simp [hb] at herr
                                cases herr
                                exact builtin_error_not_structural hb
                            · simp [hbi] at herr
                              split at herr
                              · split at herr
                                · exact nomatch herr
                                · cases herr; rfl
                              · cases herr; rfl

/-- `return_` case of `stepInstr_error_not_structural`. -/
theorem return_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (reg : Reg) {e : StepError}
    (herr : stepInstr s p frame (.return_ reg) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  by_cases hsz : p.stack.size = 1
  · simp [hsz] at herr
    exact (scheduleNext_error_is_noRunnable _ _ herr) ▸ rfl
  · simp [hsz] at herr
    split at herr
    · cases herr; rfl
    · exact nomatch herr

/-- `halt` case of `stepInstr_error_not_structural`. -/
theorem halt_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (reg : Reg) {e : StepError}
    (herr : stepInstr s p frame (.halt reg) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  exact (scheduleNext_error_is_noRunnable _ _ herr) ▸ rfl

/-- `jump` case of `stepInstr_error_not_structural`. -/
theorem jump_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (target : Label) {e : StepError}
    (herr : stepInstr s p frame (.jump target) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr; exact nomatch herr

/-- `jumpIfEq` case of `stepInstr_error_not_structural`. -/
theorem jumpIfEq_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (target : Label) (reg : Reg) (lit : Term) {e : StepError}
    (herr : stepInstr s p frame (.jumpIfEq target reg lit) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr; exact nomatch herr

/-- `getTupleElem` case of `stepInstr_error_not_structural`. -/
theorem getTupleElem_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest tupleReg : Reg) (index : Nat) {e : StepError}
    (herr : stepInstr s p frame (.getTupleElem dest tupleReg index) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  all_goals (
    try split at herr
    all_goals (
      try split at herr
      all_goals (
        try { injection herr with heq; subst heq; rfl }
        try { cases herr }
        try { exact nomatch herr }
      )
    )
  )

/-- `isTag` case of `stepInstr_error_not_structural`. -/
theorem isTag_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest reg : Reg) (tag : Tag) {e : StepError}
    (herr : stepInstr s p frame (.isTag dest reg tag) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr; exact nomatch herr

/-- `spawn` case of `stepInstr_error_not_structural`. -/
theorem spawn_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest : Reg) (funName : FunName) (argRegs : Array Reg) {e : StepError}
    (herr : stepInstr s p frame (.spawn dest funName argRegs) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  all_goals (
    try split at herr
    all_goals (
      try { injection herr with heq; subst heq; rfl }
      try { exact nomatch herr }
      try { cases herr }
    )
  )

/-- `send` case of `stepInstr_error_not_structural`. -/
theorem send_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (pidReg msgReg : Reg) {e : StepError}
    (herr : stepInstr s p frame (.send pidReg msgReg) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  all_goals (
    try split at herr
    all_goals (
      try { injection herr with heq; subst heq; rfl }
      try { exact nomatch herr }
      try { cases herr }
    )
  )

/-- `recv` case of `stepInstr_error_not_structural`. -/
theorem recv_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest : Reg) {e : StepError}
    (herr : stepInstr s p frame (.recv dest) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  · exact nomatch herr
  · simp [scheduleNext_error_is_noRunnable _ _ herr, isStructuralError]

/-- `getListElem` case of `stepInstr_error_not_structural`. -/
theorem getListElem_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest listReg : Reg) (index : Nat) {e : StepError}
    (herr : stepInstr s p frame (.getListElem dest listReg index) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  all_goals (
    try split at herr
    all_goals (
      try split at herr
      all_goals (
        try { injection herr with heq; subst heq; rfl }
        try { cases herr }
        try { exact nomatch herr }
      )
    )
  )

/-- `getListRest` case of `stepInstr_error_not_structural`. -/
theorem getListRest_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest listReg : Reg) (index : Nat) {e : StepError}
    (herr : stepInstr s p frame (.getListRest dest listReg index) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  all_goals (
    try split at herr
    all_goals (
      try split at herr
      all_goals (
        try { injection herr with heq; subst heq; rfl }
        try { cases herr }
        try { exact nomatch herr }
      )
    )
  )

/-- `enterTry` case of `stepInstr_error_not_structural`. -/
theorem enterTry_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (rescueIp : Label) (excReg : Reg) {e : StepError}
    (herr : stepInstr s p frame (.enterTry rescueIp excReg) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr; exact nomatch herr

/-- `leaveTry` case of `stepInstr_error_not_structural`. -/
theorem leaveTry_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    {e : StepError}
    (herr : stepInstr s p frame (.leaveTry) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  · injection herr with heq; subst heq; rfl
  · exact nomatch herr

/-- `raise` case of `stepInstr_error_not_structural`. -/
theorem raise_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (reg : Reg) {e : StepError}
    (herr : stepInstr s p frame (.raise reg) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  exact raiseValue_error_not_structural _ _ _ _ herr

/-- `recvPeek` case of `stepInstr_error_not_structural`. -/
theorem recvPeek_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest indexReg : Reg) (empty : Label) {e : StepError}
    (herr : stepInstr s p frame (.recvPeek dest indexReg empty) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  all_goals (
    try split at herr
    all_goals (
      try split at herr
      all_goals (
        try { injection herr with heq; subst heq; rfl }
        try { exact nomatch herr }
        try { cases herr }
      )
    )
  )

/-- `recvDrop` case of `stepInstr_error_not_structural`. -/
theorem recvDrop_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (indexReg : Reg) {e : StepError}
    (herr : stepInstr s p frame (.recvDrop indexReg) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  all_goals (
    try split at herr
    all_goals (
      try split at herr
      all_goals (
        try { injection herr with heq; subst heq; rfl }
        try { exact nomatch herr }
        try { cases herr }
      )
    )
  )

/-- `wait` case of `stepInstr_error_not_structural`. -/
theorem wait_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (retry after : Label) (timeout : Option Nat) {e : StepError}
    (herr : stepInstr s p frame (.wait retry after timeout) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  by_cases hmb : 0 < p.mailbox.size
  · simp [hmb] at herr; exact nomatch herr
  · simp [hmb] at herr
    cases hd : p.waitDeadline with
    | some d =>
      simp [hd] at herr
      by_cases hle : d ≤ s.clock
      · simp [hle] at herr; exact nomatch herr
      · simp [hle] at herr
        exact (scheduleNext_error_is_noRunnable _ _ herr) ▸ rfl
    | none =>
      simp [hd] at herr
      cases hto : timeout with
      | some n =>
        cases n with
        | zero =>
          simp [hto] at herr; exact nomatch herr
        | succ n =>
          simp [hto] at herr
          exact (scheduleNext_error_is_noRunnable _ _ herr) ▸ rfl
      | none =>
        simp [hto] at herr
        exact (scheduleNext_error_is_noRunnable _ _ herr) ▸ rfl

/-- `link` case of `stepInstr_error_not_structural`. -/
theorem link_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (pidReg : Reg) {e : StepError}
    (herr : stepInstr s p frame (.link pidReg) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  · exact linkWith_error_not_structural _ _ herr
  · cases herr; rfl

/-- `monitor` case of `stepInstr_error_not_structural`. -/
theorem monitor_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest pidReg : Reg) {e : StepError}
    (herr : stepInstr s p frame (.monitor dest pidReg) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  · exact monitorWith_error_not_structural _ _ _ herr
  · cases herr; rfl

/-- `demonitor` case of `stepInstr_error_not_structural`. -/
theorem demonitor_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (refReg : Reg) {e : StepError}
    (herr : stepInstr s p frame (.demonitor refReg) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  · exact demonitorWith_error_not_structural _ _ herr
  · cases herr; rfl

/-- `makeFun` case of `stepInstr_error_not_structural`. -/
theorem makeFun_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest : Reg) (funName : FunName) (capRegs : Array Reg) {e : StepError}
    (herr : stepInstr s p frame (.makeFun dest funName capRegs) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr; exact nomatch herr

/-- `apply` case of `stepInstr_error_not_structural`. -/
theorem apply_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest funReg : Reg) (argRegs : Array Reg) {e : StepError}
    (herr : stepInstr s p frame (.apply dest funReg argRegs) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  cases hreg : getReg! frame funReg with
  | ref r =>
    simp [hreg] at herr
    cases hnode : p.heap.get? r with
    | none =>
      simp [hnode] at herr; cases herr; rfl
    | some node =>
      cases node with
      | closure funName env =>
        simp [hnode] at herr
        cases hff : s.module.findFunction funName with
        | none =>
          simp [hff] at herr; cases herr; rfl
        | some callee =>
          simp [hff] at herr
          split at herr
          · exact nomatch herr
          · cases herr; rfl
      | tuple _ | list _ | map _ =>
        simp [hnode] at herr; cases herr; rfl
  | nil | bool _ | int _ | float _ | atom _ | string _ | bitstring _ | pid _ | reference _ =>
    simp [hreg] at herr; cases herr; rfl

/-- `loadFile` case of `stepInstr_error_not_structural`. -/
theorem loadFile_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest pathReg : Reg) {e : StepError}
    (herr : stepInstr s p frame (.loadFile dest pathReg) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  split at herr
  · exact raiseValue_error_not_structural _ _ _ _ herr
  · exact raiseValue_error_not_structural _ _ _ _ herr

/-- `applyMfa` case of `stepInstr_error_not_structural`. -/
theorem applyMfa_error_not_structural
    (s : State) (p : Process) (frame : Frame)
    (dest modReg funReg : Reg) (argRegs : Array Reg) {e : StepError}
    (herr : stepInstr s p frame (.applyMfa dest modReg funReg argRegs) = .error e) :
    isStructuralError e = false := by
  simp [stepInstr] at herr
  cases hmod : getReg! frame modReg with
  | atom modName =>
    simp [hmod] at herr
    cases hfun : getReg! frame funReg with
    | atom funName =>
      simp [hfun] at herr
      generalize hff0 : s.module.findFunction
          (modName ++ "." ++ funName ++ "/" ++
            toString (readArgs! frame argRegs).size) = oFind at herr
      cases oFind with
      | none =>
        simp [hff0] at herr
        exact raiseValue_error_not_structural _ _ _ _ herr
      | some callee =>
        simp [hff0] at herr
        split at herr
        · exact nomatch herr
        · exact raiseValue_error_not_structural _ _ _ _ herr
    | nil | bool _ | int _ | float _ | string _ | bitstring _ | pid _ | reference _ | ref _ =>
      simp [hfun] at herr
      exact raiseValue_error_not_structural _ _ _ _ herr
  | nil | bool _ | int _ | float _ | string _ | bitstring _ | pid _ | reference _ | ref _ =>
    simp [hmod] at herr
    exact raiseValue_error_not_structural _ _ _ _ herr

theorem stepInstr_error_not_structural
    (s : State) (p : Process) (frame : Frame) (instr : Instr) {e : StepError}
    (herr : stepInstr s p frame instr = .error e) :
    isStructuralError e = false := by
  cases instr with
  | loadLit reg lit => exact loadLit_error_not_structural s p frame reg lit herr
  | move dest src => exact move_error_not_structural s p frame dest src herr
  | call dest funName argRegs =>
      exact call_error_not_structural s p frame dest funName argRegs herr
  | return_ reg => exact return_error_not_structural s p frame reg herr
  | halt reg => exact halt_error_not_structural s p frame reg herr
  | jump target => exact jump_error_not_structural s p frame target herr
  | jumpIfEq target reg lit =>
      exact jumpIfEq_error_not_structural s p frame target reg lit herr
  | getTupleElem dest tupleReg index =>
      exact getTupleElem_error_not_structural s p frame dest tupleReg index herr
  | isTag dest reg tag => exact isTag_error_not_structural s p frame dest reg tag herr
  | spawn dest funName argRegs =>
      exact spawn_error_not_structural s p frame dest funName argRegs herr
  | send pidReg msgReg => exact send_error_not_structural s p frame pidReg msgReg herr
  | recv dest => exact recv_error_not_structural s p frame dest herr
  | getListElem dest listReg index =>
      exact getListElem_error_not_structural s p frame dest listReg index herr
  | getListRest dest listReg index =>
      exact getListRest_error_not_structural s p frame dest listReg index herr
  | enterTry rescueIp excReg =>
      exact enterTry_error_not_structural s p frame rescueIp excReg herr
  | leaveTry => exact leaveTry_error_not_structural s p frame herr
  | raise reg => exact raise_error_not_structural s p frame reg herr
  | recvPeek dest indexReg empty =>
      exact recvPeek_error_not_structural s p frame dest indexReg empty herr
  | recvDrop indexReg => exact recvDrop_error_not_structural s p frame indexReg herr
  | wait retry after timeout =>
      exact wait_error_not_structural s p frame retry after timeout herr
  | link pidReg => exact link_error_not_structural s p frame pidReg herr
  | monitor dest pidReg => exact monitor_error_not_structural s p frame dest pidReg herr
  | demonitor refReg => exact demonitor_error_not_structural s p frame refReg herr
  | makeFun dest funName capRegs =>
      exact makeFun_error_not_structural s p frame dest funName capRegs herr
  | apply dest funReg argRegs =>
      exact apply_error_not_structural s p frame dest funReg argRegs herr
  | loadFile dest pathReg =>
      exact loadFile_error_not_structural s p frame dest pathReg herr
  | applyMfa dest modReg funReg argRegs =>
      exact applyMfa_error_not_structural s p frame dest modReg funReg argRegs herr

/-- Progress: well-formed running states never fail structurally. -/
theorem step_progress (s : State) (hs : State.WF s) (hr : s.result = none) :
    match step s with
    | .ok _ => True
    | .error e => isStructuralError e = false := by
  cases hstep : step s with
  | ok _ => trivial
  | error e =>
    have hres : s.result.isSome = false := by simp [Option.isSome, hr]
    have hcur := hs.2.2.1
    unfold step at hstep
    simp [hres, hcur] at hstep
    by_cases hnr :
        ((s.processes[s.current]).status != .runnable) = true ∨
          (s.processes[s.current]).result.isSome = true
    · simp [hnr] at hstep
      simp [scheduleNext_error_is_noRunnable s s.current hstep, isStructuralError]
    · simp [hnr] at hstep
      have hp := hs.2.2.2 s.current hcur
      have ⟨hrun, hnone⟩ := status_runnable_of_not_deschedule _ _ hnr
      have hsz := runnable_stack_pos hp hrun hnone
      have hempty : ¬((s.processes[s.current]).stack = #[]) := by
        intro heq
        have hsz0 : (s.processes[s.current]).stack.size = 0 := by simp [heq]
        exact (Nat.ne_of_gt hsz) hsz0
      simp [hempty] at hstep
      have hfwf := runnable_top_WF hp hrun hnone
      have hipok :
          ¬(((s.processes[s.current]).stack[
              (s.processes[s.current]).stack.size - 1]!).function.code.size ≤
            ((s.processes[s.current]).stack[
              (s.processes[s.current]).stack.size - 1]!).ip) := by
        have := hfwf.2.2.1; omega
      simp [hipok] at hstep
      split at hstep
      · rename_i e' hsi
        injection hstep with heq; subst heq
        exact stepInstr_error_not_structural _ _ _ _ hsi
      · rename_i s1 hsi
        -- clock is bumped before the reductions / scheduleNext branch
        simp [afterInstr] at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · simp [scheduleNext_error_is_noRunnable _ _ hstep, isStructuralError]
          · cases hstep

end Step
end Autumn
