import Autumn.StepProgress
import Autumn.StepPreserve
import Autumn.Examples

namespace Autumn
namespace Step

/-! # Step safety: progress + preservation barrel -/

/-- Preservation: successful steps stay well-formed. -/
theorem step_preserves (s s' : State)
    (hs : State.WF s) (h : step s = .ok s') : State.WF s' := by
  by_cases hdone : s.result.isSome = true
  · unfold step at h; simp [hdone] at h; cases h; exact hs
  · have hr : s.result = none := by
      cases hx : s.result with
      | none => rfl
      | some _ => simp [Option.isSome, hx] at hdone
    have hcur := hs.2.2.1
    unfold step at h
    simp [hdone, hcur] at h
    by_cases hnr :
        ((s.processes[s.current]).status != .runnable) = true ∨
          (s.processes[s.current]).result.isSome = true
    · simp [hnr] at h
      exact scheduleNext_preserves s s.current hs h
    · simp [hnr] at h
      have hp := hs.2.2.2 s.current hcur
      have ⟨hrun, hnone⟩ := status_runnable_of_not_deschedule _ _ hnr
      have hsz := runnable_stack_pos hp hrun hnone
      have hempty : ¬((s.processes[s.current]).stack = #[]) := by
        intro heq
        have hsz0 : (s.processes[s.current]).stack.size = 0 := by simp [heq]
        exact (Nat.ne_of_gt hsz) hsz0
      simp [hempty] at h
      have hfwf := runnable_top_WF hp hrun hnone
      have hipok :
          ¬(((s.processes[s.current]).stack[
              (s.processes[s.current]).stack.size - 1]!).function.code.size ≤
            ((s.processes[s.current]).stack[
              (s.processes[s.current]).stack.size - 1]!).ip) := by
        have := hfwf.2.2.1; omega
      simp [hipok] at h
      split at h
      · cases h
      · rename_i s1 hsi
        have hs1 : State.WF s1 :=
          stepInstr_preserves s (s.processes[s.current])
            ((s.processes[s.current]).stack[(s.processes[s.current]).stack.size - 1]!)
            _
            hs hp hfwf hnone hrun hsz rfl rfl hsi
        -- clock tick after a successful instruction
        have hs1c : State.WF { s1 with clock := s1.clock + 1 } := clock_preserves s1 _ hs1
        split at h
        · cases h; exact hs1c
        · split at h
          · exact scheduleNext_preserves _ s1.current hs1c h
          · cases h
            exact reductions_preserves _ (s1.reductions - 1) hs1c

theorem addMain_has_entry :
    (addMainModule.findFunction addMainModule.entry).isSome := by
  native_decide

theorem tryRescue_has_entry :
    (tryRescueModule.findFunction tryRescueModule.entry).isSome := by
  native_decide

#eval Step.runModule addMainModule (fuel := 100)

#guard (match Step.runModule tryRescueModule (fuel := 100) with
  | .ok (.int 3) => true
  | _ => false)


end Step
end Autumn
