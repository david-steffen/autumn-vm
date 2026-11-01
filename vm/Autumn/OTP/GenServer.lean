import Autumn.Obs.Schedule

namespace Autumn
namespace OTP
namespace GenServer

/-! # Observational GenServer-shaped laws

Stdlib `genserver.ex` / `agent.ex` are Elixir on existing opcodes. These laws
use a Lean-authored request/reply image (spawn + `send`/`recv`) — same style as
`Obs.Schedule`, not a GenServer refinement.
-/

/-- Minimal call-shaped counter: server receives `{from, x}`, replies `n + x`.
Main spawns with `n = 5`, sends `{self, 2}`, expects `7`. -/
def counterCallModule : Module :=
  Module.ofFunctions "Main.main/0" #[
    {
      name := "Main.server/1"
      arity := 1
      locals := 5
      code := #[
        .recv 1,
        .getTupleElem 2 1 0,
        .getTupleElem 3 1 1,
        .call 4 "+/2" #[0, 3],
        .send 2 4,
        .return_ 4
      ]
    },
    {
      name := "Main.main/0"
      arity := 0
      locals := 5
      code := #[
        .loadLit 0 (.int 5),
        .spawn 1 "Main.server/1" #[0],
        .call 2 "self/0" #[],
        .loadLit 3 (.int 2),
        .call 4 "make_tuple/2" #[2, 3],
        .send 1 4,
        .recv 0,
        .return_ 0
      ]
    }
  ]

theorem counterCall_checkWF : Module.checkWF counterCallModule = true := by
  native_decide

/-- Round-robin and empty taped run both observe reply `7`. -/
theorem counterCall_observes_seven :
    (match State.initial counterCallModule 64 with
      | .ok s =>
        (match Step.run 1000 s with
          | .ok (.int 7) => true
          | _ => false) &&
          (match Step.runScheduled 1000 ([] : List State.ScheduleChoice) s with
            | .ok (.int 7) => true
            | _ => false)
      | .error _ => false) =
      true := by
  native_decide

#guard (match State.initial counterCallModule 64 with
  | .ok s =>
    match Step.run 1000 s with
    | .ok (.int 7) => true
    | _ => false
  | _ => false)

/-- Empty schedule tape matches ordinary `run` on the call image. -/
theorem counterCall_nil_tape_eq_run (fuel : Nat)
    {s : State} (_hi : State.initial counterCallModule 64 = .ok s) :
    Step.runScheduled fuel ([] : List State.ScheduleChoice) s = Step.run fuel s :=
  Step.runScheduled_nil_eq_run fuel s

/-- Drain-siblings world (durable sibling after entry return) still observes `0`. -/
theorem genserver_world_drains_siblings :
    (match State.initial drainSiblingsModule 64 with
      | .ok s =>
        (match Step.run 1000 s with
          | .ok (.int 0) => true
          | _ => false) &&
          (match Step.runScheduled 1000 ([] : List State.ScheduleChoice) s with
            | .ok (.int 0) => true
            | _ => false) &&
          (match Step.runScheduled 1000 Obs.Schedule.drainPreferTape s with
            | .ok (.int 0) => true
            | _ => false)
      | .error _ => false) =
      true :=
  Obs.Schedule.drainSiblings_tapes_observe_zero

end GenServer
end OTP
end Autumn
