import Autumn.Obs.Schedule
import Autumn.OTP.Supervisor

namespace Autumn
namespace Meta
namespace Explore

/-! # Light theorem / schedule exploration helpers

For local `#eval` — **not** a name-golden dump (`avoid-ceremonial-name-goldens`).
-/

/-- Pretty-print one schedule choice. -/
def ScheduleChoice.repr (c : State.ScheduleChoice) : String :=
  match c with
  | .roundRobin => "roundRobin"
  | .prefer i => s!"prefer {i}"

/-- Pretty-print a choice tape. -/
def tapeRepr (choices : List State.ScheduleChoice) : String :=
  String.intercalate ", " (choices.map ScheduleChoice.repr)

/-- Run with a tape and summarize the result (for `#eval`). -/
def runScheduledSummary (fuel : Nat) (choices : List State.ScheduleChoice) (s : State) :
    String :=
  match Step.runScheduled fuel choices s with
  | .ok t => s!"ok {reprStr t}  (tape: [{tapeRepr choices}])"
  | .error e => s!"error {reprStr e}  (tape: [{tapeRepr choices}])"

/-- Named lemmas near the schedule API (human checklist, not CI). -/
def scheduleLemmaHints : List String :=
  [ "stepScheduled_preserves"
  , "stepScheduled_progress"
  , "runScheduled_preserves"
  , "runScheduled_progress"
  , "runScheduled_nil_eq_run"
  , "Obs.Schedule.drainSiblings_tapes_observe_zero"
  ]

/-- `#eval` demo: drain-siblings under prefer tape. -/
def drainSiblingsPreferSummary : String :=
  match State.initial drainSiblingsModule 64 with
  | .ok s => runScheduledSummary 1000 Obs.Schedule.drainPreferTape s
  | .error e => s!"initial error {reprStr e}"

#eval drainSiblingsPreferSummary

#eval scheduleLemmaHints

end Explore
end Meta
end Autumn
