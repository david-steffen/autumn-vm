import Autumn.OTP.GenServer
import Autumn.State.Lemmas

namespace Autumn
namespace OTP
namespace Supervisor

/-! # Observational Supervisor-shaped laws

Stdlib `supervisor.ex` strategies are teaching OTP on spawn/monitor/EXIT.
Intensity / restart strategies stay Elixir; Lean laws here cover the EXIT
delivery contracts those strategies rely on.
-/

/-- With `trap_exit`, linked EXIT is mailbox delivery (supervisor-shaped trap). -/
theorem trap_exit_delivers_mailbox
    (fuel : Nat) (s : State) (fromPid : Nat) (heap : Heap) (reason : Value)
    (peerPid : Nat) {idx : Nat}
    (hfnd : s.findProcessIdx peerPid = some idx)
    (hpeer : idx < s.processes.size)
    (hlive : ((s.processes[idx]'hpeer).status == .exited) = false)
    (htrap : (s.processes[idx]'hpeer).trapExit = true) :
    State.signalLink (fuel + 1) s fromPid heap reason peerPid =
      State.notifyExitMailbox s fromPid heap reason peerPid :=
  signalLink_trapExit_eq_mailbox fuel s fromPid heap reason peerPid hfnd hpeer hlive htrap

/-- Call-shaped request/reply observes `7` (child serves parent under scheduling). -/
theorem child_call_observes_seven :
    (match State.initial GenServer.counterCallModule 64 with
      | .ok s =>
        (match Step.run 1000 s with
          | .ok (.int 7) => true
          | _ => false) &&
          (match Step.runScheduled 1000 ([] : List State.ScheduleChoice) s with
            | .ok (.int 7) => true
            | _ => false)
      | .error _ => false) =
      true :=
  GenServer.counterCall_observes_seven

end Supervisor
end OTP
end Autumn
