import Autumn.Instr

namespace Autumn

/-- Hand-built add demo for `--lean-demo` (Lean-authored; not a fixture golden). -/
def addMainModule : Module :=
  Module.ofFunctions "Main.main/0" #[
    {
      name := "Main.add/2"
      arity := 2
      locals := 3
      code := #[
        .call 2 "+/2" #[0, 1],
        .return_ 2
      ]
    },
    {
      name := "Main.main/0"
      arity := 0
      locals := 3
      code := #[
        .loadLit 0 (.int 1),
        .loadLit 1 (.int 2),
        .call 2 "Main.add/2" #[0, 1],
        .return_ 2
      ]
    }
  ]

/-- Hand-built try/rescue demo for Lean authoring. -/
def tryRescueModule : Module :=
  Module.ofFunctions "Main.main/0" #[
    {
      name := "Main.boom/0"
      arity := 0
      locals := 1
      code := #[
        .loadLit 0 (.atom "boom"),
        .raise 0,
        .return_ 0
      ]
    },
    {
      name := "Main.main/0"
      arity := 0
      locals := 4
      code := #[
        .enterTry 5 1,
        .call 2 "Main.boom/0" #[],
        .move 0 2,
        .leaveTry,
        .jump 11,
        .jumpIfEq 7 1 (.atom "boom"),
        .jump 10,
        .loadLit 3 (.int 3),
        .move 0 3,
        .jump 11,
        .raise 1,
        .return_ 0
      ]
    }
  ]

/-- Hand-built park-on-recv: spawn a worker then `recv` (empty mailbox → park).
Used by `Obs.Schedule` prefer-at-park observational checks. -/
def parkRecvModule : Module :=
  Module.ofFunctions "Main.main/0" #[
    {
      name := "Main.worker/0"
      arity := 0
      locals := 1
      code := #[
        .loadLit 0 (.int 1),
        .return_ 0
      ]
    },
    {
      name := "Main.main/0"
      arity := 0
      locals := 2
      code := #[
        .spawn 0 "Main.worker/0" #[],
        .recv 1,
        .return_ 1
      ]
    }
  ]

/-- Hand-built drain-siblings: entry returns `0` after spawning a short worker
that must still be drained (matches `tests/fixtures/drain_siblings.ex`). -/
def drainSiblingsModule : Module :=
  Module.ofFunctions "Main.main/0" #[
    {
      name := "Main.worker/0"
      arity := 0
      locals := 2
      code := #[
        .loadLit 0 (.int 1),
        .loadLit 1 (.int 1),
        .call 0 "+/2" #[0, 1],
        .loadLit 0 (.int 2),
        .loadLit 1 (.int 2),
        .call 0 "+/2" #[0, 1],
        .loadLit 0 (.int 1),
        .return_ 0
      ]
    },
    {
      name := "Main.main/0"
      arity := 0
      locals := 2
      code := #[
        .spawn 0 "Main.worker/0" #[],
        .loadLit 0 (.int 0),
        .return_ 0
      ]
    }
  ]

end Autumn
