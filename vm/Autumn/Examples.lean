import Autumn.Instr

namespace Autumn

/-- Hand-built `add_main` module (same as tests/fixtures/add_main.bc.json). -/
def addMainModule : Module where
  version := 1
  entry := "Main.main/0"
  functions := #[
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

end Autumn
