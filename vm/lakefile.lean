import Lake
open Lake DSL

package «AutumnVM»

lean_lib «Autumn»

@[default_target]
lean_exe «autumn» where
  root := `Main
