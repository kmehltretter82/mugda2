import Lake
open Lake DSL

package mugda2 where
  version := v!"0.1.0"

@[default_target]
lean_lib Mugda2 where
  roots := #[`Mugda2]

@[default_target]
lean_exe mugda2 where
  root := `Main
