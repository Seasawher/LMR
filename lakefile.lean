import Lake
open Lake DSL

package "LMR" where
  -- add package configuration options here

lean_lib «LMR» where
  -- add library configuration options here

@[default_target]
lean_exe "lmr" where
  root := `Main
