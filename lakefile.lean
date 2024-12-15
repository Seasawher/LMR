import Lake
open Lake DSL

package "LMR" where
  -- add package configuration options here
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «LMR» where
  -- add library configuration options here
  globs := #[.submodules `LMR]

lean_exe "lmr" where
  root := `Main
