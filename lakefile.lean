import Lake
open Lake DSL

-- Updated to v4.29.0 for integration with catept-main.
-- LeanCopilot and lean4-parser removed: incompatible with v4.29.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0"

package "lean-inf" where
  leanOptions := #[
    ⟨`autoImplicit, true⟩
  ]

lean_lib «LeanInf» where
  -- add library configuration options here

@[default_target]
lean_exe "lean-inf" where
  root := `Main
