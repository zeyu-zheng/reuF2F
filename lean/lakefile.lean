import Lake
open Lake DSL

package «reuF2F»

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

/-- Trusted task export commands. -/
lean_lib Export

@[default_target]
lean_lib «reuF2F» where
  globs := #[.andSubmodules `reuF2F]
