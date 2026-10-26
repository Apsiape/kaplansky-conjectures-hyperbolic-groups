import Lake
open Lake DSL

package KaplanskyLean where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

/-- Vendored from openai/math (commit 1581d4c, Apache-2.0); see OAI/VENDOR.md. -/
lean_lib OAI where
  globs := #[.andSubmodules `OAI]

@[default_target]
lean_lib Kaplansky where
  globs := #[.andSubmodules `Kaplansky]
