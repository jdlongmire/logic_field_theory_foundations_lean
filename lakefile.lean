import Lake
open Lake DSL

package lft
lean_lib LFT

-- Nightly-aligned deps (track latest heads)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4.git" @ "main"

require batteries from git
  "https://github.com/leanprover-community/batteries.git" @ "main"

require aesop from git
  "https://github.com/leanprover-community/aesop.git" @ "master"

require Qq from git
  "https://github.com/leanprover-community/quote4.git" @ "main"
