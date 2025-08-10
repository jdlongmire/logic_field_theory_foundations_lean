import Lake
open Lake DSL

package lft
lean_lib LFT

-- pin mathlib to today's working commit
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5646947707336a76476970763750a65107448834"

-- optional: pin a ProofWidgets release (prebuilt assets = less npm churn)
require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4.git" @ "v0.0.68"
