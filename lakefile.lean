import Lake
open Lake DSL

package lft
lean_lib LFT

-- Minimal dependency: just mathlib
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "8ad5cdd0e48e51d0aeb2e7a4c8472b1499b7c103"
