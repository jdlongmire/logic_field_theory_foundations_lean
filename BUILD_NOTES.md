## LFT Refactor Branch 2 – Build Notes
Pins: Lean v4.22.0-rc4; mathlib 8ad5cdd0e48e51d0aeb2e7a4c8472b1499b7c103

Quick verify:
  lake env lean LFT/Graphs.lean                             # typechecks
  lake env lean LFT/Examples/PlusStateFloat.lean            # prints (~0.97095, ~1.94190)

Full build (optional/CI):
  lake -v build -KleanArgs=--threads=2

Editor:
  VS Code Lean server pinned in .vscode/settings.json to rc4.
