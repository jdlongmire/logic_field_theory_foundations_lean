import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
LFT.Entropy — helpers for Shannon entropy (base 2) and normalization.
Standalone by design; we will wire this into vN later without breaking current code.
-/

namespace LFT
namespace Entropy

noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- Sum of a list of reals. -/
noncomputable def sum (xs : List ℝ) : ℝ :=
  xs.foldl (· + ·) 0

/-- Normalize a list of nonnegative reals to probabilities.
    Returns `[]` if the sum is 0 (so entropy of that list is 0). -/
noncomputable def normalize (xs : List ℝ) : List ℝ :=
  let s := sum xs
  if s = 0 then [] else xs.map (· / s)

/-- Shannon entropy in bits for a probability list.
    Ignores nonpositive entries; 0 on empty/degenerate input. -/
noncomputable def shannon (ps : List ℝ) : ℝ :=
  ps.foldl (fun acc p => if p > 0 then acc - p * log2 p else acc) 0

/-- Convenience: entropy from integer counts. -/
noncomputable def shannonFromCounts (counts : List Nat) : ℝ :=
  let xs : List ℝ := counts.map (fun n => (n : ℝ))
  shannon (normalize xs)

end Entropy
end LFT
