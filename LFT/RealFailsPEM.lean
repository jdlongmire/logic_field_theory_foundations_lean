/-
RealFailsPEM.lean
========================================
ℝ does **not** satisfy the strengthened
`PreservesExcludedMiddle` predicate.

This file depends only on:
  • LFT.Complex   (for the predicate)
  • basic real-number lemmas
-/

import LFT.Complex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Classical
noncomputable section
namespace LFT

/- Auxiliary: there is no real r with r² = -1. -/
lemma no_real_square_neg_one : ¬ ∃ r : ℝ, r * r = -1 := by
  intro h
  rcases h with ⟨r, hr⟩
  have hpos : (0 : ℝ) ≤ r * r := mul_self_nonneg r
  have hneg : r * r < 0 := by
    have : (r * r) = -1 := hr
    have : (-1 : ℝ) < 0 := by norm_num
    simpa [this] using congrArg (fun x : ℝ => x) hr ▸ this
  exact (lt_irrefl _ (lt_of_le_of_lt hpos hneg)).elim

/-- **Main lemma:** ℝ fails PEM. -/
theorem not_PEM_real : ¬ PreservesExcludedMiddle ℝ := by
  intro hPEM
  rcases hPEM.root_neg_one with ⟨i, hi⟩
  exact no_real_square_neg_one ⟨i, hi⟩

end LFT
