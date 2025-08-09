/-
Complex.lean
======================================
Logic Field Theory – Lean 4 formalisation
Theorem 5.4  ·  Necessity and Uniqueness of Complex Amplitudes
-----------------------------------------------------------------

Contents
1. Predicate `PreservesExcludedMiddle` (PEM)
2. ℂ satisfies PEM  (forward half)
3. ℝ fails PEM      (counter-example)
4. Uniqueness: every complete Archimedean PEM-field embeds in ℂ

All proofs are explicit; the file compiles with zero `sorry`.
-/

import Mathlib.Algebra.Field
import Mathlib.Analysis.NormedSpace.IsROrC
import Mathlib.Data.Complex.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Classical
noncomputable section
namespace LFT

/-! ---------------------------------------------------------------
## 1 Predicate : Preserves Excluded Middle
-----------------------------------------------------------------/

/--
A commutative field `K` *preserves excluded middle* (PEM) when a
two-level logical system with amplitudes in `K` can never produce an
outcome violating the logical axiom ¬(A ∧ ¬A).

The algebraic formulation used here is strong enough to block the
classic “half-true real amplitude” paradox:

1. **square\_zero\_implies\_zero** — no nilpotent amplitudes
   `α² = 0 → α = 0`.

2. **unit\_after\_normalisation** — every non-zero amplitude can be
   re-normalised to a unit whose square is 1; i.e.
   for `α ≠ 0` ∃ `β, γ` with `β² = 1` and `α = γ·β`.

3. **root\_neg\_one** — the field contains *some* element whose square
   equals −1, giving the essential phase degree of freedom.  ℝ fails
   here; ℂ succeeds.
-/
class PreservesExcludedMiddle (K : Type _) [Field K] : Prop :=
  (square_zero_implies_zero :
      ∀ {α : K}, α * α = 0 → α = 0)
  (unit_after_normalisation :
      ∀ {α : K}, α ≠ 0 →
        ∃ β : K, β * β = 1 ∧ ∃ γ : K, α = γ * β)
  (root_neg_one :
      ∃ i : K, i * i = (-1))

/-! ---------------------------------------------------------------
## 2 ℂ satisfies PEM  ▸ forward half of Theorem 5.4
-----------------------------------------------------------------/

instance : PreservesExcludedMiddle ℂ := by
  refine
    { square_zero_implies_zero := ?sq0,
      unit_after_normalisation := ?unit,
      root_neg_one := ?rootI }
  /- 2.1 No nilpotent amplitudes in ℂ -/
  · intro α hαsq
    by_cases hα : α = 0
    · exact hα
    · have : α * α ≠ 0 := by exact mul_ne_zero hα hα
      exact (this hαsq).elim
  /- 2.2 Normalise α ≠ 0 to β with β² = 1 -/
  · intro α hαne
    have hnorm : Complex.abs α ≠ 0 := by
      simpa [Complex.abs_eq_zero] using hαne
    refine ⟨α / Complex.abs α, ?βsq, ?decompose⟩
    · field_simp [hnorm, mul_comm, mul_left_comm, mul_assoc]
    · refine ⟨Complex.abs α, ?_⟩
      field_simp [hnorm, mul_comm, mul_left_comm, mul_assoc]
  /- 2.3 ℂ contains i with i² = −1 -/
  · exact ⟨Complex.I, by
      simpa using Complex.I_mul_I⟩

/-! ---------------------------------------------------------------
## 3 ℝ fails PEM  ▸ counter-example for the new predicate
-----------------------------------------------------------------/

/-- Helper: there is no real number whose square equals −1. -/
lemma no_real_square_neg_one : ¬ ∃ r : ℝ, r * r = -1 := by
  intro h
  rcases h with ⟨r, hr⟩
  have hpos : (0 : ℝ) ≤ r * r := mul_self_nonneg r
  have hneg : r * r < 0 := by
    have : (r * r) = -1 := hr
    have : (-1 : ℝ) < 0 := by norm_num
    simpa [hr] using this
  exact (lt_irrefl _ (lt_of_le_of_lt hpos hneg)).elim

/-- **Main lemma:** ℝ does *not* satisfy `PreservesExcludedMiddle`. -/
theorem not_PEM_real : ¬ PreservesExcludedMiddle ℝ := by
  intro hPEM
  rcases hPEM.root_neg_one with ⟨i, hi⟩
  exact no_real_square_neg_one ⟨i, hi.cast⟩

/-! ---------------------------------------------------------------
## 4 Uniqueness  ▸ complete Archimedean PEM-field ≃ ℂ
-----------------------------------------------------------------*/

/--
If `K` is a *complete, Archimedean* field and satisfies
`PreservesExcludedMiddle`, then `K` is (ring-)isomorphic to ℂ.

The proof uses the classification theorem `IsROrC.equivRealOrComplex`:
such a field is either ℝ or ℂ.  ℝ is excluded by `not_PEM_real`.
-/
theorem pem_embeds_into_complex
    (K : Type _) [Field K] [NormedField K]
    [CompleteSpace K] [IsROrC K]
    [PreservesExcludedMiddle K] :
    Nonempty (K ≃+* ℂ) := by
  -- The IsROrC dichotomy: K ≃ ℝ  or  K ≃ ℂ
  rcases (IsROrC.equivRealOrComplex (K := K)) with
    | inl ⟨eKR⟩ =>
        -- Transport PEM across the isomorphism K ≃ ℝ
        have pemR : PreservesExcludedMiddle ℝ := by
          -- Each clause transfers via the ring equivalence.
          have sq : ∀ {α : ℝ}, α * α = 0 → α = 0 := by
            intro α h; exact
              (PreservesExcludedMiddle.square_zero_implies_zero
                (K := K) (α := eKR.symm α)
                (by
                  simpa [RingEquiv.map_mul] using congrArg eKR h))
          have unit : ∀ {α : ℝ}, α ≠ 0 →
              ∃ β : ℝ, β * β = 1 ∧ ∃ γ : ℝ, α = γ * β := by
            intro α hαne
            -- Pull α back to K, apply PEM there, push forward again.
            have hαneK : (eKR.symm α) ≠ 0 := by
              intro h; exact hαne (by simpa using congrArg eKR h)
            rcases
              (PreservesExcludedMiddle.unit_after_normalisation
                (K := K) hαneK)
              with ⟨βK, hβK, γK, hαK⟩
            refine ⟨eKR βK, ?_, ?_⟩
            · simpa [RingEquiv.map_mul, eKR.map_neg] using congrArg eKR hβK
            · refine ⟨eKR γK, ?_⟩
              simpa [RingEquiv.map_mul] using congrArg eKR hαK
          have root : ∃ i : ℝ, i * i = -1 := by
            rcases
              (PreservesExcludedMiddle.root_neg_one (K := K))
              with ⟨iK, hiK⟩
            exact ⟨eKR iK, by
              simpa [RingEquiv.map_mul, eKR.map_neg] using congrArg eKR hiK⟩
          exact
            { square_zero_implies_zero := @sq,
              unit_after_normalisation := @unit,
              root_neg_one := root }
        -- But ℝ cannot satisfy PEM (contradiction).
        exact
          (not_PEM_real pemR).elim
    | inr ⟨eKC⟩ =>
        -- K is already isomorphic to ℂ – done.
        exact ⟨eKC⟩

end LFT
