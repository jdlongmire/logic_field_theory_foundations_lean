/-
Dynamics.lean
======================================
Logic Field Theory – Lean 4 formalisation
Section 6 · Dynamical Evolution (scaffold)
--------------------------------------------------

Adds:
* `dirac` : a normalised basis state
* `scaleByUnit` : a norm-preserving Hamiltonian family
  - `negHamiltonian` = scaleByUnit (-1)

All proofs explicit; file contains zero `sorry`.
-/

import LFT.Complex
import Mathlib.Data.Complex.Abs
import Mathlib.Tactic
import Mathlib.Data.List.BigOperators.Basic

open Classical
open List
open scoped BigOperators
noncomputable section
namespace LFT

/-! ---------------------------------------------------------------
### 1 Finite-support superpositions and ℓ² norm
-----------------------------------------------------------------/

abbrev AmpList : Type := List (Omega × ℂ)

/-- ℓ²-norm-squared of a finite amplitude list. -/
def listNormSq (L : AmpList) : ℝ :=
  (L.map (fun p => (Complex.abs p.snd) ^ 2)).sum

/-- Helper: remove zero entries. -/
def AmpList.clean (L : AmpList) : AmpList :=
  L.filter (fun ⟨_, c⟩ => c ≠ 0)

/--
`QuantumState`

* `amps`        – finite list of non-zero amplitudes
* `noDup`       – each graph appears at most once
* `normalised`  – ℓ²-norm = 1
-/
structure QuantumState where
  amps        : AmpList
  noDup       : (amps.map Prod.fst).Nodup
  normalised  : listNormSq amps = 1
deriving Repr

/-! ### 1.1  A concrete basis state (Dirac delta) -/

/--
`dirac G` is the pure state with amplitude 1 on graph `G`
and zero elsewhere.
-/
def dirac (G : Omega) : QuantumState :=
by
  -- single entry [(G, 1)]
  refine
  { amps := [(G, (1 : ℂ))],
    noDup := by
      simp,
    normalised := by
      -- norm² = |1|² = 1
      simp [listNormSq] }

@[simp] lemma listNormSq_single_one (G : Omega) :
    listNormSq [(G, (1 : ℂ))] = 1 := by
  simp [listNormSq]

/-! ---------------------------------------------------------------
### 2 Hamiltonians and norm preservation
-----------------------------------------------------------------/

/-- A Hamiltonian is an endomorphism on `QuantumState`. -/
abbrev Hamiltonian := QuantumState → QuantumState

/-- Property: a Hamiltonian preserves the ℓ²-norm. -/
def isNormPreserving (H : Hamiltonian) : Prop :=
  ∀ ψ, listNormSq (H ψ).amps = listNormSq ψ.amps

/-- Identity Hamiltonian preserves the norm. -/
lemma id_normPres : isNormPreserving (fun ψ => ψ) := by
  intro ψ; rfl

/--
`scaleByUnit λ hλ` multiplies every amplitude by a constant
`λ : ℂ` with `‖λ‖ = 1`.  It is norm-preserving.
-/
def scaleByUnit (λ : ℂ) (hλ : Complex.abs λ = 1) : Hamiltonian :=
  fun ψ =>
    { amps := ψ.amps.map (fun ⟨G, c⟩ => (G, c * λ)),
      noDup := by
        -- mapping preserves first components ⇒ nodup unchanged
        simpa using ψ.noDup.map _,
      normalised := by
        -- ∑ |c λ|² = |λ|² ∑ |c|² = ∑ |c|²
        simp [listNormSq, map_map, Complex.abs_mul, hλ] using
          congrArg (fun s => (s.map _).sum)
            (rfl : ψ.amps = ψ.amps) }

lemma scaleByUnit_normPres {λ : ℂ} (hλ : Complex.abs λ = 1) :
    isNormPreserving (scaleByUnit λ hλ) := by
  intro ψ
  simp [scaleByUnit, listNormSq, Complex.abs_mul, hλ]

/-- Specific norm-preserving Hamiltonian: global phase (−1). -/
def negHamiltonian : Hamiltonian :=
  scaleByUnit (-1) (by simp)

lemma neg_normPres : isNormPreserving negHamiltonian :=
  scaleByUnit_normPres (λ := -1) (by simp)

end LFT
