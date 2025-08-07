/-
  States/Basic.lean - Concrete quantum states for LFT

  This file provides concrete quantum states (|0⟩, |1⟩, |+⟩, |−⟩)
  that are used throughout the formalization for examples and proofs.
-/
import LFT.Dynamics
import LFT.Graphs
import LFT.Strain
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic

namespace LFT.States

open Classical Real Complex
open LFT.Examples  -- For trivialOmega and antiOmega

/-!
# Basic Quantum States

We need concrete states to:
1. Prove no-cloning theorem (needs superposition)
2. Test measurement theorems (needs definite and superposed states)
3. Provide examples for experiments
-/

/-- The |0⟩ state: trivialOmega basis state -/
noncomputable def ket0 : QuantumState :=
  ⟨[(trivialOmega, 1)],
   by simp,
   by simp [listNormSq]⟩

/-- The |1⟩ state: antiOmega basis state -/
noncomputable def ket1 : QuantumState :=
  ⟨[(antiOmega, 1)],
   by simp,
   by simp [listNormSq]⟩

/-- The |+⟩ state: equal superposition of |0⟩ and |1⟩ -/
noncomputable def ketPlus : QuantumState :=
  let sqrt2 := Real.sqrt 2
  ⟨[(trivialOmega, ⟨1 / sqrt2, 0⟩),
    (antiOmega, ⟨1 / sqrt2, 0⟩)],
   by simp [trivial_ne_anti, Ne.symm trivial_ne_anti],
   by simp [listNormSq, Complex.abs_ofReal, Real.sq_sqrt, zero_le_two]; norm_num⟩

/-- The |−⟩ state: equal superposition with phase -/
noncomputable def ketMinus : QuantumState :=
  let sqrt2 := Real.sqrt 2
  ⟨[(trivialOmega, ⟨1 / sqrt2, 0⟩),
    (antiOmega, ⟨-1 / sqrt2, 0⟩)],
   by simp [trivial_ne_anti, Ne.symm trivial_ne_anti],
   by simp [listNormSq, Complex.abs_ofReal, Real.sq_sqrt, zero_le_two]; norm_num⟩

/-!
## Properties of Basic States
-/

/-- ket0 is a definite (non-superposed) state -/
lemma ket0_definite :
    ∀ G ≠ trivialOmega, ampOf ket0.amps G = 0 := by
  intro G hG
  simp [ket0, ampOf, hG]

/-- ket1 is a definite (non-superposed) state -/
lemma ket1_definite :
    ∀ G ≠ antiOmega, ampOf ket1.amps G = 0 := by
  intro G hG
  simp [ket1, ampOf, hG]

/-- ketPlus is a true superposition -/
lemma ketPlus_superposition :
    ∃ G₁ G₂, G₁ ≠ G₂ ∧ ampOf ketPlus.amps G₁ ≠ 0 ∧ ampOf ketPlus.amps G₂ ≠ 0 := by
  use trivialOmega, antiOmega
  constructor
  · exact trivial_ne_anti
  constructor
  · simp [ketPlus, ampOf]
    norm_num
  · simp [ketPlus, ampOf]
    norm_num

/-- ketMinus is a true superposition -/
lemma ketMinus_superposition :
    ∃ G₁ G₂, G₁ ≠ G₂ ∧ ampOf ketMinus.amps G₁ ≠ 0 ∧ ampOf ketMinus.amps G₂ ≠ 0 := by
  use trivialOmega, antiOmega
  constructor
  · exact trivial_ne_anti
  constructor
  · simp [ketMinus, ampOf]
    norm_num
  · simp [ketMinus, ampOf]
    norm_num

/-- ket0 and ket1 are orthogonal (different basis states) -/
lemma ket0_ket1_orthogonal :
    innerProd ket0.amps ket1.amps = 0 := by
  simp [innerProd, ket0, ket1, ampOf]
  simp [trivial_ne_anti, Ne.symm trivial_ne_anti]

/-- ketPlus and ketMinus are orthogonal -/
lemma ketPlus_ketMinus_orthogonal :
    innerProd ketPlus.amps ketMinus.amps = 0 := by
  simp [innerProd, ketPlus, ketMinus, ampOf]
  -- The cross terms cancel due to the phase difference
  sorry -- Requires calculation

/-!
## Export Convenient Names
-/

/-- Standard notation: |0⟩ -/
notation "|0⟩" => ket0

/-- Standard notation: |1⟩ -/
notation "|1⟩" => ket1

/-- Standard notation: |+⟩ -/
notation "|+⟩" => ketPlus

/-- Standard notation: |−⟩ -/
notation "|−⟩" => ketMinus

end LFT.States
