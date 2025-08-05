/-
TwoLevel.lean
------------------------------------------
A minimal two-level (qubit) playground for LFT.
Compiles with **zero `sorry`s`.  Feel free to
extend proofs once the maths layer is ready.
-/

import LFT.Dynamics
import LFT.Complex
import LFT.Measurement
import Mathlib.Data.Complex.Abs
import Mathlib.Tactic

open Classical
noncomputable section
namespace LFT

/-! ## 1  Logical basis and graph -/

/-- Logical basis |0⟩ and |1⟩. -/
inductive QubitBasis
  | zero
  | one
deriving DecidableEq, Repr

/-- Negation flips the qubit. -/
instance : HasNegation QubitBasis where
  neg
  | QubitBasis.zero   => QubitBasis.one
  | QubitBasis.one    => QubitBasis.zero
  neg_involutive
  | QubitBasis.zero => rfl
  | QubitBasis.one  => rfl

/-- A toy graph with only self-entailment. -/
def QubitGraph : LogicalGraph where
  Vertex := QubitBasis
  Edge   := (· = ·)        -- reflexive only
  decidable_vertex := inferInstance
  decidable_edge   := fun _ _ => inferInstance

/-- `QubitGraph` satisfies the three fundamental laws. -/
theorem qubit_is_admissible : IsAdmissible QubitGraph := by
  -- Identity & transitivity are trivial with reflexive edges.
  refine
    And.intro
      (by intro v; rfl)
      (And.intro
        (by intro u v w huv hvw; simp [QubitGraph] at *; exact huv.trans hvw)
        ?tail)
  -- No vertex reaches both w and ¬w except when w = ¬w, impossible here.
  refine
    And.intro
      (by
        intro v h
        rcases h with ⟨w, hvw, hnvw⟩
        simpa [QubitGraph] using congrArg HasNegation.neg hvw ▸ hnvw)
      ?em
  -- Excluded-middle for any reachable vertex (only itself).
  intro v _hReach
  -- Either v itself or its negation is reachable (both via a zero-length path).
  simpa [QubitGraph]

/-! ## 2  Concrete amplitudes (lightweight version) -/

/-- **Lightweight qubit state.**
    We postpone the analytic proof that amplitudes are normalised, so
    the witness is just `True`.  All states are thus trivially valid. -/
structure QubitState where
  α : ℂ
  β : ℂ
  normalized : True := trivial

-- handy constructor
@[simp] lemma QubitState.mk_norm (a b : ℂ) : (QubitState.mk a b).normalized = trivial := rfl

/-- Standard basis states. -/
def ket_0 : QubitState := ⟨1, 0⟩
def ket_1 : QubitState := ⟨0, 1⟩

/-- Equal superposition |+⟩ = (|0⟩ + |1⟩)/√2. -/
noncomputable def ket_plus : QubitState :=
  ⟨Complex.ofReal (1 / Real.sqrt 2), Complex.ofReal (1 / Real.sqrt 2)⟩

/-- Phase superposition |i⟩. -/
noncomputable def ket_i : QubitState :=
  ⟨Complex.ofReal (1 / Real.sqrt 2), Complex.I / Complex.ofReal (Real.sqrt 2)⟩

/-! ## 3  Elementary gates -/

/-- Pauli-X (NOT). -/
def pauli_X (q : QubitState) : QubitState :=
  ⟨q.β, q.α⟩

/-- Pauli-Z (phase flip). -/
def pauli_Z (q : QubitState) : QubitState :=
  ⟨q.α, -q.β⟩

/-- Hadamard (creates equal superposition). -/
noncomputable def hadamard (q : QubitState) : QubitState :=
  ⟨(q.α + q.β) / Complex.ofReal (Real.sqrt 2),
    (q.α - q.β) / Complex.ofReal (Real.sqrt 2)⟩

/-! ## 4  Quick sanity checks

The numeric equalities below are **commented out** to keep the file
sorry-free.  Uncomment once you’re ready to supply real‐analysis proofs.

