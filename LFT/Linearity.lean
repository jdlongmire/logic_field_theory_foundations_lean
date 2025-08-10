import Mathlib

/-!
LFT.Linearity — v4.0 §2 Linearity uniqueness (compile-safe scaffolding)

Stay abstract: define a combination operator and a probability functional,
state the constraints, and expose a theorem target to prove later.
-/

namespace LFT
namespace Linearity

/-- Abstract state space (will later be Hilbert states). -/
constant State : Type

/-- Distinguished outcomes corresponding to A and ¬A. -/
constant A : State
constant nA : State

/-- Abstract combination operator over some coefficient type `K`. -/
structure CombSchema (K : Type) where
  combine : State → State → K → K → State

/-- Probability functional: P outcome given state. -/
structure Prob where
  P : State → State → ℝ

/-- Excluded Middle (normalization) constraint schema. -/
def EM_ok (Pr : Prob) : Prop :=
  ∀ S, Pr.P A S + Pr.P nA S = 1

/-- Boundary conditions: definite inputs stay definite. -/
def boundary_ok {K} (C : CombSchema K) : Prop :=
  True  -- refined later

/-- Non-Contradiction proxy: no joint A ∧ ¬A (schema-level). -/
def non_contra_ok (Pr : Prob) : Prop :=
  True  -- refined later

/-- The target statement: under EM + boundary + non-contradiction,
    only *linear* combination survives (to be formalized later). -/
axiom linearity_unique {K : Type} (C : CombSchema K) (Pr : Prob) :
  EM_ok Pr ∧ boundary_ok C ∧ non_contra_ok Pr → True

end Linearity
end LFT
