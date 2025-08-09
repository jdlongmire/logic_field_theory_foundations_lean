import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic

namespace LFT

/-- The Three Fundamental Laws of Logic -/

-- Law of Identity
axiom identity (A : Prop) : A = A

-- Law of Non-Contradiction
axiom non_contradiction (A : Prop) : ¬(A ∧ ¬A)

-- Law of Excluded Middle (already in Lean as Classical.em)
#check Classical.em

-- Verify our axioms work
example (P : Prop) : P = P := identity P
example (P : Prop) : ¬(P ∧ ¬P) := non_contradiction P

-- Our first theorem: both laws combined
theorem fundamental_consistency (P : Prop) :
  (P = P) ∧ ¬(P ∧ ¬P) :=
⟨identity P, non_contradiction P⟩

end LFT
