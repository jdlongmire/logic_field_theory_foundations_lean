import Mathlib.Logic.Basic

set_option autoImplicit false
namespace LFT

axiom identity (A : Prop) : A = A
axiom nonContradiction (A : Prop) : ¬ (A ∧ ¬ A)

open Classical

theorem fundamentalConsistency (P : Prop) :
    (P = P) ∧ ¬ (P ∧ ¬ P) := by
  exact And.intro (identity P) (nonContradiction P)

end LFT
