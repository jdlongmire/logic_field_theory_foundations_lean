import Mathlib

/-!
LFT.Complex — v4.0 §3.4 Complex necessity (compile-safe scaffolding)

We introduce minimal predicates and theorem targets. Proofs will land later.
-/

namespace LFT
namespace ComplexNecessity

/-- Abstract condition meaning "this amplitude field admits a
    measurement calculus that preserves Excluded Middle in all bases". -/
def PreservesEM (K : Type) : Prop := True   -- placeholder; refined later

/-- Abstract condition meaning "this amplitude field admits orientation
    (phase) needed to distinguish directed cycles". -/
def HasPhase (K : Type) : Prop := True      -- placeholder; refined later

/-- Real amplitudes are not sufficient (basis-dependent EM failures). -/
axiom real_failure_EM : ¬ PreservesEM ℝ

/-- Quaternionic amplitudes break composition/commutativity requirements. -/
axiom quaternion_failure : True

/-- Split-complex numbers have zero divisors → bad probability norm. -/
axiom split_complex_failure : True

/-- Finite fields lack continuity/connected dynamics. -/
axiom finite_field_failure : True

/-- Minimality target: any commutative field supporting EM + phase
    sufficient for the LFT calculus embeds (uniquely up to isomorphism) into ℂ. -/
axiom complex_minimal
  {K : Type} [Field K] :
  PreservesEM K ∧ HasPhase K → Nonempty (K ≃+* ℂ)

end ComplexNecessity
end LFT
