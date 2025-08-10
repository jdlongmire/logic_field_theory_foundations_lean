import Mathlib

/-!
LFT.Hilbert — v4.0 §5 scaffolding
Defines opaque placeholders for the graph-based basis, free space, and a state type.
We’ll replace these with real constructions after the branch skeleton is stable.
-/

namespace LFT
namespace Hilbert

/-- Opaque basis element; will become {|G⟩ : G ∈ Ω}. -/
constant BasisVec : Type

/-- Free vector space placeholder over ℂ. -/
constant V : Type

/-- Completed Hilbert space placeholder. -/
constant ℋ : Type

/-- Map from basis to vectors (Dirac ket) — placeholder signature. -/
constant ket : BasisVec → V

end Hilbert
end LFT
