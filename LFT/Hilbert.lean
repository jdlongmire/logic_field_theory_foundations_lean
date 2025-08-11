import Mathlib
import LFT.Graphs

/-!
LFT.Hilbert — minimal free vector space scaffold (compile-safe)
We use Graph as a provisional basis. Later we'll switch to Ω (admissible graphs).
No inner product yet; just a vector space and a `ket`.
-/

namespace LFT
namespace Hilbert

open Classical

/-- Provisional basis: graphs. Later: subtype of admissible graphs. -/
abbrev BasisVec := Graph

/-- Free vector space over ℂ with finite support. -/
abbrev V := BasisVec →₀ ℂ

/-- Dirac-style embedding of a basis vector. -/
noncomputable def ket (b : BasisVec) : V :=
  Finsupp.single b (1 : ℂ)

end Hilbert
end LFT
