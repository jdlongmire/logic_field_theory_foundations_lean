import Mathlib

/-!
LFT.Linearity — v4.0 linearity uniqueness scaffolding
Stay abstract; no Hilbert dependency yet.
-/

namespace LFT
namespace Linearity

/-- Opaque state type for schema. -/
constant State : Type

/-- Placeholder: only linear combination preserves constraints. -/
axiom linearity_unique : True

end Linearity
end LFT
