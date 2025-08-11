import Mathlib
import LFT.Graphs

/-!
Graph edge extractors for the existing `Graph` type.

You provide how to extract:
- identity (self-loop) vertices,
- entailment pairs,
- exclusion pairs.

Default instance returns empty lists (keeps builds green).
-/

namespace LFT
namespace Graphs

abbrev PropAtom := String

class GraphEdgeExtractors (α : Type) where
  idVertices    : α → List PropAtom
  entailsPairs  : α → List (PropAtom × PropAtom)
  excludesPairs : α → List (PropAtom × PropAtom)

/-- Default: no information (all counts 0). Override with a real instance in your app. -/
instance : GraphEdgeExtractors LFT.Graph where
  idVertices    _ := []
  entailsPairs  _ := []
  excludesPairs _ := []

end Graphs
end LFT
