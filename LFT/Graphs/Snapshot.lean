import LFT.Graphs

/-!
Graph snapshot hook (app-layer): expose finite vertices & edges.
Default returns empty lists so core stays green until you implement it.
-/

namespace LFT
namespace Graphs

abbrev PropAtom := String

structure GraphSnapshot where
  vertices : List PropAtom
  edges    : List (PropAtom × PropAtom)

class HasSnapshot (α : Type) where
  snapshot : α → GraphSnapshot

/-- Default: no info. Override in app layer. -/
instance : HasSnapshot LFT.Graph where
  snapshot _ := { vertices := [], edges := [] }

end Graphs
end LFT
