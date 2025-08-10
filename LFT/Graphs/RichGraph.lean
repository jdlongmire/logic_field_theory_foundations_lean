import Mathlib
import LFT.Graphs
import LFT.Graphs.EdgeTypes

/-!
LFT.Graphs.RichGraph
A non-breaking, richer graph that stores typed edges. It provides a
`HasEdgeTypeCounts` instance so `vN_entropy` can use real counts
without changing your existing `Graph`.
-/

namespace LFT
namespace Graphs

abbrev PropAtom := String

/-- Rich graph with explicit typed edges. -/
structure RichGraph where
  V : Finset PropAtom := {}
  /-- Edge list as (source, target, edge-type). -/
  E : List (PropAtom × PropAtom × EdgeType) := []
deriving Repr

/-- Count typed edges for `RichGraph`. -/
noncomputable def countsOf (G : RichGraph) : EdgeTypeCounts :=
  G.E.foldl
    (fun c e =>
      match e with
      | (_, _, EdgeType.id)      => { c with id := c.id + 1 }
      | (_, _, EdgeType.entails) => { c with entails := c.entails + 1 }
      | (_, _, EdgeType.excludes)=> { c with excludes := c.excludes + 1 })
    { id := 0, entails := 0, excludes := 0 }

/-- Provide counts via the typeclass. -/
instance : HasEdgeTypeCounts RichGraph where
  counts := countsOf

end Graphs
end LFT
