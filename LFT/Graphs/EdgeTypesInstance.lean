import LFT.Graphs
import LFT.Graphs.EdgeTypes
import LFT.Graphs.Extractors
import LFT.Graphs.Shadow
import LFT.Graphs.RichGraph

/-!
Concrete `HasEdgeTypeCounts Graph` instance.

Priority:
1) If an app-layer `GraphHasRichShadow Graph` instance returns some `RichGraph`,
   we use its true typed-edge counts.
2) Otherwise, we fall back to `GraphEdgeExtractors` (which your app can also override).
-/

namespace LFT
namespace Graphs

instance : HasEdgeTypeCounts LFT.Graph where
  counts (G : LFT.Graph) :=
    match (GraphHasRichShadow.toRich G) with
    | some RG => countsOf RG
    | none =>
        let ids := (GraphEdgeExtractors.idVertices G).length
        let ens := (GraphEdgeExtractors.entailsPairs G).length
        let exs := (GraphEdgeExtractors.excludesPairs G).length
        { id := ids, entails := ens, excludes := exs }

end Graphs
end LFT
