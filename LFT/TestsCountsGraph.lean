import LFT.Strain
import LFT.Graphs.EdgeTypes
import LFT.Graphs.Extractors

open LFT
open LFT.Graphs

namespace LFT.TestsCountsGraph

/-- Locally override extractors for `Graph` to demonstrate non-zero counts. -/
local instance : GraphEdgeExtractors LFT.Graph where
  idVertices    _ := ["p"]
  entailsPairs  _ := [("p","q"), ("q","r")]
  excludesPairs _ := [("q","¬q")]

def Gdemo : Graph := {}

/-- structuralCounts now reflect the local extractor: [1,2,1] -/
#eval structuralCounts Gdemo

/-- entropy over [1,2,1] should be > 0 -/
#eval vN_entropy Gdemo

end LFT.TestsCountsGraph
