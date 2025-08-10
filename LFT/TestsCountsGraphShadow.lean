import LFT.Strain
import LFT.Graphs.Shadow
import LFT.Graphs.RichGraph
import LFT.Graphs.EdgeTypes

open LFT
open LFT.Graphs

namespace LFT.TestsCountsGraphShadow

/-- Demo RichGraph with one of each edge type. -/
def rg1 : RichGraph :=
  { V := ({}.insert "p").insert "q",
    E := [("p","p", EdgeType.id),
          ("p","q", EdgeType.entails),
          ("q","p", EdgeType.excludes)] }

/-- Local app-layer shadow: map every Graph to `rg1` (for demo only). -/
local instance : GraphHasRichShadow LFT.Graph where
  toRich _ := some rg1

/-- Now counts on plain `Graph` reflect the RichGraph shadow. Should be [1,1,1]. -/
#eval (LFT.structuralCounts ({} : Graph))

/-- And entropy reflects equal counts. ~ log2 3 ≈ 1.585. -/
#eval (LFT.vN_entropy ({} : Graph))

end LFT.TestsCountsGraphShadow
