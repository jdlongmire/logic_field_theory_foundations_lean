import LFT.Graphs
import LFT.Graphs.RichGraph
import LFT.Graphs.Shadow
import LFT.Graphs.EdgeTypes

/-!
App-layer: provide a real (for now: demo) mapping from `Graph` → `RichGraph`.
This activates entropy-based vN for plain `Graph` via the shadow hook.
-/

namespace App
open LFT
open LFT.Graphs

/-- Demo RichGraph: one of each edge type. Replace with your real converter later. -/
def rg_demo : RichGraph :=
  { V := ({}.insert "p").insert "q",
    E := [("p","p", EdgeType.id),
          ("p","q", EdgeType.entails),
          ("q","p", EdgeType.excludes)] }

/-- Real converter placeholder: always returns `rg_demo` for now. -/
def toRichGraph (G : LFT.Graph) : Option RichGraph := some rg_demo

/-- Non-local instance: activates shadow for all `Graph` values. -/
instance : GraphHasRichShadow LFT.Graph where
  toRich := toRichGraph

end App
