import LFT.Graphs.Snapshot

/-!
App-layer snapshot provider for `LFT.Graph`.

Fill `listVertices` and `listEdges` with your real backend data.
This feeds the RichGraph shadow → typed-edge counts → vN_entropy → Dcfg.
-/

namespace App
open LFT LFT.Graphs

/-- TODO: Return your graph's vertices as `List String` (PropAtom). -/
def listVertices (_G : LFT.Graph) : List String := [
  -- e.g. "p", "q", "r"
]

/-- TODO: Return your graph's directed edges as `(src, dst)` pairs. -/
def listEdges (_G : LFT.Graph) : List (String × String) := [
  -- e.g. ("p","p"), ("p","q"), ("q","r")
]

/-- Build the snapshot from your backend. -/
def snapshotGraph (G : LFT.Graph) : GraphSnapshot :=
  { vertices := listVertices G, edges := listEdges G }

/-- Non-local app instance: activates snapshot across the app. -/
instance : HasSnapshot LFT.Graph where
  snapshot := snapshotGraph

end App
