import LFT.Graphs
import LFT.Graphs.RichGraph
import LFT.Graphs.Shadow
import LFT.Graphs.Snapshot
import LFT.Graphs.EdgeTypes
import App.EdgeClassifier

/-!
App-layer shadow: build RichGraph from your Graph snapshot using a classifier.
-/

namespace App
open LFT
open LFT.Graphs

/-- Convert a core Graph to a RichGraph using the app snapshot & classifier. -/
def toRichGraph (G : LFT.Graph) : Option RichGraph :=
  let snap := (HasSnapshot.snapshot G)
  let V    := snap.vertices.foldl (fun acc v => acc.insert v) ({} : Finset String)
  let E : List (String × String × EdgeType) :=
    snap.edges.map (fun (vw : String × String) =>
      let v := vw.fst; let w := vw.snd
      if EdgeClassifier.isId v w then (v, w, EdgeType.id)
      else if EdgeClassifier.isExcludes v w then (v, w, EdgeType.excludes)
      else (v, w, EdgeType.entails))
  if V.isEmpty ∧ E.isEmpty then none else some { V := V, E := E }

/-- Non-local instance: activates shadow for all `Graph` values using snapshot+classifier. -/
instance : GraphHasRichShadow LFT.Graph where
  toRich := toRichGraph

end App
