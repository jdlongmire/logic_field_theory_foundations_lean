import LFT.Graphs
import LFT.Graphs.RichGraph
import LFT.Graphs.Shadow
import LFT.Graphs.Snapshot
import LFT.Graphs.EdgeTypes
import App.EdgeClassifier
import App.Data.Seed

/-!
App-layer shadow: build a `RichGraph` from either
1) your app snapshot (if provided), or
2) a selected seed dataset (fallback).

This feeds typed-edge counts → vN_entropy → Dcfg.
-/

namespace App
open LFT
open LFT.Graphs

/-- Pick which built-in seed dataset to expose if the app snapshot is empty. -/
inductive Scenario | classical | entailment | superposition | epr
deriving Repr, DecidableEq

/-- Change this to try different seeds quickly. -/
def activeScenario : Scenario := .epr

/-- Resolve the active seed dataset. -/
def pickDataset : App.Data.Dataset :=
  match activeScenario with
  | .classical     => App.Data.classical
  | .entailment    => App.Data.entailment_chain
  | .superposition => App.Data.superposition_precursor
  | .epr           => App.Data.epr_correlation

/-- Convert a core `Graph` to a `RichGraph` using snapshot + classifier.
    If the app snapshot has no data, we fall back to the selected seed. -/
def toRichGraph (G : LFT.Graph) : Option RichGraph :=
  let snapCore := (HasSnapshot.snapshot G)
  let snapSeed :=
    let d := pickDataset
    { vertices := d.vertices, edges := d.edges }
  -- prefer app snapshot when non-empty
  let snap :=
    if snapCore.vertices ≠ [] ∨ snapCore.edges ≠ [] then snapCore else snapSeed
  -- build Finset of vertices
  let V : Finset String := snap.vertices.foldl (fun acc v => acc.insert v) ({} : Finset String)
  -- classify each edge
  let E : List (String × String × EdgeType) :=
    snap.edges.map (fun (vw : String × String) =>
      let v := vw.fst; let w := vw.snd
      if EdgeClassifier.isId v w then (v, w, EdgeType.id)
      else if EdgeClassifier.isExcludes v w then (v, w, EdgeType.excludes)
      else (v, w, EdgeType.entails))
  let emptyV := V.card = 0
  let emptyE := E = []
  if emptyV ∧ emptyE then none else some { V := V, E := E }

/-- Non-local instance: activates the shadow for all `Graph` values. -/
instance : GraphHasRichShadow LFT.Graph where
  toRich := toRichGraph

end App
