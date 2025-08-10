/-
LFT/Fork.lean
Pre-quantum “fork” graph model to address circularity concerns.
No quantum concepts assumed: just counts of edge categories.

We keep this separate from LFT.Graphs to avoid API coupling and any hint of circularity.
-/
import Mathlib.Init
import LFT.Strain

namespace LFT

/-- Edge categories used in the fork model. -/
inductive EdgeType
| identity     -- self / coherence edge
| entailment   -- root → branch entailment
deriving DecidableEq

/-- Minimal fork graph: counts by edge category. -/
structure ForkGraph where
  idEdges     : Nat
  entailEdges : Nat
deriving Repr

namespace ForkGraph

/-- Total edge count. -/
def total (F : ForkGraph) : Nat :=
  F.idEdges + F.entailEdges

/-- Edge distribution as probabilities (ℝ). -/
noncomputable def edgeDistribution (F : ForkGraph) : List ℝ :=
  let t : ℝ := (F.total : Nat)
  if h : t = 0 then [] else
    let pId  : ℝ := (F.idEdges     : Nat) / t
    let pEnt : ℝ := (F.entailEdges : Nat) / t
    [pId, pEnt]

/-- Internal contradiction strain for the fork model: none by construction. -/
noncomputable def vI (F : ForkGraph) : ℝ := 0.0

/-- Non-classicality via base-2 entropy of edge categories. -/
noncomputable def vN (F : ForkGraph) : ℝ :=
  entropy2 (F.edgeDistribution)

/-- No environment misfit in the isolated fork model. -/
noncomputable def vE (F : ForkGraph) : ℝ := 0.0

/-- Total strain for fork graphs using generic weights. -/
noncomputable def D (W : StrainWeights) (F : ForkGraph) : ℝ :=
  W.wI * vI F + W.wN * vN F + W.wE * vE F

end ForkGraph

/-- Default weights emphasizing vN per reviewer: 1:2:1 ratio. -/
def defaultWeights121 : StrainWeights :=
  { wI := 1.0, wN := 2.0, wE := 1.0 }

/-- Reviewer’s qubit-plus-like fork: 3 identity edges, 2 entailment edges. -/
def qubitPlusFork : ForkGraph :=
  { idEdges := 3, entailEdges := 2 }

end LFT
