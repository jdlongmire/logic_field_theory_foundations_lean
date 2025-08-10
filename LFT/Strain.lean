/-
LFT/Strain.lean
Implements weights, strain components, total D, and a basic lemma.
Relies on small `Graphs.lean` API.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LFT.Graphs
import LFT.Graphs.EdgeTypes
import LFT.Entropy

namespace LFT

/--
Weights for the three logical strain components:
* `wI` – internal contradiction strain
* `wN` – non-classicality strain
* `wE` – external misfit strain
-/
structure StrainWeights where
  wI : ℝ := 1.0
  wN : ℝ := 1.0
  wE : ℝ := 1.0
-- no `deriving Repr` to avoid unsafe `Real` instance

noncomputable section

/-- Internal contradiction strain via path proximity.
    Zero if no contradiction path exists; otherwise 1 / (1 + d_min). -/
noncomputable def vI (G : Graph) : ℝ :=
  match G.minContradictionDistance? with
  | none    => 0.0
  | some d  => 1.0 / (1.0 + (d : ℝ))

/-- Non-classicality strain using a simple uniform-entropy proxy
    on the count of indefinite propositions. -/
noncomputable def vN (G : Graph) : ℝ :=
  let n := G.indefiniteCount
  if h : n ≤ 1 then 0.0 else Real.log (n : ℝ)

/-- External misfit strain as a real lift of the boundary misfit score. -/
noncomputable def vE (G : Graph) : ℝ :=
  (G.boundaryMisfit : ℝ)

/-- Total logical strain functional. -/
noncomputable def D (W : StrainWeights) (G : Graph) : ℝ :=
  W.wI * vI G + W.wN * vN G + W.wE * vE G

/-- Lemma: strain is zero if all components vanish. -/
lemma D_zero_if_components_zero
    (W : StrainWeights) (G : Graph)
    (hI : vI G = 0) (hN : vN G = 0) (hE : vE G = 0) :
    D W G = 0 := by
  simp [D, hI, hN, hE]

end  -- closes `noncomputable section`

/-! # Utilities: base-2 entropy and experimental visibility hook -/

noncomputable def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- Shannon entropy in bits (base 2) for a finite list of probabilities.
    Ignores nonpositive entries. Returns 0 for empty/degenerate inputs. -/
noncomputable def entropy2 (ps : List ℝ) : ℝ :=
  ps.foldl (fun acc p => if p > 0 then acc - p * log2 p else acc) 0.0

/-- Simple visibility prediction model: V = 1 − 10^{-6} D. -/
noncomputable def predictedVisibility (Dval : ℝ) : ℝ :=
  1.0 - (1e-6 : ℝ) * Dval


end LFT

namespace LFT

/-- Provisional admissibility: all three strain components vanish. -/
def Admissible (W : StrainWeights) (G : Graph) : Prop :=
  vI G = 0 ∧ vN G = 0 ∧ vE G = 0

/-- Ω as the subtype of graphs admissible under weights W. -/
def Omega (W : StrainWeights) := { G : Graph // Admissible W G }

/-- Target theorem placeholder: admissible ↔ zero total strain (will be proved when vᵢ are final). -/
axiom admissible_iff_zero_strain (W : StrainWeights) (G : Graph) :
  Admissible W G ↔ D W G = 0

end LFT

/-! ## Non-breaking `vN` migration helpers (entropy-backed), compile-safe
We keep the current `vN` as-is. The helpers below let us compute an
entropy version side-by-side and swap in later once the edge-type
counts API is finalized.
-/

namespace LFT

/-- Placeholder hook: per-graph structural counts (to be derived from edge types).
    For now returns `[]`. -/
noncomputable def structuralCounts (G : Graph) : List Nat := []

/-- Entropy-backed alternative for non-classicality strain (Shannon in bits). -/
noncomputable def vN_entropy (G : Graph) : ℝ :=
  Entropy.shannonFromCounts (structuralCounts G)

end LFT

/-! ## Wiring `vN_entropy` to real edge-type counts (non-breaking)
We keep the existing `vN` unchanged for now. The helpers below pull
counts via the `HasEdgeTypeCounts` typeclass; your current default
instance returns zeros, so everything stays green until you add a
real instance.
-/

namespace LFT
open LFT.Graphs

/-- Generic structural-counts helper for any type with `HasEdgeTypeCounts`. -/
noncomputable def structuralCountsOf {α} [Graphs.HasEdgeTypeCounts α] (x : α) : List Nat :=
  let c := (Graphs.HasEdgeTypeCounts.counts (α := α) x)
  [c.id, c.entails, c.excludes]

/-- Specialization to your `Graph`. This will start returning real counts
once you provide a concrete `HasEdgeTypeCounts Graph` instance. -/
noncomputable def structuralCounts (G : Graph) : List Nat :=
  structuralCountsOf G

/-- Entropy-backed alternative for non-classicality strain (Shannon, bits). -/
noncomputable def vN_entropy (G : Graph) : ℝ :=
  Entropy.shannonFromCounts (structuralCounts G)

end LFT

/-! ## Configurable vN: toggle entropy-backed variant without touching `D` -/

namespace LFT

/-- Feature flag for which `vN` to use. Default keeps the current `vN`. -/
structure StrainConfig where
  useEntropyVN : Bool := false

/-- Final `vN` selected by config. -/
noncomputable def vN_final (cfg : StrainConfig) (G : Graph) : ℝ :=
  if cfg.useEntropyVN then vN_entropy G else vN G

/-- Strain using the configurable `vN`. We keep `D` unchanged for backward compat. -/
noncomputable def Dcfg (cfg : StrainConfig) (W : StrainWeights) (G : Graph) : ℝ :=
  W.wI * vI G + W.wN * vN_final cfg G + W.wE * vE G

/-- If the flag is off, `Dcfg = D`. -/
lemma Dcfg_eq_D_when_disabled
    (cfg : StrainConfig) (W : StrainWeights) (G : Graph)
    (h : cfg.useEntropyVN = false) :
    Dcfg cfg W G = D W G := by
  simp [Dcfg, vN_final, h, D]

end LFT
