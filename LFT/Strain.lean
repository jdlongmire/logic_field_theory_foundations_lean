/-
LFT/Strain.lean
Implements weights, strain components, total D, and a basic lemma.
Relies on small `Graphs.lean` API.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LFT.Graphs

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

end LFT
