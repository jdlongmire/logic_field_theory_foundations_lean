import Mathlib
import LFT.Graphs
import LFT.Strain
import LFT.Omega

namespace LFT
open Classical

/-- Trivial graph using defaults from `LFT.Graphs`. -/
def G0 : Graph := {}

/-- Components vanish on G0 with the current placeholders. -/
lemma G0_components_zero :
  vI G0 = 0 ∧ vN G0 = 0 ∧ vE G0 = 0 := by
  -- All three helpers return 0/none in the current scaffold
  have hI : vI G0 = 0 := by
    simp [vI, Graph.minContradictionDistance?]
  have hN : vN G0 = 0 := by
    simp [vN, Graph.indefiniteCount]
  have hE : vE G0 = 0 := by
    simp [vE, Graph.boundaryMisfit]
  exact And.intro hI (And.intro hN hE)

/-- Therefore the total strain is zero for any weights. -/
lemma G0_strain_zero (W : StrainWeights) : D W G0 = 0 := by
  rcases G0_components_zero with ⟨hI, hN, hE⟩
  simpa [D, hI, hN, hE] using D_zero_if_components_zero W G0 hI hN hE

end LFT

/-- By the same token, `G0` is in Ω defined via total strain. -/
lemma G0_mem_OmegaD (W : StrainWeights) : G0 ∈ LFT.OmegaD W := by
  have h := G0_strain_zero W
  simpa [LFT.OmegaD] using h
