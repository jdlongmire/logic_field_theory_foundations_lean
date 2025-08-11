import LFT.Strain
import LFT.Graphs

/-!
LFT.Omega — provisional Ω definitions that don't disturb existing code.

- `OmegaD W` : graphs with zero total strain for weights `W`.
- `OmegaComponents W` : graphs with all three components zero.

We also link them via the existing lemma `D_zero_if_components_zero`.
-/

namespace LFT

def OmegaD (W : StrainWeights) : Set Graph := fun G => D W G = 0

def OmegaComponents (W : StrainWeights) : Set Graph :=
  fun G => vI G = 0 ∧ vN G = 0 ∧ vE G = 0

lemma mem_OmegaD_of_components_zero
  (W : StrainWeights) {G : Graph}
  (hI : vI G = 0) (hN : vN G = 0) (hE : vE G = 0) :
  G ∈ OmegaD W := by
  simpa [OmegaD] using D_zero_if_components_zero W G hI hN hE

end LFT
