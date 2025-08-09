/-
  Probability.lean - Born probability notation for LFT
  Provides the ℙ[_] notation for quantum state probabilities
-/
import LFT.Dynamics
import LFT.Graphs

namespace LFT

open Classical

/-- Born probability of outcome `G` in state `ψ` -/
notation "ℙ[" ψ "]" => fun G : Omega ↦ Complex.abs (ampOf ψ.amps G) ^ 2

/-- Helper lemma: probability of delta state -/
lemma prob_delta_self (G : Omega) (a : ℂ) (h : Complex.abs a = 1) :
    ℙ[⟨[(G, a)], by simp, by simp [listNormSq, h]⟩] G = 1 := by
  simp [ampOf, ampOf_eq_of_mem]
  rw [h]
  norm_num

end LFT
