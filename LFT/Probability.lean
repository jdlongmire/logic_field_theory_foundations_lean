/-
  Probability.lean - Born probability notation for LFT
  Provides the ℙ[_] notation for quantum state probabilities
-/
import LFT.Dynamics
import LFT.Graphs

namespace LFT

open Classical

/-- Extract amplitude for a specific graph from state's amplitude list -/
noncomputable def ampOf (amps : List (Omega × ℂ)) (G : Omega) : ℂ :=
  (amps.find? (fun p => p.1 = G)).map (·.2) |>.getD 0

/-- Born probability of outcome `G` in state `ψ` -/
notation "ℙ[" ψ "]" => fun G : Omega ↦ Complex.abs (ampOf ψ.amps G) ^ 2

/-- Helper lemma: probability of delta state -/
lemma prob_delta_self (G : Omega) (a : ℂ) (h : Complex.abs a = 1) :
    ℙ[⟨[(G, a)], by simp, by simp [listNormSq, h]⟩] G = 1 := by
  simp [ampOf]
  rw [h]
  norm_num

end LFT