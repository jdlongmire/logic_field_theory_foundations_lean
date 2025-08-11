import Mathlib

namespace LFT
namespace Predictions

/-- Interference visibility modification: V_LFT = V_QM * (1 - κ * D). -/
structure InterferenceParams where
  V_QM : ℝ
  κ : ℝ
  D : ℝ

noncomputable def V_LFT (p : InterferenceParams) : ℝ :=
  p.V_QM * (1 - p.κ * p.D)

end Predictions
end LFT
