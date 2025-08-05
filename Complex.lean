import LFT.Coherence
import Mathlib.Data.Complex.Basic

namespace LFT

/-- A measurement basis is a pair of orthogonal states -/
structure MeasurementBasis where
  plus : Omega
  minus : Omega
  orthogonal : Coherence plus minus = 0

/-- Real amplitudes violate Excluded Middle in some basis -/
theorem real_amplitude_problem : True := by
  -- TODO: Prove that real superpositions can give 50/50
  sorry

/-- Complex amplitudes preserve Excluded Middle -/
theorem complex_amplitude_solution : True := by
  -- TODO: Prove complex phase ensures definiteness
  sorry

end LFT
