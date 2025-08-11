import Mathlib

/-!
LFT.Measurement.Normalization — v4.0 §7 skeleton
Goal: formal route that the only probability functional compatible with
normalization and scaling is F(x) = x^2 (Born rule).
We keep this compile-safe: clean statements + TODO proof notes.
-/

namespace LFT
namespace Measurement

/-- Probability functional over nonnegative amplitudes.
    Domain is ℝ≥0 to reflect magnitude (|ψ(G)|). -/
abbrev ProbFun := (ℝ≥0 → ℝ≥0)

/-- Normalization constraint for a finite outcome family. -/
def normalized (F : ProbFun) (xs : List ℝ≥0) : Prop :=
  (xs.map (fun x => F x)).foldl (· + ·) 0 = 1

/-- Scaling compatibility:
    For any α ≥ 0, scaling amplitudes by α scales probabilities by α^2. -/
def scaling_ok (F : ProbFun) : Prop :=
  ∀ (α x : ℝ≥0), F (α * x) = α^2 * F x

/-- Additivity over disjoint outcomes (finite additivity). -/
def additive_ok (F : ProbFun) : Prop :=
  ∀ (x y : ℝ≥0), F x + F y = F (x) + F (y)  -- placeholder, refined later

/-- Target statement (skeleton): Born from scaling + normalization.
    TODO: strengthen `additive_ok` to the exact finite-additivity we need,
    then prove uniqueness of F(x)=x^2 up to normalization. -/
axiom born_from_scaling_normalization
  (F : ProbFun) :
  scaling_ok F → (∀ xs, normalized F xs) → True  -- TODO: conclude F = (·)^2

end Measurement
end LFT
