/- LFT/ForkCore.lean — minimal fork model using ℝ, entropy kept symbolic. -/

import Mathlib.Data.Real.Basic

namespace LFT

/-- Local weights. -/
structure ForkStrainWeights where
  wI : ℝ := 1
  wN : ℝ := 1
  wE : ℝ := 1

/-- Opaque base-2 log; we do not evaluate it. -/
noncomputable opaque fork_log2 : ℝ → ℝ

/-- Symbolic base-2 entropy. -/
noncomputable def fork_entropy2 (ps : List ℝ) : ℝ :=
  ps.foldl (fun acc p => if p > 0 then acc - p * fork_log2 p else acc) 0

inductive EdgeType | identity | entailment deriving DecidableEq

structure ForkGraph where
  idEdges     : Nat
  entailEdges : Nat

namespace ForkGraph

/-- Total edge count. -/
def total (F : ForkGraph) : Nat := F.idEdges + F.entailEdges

/-- Edge distribution as reals; non-dependent `if` so `simp` can pick the branch. -/
noncomputable def edgeDistribution (F : ForkGraph) : List ℝ :=
  let t := F.total
  if t = 0 then [] else
    let tR : ℝ := (t : ℝ)
    let pId  : ℝ := (F.idEdges : ℝ) / tR
    let pEnt : ℝ := (F.entailEdges : ℝ) / tR
    [pId, pEnt]

noncomputable def vI (_ : ForkGraph) : ℝ := 0
noncomputable def vN (F : ForkGraph) : ℝ := fork_entropy2 (F.edgeDistribution)
noncomputable def vE (_ : ForkGraph) : ℝ := 0

noncomputable def D (W : ForkStrainWeights) (F : ForkGraph) : ℝ :=
  W.wI * vI F + W.wN * vN F + W.wE * vE F

@[simp] theorem vI_zero (F : ForkGraph) : vI F = 0 := rfl
@[simp] theorem vE_zero (F : ForkGraph) : vE F = 0 := rfl

end ForkGraph

def defaultWeights121 : ForkStrainWeights := { wI := 1, wN := 2, wE := 1 }
def qubitPlusFork : ForkGraph := { idEdges := 3, entailEdges := 2 }

/-- Edge distribution for qubit plus fork is [3/5, 2/5]. -/
theorem edgeDistribution_qubitPlusFork :
  ForkGraph.edgeDistribution qubitPlusFork = [(3 : ℝ) / 5, (2 : ℝ) / 5] := by
  -- `simp` reduces `if 5 = 0` to the else-branch and computes entries.
  simp [ForkGraph.edgeDistribution, ForkGraph.total, qubitPlusFork]

/-- Symbolic result: D = 2 · H₂([3/5, 2/5]). -/
theorem D_qubitPlusFork_symbolic :
  ForkGraph.D defaultWeights121 qubitPlusFork =
    (2 : ℝ) * fork_entropy2 [(3 : ℝ) / 5, (2 : ℝ) / 5] := by
  -- Expand D, collapse vI,vE via `[simp]`, and rewrite the distribution.
  simp [ForkGraph.D, ForkGraph.vN, defaultWeights121, edgeDistribution_qubitPlusFork]

end LFT
