import Mathlib
import LFT.Graphs
import LFT.Strain

namespace LFT

/-- default config (flag off) -/
def cfg0 : StrainConfig := {}

/-- trivial graph (your scaffold treats this as empty) -/
def G00 : Graph := {}

/-- With flag off, `Dcfg` equals the original `D`. -/
lemma Dcfg_eq_D_G00 (W : StrainWeights) :
  Dcfg cfg0 W G00 = D W G00 := by
  have h : cfg0.useEntropyVN = false := rfl
  simpa [cfg0] using Dcfg_eq_D_when_disabled cfg0 W G00 h

end LFT
