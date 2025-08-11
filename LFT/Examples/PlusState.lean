import LFT.Strain
import LFT.Entropy
import App.GraphShadowReal

open LFT

namespace LFT.Examples.PlusState

def Gplus : Graph := {}
def cfg_on : StrainConfig := { useEntropyVN := true }
/-- Only vN contributes; factor 2. -/
def Wplus : StrainWeights := { wI := 0, wN := 2, wE := 0 }

/-- Expect counts = [3,2,0] for the .qubitPlus seed. -/
#eval LFT.structuralCounts Gplus

/-- H₂([3,2]) and 2·H₂ (base 2). -/
#eval (let h := LFT.Entropy.shannonFromCounts [3,2]; (h, 2*h))

/-- Dcfg with Wplus; should match 2·H₂ numerically. -/
#eval LFT.Dcfg cfg_on Wplus Gplus

end LFT.Examples.PlusState
