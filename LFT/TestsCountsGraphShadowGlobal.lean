import LFT.Strain
import LFT.Entropy
import LFT.Graphs.EdgeTypes
import App.GraphShadowReal

open LFT

/-- Plain core Graph value. -/
def Gplain : Graph := {}

/-- With the app-layer shadow active, structuralCounts are [1,1,1]. -/
#eval LFT.structuralCounts Gplain

/-- Entropy should be ~ log2 3 ≈ 1.58496. -/
#eval LFT.vN_entropy Gplain

/-- Since the `vN` flag is ON by default, Dcfg now includes that entropy. -/
def cfg_on : StrainConfig := { useEntropyVN := true }
def W1 : StrainWeights := {}

#eval LFT.Dcfg cfg_on W1 Gplain

/-- Visibility hook reflects the strain value. -/
#eval LFT.predictedVisibility (LFT.Dcfg cfg_on W1 Gplain)
