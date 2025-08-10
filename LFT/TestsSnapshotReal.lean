import LFT.Strain
import LFT.Entropy
import App.GraphSnapshotReal
import App.GraphShadowReal   -- uses snapshot + classifier

open LFT

def Gplain : Graph := {}

/-- Will be [] until you fill snapshot TODOs. -/
#eval LFT.structuralCounts Gplain

/-- Will be 0.0 until counts are non-zero. -/
#eval LFT.vN_entropy Gplain

/-- Dcfg uses entropy-backed vN by default; will rise once snapshot is real. -/
#eval LFT.Dcfg { useEntropyVN := true } {} Gplain
