import LFT.Strain
import LFT.Entropy
import LFT.Graphs.Snapshot
import LFT.Graphs.EdgeTypes
import App.GraphShadowReal
import App.EdgeClassifier

open LFT
open LFT.Graphs

namespace LFT.TestsSnapshotPipeline

-- Local demo snapshot: vertices = {p,q}, edges = {(p,p), (p,q)}
local instance : HasSnapshot LFT.Graph where
  snapshot _ := { vertices := ["p","q"], edges := [("p","p"), ("p","q")] }

def Gdemo : Graph := {}

/-- structuralCounts should reflect { id=1, entails=1, excludes=0 } → [1,1,0] -/
#eval LFT.structuralCounts Gdemo

/-- entropy should be entropy([1,1,0]) = entropy([1,1]) ≈ 1.0 bit -/
#eval LFT.vN_entropy Gdemo

/-- With flag ON by default, Dcfg includes vN_entropy (wI,vE still 0). -/
def cfg_on : StrainConfig := { useEntropyVN := true }
def W1 : StrainWeights := {}
#eval LFT.Dcfg cfg_on W1 Gdemo

end LFT.TestsSnapshotPipeline
