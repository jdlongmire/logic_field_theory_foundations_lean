import LFT.Strain
import LFT.Graphs.RichGraph
import LFT.Graphs.EdgeTypes
import LFT.Entropy

open LFT
open LFT.Graphs

/-- Rich graph with 1 id, 1 entails, 1 excludes. -/
def rg_demo : RichGraph :=
  { V := ({}.insert "p").insert "q",
    E := [("p","p", EdgeType.id),
          ("p","q", EdgeType.entails),
          ("q","p", EdgeType.excludes)] }

/-- Structural counts should be [1,1,1]. -/
#eval LFT.structuralCountsOf rg_demo

/-- Entropy (in bits) should be close to log2 3 ≈ 1.58496. -/
#eval LFT.Entropy.shannonFromCounts (LFT.structuralCountsOf rg_demo)

/-- Show what the final vN on a plain Graph looks like with the flag ON.
    (Still 0.0 until Graph gets real counts.) -/
def cfg_on : StrainConfig := { useEntropyVN := true }
def W1 : StrainWeights := {}
def Gplain : Graph := {}

#eval vN_final cfg_on Gplain  -- expect 0.0 with current Graph counts
