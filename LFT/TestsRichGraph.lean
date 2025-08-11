import LFT.Entropy
import LFT.Strain
import LFT.Graphs.RichGraph
import LFT.Graphs.EdgeTypes

open LFT
open LFT.Graphs

/-- A small rich graph with one of each edge type. -/
def rg1 : RichGraph :=
  { V := ({}.insert "p").insert "q",
    E := [("p","p", EdgeType.id),
          ("p","q", EdgeType.entails),
          ("q","p", EdgeType.excludes)] }

/-- Show the structural counts we derive (should be [1,1,1]). -/
#eval LFT.structuralCountsOf rg1

/-- Entropy of equal counts [1,1,1] should be ≈ log2 3 ≈ 1.585. -/
#eval LFT.Entropy.shannonFromCounts (LFT.structuralCountsOf rg1)
