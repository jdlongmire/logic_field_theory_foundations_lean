import Mathlib
import LFT.Graphs

/-!
Edge-type counts API for `Graph`, non-breaking.

Provide a typeclass `HasEdgeTypeCounts` so different graph backends
can supply real counts. We ship a default "all zeros" instance so
existing code keeps compiling until you implement real counts.
-/

namespace LFT
namespace Graphs

inductive EdgeType | id | entails | excludes
deriving DecidableEq, Repr

structure EdgeTypeCounts where
  id : Nat
  entails : Nat
  excludes : Nat
deriving Repr

class HasEdgeTypeCounts (α : Type) where
  counts : α → EdgeTypeCounts

-- Default dummy instance so current graphs still compile.
instance : HasEdgeTypeCounts LFT.Graph where
  counts _ := { id := 0, entails := 0, excludes := 0 }

end Graphs
end LFT
