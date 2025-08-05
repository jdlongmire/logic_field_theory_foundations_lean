import LFT.Basic

/-!
# Logical Graphs for Logic Field Theory

This file defines the graph-theoretic foundation for LFT:
- `LogicalGraph`: Directed graphs representing logical relationships
- `HasNegation`: Negation structure on vertices
- `Reachable`: Path existence in graphs
- `IsAdmissible`: Graphs satisfying the three fundamental laws
- `Omega`: The space of all admissible graphs

## Main definitions

* `LogicalGraph`: A type with a decidable edge relation
* `IsAdmissible`: Predicate for graphs satisfying 3FLL
* `Omega`: Structure containing admissible graphs with negation

-/

namespace LFT

/-- A logical graph with propositions as vertices and entailment as edges -/
structure LogicalGraph where
  Vertex : Type*
  Edge : Vertex → Vertex → Prop
  decidable_vertex : DecidableEq Vertex
  decidable_edge : ∀ v w, Decidable (Edge v w)

-- Test: Can we create a simple graph?
example : LogicalGraph where
  Vertex := Bool
  Edge := fun a b => a = true → b = true
  decidable_vertex := inferInstance
  decidable_edge := fun _ _ => inferInstance

/-- Negation structure on vertices -/
class HasNegation (V : Type*) where
  neg : V → V
  neg_involutive : ∀ v, neg (neg v) = v

-- Test: Bool has natural negation
instance : HasNegation Bool where
  neg := not
  neg_involutive := by
    intro b
    cases b <;> rfl

/-- Reachability via directed paths -/
inductive Reachable {G : LogicalGraph} : G.Vertex → G.Vertex → Prop
  | refl (v : G.Vertex) : Reachable v v
  | step {u v w : G.Vertex} : Reachable u v → G.Edge v w → Reachable u w

-- Test: Every vertex reaches itself
example (G : LogicalGraph) (v : G.Vertex) : Reachable v v := by
  exact Reachable.refl v

/-- A graph satisfies Identity if every vertex has a self-edge -/
def SatisfiesIdentity (G : LogicalGraph) : Prop :=
  ∀ v : G.Vertex, G.Edge v v

/-- A graph satisfies Transitivity -/
def SatisfiesTransitivity (G : LogicalGraph) : Prop :=
  ∀ u v w : G.Vertex, G.Edge u v → G.Edge v w → G.Edge u w

/-- A graph satisfies Non-Contradiction -/
def SatisfiesNonContradiction (G : LogicalGraph) [HasNegation G.Vertex] : Prop :=
  ∀ v : G.Vertex, ¬∃ w, Reachable v w ∧ Reachable v (HasNegation.neg w)

/-- A graph satisfies Excluded Middle for engaged propositions -/
def SatisfiesExcludedMiddle (G : LogicalGraph) [HasNegation G.Vertex] : Prop :=
  ∀ v : G.Vertex, (∃ u, Reachable u v) →
    (∃ u, Reachable u v ∨ Reachable u (HasNegation.neg v))

/-- The admissibility operator L -/
def IsAdmissible (G : LogicalGraph) [HasNegation G.Vertex] : Prop :=
  SatisfiesIdentity G ∧
  SatisfiesTransitivity G ∧
  SatisfiesNonContradiction G ∧
  SatisfiesExcludedMiddle G

/-- The space of admissible graphs -/
structure Omega where
  graph : LogicalGraph
  neg : HasNegation graph.Vertex
  admissible : IsAdmissible graph

-- Note: A trivial graph with identity negation is NOT admissible
-- because it violates non-contradiction (v reaches both v and neg(v) = v)

end LFT
