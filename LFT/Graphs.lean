import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import LFT.Basic

set_option autoImplicit false
namespace LFT

/-- A directed graph with vertices `Vertex` and edge relation `Edge`. -/
structure Graph where
  Vertex : Type
  Edge   : Vertex → Vertex → Prop

namespace Graph

variable (G : Graph)

/-- Reachability is the reflexive–transitive closure of `Edge`. -/
def Reachable : G.Vertex → G.Vertex → Prop :=
  Relation.ReflTransGen G.Edge

/-- One-step reachability via a single edge. -/
def step {a b : G.Vertex} (h : G.Edge a b) : G.Reachable a b :=
  Relation.ReflTransGen.single h

/-- Reflexivity of reachability. -/
theorem reachable_refl (a : G.Vertex) : G.Reachable a a :=
  Relation.ReflTransGen.refl

/-- Transitivity of reachability. -/
theorem reachable_trans {a b c : G.Vertex}
    (hab : G.Reachable a b) (hbc : G.Reachable b c) :
    G.Reachable a c :=
  Relation.ReflTransGen.trans hab hbc

/-- If there is an edge `a → b` and `b` reaches `c`, then `a` reaches `c`. -/
theorem step_then {a b c : G.Vertex}
    (h : G.Edge a b) (hbc : G.Reachable b c) :
    G.Reachable a c :=
  reachable_trans (G := G) (step (G := G) h) hbc

/-- Placeholder for LFT's logical-admissibility predicate on graphs. -/
def isAdmissible : Prop := True

end Graph

/-- A tiny concrete vertex type with two labeled points. -/
inductive TwoVertex
| positive
| negative
deriving DecidableEq, Repr

namespace TwoVertex
notation "P⁺" => TwoVertex.positive
notation "P⁻" => TwoVertex.negative
end TwoVertex

/-- A minimal concrete graph on `TwoVertex` for sanity checks. -/
def classicalGraph : Graph where
  Vertex := TwoVertex
  Edge
    | .positive, .negative => True
    | _, _                  => False

namespace classicalGraph

/-- Shorthand: the canonical two-vertex graph. -/
def G : Graph := classicalGraph

/-- There is an edge from P⁺ to P⁻ in `classicalGraph`. -/
lemma edge_pos_to_neg : (G.Edge TwoVertex.positive TwoVertex.negative) := by
  exact True.intro

/-- Therefore P⁺ reaches P⁻. -/
lemma reachable_pos_to_neg :
    (G.Reachable TwoVertex.positive TwoVertex.negative) :=
  Graph.step (G := G) edge_pos_to_neg

/-- Reachability is reflexive at P⁺. -/
lemma reachable_refl_pos :
    (G.Reachable TwoVertex.positive TwoVertex.positive) :=
  Graph.reachable_refl (G := G) TwoVertex.positive

end classicalGraph

end LFT
