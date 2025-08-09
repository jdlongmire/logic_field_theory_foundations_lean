/-
  Graphs.lean - Logical graph structures for Logic Field Theory (LFT)

  This file defines the graph-theoretic foundation for LFT (Section 3 of the paper):
  - `LogicalGraph`: Directed graphs with propositions as vertices and entailments as edges (Definition 3.1)
  - `HasNegation`: Involutive negation structure on vertices
  - `Reachable`: Path existence for logical inference (Definition 3.5)
  - `IsAdmissible`: Graphs satisfying the three fundamental laws of logic (Definition 3.2)
  - `Omega`: The space of admissible graphs (Definition 3.3)
  - `Superposition`: Formal sums over graphs for quantum states (Definition 3.6)
  - Concrete examples (e.g., qubit graphs, Section 3.6)
-/

import LFT.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum

namespace LFT

/-- A logical graph with propositions as vertices and entailment as edges (Definition 3.1) -/
structure LogicalGraph where
  Vertex : Type
  Edge : Vertex → Vertex → Prop
  finite_vertex : Fintype Vertex
  decidable_vertex : DecidableEq Vertex
  decidable_edge : ∀ v w, Decidable (Edge v w)

/-- Negation structure on vertices -/
class HasNegation (V : Type) where
  neg : V → V
  neg_involutive : ∀ v, neg (neg v) = v

/-- Reachability via directed paths (Definition 3.5) -/
inductive Reachable {G : LogicalGraph} : G.Vertex → G.Vertex → Prop
  | refl (v : G.Vertex) : Reachable v v
  | step {u v w : G.Vertex} : Reachable u v → G.Edge v w → Reachable u w

/-- A graph satisfies Identity if every vertex has a self-edge (Definition 3.2) -/
def SatisfiesIdentity (G : LogicalGraph) : Prop :=
  ∀ v : G.Vertex, G.Edge v v

/-- A graph satisfies Non-Contradiction (Definition 3.2) -/
def SatisfiesNonContradiction (G : LogicalGraph) [HasNegation G.Vertex] : Prop :=
  ∀ v : G.Vertex, ¬∃ w, Reachable v w ∧ Reachable v (HasNegation.neg w)

/-- A graph satisfies Excluded Middle universally (Definition 3.2) -/
def SatisfiesExcludedMiddle (G : LogicalGraph) [HasNegation G.Vertex] : Prop :=
  ∀ v : G.Vertex, ∃ u, Reachable u v ∨ Reachable u (HasNegation.neg v)

/-- A graph is admissible if it satisfies the three fundamental laws (Definition 3.2) -/
def IsAdmissible (G : LogicalGraph) [HasNegation G.Vertex] : Prop :=
  SatisfiesIdentity G ∧ SatisfiesNonContradiction G ∧ SatisfiesExcludedMiddle G

/-- The space of admissible graphs (Definition 3.3) -/
structure Omega where
  graph : LogicalGraph
  neg : HasNegation graph.Vertex
  admissible : IsAdmissible graph

/-- Superposition of vertices in a graph (preliminary for Definition 3.6) -/
structure Superposition (G : LogicalGraph) where
  coeffs : G.Vertex → ℂ
  norm : Finset.sum (Fintype.elems G.Vertex) (fun v => Complex.abs (coeffs v) ^ 2) = 1

/-- Superposition over graphs (Definition 3.6) -/
def GraphSuperposition : Type := Σ (G : Omega), Superposition G.graph

/-!
## Concrete Examples of Admissible Graphs (Section 3.6)
-/

namespace Examples

/-- A two-element type for vertices (e.g., qubit states) -/
inductive TwoVertex : Type
  | positive : TwoVertex
  | negative : TwoVertex
  deriving DecidableEq, Fintype

/-- Negation on TwoVertex -/
instance twoVertexNegation : HasNegation TwoVertex where
  neg v := match v with
    | TwoVertex.positive => TwoVertex.negative
    | TwoVertex.negative => TwoVertex.positive
  neg_involutive v := by
    cases v <;> rfl

/-- The minimal admissible graph with two vertices (Example 3.7) -/
def minimalGraph : LogicalGraph where
  Vertex := TwoVertex
  Edge := fun v w => v = w
  finite_vertex := by apply_instance
  decidable_vertex := by apply_instance
  decidable_edge := fun _ _ => by apply_instance

/-- Helper: In minimal graph, reachability implies equality -/
lemma minimal_reachable_eq {v w : minimalGraph.Vertex} :
    Reachable (G := minimalGraph) v w → v = w := by
  intro h
  induction h with
  | refl => rfl
  | step hreach hedge ih =>
    simp [minimalGraph] at hedge
    rw [← hedge, ih]

/-- The minimal graph is admissible -/
def minimalOmega : Omega where
  graph := minimalGraph
  neg := twoVertexNegation
  admissible := by
    constructor
    · -- Identity
      intro v; rfl
    constructor
    · -- Non-Contradiction
      intro v; push_neg; intro w ⟨hvw, hvnegw⟩
      have hw := minimal_reachable_eq hvw
      have hnegw := minimal_reachable_eq hvnegw
      rw [← hw] at hnegw
      cases w <;> simp [twoVertexNegation] at hnegw
    · -- Excluded Middle
      intro v
      use v
      left
      exact Reachable.refl v

/-- Alternative classical graph with asymmetric edges -/
def classicalGraph : LogicalGraph where
  Vertex := TwoVertex
  Edge := fun v w => v = w ∨ v = TwoVertex.positive
  finite_vertex := by apply_instance
  decidable_vertex := by apply_instance
  decidable_edge := fun _ _ => by apply_instance

/-- The classical graph is admissible -/
def classicalOmega : Omega where
  graph := classicalGraph
  neg := twoVertexNegation
  admissible := by
    constructor
    · -- Identity
      intro v; left; rfl
    constructor
    · -- Non-Contradiction
      intro v; push_neg; intro w ⟨hvw, hvnegw⟩
      simp [classicalGraph, twoVertexNegation] at hvw hvnegw
      cases v <;> cases w <;> tauto
    · -- Excluded Middle
      intro v
      use TwoVertex.positive
      cases v
      · left; right; rfl
      · right; right; rfl

/-- Proof that minimalOmega and classicalOmega are distinct -/
lemma minimal_ne_classical : minimalOmega ≠ classicalOmega := by
  intro h
  have edge_diff : minimalGraph.Edge TwoVertex.positive TwoVertex.negative ≠
                   classicalGraph.Edge TwoVertex.positive TwoVertex.negative := by
    simp [minimalGraph, classicalGraph]
    intro h; cases h <;> contradiction
  injection h with h_graph
  contradiction

/-- Export the first concrete Omega -/
def trivialOmega : Omega := minimalOmega

/-- Export the second concrete Omega -/
def antiOmega : Omega := classicalOmega

/-- They are distinct -/
lemma trivial_ne_anti : trivialOmega ≠ antiOmega := minimal_ne_classical

end Examples
end LFT
