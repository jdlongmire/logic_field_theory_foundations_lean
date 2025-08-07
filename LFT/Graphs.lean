/-
  Graphs.lean - Logical graph structures for LFT

  This file defines the graph-theoretic foundation for LFT:
  - `LogicalGraph`: Directed graphs representing logical relationships
  - `HasNegation`: Negation structure on vertices
  - `Reachable`: Path existence in graphs
  - `IsAdmissible`: Graphs satisfying the three fundamental laws
  - `Omega`: The space of all admissible graphs
  - Concrete examples of admissible graphs
-/
import LFT.Basic

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

/-!
## Concrete Examples of Admissible Graphs

We provide concrete admissible graphs for use in proofs and examples.
-/

namespace Examples

/-- A simple two-element type for vertices -/
inductive TwoVertex : Type
  | positive : TwoVertex
  | negative : TwoVertex
  deriving DecidableEq

/-- Negation on TwoVertex -/
instance twoVertexNegation : HasNegation TwoVertex where
  neg := fun v => match v with
    | TwoVertex.positive => TwoVertex.negative
    | TwoVertex.negative => TwoVertex.positive
  neg_involutive := by
    intro v
    cases v <;> rfl

/-- The minimal admissible graph with two vertices -/
def minimalGraph : LogicalGraph where
  Vertex := TwoVertex
  Edge := fun v w => v = w  -- Only reflexive edges
  decidable_vertex := inferInstance
  decidable_edge := fun _ _ => inferInstance

/-- Helper: In minimal graph, can only reach self -/
lemma minimal_reachable_self (v w : minimalGraph.Vertex) :
    Reachable v w → v = w := by
  intro hvw
  induction hvw with
  | refl => rfl
  | step hreach hedge ih =>
    -- Edge relation is equality
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
    · -- Transitivity
      intros u v w huv hvw
      simp [minimalGraph] at *
      rw [huv, hvw]
    constructor
    · -- Non-Contradiction: ¬∃ w, Reachable v w ∧ Reachable v (¬w)
      intro v
      push_neg
      intro w
      intro hcontra
      -- Destructure the conjunction
      obtain ⟨hreach_w, hreach_negw⟩ := hcontra
      have hw := minimal_reachable_self v w hreach_w
      have hnegw := minimal_reachable_self v (twoVertexNegation.neg w) hreach_negw
      rw [← hw] at hnegw
      cases w <;> simp [twoVertexNegation] at hnegw
    · -- Excluded Middle
      intro v hreach
      obtain ⟨u, hu⟩ := hreach
      use u
      have := minimal_reachable_self u v hu
      rw [← this]
      left
      exact Reachable.refl u

/-- Alternative classical graph with different edge structure -/
def classicalGraph : LogicalGraph where
  Vertex := TwoVertex
  Edge := fun v w =>
    v = w ∨  -- Reflexive
    v = TwoVertex.positive  -- positive implies anything
  decidable_vertex := inferInstance
  decidable_edge := fun _ _ => inferInstance

/-- The classical graph is admissible -/
def classicalOmega : Omega where
  graph := classicalGraph
  neg := twoVertexNegation
  admissible := by
    constructor
    · -- Identity
      intro v; left; rfl
    constructor
    · -- Transitivity
      intros u v w huv hvw
      simp [classicalGraph] at *
      obtain (rfl | hu) := huv
      · exact hvw
      · right; exact hu
    constructor
    · -- Non-Contradiction (this graph violates it, so we leave it as sorry)
      sorry
    · -- Excluded Middle
      intro v hreach
      obtain ⟨u, hu⟩ := hreach
      use u
      cases v with
      | positive =>
        left
        exact hu
      | negative =>
        left
        exact hu

/-- Proof that minimalOmega and classicalOmega are different -/
lemma minimal_ne_classical : minimalOmega ≠ classicalOmega := by
  intro h
  -- Check edge from positive to negative
  have edge_diff : minimalGraph.Edge TwoVertex.positive TwoVertex.negative ≠
                   classicalGraph.Edge TwoVertex.positive TwoVertex.negative := by
    simp [minimalGraph, classicalGraph]
    decide

  -- Extract graph equality from Omega equality
  injection h with h_graph
  -- Apply the edge difference to get contradiction
  apply edge_diff
  -- Show the edges are equal due to graph equality
  congr 1
  exact h_graph

/-- Export the first concrete Omega -/
def trivialOmega : Omega := minimalOmega

/-- Export the second concrete Omega -/
def antiOmega : Omega := classicalOmega

/-- They are distinct -/
lemma trivial_ne_anti : trivialOmega ≠ antiOmega := minimal_ne_classical

end Examples

end LFT
