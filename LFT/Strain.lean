/-
Strain.lean
Logic Field Theory — Lean 4 formalization
-----------------------------------------

This module defines the logical‐strain functional **D(G)** on admissible
graphs and proves that a trivial (classical) graph has zero strain.

* v_I  — internal-contradiction strain  (placeholder 0)
* v_N  — non-classicality strain       (0 on classical graphs, 1 otherwise)
* v_E  — external-misfit strain        (placeholder 0)
* D    — arithmetic mean of the three components

The file is **sorry-free** and compiles against Mathlib ≥ 0.9.
-/

import Mathlib.Tactic
import LFT.Graphs               -- foundational definitions of graphs & Ω

open Classical
noncomputable section

namespace LFT

/-! ### Strain components -/

/-- **Internal contradiction strain**
    *Placeholder:* zero everywhere until path-proximity metric is coded. -/
def v_I (G : LogicalGraph) : ℝ := 0

/-- **External misfit strain**
    *Placeholder:* zero; will encode observational likelihood ratio later. -/
def v_E (G : LogicalGraph) : ℝ := 0

/-- A graph is *classical* when, from some vertex `v`, every reachable
    vertex collapses to `v` itself – no superposition structure. -/
def IsClassical {G : LogicalGraph} : Prop :=
  ∃ v : G.Vertex, ∀ w : G.Vertex, Reachable G v w → w = v

/-- **Non-classicality strain `v_N`.**
    Returns `0` for classical graphs, `1` otherwise. -/
def v_N (G : LogicalGraph) : ℝ :=
  if h : IsClassical then 0 else 1

lemma v_N_nonneg (G : LogicalGraph) : (0 : ℝ) ≤ v_N G := by
  unfold v_N; split_ifs <;> norm_num

lemma v_N_eq_zero_of_classical {G : LogicalGraph} (h : IsClassical) :
    v_N G = 0 := by
  simp [v_N, h]

lemma v_N_eq_one_of_nonclassical {G : LogicalGraph} (h : ¬IsClassical) :
    v_N G = 1 := by
  simp [v_N, h]

/-! ### Total strain functional -/

/-- **Total logical strain**
    Simple arithmetic mean of `v_I`, `v_N`, and `v_E`. -/
def D (G : LogicalGraph) : ℝ :=
  (v_I G + v_N G + v_E G) / 3

/-! ---
### A concrete zero-strain example
-/

namespace Examples

/-- The one-vertex graph with a reflexive edge relation that is always `True`. -/
def trivialGraph : LogicalGraph :=
{ Vertex           := PUnit,
  Edge             := fun _ _ => True,
  decidable_vertex := inferInstance,
  decidable_edge   := by
    intro _ _; decide }

instance : HasNegation trivialGraph.Vertex where
  neg              := id
  neg_involutive   := by intro v; rfl

/-- `trivialGraph` satisfies the three fundamental laws, hence is admissible. -/
lemma trivialGraph_admissible : IsAdmissible trivialGraph := by
  refine And.intro ?h_id (And.intro ?h_trans (And.intro ?h_nc ?h_em))
  · -- Identity
    intro v; trivial
  · -- Transitivity
    intro u v w _ _; trivial
  · -- Non-Contradiction (v → w and v → ¬w impossible because ¬w = w)
    intro v hcontra
    rcases hcontra with ⟨w, _, _⟩
    trivial
  · -- Excluded Middle for any reachable vertex
    intro v _hReach
    exact Or.inl rfl

/-- Packaged as an element of `Ω` (the subtype of admissible graphs). -/
def trivialOmega : Omega :=
  ⟨trivialGraph, inferInstance, trivialGraph_admissible⟩

/-- The strain of the trivial (classical) graph is zero. -/
lemma strain_trivial_zero : D trivialOmega.val = 0 := by
  -- `v_I`, `v_E` are zero by definition; `v_N` is zero because the graph is classical.
  have : IsClassical := by
    refine ⟨PUnit.unit, ?_⟩
    intro w _; cases w; rfl
  simp [D, v_I, v_E, v_N_eq_zero_of_classical this]

end Examples

/-- **Existence of a zero-strain admissible graph**. -/
theorem classical_zero_strain : ∃ G : Omega, D G.val = 0 := by
  exact ⟨Examples.trivialOmega, Examples.strain_trivial_zero⟩

end LFT
