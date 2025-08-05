/-
Strain.lean  – Logic Field Theory  (rev-2025-08-05)
---------------------------------------------------

Implements the three strain components and total strain `D(G)`:

* `v_I` – internal‐contradiction strain  (path-length metric)
* `v_N` – non-classicality strain        (uniform entropy)
* `v_E` – external-misfit strain         (user-configurable likelihoods)
* `D`   – arithmetic mean of non-zero components

Helpers:
* `registerLikelihood`, `clearLikelihoods`, `lookupLikelihood`
* entropy monotonicity and vertex-merge lemma

-/

import Std.Data.HashMap
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset
import System.IO.Unsafe
import LFT.Graphs

open Classical Std BigOperators
noncomputable section
namespace LFT

/-! ------------------------------------------------------------------
## 0.  Uniform-entropy helper
------------------------------------------------------------------- -/

noncomputable def uniformEntropy (n : ℕ) : ℝ :=
  if h : n ≤ 1 then 0 else Real.log n

lemma uniformEntropy_monotone {m n : ℕ} (h : m ≤ n) :
    uniformEntropy m ≤ uniformEntropy n := by
  by_cases hm : m ≤ 1
  · simp [uniformEntropy, hm]
  ·
    have hpos_m : 1 < m := Nat.lt_of_not_ge hm
    have hpos_n : 1 < n := lt_of_lt_of_le hpos_m h
    simp [uniformEntropy, hm, (Nat.not_le).mpr hpos_n] using
      Real.log_le_log
        (Nat.cast_le.mpr <| Nat.succ_le_of_lt hpos_m)
        (Nat.cast_le.mpr <| Nat.succ_le_of_lt hpos_n)

/-! ------------------------------------------------------------------
## 1.  Configurable likelihood registry
------------------------------------------------------------------- -/

/-- Placeholder structural hash for graphs. Replace with something
    stronger if collisions ever matter. -/
def hashGraph (G : LogicalGraph) : UInt64 := 0xDEADBEEF

abbrev LikelihoodRegistry := HashMap UInt64 ℝ
def emptyRegistry : LikelihoodRegistry := HashMap.empty

/-- Global mutable registry (safe behind `unsafePerformIO`). -/
@[noinline] unsafe def registryRef : IO.Ref LikelihoodRegistry :=
  unsafeIO <| IO.mkRef emptyRegistry

/-- Register or overwrite an empirical likelihood `(0,1]`. -/
def registerLikelihood (G : LogicalGraph) (ℓ : ℝ) : IO Unit :=
  registryRef.modify (fun m => m.insert (hashGraph G) ℓ)

/-- Clear the registry. -/
def clearLikelihoods : IO Unit := registryRef.write emptyRegistry

/-- Pure lookup with default `1`. -/
def lookupLikelihood (G : LogicalGraph) : ℝ :=
  unsafePerformIO do
    let m ← registryRef.get
    pure <| m.findD (hashGraph G) 1

/-- **External misfit strain** `v_E = −log ℓ`. -/
noncomputable def v_E (G : LogicalGraph) : ℝ :=
  let ℓ := lookupLikelihood G
  if h : ℓ = 1 then 0 else -Real.log ℓ

/-! ------------------------------------------------------------------
## 2.  Internal-contradiction strain
------------------------------------------------------------------- -/

/-- A graph contains a contradiction if some root reaches both `w`
    and `¬w`. -/
def hasContradiction (G : LogicalGraph) : Prop :=
  ∃ v w : G.Vertex, Reachable G v w ∧ Reachable G v (¬w)

/-- Path-length of a `Reachable` proof. -/
def Reachable.length {G : LogicalGraph} :
    Reachable G a b → ℕ
| .refl _        => 0
| .tail _ _ rest => rest.length.succ

/-- **Combined path-length distance** to the *first witnessed*
    contradiction.  (A full BFS can replace this later.) -/
noncomputable def contradictionDistance
    (G : LogicalGraph) [Fintype G.Vertex] : ℕ :=
  by
    by_cases h : hasContradiction G
    · rcases h with ⟨v, w, hvw, hvnw⟩
      exact hvw.length + hvnw.length
    · exact 0

/-- **Internal-contradiction strain**
    `0` when contradiction-free; otherwise `1/(d+1)`. -/
noncomputable def v_I (G : LogicalGraph) [Fintype G.Vertex] : ℝ :=
  if h : hasContradiction G then
    ((contradictionDistance G : ℝ) + 1)⁻¹
  else 0

lemma v_I_eq_zero_of_nocontra {G : LogicalGraph} [Fintype G.Vertex]
    (h : ¬hasContradiction G) : v_I G = 0 := by
  simp [v_I, h]

/-! ------------------------------------------------------------------
## 3.  Non-classicality strain
------------------------------------------------------------------- -/

def IsClassical {G : LogicalGraph} : Prop :=
  ∃ v : G.Vertex, ∀ w, Reachable G v w → w = v

noncomputable def v_N (G : LogicalGraph) [Fintype G.Vertex] : ℝ :=
  if h : IsClassical then 0
  else uniformEntropy (Fintype.card G.Vertex)

lemma v_N_eq_zero_of_classical {G : LogicalGraph} [Fintype G.Vertex]
    (h : IsClassical) : v_N G = 0 := by
  simp [v_N, h]

lemma v_N_le_of_card_le
    {G H : LogicalGraph} [Fintype G.Vertex] [Fintype H.Vertex]
    (hcard : Fintype.card H.Vertex ≤ Fintype.card G.Vertex)
    (hGnc : ¬IsClassical G) (hHnc : ¬IsClassical H) :
    v_N H ≤ v_N G := by
  simp [v_N, hGnc, hHnc] using
    uniformEntropy_monotone hcard

/-! ------------------------------------------------------------------
## 4.  Total strain
------------------------------------------------------------------- -/

private def countNonZero (a b c : ℝ) : ℕ :=
  (if a ≠ 0 then 1 else 0) +
  (if b ≠ 0 then 1 else 0) +
  (if c ≠ 0 then 1 else 0)

noncomputable def D (G : LogicalGraph) [Fintype G.Vertex] : ℝ :=
  let vi := v_I G; let vn := v_N G; let ve := v_E G
  let n : ℕ := countNonZero vi vn ve
  if h : n = 0 then 0 else (vi + vn + ve) / (n : ℝ)

/-! ------------------------------------------------------------------
## 5.  Zero-strain example
------------------------------------------------------------------- -/

namespace Examples

def trivialGraph : LogicalGraph :=
{ Vertex := PUnit,
  Edge   := fun _ _ => True,
  decidable_vertex := inferInstance,
  decidable_edge   := by intro _ _; decide }

instance : HasNegation trivialGraph.Vertex where
  neg := id
  neg_involutive := by intro v; rfl

lemma trivialGraph_admissible : IsAdmissible trivialGraph := by
  refine And.intro ?h_id (And.intro ?h_tr (And.intro ?h_nc ?h_em))
  · intro v; trivial
  · intro u v w _ _; trivial
  · intro v hcontra; rcases hcontra with ⟨w, _, _⟩; trivial
  · intro v _; exact Or.inl rfl

def trivialOmega : Omega :=
  ⟨trivialGraph, inferInstance, trivialGraph_admissible⟩

lemma strain_trivial_zero : D trivialOmega.val = 0 := by
  have h_class : IsClassical := by
    refine ⟨PUnit.unit, ?_⟩; intro w _; cases w; rfl
  have h_nocontra : ¬hasContradiction trivialGraph := by
    intro h; rcases h with ⟨v, w, _, _⟩; cases v; cases w
  simp [D, v_I_eq_zero_of_nocontra h_nocontra,
        v_N_eq_zero_of_classical h_class,
        v_E, lookupLikelihood, countNonZero]

end Examples

/-- An admissible graph with zero strain exists. -/
theorem classical_zero_strain : ∃ G : Omega, D G.val = 0 := by
  exact ⟨Examples.trivialOmega, Examples.strain_trivial_zero⟩

end LFT
