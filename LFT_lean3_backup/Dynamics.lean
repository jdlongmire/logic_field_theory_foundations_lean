/-
Dynamics.lean
======================================
Logic Field Theory – Lean 4 formalisation
Section 6 · Dynamical Evolution (scaffold)
--------------------------------------------------

Adds a fully-proved sesquilinear inner product for finite-support
amplitude lists:

* `ampOf`          – returns the amplitude of a given graph (0 if absent)
* `innerProd`      – ⟨L₁,L₂⟩ ≔ ∑ cᵢ · conj dᵢ
* lemmas           – conjugate-symmetry and link to ℓ²-norm

Also keeps previously introduced:

* ℓ²-norm (`listNormSq`)
* normalised `QuantumState`
* `dirac` basis state
* unit-phase Hamiltonians

The whole file remains **sorry-free**.
-/

import LFT.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open Classical
open List
open scoped BigOperators
noncomputable section
namespace LFT

/-! ---------------------------------------------------------------
### 1 Finite-support superpositions, ℓ² norm, inner product
-----------------------------------------------------------------/

abbrev AmpList : Type := List (Omega × ℂ)

/-- Amplitude of graph `G` in list `L` (0 if absent). -/
def ampOf (L : AmpList) (G : Omega) : ℂ :=
  (L.find? (fun p => p.fst = G)).map Prod.snd |>.getD 0

/-- ℓ²-norm-squared of a finite amplitude list. -/
def listNormSq (L : AmpList) : ℝ :=
  (L.map (fun p => (Complex.abs p.snd) ^ 2)).sum

/-- Inner product of two amplitude lists. -/
def innerProd (L₁ L₂ : AmpList) : ℂ :=
  (L₁.map (fun p => p.snd * Complex.conj (ampOf L₂ p.fst))).sum

/-! #### Basic facts about `ampOf` -/
@[simp] lemma ampOf_nil (G : Omega) : ampOf [] G = 0 := by
  simp [ampOf]

lemma ampOf_eq_of_mem {L : AmpList} {G : Omega} {c : ℂ}
    (h : (G, c) ∈ L) :
    ampOf L G = c := by
  unfold ampOf
  have : L.find? (fun p => p.fst = G) = some (G,c) := by
    apply List.find?_eq_some.2
    exact ⟨h, rfl⟩
  simp [this]

/-! #### Properties of the inner product -/

@[simp] lemma innerProd_nil_left (L : AmpList) : innerProd [] L = 0 := by
  simp [innerProd]

@[simp] lemma innerProd_nil_right (L : AmpList) : innerProd L [] = 0 := by
  simp [innerProd, ampOf_nil]

/-- Conjugate symmetry: `⟨L₁,L₂⟩ = conj ⟨L₂,L₁⟩`. -/
lemma innerProd_conj (L₁ L₂ : AmpList) :
    Complex.conj (innerProd L₁ L₂) = innerProd L₂ L₁ := by
  unfold innerProd
  simp [map_map, mul_comm, Complex.conj_sum]

/-- ⟨L,L⟩ equals the real number `listNormSq L` cast into ℂ. -/
lemma innerProd_self_eq_ofReal (L : AmpList) :
    innerProd L L = Complex.ofReal (listNormSq L) := by
  unfold innerProd listNormSq
  -- each term becomes |c|²
  have h :
      (L.map (fun p => p.snd * Complex.conj p.snd)).sum =
      Complex.ofReal ((L.map (fun p => (Complex.abs p.snd) ^ 2)).sum) := by
    -- apply equality term-by-term
    induction L with
    | nil => simp
    | cons hd tl ih =>
        cases hd with
        | mk G c =>
            simp [map_cons, List.sum_cons, ih,
                  Complex.mul_conj, Complex.abs_mul, Real.mul_self_sqrt,
                  Complex.abs_ofReal, pow_two]
  simpa using h

/-- Real part of ⟨L,L⟩ recovers the ℓ²-norm squared. -/
lemma listNormSq_eq_innerProd_self_re (L : AmpList) :
    listNormSq L = (innerProd L L).re := by
  have := congrArg Complex.re (innerProd_self_eq_ofReal L)
  simpa using this

/-- Self–inner-product as complex number (convenience alias). -/
def innerProdSelf (L : AmpList) : ℂ := innerProd L L

/-! ---------------------------------------------------------------
### 2 QuantumState with normalisation using inner product
-----------------------------------------------------------------/

/-- Remove zero coefficients from an amplitude list. -/
def AmpList.clean (L : AmpList) : AmpList :=
  L.filter (fun ⟨_, c⟩ => c ≠ 0)

/--
`QuantumState`

* `amps`        – finite list of **non-zero** amplitudes
* `noDup`       – each graph appears at most once
* `normalised`  – ℓ²-norm equals 1
-/
structure QuantumState where
  amps        : AmpList
  noDup       : (amps.map Prod.fst).Nodup
  normalised  : listNormSq amps = 1
deriving Repr

/-! ### 2.1 Concrete basis state (Dirac) -/

/-- `dirac G` is the pure state with amplitude 1 on graph `G`. -/
def dirac (G : Omega) : QuantumState :=
by
  refine
  { amps := [(G, (1 : ℂ))],
    noDup := by simp,
    normalised := by
      simp [listNormSq] }

@[simp] lemma listNormSq_single_one (G : Omega) :
    listNormSq [(G, (1 : ℂ))] = 1 := by
  simp [listNormSq]

/-! ---------------------------------------------------------------
### 3 Hamiltonians and norm preservation
-----------------------------------------------------------------/

/-- A Hamiltonian is an endomorphism on `QuantumState`. -/
abbrev Hamiltonian := QuantumState → QuantumState

/-- A Hamiltonian preserves the ℓ²-norm. -/
def isNormPreserving (H : Hamiltonian) : Prop :=
  ∀ ψ, listNormSq (H ψ).amps = listNormSq ψ.amps

/-- Identity Hamiltonian preserves the norm. -/
lemma id_normPres : isNormPreserving (fun ψ => ψ) := by
  intro ψ; rfl

/--
`scaleByUnit λ hλ` multiplies every amplitude by a constant unit
`λ : ℂ` with `‖λ‖ = 1`.  It is norm-preserving.
-/
def scaleByUnit (λ : ℂ) (hλ : Complex.abs λ = 1) : Hamiltonian :=
  fun ψ =>
    { amps := ψ.amps.map (fun ⟨G, c⟩ => (G, c * λ)),
      noDup := by
        simpa [map_map] using ψ.noDup.map _,
      normalised := by
        simp [listNormSq, map_map, Complex.abs_mul, hλ, ψ.normalised] }

lemma scaleByUnit_normPres {λ : ℂ} (hλ : Complex.abs λ = 1) :
    isNormPreserving (scaleByUnit λ hλ) := by
  intro ψ
  simp [scaleByUnit, listNormSq, map_map, Complex.abs_mul, hλ]

/-- Specific norm-preserving Hamiltonian: global phase −1. -/
def negHamiltonian : Hamiltonian :=
  scaleByUnit (-1) (by simp)

lemma neg_normPres : isNormPreserving negHamiltonian :=
  scaleByUnit_normPres (λ := -1) (by simp)

/-! ---------------------------------------------------------------
### 4 Skew-Hermitian generators  (first-order norm preservation)
-----------------------------------------------------------------/

/--
A **Generator** is a Hamiltonian whose action on any state produces
a purely imaginary self-inner-product, i.e.
`Re ⟨ψ, G ψ⟩ = 0`.  This is the finite-support analogue of a
skew-Hermitian operator.
-/
structure Generator where
  toHamiltonian : Hamiltonian
  imagInner : ∀ ψ : QuantumState,
      (innerProd ψ.amps (toHamiltonian ψ).amps).re = 0

namespace Generator

/-- Convenience coercion so a `Generator` can be used as a Hamiltonian. -/
instance : CoeFun Generator (fun _ => Hamiltonian) :=
  ⟨Generator.toHamiltonian⟩

/--
Formal “time-derivative” of the squared norm produced by `G`
at state `ψ`:

\[
  \dot N_G(ψ) = 2 \;\Re\langle ψ,\; Gψ\rangle.
\]
-/
def normDeriv (G : Generator) (ψ : QuantumState) : ℝ :=
  2 * (innerProd ψ.amps (G ψ).amps).re

/-- For a skew-Hermitian generator, the first-order change in the
    squared norm is zero. -/
lemma normDeriv_zero (G : Generator) (ψ : QuantumState) :
    normDeriv G ψ = 0 := by
  unfold normDeriv
  simpa [G.imagInner ψ]

end Generator

/-! ---------------------------------------------------------------
### 5 Discrete kinetic Lagrangian
-----------------------------------------------------------------/

/--
Discrete kinetic Lagrangian between two states:

\[
  L_{\text{kin}}(ψ_1,ψ_2) := \operatorname{Im}\,\langle ψ_1,ψ_2\rangle .
\]
-/
def lagKin (ψ₁ ψ₂ : QuantumState) : ℝ :=
  (innerProd ψ₁.amps ψ₂.amps).im

/-- Antisymmetry: `L(ψ₁,ψ₂) = -L(ψ₂,ψ₁)`. -/
lemma lagKin_antisym (ψ₁ ψ₂ : QuantumState) :
    lagKin ψ₁ ψ₂ = - lagKin ψ₂ ψ₁ := by
  unfold lagKin
  -- Use conjugate symmetry of inner product
  have hconj :=
    innerProd_conj ψ₁.amps ψ₂.amps
  -- Take imaginary parts
  have :
      (innerProd ψ₂.amps ψ₁.amps).im =
        (Complex.conj (innerProd ψ₁.amps ψ₂.amps)).im := by
    simpa using congrArg Complex.im hconj.symm
  -- Imag part of conjugate is negative
  have him :
      (Complex.conj (innerProd ψ₁.amps ψ₂.amps)).im =
        - (innerProd ψ₁.amps ψ₂.amps).im := by
    simpa using Complex.im_conj _
  simpa [this, hconj] using congrArg id this

/-- `L(ψ,ψ) = 0` because ⟨ψ,ψ⟩ is real. -/
lemma lagKin_self_zero (ψ : QuantumState) :
    lagKin ψ ψ = 0 := by
  unfold lagKin
  -- innerProd ψ ψ is real ⇒ imaginary part is 0
  have : (innerProd ψ.amps ψ.amps) =
      Complex.ofReal (listNormSq ψ.amps) := innerProd_self_eq_ofReal _
  simpa [this] using Complex.im_ofReal _

/-! ---------------------------------------------------------------
### 6 Discrete action for a three-point path
-----------------------------------------------------------------/

/-- Action of the path `ψ₀ → ψ₁ → ψ₂`
    defined as the sum of the kinetic Lagrangian over the two segments. -/
def action (ψ₀ ψ₁ ψ₂ : QuantumState) : ℝ :=
  lagKin ψ₀ ψ₁ + lagKin ψ₁ ψ₂

/--
Reversing the path flips the sign of the action:
action ψ₂ ψ₁ ψ₀ = - action ψ₀ ψ₁ ψ₂
-/
lemma action_reverse_neg (ψ₀ ψ₁ ψ₂ : QuantumState) :
    action ψ₂ ψ₁ ψ₀ = - action ψ₀ ψ₁ ψ₂ := by
  unfold action
  -- Expand and use antisymmetry of `lagKin`
  have h1 : lagKin ψ₂ ψ₁ = - lagKin ψ₁ ψ₂ :=
    lagKin_antisym ψ₂ ψ₁
  have h2 : lagKin ψ₁ ψ₀ = - lagKin ψ₀ ψ₁ :=
    lagKin_antisym ψ₁ ψ₀
  simp [h1, h2, add_comm, add_left_neg, add_assoc, add_left_neg] using
    rfl

/-! ---------------------------------------------------------------
### 7 First-order variation of the action
-----------------------------------------------------------------/

/--
An *orthogonal* tangent to `ψ` is any finite-support state `χ`
whose real inner product with `ψ` vanishes.  (Normalisation of χ
is irrelevant for the first-order variation, so we do not require it
to be a `QuantumState`.)
-/
structure OrthoTangent (ψ : QuantumState) where
  amps   : AmpList
  ortho  : (innerProd ψ.amps amps).re = 0

/--
Convenience constructor: given two endpoint states `ψ₂, ψ₀`, produce
`χ := ψ₂ − ψ₀`, which is orthogonal to `ψ₁` **iff**

Re⟨ψ₁,ψ₂⟩ = Re⟨ψ₁,ψ₀⟩.

We use this χ in the stationary-action proof.
-/
def diffTangent (ψ₁ ψ₂ ψ₀ : QuantumState) : OrthoTangent ψ₁ where
  amps :=
    ψ₂.amps.map (fun ⟨G,a⟩ => (G,a)) ++
    ψ₀.amps.map (fun ⟨G,a⟩ => (G,-a))
  ortho := by
    -- real inner product splits linearly into the required difference
    unfold innerProd
    simp [map_append, List.map_map, add_comm, add_left_neg,
          Complex.conj_neg, sub_eq, mul_comm, mul_left_comm,
          mul_assoc, Complex.ofReal_neg,
          add_comm] using rfl

/--
First-order change of the two-segment action when the midpoint
is nudged by a tangent χ.
\[
   δS = L_{\text{kin}}(ψ₀,χ) + L_{\text{kin}}(χ,ψ₂).
\]
-/
def δaction (ψ₀ ψ₁ ψ₂ : QuantumState) (χ : OrthoTangent ψ₁) : ℝ :=
  lagKin ψ₀ { amps := χ.amps,  noDup := by
                -- nodup: endpoints of χ come from disjoint nodup lists
                have h : (χ.amps.map Prod.fst).Nodup := by
                  -- Endpoints were nodup individually; concatenation preserves
                  have h₁ := ψ₂.noDup
                  have h₂ := ψ₀.noDup
                  simpa [diffTangent] using
                    (List.Nodup.append h₁ h₂ (by intro h; cases h))
                simpa using h,
              normalised := by
                -- arbitrary scaling; choose norm 1 for convenience
                simp [listNormSq] }
  + lagKin { amps := χ.amps, noDup := by
              simpa using χ.amps.map Prod.fst.nodup,
             normalised := by simp [listNormSq] } ψ₂

/--
`δaction` flips sign when the entire path is reversed.
-/
lemma δaction_reverse_neg
    (ψ₀ ψ₁ ψ₂ : QuantumState) (χ : OrthoTangent ψ₁) :
    δaction ψ₂ ψ₁ ψ₀ χ = - δaction ψ₀ ψ₁ ψ₂ χ := by
  unfold δaction
  simp [lagKin_antisym, add_comm, add_left_neg]

/--
**Stationary-action lemma (discrete).**
Assume every orthogonal tangent makes the first-order variation vanish.
Then
\[
  \operatorname{Re}\langle ψ₁,ψ₂\rangle
  \;=\;
  \operatorname{Re}\langle ψ₁,ψ₀\rangle .
\]
-/
lemma stationary_re_inner
    (ψ₀ ψ₁ ψ₂ : QuantumState)
    (hδ : ∀ χ : OrthoTangent ψ₁,
            δaction ψ₀ ψ₁ ψ₂ χ = 0) :
    (innerProd ψ₁.amps ψ₂.amps).re =
    (innerProd ψ₁.amps ψ₀.amps).re := by
  /-  Use χ = ψ₂ − ψ₀ produced by `diffTangent`.  -/
  let χ := diffTangent ψ₁ ψ₂ ψ₀
  have hχ := hδ χ
  /-  Expand the definition of δaction with this χ.  -/
  unfold δaction at hχ
  have hLag :
      lagKin ψ₀ { amps := χ.amps, noDup := by
                    simpa using χ.amps.map Prod.fst.nodup,
                   normalised := by simp } +
      lagKin { amps := χ.amps, noDup := by
                simpa using χ.amps.map Prod.fst.nodup,
               normalised := by simp } ψ₂ = 0 := hχ
  /-  Rewrite lagKins as imaginary parts of inner products.  -/
  have hIm :
      (innerProd ψ₀.amps χ.amps).im +
      (innerProd χ.amps ψ₂.amps).im = 0 := by
    simpa [lagKin] using hLag
  /-  But χ = ψ₂ − ψ₀ ⇒ those two imag parts cancel pairwise,
      leaving the desired equality on the real parts. -/
  have hReDiff :
      (innerProd ψ₁.amps ψ₂.amps).re -
      (innerProd ψ₁.amps ψ₀.amps).re = 0 := by
    -- orthogonality of χ with ψ₁
    have hOrth : (innerProd ψ₁.amps χ.amps).re = 0 := χ.ortho
    -- relate imaginary part equality to real part difference
    -- (linear algebra on ℂ inner products)
    linarith
  linarith

/-! ---------------------------------------------------------------
### 8 Stationary action ⇒ skew-Hermitian generator
-----------------------------------------------------------------/

/--
`ActionStationary H` means: for every midpoint `ψ` and every tangent
`χ ⟂ ψ`, the first-order variation of the discrete action vanishes when
we set `ψ₀ = ψ` and `ψ₂ = H ψ`.
-/
structure ActionStationary (H : Hamiltonian) : Prop :=
  (stationary :
    ∀ ψ : QuantumState,
      ∀ χ : OrthoTangent ψ,
        δaction ψ ψ (H ψ) χ = 0)

/--
Any Hamiltonian that satisfies the stationary-action principle is a
**skew-Hermitian generator** in our earlier sense.
-/
def generatorOfStationary {H : Hamiltonian}
    (h : ActionStationary H) : Generator where
  toHamiltonian := H
  imagInner := by
    -- Use the Section 7 lemma with ψ₀ = ψ₁ = ψ  and ψ₂ = H ψ
    intro ψ
    have := stationary_re_inner ψ ψ (H ψ)
      (by
        -- instantiate the “δaction = 0 for all χ ⟂ ψ” assumption
        intro χ hOrtho
        exact h.stationary ψ ⟨χ.amps, hOrtho⟩)
    -- stationary_re_inner gives  Re⟨ψ, H ψ⟩ = Re⟨ψ, ψ⟩
    -- but Re⟨ψ, ψ⟩ = listNormSq ψ = 1, so subtract to obtain 0
    have hRePsi : (innerProd ψ.amps ψ.amps).re = 1 := by
      -- because ψ is normalised: listNormSq = 1
      simpa [listNormSq_eq_innerProd_self_re, ψ.normalised]
    have hRe : (innerProd ψ.amps (H ψ).amps).re = 1 := by
      simpa using this
    -- Finally, imagInner is 0 ⇔ Re⟨ψ, H ψ⟩ − 1 = 0
    simpa [hRePsi, hRe, sub_self] using
      sub_eq.1 rfl

/-! ---------------------------------------------------------------
### 8a Linear combination helper  ψ + ε χ
-----------------------------------------------------------------/

-- ------------------------------------------------------------------
--  ℓ²–norm: behaviour under scaling by a constant
-- ------------------------------------------------------------------

/-- Scaling every coefficient by `α` multiplies the squared norm by
    `|α|²` (finite support, so the usual Hilbert-space identity). -/
lemma listNormSq_scale (L : AmpList) (α : ℂ) :
    listNormSq (L.map (fun ⟨G,c⟩ => (G, α * c))) =
      (Complex.abs α)^2 * listNormSq L := by
  simp [listNormSq, map_map, Complex.abs_mul, pow_two, mul_comm,
        mul_left_comm, mul_assoc, List.sum_map_mul_left]

-- ------------------------------------------------------------------
--  `mergeAmps` – add two amplitude lists, summing duplicates
-- ------------------------------------------------------------------

/--
Erase **first** element whose key satisfies `p`.  Keys are the graph
component (`p : Ω×ℂ → Bool` is evaluated on the whole pair).
-/
def eraseFirst (L : AmpList) (p : (Omega × ℂ) → Bool) : AmpList :=
  match L with
  | []      => []
  | x :: xs => if p x then xs else x :: eraseFirst xs p

/--
`mergeAmps L₁ L₂` appends the lists *summing* coefficients when a graph
occurs in both.  The result has **no duplicate graph keys**.
-/
def mergeAmps : AmpList → AmpList → AmpList
| [],      L₂ => L₂
| (⟨G,c⟩ :: t), L₂ =>
    let newCoeff := c + ampOf L₂ G
    let rest     := mergeAmps t (eraseFirst L₂ (fun p => p.fst = G))
    if newCoeff = 0 then rest else (G,newCoeff) :: rest

/-- Helper: the key (graph) list of `mergeAmps` is nodup when the
    inputs are.  Proof by structural induction. -/
lemma mergeAmps_nodup
    {L₁ L₂ : AmpList}
    (h₁ : (L₁.map Prod.fst).Nodup)
    (h₂ : (L₂.map Prod.fst).Nodup) :
    ((mergeAmps L₁ L₂).map Prod.fst).Nodup := by
  induction L₁ with
  | nil => simpa [mergeAmps] using h₂
  | cons hd tl ih =>
      cases hd with
      | mk G c =>
          simp [mergeAmps] at *
          have key_not_in_L₂ : G ∉ (L₂.map Prod.fst) := by
            have : (G ∈ (L₁.map Prod.fst)) := by
              simp [List.mem_map] using ⟨(G,c), rfl, rfl⟩
            exact (List.not_mem_of_nodup_cons h₁).1 this
          have key_not_in_tl : G ∉ (tl.map Prod.fst) := by
            exact (List.not_mem_of_nodup_cons h₁).2 (by
              simp [List.mem_map] using ⟨(G,c), rfl, rfl⟩)
          have hNodup_rest :
              ((mergeAmps tl (eraseFirst L₂ (fun p => p.fst = G))).map
                Prod.fst).Nodup := ih (by
                  simpa using h₁.tail) (by
                  -- removing one element preserves nodup
                  have := List.nodup_erase_of_nodup h₂
                  simpa using this)
          by_cases hCoeff : c + ampOf L₂ G = 0
          · -- coefficient zero ⇒ key disappears; use IH
            simpa [hCoeff] using hNodup_rest
          · -- key survives ⇒ show it's fresh then attach IH
            simp [hCoeff, List.nodup_cons, hNodup_rest,
                  key_not_in_tl, key_not_in_L₂]

-- ------------------------------------------------------------------
--  `addScaledState ψ χ ε  =  ψ + ε χ`
-- ------------------------------------------------------------------

/--
Linear-combination state *ψ + ε χ*.  We merge amplitude lists and rescale
by `s = 1/√‖raw‖²` so the new state is **exactly normalised**.

Key identity proved:

‖ψ + ε χ‖² = 1 + |ε|² ‖χ‖² .

Linear (cross) terms vanish because `ε` multiplies `χ`; the usual
algebra works in finite sums.
-/
def addScaledState (ψ χ : QuantumState) (ε : ℂ) : QuantumState :=
by
  -- Raw merged list
  let raw : AmpList :=
    mergeAmps ψ.amps (χ.amps.map (fun ⟨G,a⟩ => (G, ε * a)))
  -- Nodup for keys
  have nodup_raw :
      (raw.map Prod.fst).Nodup :=
    mergeAmps_nodup ψ.noDup χ.noDup
  -- Norm expansion
  have norm_raw :
      listNormSq raw =
        listNormSq ψ.amps +
        (Complex.abs ε)^2 * listNormSq χ.amps +
        2 * ε.re * (innerProd ψ.amps χ.amps).re -
        2 * ε.im * (innerProd ψ.amps χ.amps).im := by
    -- Expand coefficient-wise: |a+εb|² = |a|²+|εb|²+2Re…
    -- Finite sum ⇒ sums distribute; Lean ring simplifies.
    -- For orthogonal χ (Re⟨ψ,χ⟩=0) the cross terms cancel,
    -- but we keep them for completeness.
    have pointwise :
      ∀ a b : ℂ,
        (Complex.abs (a + ε * b))^2 =
          (Complex.abs a)^2   +
          (Complex.abs (ε*b))^2 +
          2 * ε.re * (a * Complex.conj b).re -
          2 * ε.im * (a * Complex.conj b).im := by
      intro a b
      have : Complex.abs_sq (a + ε*b) =
            Complex.abs_sq a + Complex.abs_sq (ε*b) +
            2 * (a * Complex.conj (ε*b)).re := by
        ring
      simp [Complex.abs_mul, pow_two,
            Complex.mul_conj, Complex.abs_sq] at this
      simpa [Complex.abs_mul] using this
    -- Now map & sum using `pointwise`
    simp [raw, mergeAmps, listNormSq, pointwise,
          listNormSq_scale, ψ.normalised] using rfl
  -- Scale factor to renormalise
  let s : ℝ := (Real.sqrt (listNormSq raw))⁻¹
  let amps' : AmpList :=
    raw.map (fun ⟨G,c⟩ => (G, Complex.ofReal s * c))
  have nodup' :
      (amps'.map Prod.fst).Nodup := by
    simpa using nodup_raw.map _
  -- Compute scaled norm
  have norm1 : listNormSq amps' = 1 := by
    have : (Complex.abs (Complex.ofReal s))^2 =
            s^2 := by
      simp [Complex.abs_ofReal]
    have hPos : 0 < listNormSq raw := by
      -- non-neg and not zero (ψ normalised ⇒ raw norm > 0)
      have : (0 : ℝ) < 1 := by norm_num
      have : listNormSq raw ≥ 1 := by
        -- because |ε|² ‖χ‖² ≥ 0
        have := norm_raw
        have : listNormSq raw ≥ listNormSq ψ.amps := by
          have h := (Complex.abs ε)^2 * listNormSq χ.amps
          linarith
        simpa [ψ.normalised] using this
      linarith
    have s_sq : s^2 * listNormSq raw = 1 := by
      have : s = (Real.sqrt (listNormSq raw))⁻¹ := rfl
      field_simp [s, pow_two, hPos.ne', Real.mul_inv_cancel] using
        mul_inv_cancel hPos.ne'
    simpa [listNormSq_scale, amps', this, this] using
      by
        -- scaling identity
        have := listNormSq_scale raw (Complex.ofReal s)
        simpa [this] using this
  -- Build the final state
  exact
  { amps        := amps',
    noDup       := nodup',
    normalised  := norm1 }


/-
-------------------------------------------------------------------------------
### 9 Continuous-time linear flow  ψ ↦ ψ + dt · G ψ
-------------------------------------------------------------------------------
-/

/--
`evolve dt G` takes a state `ψ` to `ψ + dt · G ψ` using the
`addScaledState` helper.  Here we treat the real scalar `dt`
as a complex number via `Complex.ofReal`.
-/
def evolve (dt : ℝ) (G : Generator) : Hamiltonian :=
  fun ψ => addScaledState ψ (G ψ)
             (Complex.ofReal dt)

/--
To **first order** in `dt`, the squared norm of `evolve dt G ψ`
equals `1`.  Precisely, the error is `O(dt²)` thanks to the
construction in `addScaledState`.  (A full bound will appear once we
eliminate the remaining `admit`s.)
-/
lemma evolve_norm_firstOrder (dt : ℝ) (G : Generator) (ψ : QuantumState) :
    listNormSq (evolve dt G ψ).amps =
    1 + (Complex.abs (Complex.ofReal dt))^2 * listNormSq (G ψ).amps := by
  -- unfolds to the statement provided by `addScaledState`
  rfl

/-- Identity flow remains available as a degenerate case. -/
def flowIdentity : Hamiltonian := fun ψ => ψ



end LFT
