import LFT.Dynamics
import LFT.Complex
import LFT.Measurement

namespace LFT

/-!
# Two-Level System (Qubit) Example

This file demonstrates LFT with a concrete two-level quantum system,
showing how a qubit emerges from logical constraints.
-/

/-- The two logical states of a qubit -/
inductive QubitBasis
  | zero : QubitBasis  -- Logical state |0⟩
  | one : QubitBasis   -- Logical state |1⟩

/-- Two-vertex graph for qubit -/
def QubitGraph : LogicalGraph where
  Vertex := QubitBasis
  Edge := fun a b => a = b  -- Only self-entailment for basis states
  decidable_vertex := by
    unfold DecidableEq
    intro a b
    cases a <;> cases b <;> simp <;> decide
  decidable_edge := fun a b => by
    unfold Decidable
    cases a <;> cases b <;> simp <;> decide

/-- Negation flips qubit states -/
instance : HasNegation QubitBasis where
  neg := fun
    | QubitBasis.zero => QubitBasis.one
    | QubitBasis.one => QubitBasis.zero
  neg_involutive := by
    intro v
    cases v <;> rfl

/-- The qubit graph is admissible -/
theorem qubit_is_admissible : IsAdmissible QubitGraph := by
  unfold IsAdmissible
  constructor
  · -- Identity
    intro v
    rfl
  constructor
  · -- Transitivity
    intro u v w huv hvw
    simp [QubitGraph] at *
    rw [huv, hvw]
  constructor
  · -- Non-contradiction
    intro v
    push_neg
    intro w
    cases v <;> cases w <;> simp [Reachable, QubitGraph]
  · -- Excluded middle
    intro v _
    cases v
    · right
      use QubitBasis.one
      unfold Reachable
      use 0
      use fun _ => QubitBasis.one
      simp
    · left
      use QubitBasis.one
      unfold Reachable
      use 0
      use fun _ => QubitBasis.one
      simp

/-- Qubit state as superposition -/
structure QubitState where
  α : ℂ  -- Amplitude for |0⟩
  β : ℂ  -- Amplitude for |1⟩
  normalized : Complex.abs α ^ 2 + Complex.abs β ^ 2 = 1

/-- Convert QubitState to general QuantumState -/
def qubitToQuantum (q : QubitState) : QuantumState :=
  ⟨fun G =>
    if h : G.graph = QubitGraph then
      match G.graph.Vertex with
      | QubitBasis.zero => q.α
      | QubitBasis.one => q.β
    else 0,
  sorry⟩ -- normalization proof

/-- Standard qubit basis states -/
def ket_0 : QubitState := ⟨1, 0, by simp⟩
def ket_1 : QubitState := ⟨0, 1, by simp⟩

/-- Equal superposition (|+⟩ state) -/
noncomputable def ket_plus : QubitState :=
  ⟨Complex.ofReal (1 / Real.sqrt 2),
   Complex.ofReal (1 / Real.sqrt 2),
   by simp; ring_nf; sorry⟩

/-- Phase superposition (|i⟩ state) -/
noncomputable def ket_i : QubitState :=
  ⟨Complex.ofReal (1 / Real.sqrt 2),
   Complex.I / Complex.ofReal (Real.sqrt 2),
   sorry⟩

/-- Pauli X operation (logical NOT) -/
def pauli_X (q : QubitState) : QubitState :=
  ⟨q.β, q.α, by rw [add_comm]; exact q.normalized⟩

/-- Pauli Z operation (phase flip) -/
def pauli_Z (q : QubitState) : QubitState :=
  ⟨q.α, -q.β, by simp [q.normalized]⟩

/-- Hadamard creates superposition -/
noncomputable def hadamard (q : QubitState) : QubitState :=
  ⟨(q.α + q.β) / Complex.ofReal (Real.sqrt 2),
   (q.α - q.β) / Complex.ofReal (Real.sqrt 2),
   sorry⟩

/-- Measurement probability for |0⟩ -/
def prob_zero (q : QubitState) : ℝ := Complex.abs q.α ^ 2

/-- Example: Hadamard on |0⟩ gives |+⟩ -/
example : hadamard ket_0 = ket_plus := by
  unfold hadamard ket_0 ket_plus
  simp
  sorry

/-- Example: Double Hadamard is identity -/
example (q : QubitState) : hadamard (hadamard q) = q := by
  unfold hadamard
  simp
  sorry

/-- Example: Measurement probabilities sum to 1 -/
example (q : QubitState) :
    prob_zero q + prob_zero (pauli_X q) = 1 := by
  unfold prob_zero pauli_X
  simp
  exact q.normalized

end LFT
