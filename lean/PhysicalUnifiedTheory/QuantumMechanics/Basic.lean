/-
# Quantum Mechanics

This module formalizes the mathematical foundations of quantum mechanics.

## Contents

1. State spaces and Hilbert spaces
2. Observables as self-adjoint operators
3. Measurement postulates
4. Time evolution (Schrödinger equation)
5. Basic quantum systems

## Key Postulates

1. **States**: A quantum system is described by a state vector |ψ⟩ in a complex Hilbert space H.
2. **Observables**: Physical observables correspond to self-adjoint (Hermitian) operators on H.
3. **Measurement**: Measurement outcomes are eigenvalues; probabilities follow the Born rule.
4. **Evolution**: Time evolution is governed by the Schrödinger equation: iℏ∂|ψ⟩/∂t = H|ψ⟩.

## References

- Sakurai, "Modern Quantum Mechanics"
- Nielsen & Chuang, "Quantum Computation and Quantum Information"
- Lean-QuantumInfo: https://github.com/duckki/lean-quantum
-/

import PhysicalUnifiedTheory.Foundations.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Hermitian

namespace PhysicalUnifiedTheory.QuantumMechanics

open PhysicalUnifiedTheory.Foundations
open scoped Matrix ComplexOrder

/-!
## Qubit: The Simplest Quantum System

A qubit is a two-level quantum system, the quantum analog of a classical bit.
-/

/-- A qubit state is a unit vector in a 2D complex Hilbert space. -/
structure QubitState where
  /-- The underlying vector in ℂ² -/
  vec : Fin 2 → ℂ
  /-- The state must be normalized: |α|² + |β|² = 1 -/
  normalized : ‖EuclideanSpace.equiv (Fin 2) ℂ |>.symm vec‖ = 1

/-- The computational basis state |0⟩ -/
def ket0 : QubitState where
  vec := ![1, 0]
  normalized := by simp [EuclideanSpace.norm_eq]

/-- The computational basis state |1⟩ -/
def ket1 : QubitState where
  vec := ![0, 1]
  normalized := by simp [EuclideanSpace.norm_eq]

/-!
## Quantum Gates

Quantum gates are unitary operators acting on qubit states.
-/

/-- The Pauli X gate (quantum NOT gate): |0⟩ ↔ |1⟩ -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli Y gate -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli Z gate: |0⟩ → |0⟩, |1⟩ → -|1⟩ -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Hadamard gate: creates superposition -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / Real.sqrt 2 : ℂ) • !![1, 1; 1, -1]

/-- Pauli X is Hermitian (self-adjoint). -/
theorem pauliX_hermitian : pauliX.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose]

/-- Pauli Z is Hermitian (self-adjoint). -/
theorem pauliZ_hermitian : pauliZ.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose]

/-!
## Born Rule and Measurement

The probability of measuring a basis state is the squared magnitude of its amplitude.
-/

/-- Probability of measuring |0⟩ for a qubit state -/
def prob0 (ψ : QubitState) : ℝ := Complex.normSq (ψ.vec 0)

/-- Probability of measuring |1⟩ for a qubit state -/
def prob1 (ψ : QubitState) : ℝ := Complex.normSq (ψ.vec 1)

/-- Probabilities sum to 1 (conservation of probability) -/
theorem prob_sum_one (ψ : QubitState) : prob0 ψ + prob1 ψ = 1 := by
  simp only [prob0, prob1]
  have h := ψ.normalized
  simp only [EuclideanSpace.norm_eq] at h
  have h2 : Real.sqrt (∑ i : Fin 2, ‖ψ.vec i‖^2) = 1 := h
  have h3 : ∑ i : Fin 2, ‖ψ.vec i‖^2 = 1 := by
    have := Real.sqrt_eq_one.mp h2
    linarith [Finset.sum_nonneg (fun i _ => sq_nonneg ‖ψ.vec i‖)]
  simp only [Fin.sum_univ_two, Complex.norm_eq_abs] at h3
  simp only [Complex.normSq_eq_abs, sq_abs]
  exact h3

end PhysicalUnifiedTheory.QuantumMechanics
