# Quantum Mechanics: Formalization Guide

This document provides background on quantum mechanics for contributors working on the formalization.

## Overview

Quantum mechanics describes physics at atomic and subatomic scales. It differs fundamentally from classical physics:

1. **Superposition**: Systems can exist in multiple states simultaneously
2. **Measurement**: Observation affects the system and produces probabilistic outcomes
3. **Entanglement**: Correlations between particles that defy classical explanation
4. **Wave-Particle Duality**: Matter exhibits both wave and particle properties

## Mathematical Framework

### State Space

A quantum system is described by a **Hilbert space** H:
- States are unit vectors |ψ⟩ ∈ H with ‖ψ‖ = 1
- Overall phase is unphysical: |ψ⟩ and e^(iθ)|ψ⟩ represent the same state
- More general: density matrices ρ for mixed states

For a qubit (2-level system):
```
H = ℂ²
|ψ⟩ = α|0⟩ + β|1⟩ with |α|² + |β|² = 1
```

### Observables

Physical observables correspond to **self-adjoint operators** A = A†:
- Eigenvalues are possible measurement outcomes
- Eigenvectors are states with definite values

Examples:
- Position: x̂ψ(x) = xψ(x)
- Momentum: p̂ψ(x) = -iℏ(∂/∂x)ψ(x)
- Energy (Hamiltonian): H

### Measurement

The **Born rule** gives measurement probabilities:
- Probability of outcome a: P(a) = |⟨a|ψ⟩|²
- After measurement, state collapses to |a⟩

For a qubit in state |ψ⟩ = α|0⟩ + β|1⟩:
- P(0) = |α|²
- P(1) = |β|²

### Time Evolution

The **Schrödinger equation** governs dynamics:
```
iℏ ∂|ψ⟩/∂t = H|ψ⟩
```

Solution: |ψ(t)⟩ = e^(-iHt/ℏ)|ψ(0)⟩

The evolution operator U(t) = e^(-iHt/ℏ) is unitary.

## Key Structures to Formalize

### 1. Qubit Systems

The simplest non-trivial quantum system:

```lean
-- In Lean
structure QubitState where
  vec : Fin 2 → ℂ
  normalized : ‖vec‖ = 1
```

```coq
(* In Rocq *)
Record QubitState := {
  amplitude_0 : C;
  amplitude_1 : C;
  is_normalized : |amplitude_0|² + |amplitude_1|² = 1
}.
```

### 2. Quantum Gates

Unitary 2×2 matrices acting on qubits:

| Gate | Matrix | Action |
|------|--------|--------|
| Pauli X | [[0,1],[1,0]] | Bit flip: \|0⟩↔\|1⟩ |
| Pauli Y | [[0,-i],[i,0]] | Bit + phase flip |
| Pauli Z | [[1,0],[0,-1]] | Phase flip: \|1⟩→-\|1⟩ |
| Hadamard | (1/√2)[[1,1],[1,-1]] | Creates superposition |
| CNOT | 4×4 | Entangling gate |

### 3. Harmonic Oscillator

The quantum harmonic oscillator is fundamental:

- Hamiltonian: H = (p² + ω²x²)/2 = ℏω(a†a + 1/2)
- Energy levels: E_n = ℏω(n + 1/2)
- Creation: a†|n⟩ = √(n+1)|n+1⟩
- Annihilation: a|n⟩ = √n|n-1⟩

### 4. Angular Momentum

Operators J_x, J_y, J_z satisfying:
```
[J_x, J_y] = iℏJ_z  (cyclic)
```

Eigenvalues: j(j+1)ℏ² for J² and mℏ for J_z, where m ∈ {-j, ..., j}.

### 5. Composite Systems

For systems A and B:
- State space: H_A ⊗ H_B
- Separable: |ψ⟩ = |ψ_A⟩ ⊗ |ψ_B⟩
- Entangled: cannot be written as tensor product

Bell state (maximally entangled):
```
|Φ⁺⟩ = (|00⟩ + |11⟩)/√2
```

## Formalization Challenges

### 1. Unbounded Operators

Many physical operators (position, momentum, Hamiltonian) are unbounded:
- Not defined on all of H
- Domain considerations are crucial
- Mathlib has foundational work but gaps remain

### 2. Infinite Dimensions

Most interesting systems require infinite-dimensional Hilbert spaces:
- L²(ℝ³) for a particle in 3D
- Fock space for variable particle number
- Careful treatment of convergence required

### 3. Continuous Spectrum

Position and momentum have continuous spectra:
- Eigenfunctions are distributions, not proper vectors
- Requires rigged Hilbert space formalism
- Often handled via spectral measures

### 4. Path Integrals

Feynman's path integral formulation:
```
⟨x_f, t_f | x_i, t_i⟩ = ∫ Dx(t) e^(iS[x]/ℏ)
```

Mathematically ill-defined in general (measure on path space).

## Resources

### Textbooks
- Sakurai, "Modern Quantum Mechanics"
- Nielsen & Chuang, "Quantum Computation and Quantum Information"
- Griffiths, "Introduction to Quantum Mechanics"

### Existing Formalizations
- [Lean-QuantumInfo](https://github.com/duckki/lean-quantum)
- [PhysLean](https://physlean.com/) - Quantum harmonic oscillator
- [CoqQ](https://ncatlab.org/nlab/show/CoqQ) - Quantum programs in Coq

### Papers
- [Formalization of Quantum Stein's Lemma](https://arxiv.org/html/2510.08672v1)
- [LeanForPhysics](https://arxiv.org/html/2510.26094)

## Getting Started

1. Start with finite-dimensional systems (qubits, qutrits)
2. Formalize basic gates and their properties
3. Prove simple theorems (unitarity, orthonormality)
4. Gradually add complexity (multiple qubits, entanglement)
5. Connect to Mathlib's inner product space infrastructure

See the `lean/PhysicalUnifiedTheory/QuantumMechanics/` directory for our implementations.
