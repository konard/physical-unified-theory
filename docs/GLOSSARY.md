# Glossary of Terms

A reference guide for key concepts in quantum mechanics, general relativity, and their attempted unification.

---

## Mathematical Foundations

### Hilbert Space
A complete inner product space. In quantum mechanics, states are vectors in a complex Hilbert space. Finite-dimensional examples include ℂⁿ; infinite-dimensional examples include L²(ℝ³).

### Inner Product
A function ⟨·,·⟩ : H × H → ℂ that is linear in the second argument, conjugate-symmetric, and positive definite. Used to define orthogonality and probabilities.

### Self-Adjoint Operator
An operator A on a Hilbert space such that A = A†. In quantum mechanics, observables are self-adjoint operators. Also called Hermitian in finite dimensions.

### Unitary Operator
An operator U such that U†U = UU† = I. Unitary operators preserve inner products and represent symmetries and time evolution.

### Tensor Product
A construction H₁ ⊗ H₂ that combines two Hilbert spaces. Used to describe composite quantum systems.

### Manifold
A topological space that locally looks like ℝⁿ. Spacetime in general relativity is a 4-dimensional smooth manifold.

### Metric Tensor
A symmetric (0,2)-tensor field gμν that defines distances and angles on a manifold. In GR, the metric encodes gravity.

### Curvature Tensor
The Riemann tensor R^ρ_σμν measures how vectors rotate when parallel transported around loops. Non-zero curvature indicates gravity.

---

## Quantum Mechanics

### State Vector
A unit vector |ψ⟩ in a Hilbert space representing the state of a quantum system. Contains all physical information.

### Superposition
A fundamental quantum principle: if |ψ₁⟩ and |ψ₂⟩ are possible states, so is α|ψ₁⟩ + β|ψ₂⟩ (with normalization).

### Observable
A physical quantity that can be measured. Represented by a self-adjoint operator. Measurement outcomes are eigenvalues.

### Born Rule
The probability of measuring eigenvalue a for observable A in state |ψ⟩ is |⟨a|ψ⟩|², where |a⟩ is the eigenstate.

### Schrödinger Equation
The equation governing time evolution: iℏ∂|ψ⟩/∂t = H|ψ⟩, where H is the Hamiltonian operator.

### Qubit
A two-level quantum system. The simplest non-trivial quantum system, used as the basic unit in quantum computing.

### Entanglement
A quantum correlation between subsystems that cannot be described by local hidden variables. Key resource in quantum information.

### Pauli Matrices
The 2×2 matrices σₓ, σᵧ, σᵤ that generate rotations of a qubit. Fundamental in spin-1/2 physics.

### Commutator
[A, B] = AB - BA. Non-commuting observables cannot be simultaneously measured with arbitrary precision (Heisenberg uncertainty).

### Density Matrix
ρ = Σᵢ pᵢ |ψᵢ⟩⟨ψᵢ|. Describes mixed states (statistical ensembles) rather than pure states.

---

## General Relativity

### Spacetime
The 4-dimensional manifold combining space and time. Events are points in spacetime.

### Minkowski Metric
The flat spacetime metric of special relativity: ds² = -c²dt² + dx² + dy² + dz². No gravity.

### Lorentz Transformation
Coordinate transformations that preserve the Minkowski metric. Relate observations in different inertial frames.

### Geodesic
The path of a freely falling particle. Extremizes proper time. Straight lines in flat spacetime, curves in curved spacetime.

### Einstein Field Equations
Gμν = 8πG Tμν. Relates spacetime curvature (left side) to matter-energy content (right side).

### Ricci Tensor
Rμν = R^ρ_μρν. A contraction of the Riemann tensor. Appears in the Einstein equations.

### Scalar Curvature
R = g^μν Rμν. The trace of the Ricci tensor. Measures "total curvature" at a point.

### Schwarzschild Solution
The unique spherically symmetric vacuum solution. Describes non-rotating black holes.

### Event Horizon
The boundary of a black hole from which nothing can escape. Located at r = 2GM/c² for Schwarzschild.

### Cosmological Constant
Λ. An additional term in Einstein's equations representing vacuum energy (dark energy).

### ADM Formalism
A Hamiltonian formulation of GR. Decomposes spacetime into space + time. Basis for canonical quantum gravity.

---

## Quantum Field Theory

### Field
A physical quantity defined at every point in spacetime. Example: electromagnetic field, electron field.

### Quantization
The process of promoting a classical field to a quantum operator satisfying canonical commutation relations.

### Fock Space
The Hilbert space for variable particle number. Built from tensor products of single-particle spaces.

### Creation/Annihilation Operators
Operators a† and a that add or remove particles from a state. Satisfy [a, a†] = 1.

### Vacuum State
|0⟩. The state with no particles. Has non-zero energy due to quantum fluctuations.

### Propagator
G(x,y). The amplitude for a particle to travel from y to x. Fundamental building block of QFT.

### Feynman Diagram
A pictorial representation of terms in perturbation theory. Vertices represent interactions.

### Renormalization
A systematic procedure for handling infinities in QFT calculations. Absorbs divergences into physical parameters.

### Gauge Symmetry
A local symmetry transformation. The Standard Model is based on SU(3) × SU(2) × U(1) gauge symmetry.

### Yang-Mills Theory
A non-Abelian gauge theory. Foundation of the Standard Model (QCD, electroweak theory).

---

## Unification and Quantum Gravity

### Planck Scale
The scale where quantum gravity effects are important: ℓ_P ≈ 10⁻³⁵ m, t_P ≈ 10⁻⁴⁴ s, E_P ≈ 10¹⁹ GeV.

### Background Independence
A property where the theory does not assume a fixed spacetime. GR is background-independent; standard QFT is not.

### Problem of Time
In canonical quantum gravity, the Hamiltonian constraint H|Ψ⟩ = 0 implies no time evolution. A major conceptual puzzle.

### Non-renormalizability
Gravity treated as a QFT requires infinitely many counterterms. Signals breakdown at high energies.

### String Theory
A framework where fundamental objects are 1D strings rather than points. Requires extra dimensions. Includes gravity.

### Loop Quantum Gravity
A canonical quantization of GR. Predicts discrete area and volume spectra. Uses spin networks.

### Spin Network
A graph with edges labeled by spins. Represents a quantum state of geometry in LQG.

### Spin Foam
A 2D analog of spin networks representing spacetime histories. Path integral formulation of LQG.

### Holographic Principle
Information in a region scales with surface area, not volume. Realized in AdS/CFT correspondence.

### AdS/CFT Correspondence
A duality between gravity in Anti-de Sitter space and a conformal field theory on its boundary. A non-perturbative definition of quantum gravity in AdS.

### Emergence
The idea that spacetime (and gravity) might not be fundamental but emerge from more primitive structures (like entanglement).

---

## Proof Assistants

### Lean
A theorem prover developed at Microsoft Research. Uses dependent type theory. Mathlib provides extensive mathematics.

### Rocq (Coq)
A theorem prover developed at Inria. One of the oldest and most established proof assistants.

### Mathlib
The mathematical library for Lean. Contains formalized algebra, analysis, topology, and more.

### Dependent Type
A type that depends on a value. Enables expressing mathematical statements as types (Curry-Howard correspondence).

### Tactic
A command that constructs proofs in an interactive proof assistant. Examples: `simp`, `ring`, `exact`.

### Formalization
The process of expressing mathematics in a proof assistant's formal language, enabling mechanical verification.

---

## Resources

- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [PhysLean](https://physlean.com/)
- [Stanford Encyclopedia of Philosophy: Quantum Gravity](https://plato.stanford.edu/entries/quantum-gravity/)
- [nLab](https://ncatlab.org/) - Category-theoretic perspective on mathematics and physics
