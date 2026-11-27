module

/-
# Linear Algebra and Functional Analysis (A.1)

This module formalizes the linear algebra and functional analysis infrastructure
required for quantum mechanics and other tracks.

## Contents

- A.1.1: Hilbert space definitions and basic properties
- A.1.2: Bounded and unbounded operators
- A.1.3: Spectral theory (spectral theorem, functional calculus)
- A.1.4: Distribution theory (Schwartz space, tempered distributions)
- A.1.5: Rigged Hilbert spaces (Gelfand triples)

## Dependencies

- `Mathlib.Analysis.InnerProductSpace.Basic` for inner product spaces
- `Mathlib.Analysis.InnerProductSpace.Adjoint` for adjoint operators
- `Mathlib.Analysis.InnerProductSpace.LinearPMap` for domain-aware adjoints
- `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic` for bounded spectral calculus

## References

- Reed & Simon, "Methods of Modern Mathematical Physics"
- Rudin, "Functional Analysis"
-/

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PhysicalUnifiedTheory.Foundations.LinearAlgebra

/-!
## A.1.1: Hilbert Space Definitions

A Hilbert space is a complete inner product space over ℝ or ℂ.
In quantum mechanics, we work primarily with complex Hilbert spaces.
-/

/-- A separable complex Hilbert space modelled on a type with an orthonormal basis.
    Quantum states are unit vectors in such a space. -/
abbrev ComplexHilbertSpace (ι : Type*) [Fintype ι] :=
  EuclideanSpace ℂ ι

/-- The standard two-dimensional complex Hilbert space (qubit space). -/
abbrev QubitSpace := ComplexHilbertSpace (Fin 2)

/-- A quantum state is a unit vector in the Hilbert space.
    Normalization ensures probabilistic interpretation via the Born rule. -/
structure QuantumState (ι : Type*) [Fintype ι] where
  /-- The state vector -/
  vec : ComplexHilbertSpace ι
  /-- Normalization condition: ⟨ψ|ψ⟩ = 1 -/
  normalized : ‖vec‖ = 1

/-- The inner product of two quantum states (Dirac bra-ket notation: ⟨φ|ψ⟩). -/
noncomputable def braket {ι : Type*} [Fintype ι]
    (φ ψ : QuantumState ι) : ℂ :=
  inner ℂ φ.vec ψ.vec

/-- The probability amplitude squared gives the transition probability.
    This is a consequence of the Born rule. -/
noncomputable def transitionProbability {ι : Type*} [Fintype ι]
    (φ ψ : QuantumState ι) : ℝ :=
  Complex.normSq (braket φ ψ)

/-- Transition probabilities are non-negative. -/
theorem transitionProbability_nonneg {ι : Type*} [Fintype ι]
    (φ ψ : QuantumState ι) : 0 ≤ transitionProbability φ ψ :=
  Complex.normSq_nonneg _

/-- A state has transition probability 1 to itself (self-overlap). -/
theorem transitionProbability_self {ι : Type*} [Fintype ι]
    (ψ : QuantumState ι) : transitionProbability ψ ψ = 1 := by
  simp [transitionProbability, braket, inner_self_eq_norm_sq_to_K, ψ.normalized]

/-!
## A.1.2: Linear Operators

Observables in quantum mechanics correspond to self-adjoint (Hermitian) operators.
Symmetries are represented by unitary operators.
-/

/-- A bounded linear map on a Hilbert space representing a quantum observable.
    In finite dimensions, all linear operators are bounded. -/
abbrev BoundedOp (ι : Type*) [Fintype ι] :=
  ComplexHilbertSpace ι →L[ℂ] ComplexHilbertSpace ι

/-- The identity operator on a Hilbert space. -/
noncomputable def idOp (ι : Type*) [Fintype ι] :
    BoundedOp ι :=
  ContinuousLinearMap.id ℂ (ComplexHilbertSpace ι)

/-- Composition of two bounded operators. -/
noncomputable def compOp {ι : Type*} [Fintype ι]
    (A B : BoundedOp ι) : BoundedOp ι :=
  A.comp B

/-- The adjoint of a bounded operator A is denoted A†.
    In quantum mechanics, an observable is self-adjoint: A = A†. -/
noncomputable def adjointOp {ι : Type*} [Fintype ι]
    (A : BoundedOp ι) : BoundedOp ι :=
  ContinuousLinearMap.adjoint A

/-- An operator is self-adjoint (Hermitian) if A = A†.
    Hermitian operators have real eigenvalues, corresponding to measurable quantities. -/
def isSelfAdjoint {ι : Type*} [Fintype ι] (A : BoundedOp ι) : Prop :=
  adjointOp A = A

/-- An operator is unitary if A† ∘ A = A ∘ A† = id.
    Unitary operators preserve inner products and represent symmetries. -/
def isUnitary {ι : Type*} [Fintype ι] (U : BoundedOp ι) : Prop :=
  compOp (adjointOp U) U = idOp ι ∧ compOp U (adjointOp U) = idOp ι

/-- The commutator [A, B] = AB - BA measures non-commutativity.
    Non-zero commutators encode Heisenberg uncertainty relations. -/
noncomputable def commutator {ι : Type*} [Fintype ι]
    (A B : BoundedOp ι) : BoundedOp ι :=
  compOp A B - compOp B A

/-- A linear operator on a complex Hilbert space, with its domain as a submodule.
The operator acts on the domain and can be unbounded there. -/
abbrev HilbertOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  H →ₗ.[ℂ] H

section GeneralOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A self-adjoint operator has dense domain and closed graph. -/
theorem selfAdjointOperator_dense_closed {A : HilbertOperator H} (hA : IsSelfAdjoint A) :
    Dense (A.domain : Set H) ∧ A.IsClosed :=
  ⟨hA.dense_domain, hA.isClosed⟩

/-- Restricting a bounded observable to a dense core keeps the same adjoint,
whose domain is the whole space. -/
theorem adjoint_dense_restriction (A : H →L[ℂ] H) {D : Submodule ℂ H}
    (hD : Dense (D : Set H)) :
    (A.toPMap D).adjoint = A.adjoint.toPMap ⊤ :=
  A.toPMap_adjoint_eq_adjoint_toPMap_of_dense hD

/-!
## A.1.3: Spectral Theory

The continuous functional calculus realizes functions on the spectrum of a
bounded self-adjoint operator as operators on the same Hilbert space.
-/

/-- The continuous functional calculus on the real spectrum of a bounded
observable, as a star algebra homomorphism. -/
noncomputable def observableCalculus (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H) :=
  cfcHom hA

/-- The coordinate function on the spectrum recovers the original observable. -/
theorem observableCalculus_id (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    observableCalculus A hA ((ContinuousMap.id ℝ).restrict (spectrum ℝ A)) = A :=
  cfcHom_id hA

/-- The spectrum of a function of an observable is the image of its spectrum
under that function. -/
theorem observableCalculus_spectrum (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (f : C(spectrum ℝ A, ℝ)) :
    spectrum ℝ (observableCalculus A hA f) = Set.range f :=
  cfcHom_map_spectrum hA f

end GeneralOperators

/-- A projection operator satisfies P² = P and P = P†.
    Projections represent quantum measurement events. -/
def isProjection {ι : Type*} [Fintype ι] (P : BoundedOp ι) : Prop :=
  compOp P P = P ∧ isSelfAdjoint P

/-- The expectation value of an observable A in state ψ is ⟨ψ|A|ψ⟩.
    This gives the average measurement outcome. -/
noncomputable def expectationValue {ι : Type*} [Fintype ι]
    (A : BoundedOp ι) (ψ : QuantumState ι) : ℂ :=
  inner ℂ ψ.vec (A ψ.vec)

/-- Expectation values of self-adjoint operators are real. -/
theorem expectationValue_real {ι : Type*} [Fintype ι]
    (A : BoundedOp ι) (ψ : QuantumState ι)
    (hA : isSelfAdjoint A) :
    (expectationValue A ψ).im = 0 := by
  have h := ContinuousLinearMap.adjoint_inner_left A ψ.vec ψ.vec
  rw [show ContinuousLinearMap.adjoint A = A from hA] at h
  have hIm := inner_im_symm (𝕜 := ℂ) ψ.vec (A ψ.vec)
  rw [h] at hIm
  change (inner ℂ ψ.vec (A ψ.vec)).im = 0
  change (inner ℂ ψ.vec (A ψ.vec)).im = -(inner ℂ ψ.vec (A ψ.vec)).im at hIm
  linarith

/-!
## A.1.4: Distribution Theory

Distributions (generalized functions) extend classical functions and are essential
for making sense of the Dirac delta and other singular objects in physics.
-/

-- `Foundations.Distributions` supplies these spaces and their embeddings.

/-!
## A.1.5: Rigged Hilbert Spaces (Gelfand Triples)

A rigged Hilbert space (Gelfand triple) Φ ⊂ H ⊂ Φ' provides the mathematical
framework for handling continuous spectra in quantum mechanics (e.g., position/momentum).

**Hypothesis**: Rigged Hilbert spaces resolve continuous spectrum issues in QM.
-/

-- `Foundations.Distributions` constructs the Schwartz–L²–tempered triple.

end PhysicalUnifiedTheory.Foundations.LinearAlgebra
