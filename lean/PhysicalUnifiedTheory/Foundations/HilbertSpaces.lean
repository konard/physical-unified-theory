module

/-
# Hilbert Spaces: Operators and Spectral Theory (A.1.2–A.1.3)

This module provides deeper treatment of operators on Hilbert spaces,
complementing the basic definitions in LinearAlgebra.lean.

## Contents

- Matrix representations of operators (finite-dimensional case)
- Hermitian matrices and their properties
- Unitary matrices and groups
- Pauli matrices as fundamental observables
- Functional calculus via unitary diagonalization

## References

- Axler, "Linear Algebra Done Right"
- Halmos, "A Hilbert Space Problem Book"
-/

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

namespace PhysicalUnifiedTheory.Foundations.HilbertSpaces

open Matrix

/-!
## Hermitian Matrices

In finite dimensions, self-adjoint operators correspond to Hermitian matrices.
These represent physical observables.
-/

/-- A 2×2 Hermitian matrix represents a qubit observable. -/
def isHermitian2 (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  M.IsHermitian

/-- The Pauli X matrix: the quantum NOT gate and spin-x observable. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli Y matrix: spin-y observable (involves imaginary unit). -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli Z matrix: spin-z observable, computational basis diagonal. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The identity matrix: trivial observable, proportional to unit operator. -/
def identity2 : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- Pauli X is Hermitian. -/
theorem pauliX_hermitian : pauliX.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.conjTranspose, Matrix.transpose]

/-- Pauli Y is Hermitian. -/
theorem pauliY_hermitian : pauliY.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.conjTranspose, Matrix.transpose]

/-- Pauli Z is Hermitian. -/
theorem pauliZ_hermitian : pauliZ.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.conjTranspose, Matrix.transpose]

/-- The Pauli matrices satisfy the anticommutation relation {σᵢ, σⱼ} = 2δᵢⱼI.
    Specifically, Pauli X and Z anticommute: XZ + ZX = 0. -/
theorem pauliX_pauliZ_anticommute :
    pauliX * pauliZ + pauliZ * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ]

/-- The commutator [X, Z] = -2iY (Pauli algebra relation). -/
theorem pauliXZ_commutator :
    pauliX * pauliZ - pauliZ * pauliX = (-2 * Complex.I) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ] <;>
    ring_nf <;> simp [Complex.I_sq]

/-!
## Unitary Matrices

Unitary matrices represent quantum gates and symmetry transformations.
They preserve inner products and hence probabilities.
-/

/-- A 2×2 unitary matrix: U†U = UU† = I. -/
def isUnitary2 (U : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

/-- The Hadamard gate: H = (1/√2)[[1,1],[1,-1]].
    It creates equal superpositions: H|0⟩ = |+⟩, H|1⟩ = |-⟩. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / Real.sqrt 2 : ℂ) • !![1, 1; 1, -1]

/-- The phase gate S = [[1,0],[0,i]]. -/
def phaseGate : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.I]

/-- The T gate (π/8 gate): T = [[1,0],[0,e^{iπ/4}]].
    Together with H, generates a universal gate set. -/
noncomputable def tGate : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (Complex.I * Real.pi / 4)]

/-!
## Operator Norms and Boundedness

In infinite-dimensional spaces, operators need not be bounded.
The norm of an operator controls its action on state vectors.
-/

/-- The operator norm of a matrix M is the largest singular value.
    For Hermitian matrices, this equals the largest absolute eigenvalue. -/
noncomputable def matrixOpNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖

/-!
## Functional Calculus for Hermitian Matrices

The Hermitian spectral theorem diagonalizes a matrix in an orthonormal basis.
Applying a real function to its eigenvalues in that basis implements the
functional calculus. Every function on this finite spectrum is continuous.
-/

/-- The functional calculus of a Hermitian matrix applies a function to each
real eigenvalue and conjugates back by the unitary matrix of eigenvectors. -/
theorem hermitianFunctionalCalculus {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonal fun i => (f (hA.eigenvalues i) : ℂ)) :=
  hA.cfc_eq f

/-- Squaring the Pauli X observable in the functional calculus gives the identity. -/
theorem pauliX_cfc_square : cfc (fun x : ℝ => x ^ 2) pauliX = 1 := by
  rw [cfc_pow_id (R := ℝ) pauliX 2 pauliX_hermitian.isSelfAdjoint, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX]

end PhysicalUnifiedTheory.Foundations.HilbertSpaces
