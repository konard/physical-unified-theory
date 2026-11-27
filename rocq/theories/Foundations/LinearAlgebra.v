(** * Linear Algebra and Functional Analysis (A.1)

    This module formalizes the linear algebra and functional analysis infrastructure
    required for quantum mechanics and other tracks.

    Contents:
    - A.1.1: Hilbert space definitions and basic properties
    - A.1.2: Bounded linear operators (2x2 matrix case)
    - A.1.3: Expectation values

    References:
    - Reed & Simon, "Methods of Modern Mathematical Physics"
    - Rudin, "Functional Analysis"
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

Require Import PhysicalUnifiedTheory.Foundations.Basic.

(** ** A.1.1: Hilbert Space Definitions

    In finite dimensions, a Hilbert space over ℝ is a real vector space
    with an inner product. A normalized state has unit norm. *)

(** A state in a 2D real Hilbert space (analogous to a qubit in the real case). *)
Record State2D : Type := mkState2D {
  component0 : R;
  component1 : R;
  (** Normalization: α² + β² = 1 *)
  normalized2D : component0 * component0 + component1 * component1 = 1
}.

(** The basis state |0⟩ (component0 = 1, component1 = 0). *)
Program Definition basis_state0 : State2D := {|
  component0 := 1;
  component1 := 0
|}.
Next Obligation.
  lra.
Qed.

(** The basis state |1⟩ (component0 = 0, component1 = 1). *)
Program Definition basis_state1 : State2D := {|
  component0 := 0;
  component1 := 1
|}.
Next Obligation.
  lra.
Qed.

(** The inner product of two 2D states: ⟨φ|ψ⟩ = φ₀ψ₀ + φ₁ψ₁. *)
Definition inner2D (phi psi : State2D) : R :=
  phi.(component0) * psi.(component0) + phi.(component1) * psi.(component1).

(** The basis states are orthogonal: ⟨0|1⟩ = 0. *)
Lemma basis_orthogonal : inner2D basis_state0 basis_state1 = 0.
Proof.
  unfold inner2D, basis_state0, basis_state1.
  simpl.
  lra.
Qed.

(** Each basis state has norm 1: ⟨0|0⟩ = 1. *)
Lemma basis0_normalized : inner2D basis_state0 basis_state0 = 1.
Proof.
  unfold inner2D, basis_state0.
  simpl.
  lra.
Qed.

(** Each basis state has norm 1: ⟨1|1⟩ = 1. *)
Lemma basis1_normalized : inner2D basis_state1 basis_state1 = 1.
Proof.
  unfold inner2D, basis_state1.
  simpl.
  lra.
Qed.

(** For any normalized state, the inner product with itself equals 1. *)
Lemma state_self_inner (psi : State2D) : inner2D psi psi = 1.
Proof.
  unfold inner2D.
  pose proof psi.(normalized2D) as h.
  lra.
Qed.

(** ** A.1.2: Linear Operators *)

(** A 2×2 real matrix represents a linear operator on the 2D Hilbert space. *)
Record Matrix2x2 : Type := mkMatrix2x2 {
  m00 : R; m01 : R;
  m10 : R; m11 : R
}.

(** Apply a matrix to a vector (matrix-vector multiplication). *)
Definition matVecMul (M : Matrix2x2) (v : R * R) : R * R :=
  (M.(m00) * fst v + M.(m01) * snd v,
   M.(m10) * fst v + M.(m11) * snd v).

(** Matrix multiplication. *)
Definition matMul (A B : Matrix2x2) : Matrix2x2 := {|
  m00 := A.(m00) * B.(m00) + A.(m01) * B.(m10);
  m01 := A.(m00) * B.(m01) + A.(m01) * B.(m11);
  m10 := A.(m10) * B.(m00) + A.(m11) * B.(m10);
  m11 := A.(m10) * B.(m01) + A.(m11) * B.(m11)
|}.

(** The transpose of a matrix (also the adjoint for real matrices). *)
Definition transpose (M : Matrix2x2) : Matrix2x2 := {|
  m00 := M.(m00); m01 := M.(m10);
  m10 := M.(m01); m11 := M.(m11)
|}.

(** A matrix is symmetric (Hermitian in the real case) if M = Mᵀ,
    i.e., the off-diagonal entries are equal. *)
Definition isSymmetric (M : Matrix2x2) : Prop :=
  M.(m01) = M.(m10).

(** The Pauli Z matrix: [[1, 0], [0, -1]]. *)
Definition pauliZ_real : Matrix2x2 := {|
  m00 := 1; m01 := 0;
  m10 := 0; m11 := -1
|}.

(** Pauli Z is symmetric. *)
Lemma pauliZ_symmetric : isSymmetric pauliZ_real.
Proof.
  unfold isSymmetric, pauliZ_real. simpl. lra.
Qed.

(** The identity matrix. *)
Definition identity2 : Matrix2x2 := {|
  m00 := 1; m01 := 0;
  m10 := 0; m11 := 1
|}.

(** The identity matrix is symmetric. *)
Lemma identity_symmetric : isSymmetric identity2.
Proof.
  unfold isSymmetric, identity2. simpl. lra.
Qed.

(** ** A.1.3: Expectation Values *)

(** The expectation value of operator M in state ψ: ⟨ψ|M|ψ⟩.
    This gives the average measurement outcome. *)
Definition expectationValue2D (M : Matrix2x2) (psi : State2D) : R :=
  let Mpsi := matVecMul M (psi.(component0), psi.(component1)) in
  psi.(component0) * fst Mpsi + psi.(component1) * snd Mpsi.

(** The expectation value of Pauli Z in the |0⟩ state is +1.
    This corresponds to measuring spin-up: ⟨0|σ_z|0⟩ = +1. *)
Lemma expectation_pauliZ_basis0 :
    expectationValue2D pauliZ_real basis_state0 = 1.
Proof.
  unfold expectationValue2D, pauliZ_real, basis_state0, matVecMul.
  simpl. lra.
Qed.

(** The expectation value of Pauli Z in the |1⟩ state is -1.
    This corresponds to measuring spin-down: ⟨1|σ_z|1⟩ = -1. *)
Lemma expectation_pauliZ_basis1 :
    expectationValue2D pauliZ_real basis_state1 = -1.
Proof.
  unfold expectationValue2D, pauliZ_real, basis_state1, matVecMul.
  simpl. lra.
Qed.
