(** * Hilbert Spaces: Operators and Spectral Theory (A.1.2–A.1.3)

    This module provides deeper treatment of operators on Hilbert spaces,
    complementing LinearAlgebra.v with density matrices and the Born rule.

    Contents:
    - Density matrices (mixed quantum states)
    - Born rule and measurement probabilities

    References:
    - Halmos, "A Hilbert Space Problem Book"
    - Nielsen & Chuang, "Quantum Computation and Quantum Information"
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

Require Import PhysicalUnifiedTheory.Foundations.Basic.
Require Import PhysicalUnifiedTheory.Foundations.LinearAlgebra.

(** ** Density Matrices

    A density matrix ρ represents a (possibly mixed) quantum state.
    Properties: ρ is symmetric, Tr(ρ) = 1, diagonal entries >= 0.
    For a pure state |ψ⟩: ρ = |ψ⟩⟨ψ|. *)

(** A density matrix in 2D: symmetric, trace = 1, non-negative diagonal. *)
Record DensityMatrix2D : Type := mkDensity {
  d00 : R;  (** probability weight of |0⟩ *)
  d01 : R;  (** off-diagonal coherence *)
  d11 : R;  (** probability weight of |1⟩ *)
  (** Trace = 1: d00 + d11 = 1 *)
  trace_one : d00 + d11 = 1;
  (** Positive semidefinite diagonal entries *)
  d00_nonneg : 0 <= d00;
  d11_nonneg : 0 <= d11
}.

(** The pure state |0⟩ has density matrix [[1, 0], [0, 0]]. *)
Program Definition pure_state0 : DensityMatrix2D := {|
  d00 := 1; d01 := 0; d11 := 0
|}.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.

(** The pure state |1⟩ has density matrix [[0, 0], [0, 1]]. *)
Program Definition pure_state1 : DensityMatrix2D := {|
  d00 := 0; d01 := 0; d11 := 1
|}.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.

(** The maximally mixed state has density matrix (1/2)I = [[1/2, 0], [0, 1/2]].
    It represents complete ignorance about the quantum state. *)
Program Definition maximallyMixed : DensityMatrix2D := {|
  d00 := 1/2; d01 := 0; d11 := 1/2
|}.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.

(** ** Born Rule

    The probability of measuring outcome |0⟩ in density matrix ρ is Tr(P₀ρ) = ρ₀₀.
    The probability of measuring outcome |1⟩ is Tr(P₁ρ) = ρ₁₁. *)

(** Probability of measuring |0⟩. *)
Definition prob_outcome0 (rho : DensityMatrix2D) : R := rho.(d00).

(** Probability of measuring |1⟩. *)
Definition prob_outcome1 (rho : DensityMatrix2D) : R := rho.(d11).

(** Probabilities are non-negative. *)
Lemma prob0_nonneg (rho : DensityMatrix2D) : 0 <= prob_outcome0 rho.
Proof.
  exact rho.(d00_nonneg).
Qed.

Lemma prob1_nonneg (rho : DensityMatrix2D) : 0 <= prob_outcome1 rho.
Proof.
  exact rho.(d11_nonneg).
Qed.

(** Probabilities sum to 1 (conservation of probability). *)
Lemma prob_sum_one (rho : DensityMatrix2D) :
    prob_outcome0 rho + prob_outcome1 rho = 1.
Proof.
  exact rho.(trace_one).
Qed.

(** For the pure state |0⟩, measuring |0⟩ gives probability 1. *)
Lemma pure0_certain : prob_outcome0 pure_state0 = 1.
Proof.
  unfold prob_outcome0, pure_state0. simpl. lra.
Qed.

(** For the pure state |0⟩, measuring |1⟩ gives probability 0. *)
Lemma pure0_definite : prob_outcome1 pure_state0 = 0.
Proof.
  unfold prob_outcome1, pure_state0. simpl. lra.
Qed.

(** For the maximally mixed state, each outcome has probability 1/2. *)
Lemma mixed_equal_probs : prob_outcome0 maximallyMixed = 1/2.
Proof.
  unfold prob_outcome0, maximallyMixed. simpl. lra.
Qed.

(** ** Binary Entropy

    The binary entropy H(p) = -p log p - (1-p) log(1-p) measures uncertainty.
    H(1/2) = log 2 is the maximal entropy for a two-outcome measurement. *)

(** Binary entropy function H(p) for p ∈ (0,1). *)
Definition binary_entropy (p : R) : R :=
  -(p * ln p + (1 - p) * ln (1 - p)).

(** The maximally mixed state has maximal entropy: H(1/2) = log(2).
    Proof uses ln(1/2) = -ln(2) from the property ln(x*y) = ln(x) + ln(y). *)
Lemma mixed_max_entropy : binary_entropy (1/2) = ln 2.
Proof.
  unfold binary_entropy.
  assert (h1 : (1 : R) - 1/2 = 1/2) by lra.
  rewrite h1.
  assert (hln : ln (1/2) = - ln 2).
  { assert (hsum : ln (1/2) + ln 2 = ln (1/2 * 2)).
    { symmetry. apply ln_mult; lra. }
    assert (hmul : 1/2 * 2 = 1) by ring.
    rewrite hmul in hsum.
    rewrite ln_1 in hsum.
    lra. }
  rewrite hln.
  ring.
Qed.
