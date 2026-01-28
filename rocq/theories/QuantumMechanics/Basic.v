(** * Quantum Mechanics

    This module formalizes the mathematical foundations of quantum mechanics.

    Key Postulates:
    1. States: A quantum system is described by a state vector |ψ⟩ in a Hilbert space.
    2. Observables: Physical observables are Hermitian operators.
    3. Measurement: Outcomes are eigenvalues; probabilities follow the Born rule.
    4. Evolution: Time evolution is governed by the Schrödinger equation.

    References:
    - Sakurai, "Modern Quantum Mechanics"
    - Nielsen & Chuang, "Quantum Computation and Quantum Information"
*)

Require Import Reals.
Require Import Coquelicot.Complex.
Require Import PhysicalUnifiedTheory.Foundations.Basic.
Open Scope R_scope.

(** ** Qubit States *)

(** A qubit is the simplest quantum system - a two-level system.
    States are unit vectors in ℂ². *)

(** A normalized qubit state *)
Record QubitState := mkQubitState {
  amplitude_0 : C;
  amplitude_1 : C;
  is_normalized : Cre (Cplus (Cmult (Cconj amplitude_0) amplitude_0)
                             (Cmult (Cconj amplitude_1) amplitude_1)) = 1
}.

(** The computational basis states |0⟩ and |1⟩ *)
Program Definition ket0 : QubitState := {|
  amplitude_0 := RtoC 1;
  amplitude_1 := RtoC 0
|}.
Next Obligation.
  unfold Cconj, Cmult, Cplus, Cre, RtoC. simpl. ring.
Qed.

Program Definition ket1 : QubitState := {|
  amplitude_0 := RtoC 0;
  amplitude_1 := RtoC 1
|}.
Next Obligation.
  unfold Cconj, Cmult, Cplus, Cre, RtoC. simpl. ring.
Qed.

(** ** Born Rule: Measurement Probabilities *)

(** The probability of measuring |0⟩ is |α|² where α is the amplitude. *)
Definition prob_0 (psi : QubitState) : R :=
  Cre (Cmult (Cconj (amplitude_0 psi)) (amplitude_0 psi)).

(** The probability of measuring |1⟩ is |β|² where β is the amplitude. *)
Definition prob_1 (psi : QubitState) : R :=
  Cre (Cmult (Cconj (amplitude_1 psi)) (amplitude_1 psi)).

(** Probabilities sum to 1 (conservation of probability). *)
Theorem probabilities_sum_to_one : forall psi : QubitState,
  prob_0 psi + prob_1 psi = 1.
Proof.
  intros psi.
  unfold prob_0, prob_1.
  destruct psi as [a0 a1 H]. simpl.
  exact H.
Qed.

(** Measuring |0⟩ in state |0⟩ gives probability 1. *)
Theorem measure_ket0_gives_0 : prob_0 ket0 = 1.
Proof.
  unfold prob_0, ket0. simpl.
  unfold Cconj, Cmult, Cre, RtoC. simpl. ring.
Qed.

(** Measuring |1⟩ in state |0⟩ gives probability 0. *)
Theorem measure_ket0_gives_not_1 : prob_1 ket0 = 0.
Proof.
  unfold prob_1, ket0. simpl.
  unfold Cconj, Cmult, Cre, RtoC. simpl. ring.
Qed.

(** ** Quantum Gates as 2x2 Matrices *)

(** A 2x2 complex matrix *)
Definition Matrix2 := (C * C * C * C)%type.

(** Matrix application to a vector *)
Definition apply_matrix (m : Matrix2) (v : C2) : C2 :=
  match m with
  | (a, b, c, d) =>
    (Cplus (Cmult a (fst v)) (Cmult b (snd v)),
     Cplus (Cmult c (fst v)) (Cmult d (snd v)))
  end.

(** The Pauli X gate (quantum NOT): swaps |0⟩ and |1⟩ *)
Definition pauli_X : Matrix2 := (RtoC 0, RtoC 1, RtoC 1, RtoC 0).

(** The Pauli Z gate: |0⟩ → |0⟩, |1⟩ → -|1⟩ *)
Definition pauli_Z : Matrix2 := (RtoC 1, RtoC 0, RtoC 0, RtoC (-1)).

(** Identity gate *)
Definition identity : Matrix2 := (RtoC 1, RtoC 0, RtoC 0, RtoC 1).

(** Pauli X swaps the basis states *)
Lemma pauli_X_on_0 : apply_matrix pauli_X basis_0 = basis_1.
Proof.
  unfold apply_matrix, pauli_X, basis_0, basis_1.
  unfold Cmult, Cplus, RtoC. simpl.
  f_equal; f_equal; ring.
Qed.

Lemma pauli_X_on_1 : apply_matrix pauli_X basis_1 = basis_0.
Proof.
  unfold apply_matrix, pauli_X, basis_0, basis_1.
  unfold Cmult, Cplus, RtoC. simpl.
  f_equal; f_equal; ring.
Qed.
