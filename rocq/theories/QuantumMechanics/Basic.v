(** * Quantum Mechanics

    This module provides foundational definitions for quantum mechanics.

    Key Postulates:
    1. States: A quantum system is described by a state vector |ψ⟩ in a Hilbert space.
    2. Observables: Physical observables are Hermitian operators.
    3. Measurement: Outcomes are eigenvalues; probabilities follow the Born rule.
    4. Evolution: Time evolution is governed by the Schrödinger equation.

    Note: Full complex Hilbert space formalization requires additional libraries.
    This module establishes the basic structure.

    References:
    - Sakurai, "Modern Quantum Mechanics"
    - Nielsen & Chuang, "Quantum Computation and Quantum Information"
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Require Import PhysicalUnifiedTheory.Foundations.Basic.
Open Scope R_scope.

(** ** Probability Theory Basics *)

(** Probabilities must be between 0 and 1 *)
Definition is_probability (p : R) : Prop := 0 <= p <= 1.

(** Two probabilities that sum to 1 (like qubit measurement outcomes) *)
Record TwoOutcomeProbabilities := {
  prob_0 : R;
  prob_1 : R;
  prob_0_valid : 0 <= prob_0 <= 1;
  prob_1_valid : 0 <= prob_1 <= 1;
  probs_sum_to_one : prob_0 + prob_1 = 1
}.

(** For the |0⟩ state: P(0) = 1, P(1) = 0 *)
Program Definition ket0_probs : TwoOutcomeProbabilities := {|
  prob_0 := 1;
  prob_1 := 0
|}.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.

(** For the |1⟩ state: P(0) = 0, P(1) = 1 *)
Program Definition ket1_probs : TwoOutcomeProbabilities := {|
  prob_0 := 0;
  prob_1 := 1
|}.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.

(** For the |+⟩ state (equal superposition): P(0) = 1/2, P(1) = 1/2 *)
Program Definition plus_state_probs : TwoOutcomeProbabilities := {|
  prob_0 := 1/2;
  prob_1 := 1/2
|}.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.
Next Obligation. field. Qed.

(** ** Born Rule Properties *)

(** The Born rule states that for a state |ψ⟩ = α|0⟩ + β|1⟩:
    P(0) = |α|² and P(1) = |β|²

    Since |α|² + |β|² = 1 (normalization), we have P(0) + P(1) = 1 *)

Theorem probabilities_sum_one :
  forall p : TwoOutcomeProbabilities,
  prob_0 p + prob_1 p = 1.
Proof.
  intros p.
  exact (probs_sum_to_one p).
Qed.

(** Measuring |0⟩ always gives outcome 0 *)
Theorem measure_ket0 : prob_0 ket0_probs = 1.
Proof.
  reflexivity.
Qed.

(** Measuring |1⟩ always gives outcome 1 *)
Theorem measure_ket1 : prob_1 ket1_probs = 1.
Proof.
  reflexivity.
Qed.

(** ** Energy Quantization *)

(** Energy levels of a quantum harmonic oscillator:
    E_n = ℏω(n + 1/2)

    In natural units (ℏ = 1): E_n = ω(n + 1/2) *)

Definition harmonic_oscillator_energy (omega : R) (n : nat) : R :=
  omega * (INR n + 1/2).

(** Ground state energy (zero-point energy) *)
Definition ground_state_energy (omega : R) : R :=
  harmonic_oscillator_energy omega 0.

(** Ground state energy is ω/2 *)
Theorem ground_state_is_half_omega :
  forall omega : R,
  ground_state_energy omega = omega / 2.
Proof.
  intros omega.
  unfold ground_state_energy, harmonic_oscillator_energy.
  simpl. field.
Qed.

(** Energy difference between adjacent levels is ℏω = ω (in natural units) *)
Theorem energy_spacing :
  forall omega : R, forall n : nat,
  harmonic_oscillator_energy omega (S n) - harmonic_oscillator_energy omega n = omega.
Proof.
  intros omega n.
  unfold harmonic_oscillator_energy.
  rewrite S_INR.
  ring.
Qed.
