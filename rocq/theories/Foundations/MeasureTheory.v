(** * Measure Theory and Probability (A.5)

    This module formalizes measure-theoretic probability as needed for
    quantum mechanics (Born rule, density matrices).

    Contents:
    - A.5.1: Probability theory basics (discrete case)
    - A.5.2: Born rule and quantum measurement
    - A.5.3: Shannon entropy

    References:
    - Rudin, "Real and Complex Analysis"
    - Glimm & Jaffe, "Quantum Physics: A Functional Integral Point of View"

    Hypothesis: Rigorous path integrals can be constructed in 4D via
    constructive QFT methods (Osterwalder-Schrader axioms).
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Psatz.
Require Import PhysicalUnifiedTheory.Foundations.Basic.
Open Scope R_scope.

(** ** A.5.1: Probability Theory Basics *)

(** A probability is a real number in [0, 1]. *)
Definition is_probability (p : R) : Prop := 0 <= p <= 1.

(** The complementary probability: q = 1 - p. *)
Definition complementary_prob (p : R) : R := 1 - p.

(** If p is a probability, so is its complement. *)
Lemma comp_prob_valid (p : R) (h : is_probability p) :
    is_probability (complementary_prob p).
Proof.
  unfold is_probability, complementary_prob in *.
  lra.
Qed.

(** A two-outcome probability distribution. *)
Record TwoProbs : Type := mkTwoProbs {
  p0 : R;
  p1 : R;
  p0_valid : is_probability p0;
  p1_valid : is_probability p1;
  sum_one : p0 + p1 = 1
}.

(** A certain outcome: all probability on |0⟩. *)
Program Definition certain_outcome0 : TwoProbs := {|
  p0 := 1; p1 := 0
|}.
Next Obligation. unfold is_probability. lra. Qed.
Next Obligation. unfold is_probability. lra. Qed.
Next Obligation. lra. Qed.

(** Equal probabilities: maximally uncertain case. *)
Program Definition equal_probs : TwoProbs := {|
  p0 := 1/2; p1 := 1/2
|}.
Next Obligation. unfold is_probability. lra. Qed.
Next Obligation. unfold is_probability. lra. Qed.
Next Obligation. lra. Qed.

(** ** A.5.2: Born Rule *)

(** A quantum measurement state with real amplitudes α, β (α² + β² = 1). *)
Record TwoOutcomeMeasurement : Type := mkMeasurement {
  amplitude0 : R;
  amplitude1 : R;
  norm_cond : amplitude0 * amplitude0 + amplitude1 * amplitude1 = 1;
  amp0_nonneg : 0 <= amplitude0;
  amp1_nonneg : 0 <= amplitude1
}.

(** Born rule: probability = |amplitude|². *)
Definition born_prob0 (m : TwoOutcomeMeasurement) : R :=
  m.(amplitude0) * m.(amplitude0).

Definition born_prob1 (m : TwoOutcomeMeasurement) : R :=
  m.(amplitude1) * m.(amplitude1).

(** Born rule probabilities are valid (in [0,1]). *)
Lemma born_prob0_valid (m : TwoOutcomeMeasurement) :
    is_probability (born_prob0 m).
Proof.
  unfold is_probability, born_prob0.
  pose proof m.(amp0_nonneg) as h0.
  pose proof m.(amp1_nonneg) as h1.
  pose proof m.(norm_cond) as hn.
  split; nra.
Qed.

(** Born rule probabilities sum to 1. *)
Lemma born_probs_sum_one (m : TwoOutcomeMeasurement) :
    born_prob0 m + born_prob1 m = 1.
Proof.
  unfold born_prob0, born_prob1.
  exact m.(norm_cond).
Qed.

(** The |0⟩ state: amplitude0 = 1, amplitude1 = 0. *)
Program Definition ket0_measurement : TwoOutcomeMeasurement := {|
  amplitude0 := 1; amplitude1 := 0
|}.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.

(** For |0⟩, measuring outcome 0 is certain. *)
Lemma ket0_certain : born_prob0 ket0_measurement = 1.
Proof.
  unfold born_prob0, ket0_measurement. simpl. lra.
Qed.

(** The |+⟩ state: amplitude0 = amplitude1 = 1/√2. *)
Program Definition plus_measurement : TwoOutcomeMeasurement := {|
  amplitude0 := 1 / sqrt 2; amplitude1 := 1 / sqrt 2
|}.
Next Obligation.
  assert (hsqrt : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  assert (hsq : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  field_simplify.
  rewrite hsq. lra.
Qed.
Next Obligation.
  assert (hsqrt : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  apply Rlt_le. apply Rdiv_lt_0_compat; lra.
Qed.
Next Obligation.
  assert (hsqrt : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  apply Rlt_le. apply Rdiv_lt_0_compat; lra.
Qed.

(** For |+⟩, each outcome has probability 1/2. *)
Lemma plus_state_equal_probs : born_prob0 plus_measurement = 1/2.
Proof.
  unfold born_prob0, plus_measurement. simpl.
  assert (hsqrt : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  assert (hsq : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  field_simplify.
  rewrite hsq. lra.
Qed.

(** ** A.5.3: Shannon/von Neumann Entropy *)

(** Binary entropy H(p) = -p ln p - (1-p) ln(1-p) for p ∈ (0,1). *)
Definition binary_entropy (p : R) (hp0 : 0 < p) (hp1 : p < 1) : R :=
  -(p * ln p) - ((1 - p) * ln (1 - p)).

(** Entropy is non-negative for p ∈ (0,1). *)
Lemma binary_entropy_nonneg (p : R) (hp0 : 0 < p) (hp1 : p < 1) :
    0 <= binary_entropy p hp0 hp1.
Proof.
  unfold binary_entropy.
  assert (hln_p : ln p <= 0) by (apply ln_le_zero; lra).
  assert (hln_1mp : ln (1 - p) <= 0) by (apply ln_le_zero; lra).
  nra.
Qed.

(** ** A.5.4: Independence *)

(** Two events are independent if P(A∩B) = P(A)P(B). *)
Definition independent (pA pB pAB : R) : Prop := pAB = pA * pB.

Lemma product_state_independent (p q : R)
    (hp : is_probability p) (hq : is_probability q) :
    independent p q (p * q).
Proof.
  unfold independent. reflexivity.
Qed.
