(** * The CHSH Bell inequality

    The local model uses a finite shared distribution independent of the
    measurement choices. The quantum model uses the real coordinates of
    the Bell state (|00> + |11>) / sqrt 2.
*)
From Stdlib Require Import Reals Lra List Bool.
Open Scope R_scope.

Definition response (outcome : bool) : R := if outcome then 1 else -1.

Definition local_score (a0 a1 b0 b1 : bool) : R :=
  response a0 * (response b0 + response b1) +
  response a1 * (response b0 - response b1).

Lemma local_score_bounds (a0 a1 b0 b1 : bool) :
  -2 <= local_score a0 a1 b0 b1 <= 2.
Proof. destruct a0, a1, b0, b1; unfold local_score, response; lra. Qed.

Record local_trial := {
  probability : R;
  alice0 : bool;
  alice1 : bool;
  bob0 : bool;
  bob1 : bool;
}.

Fixpoint total_weight (trials : list local_trial) : R :=
  match trials with
  | nil => 0
  | trial :: rest => probability trial + total_weight rest
  end.

Fixpoint local_average (trials : list local_trial) : R :=
  match trials with
  | nil => 0
  | trial :: rest => probability trial *
      local_score (alice0 trial) (alice1 trial) (bob0 trial) (bob1 trial) + local_average rest
  end.

Lemma local_average_bounds (trials : list local_trial)
    (nonnegative : Forall (fun trial => 0 <= probability trial) trials) :
  -2 * total_weight trials <= local_average trials <= 2 * total_weight trials.
Proof.
  induction nonnegative as [|trial rest hweight _ ih].
  - cbn [local_average total_weight]. lra.
  - cbn [local_average total_weight].
    destruct (local_score_bounds (alice0 trial) (alice1 trial) (bob0 trial) (bob1 trial))
      as [lower upper].
    pose proof (Rmult_le_compat_l _ _ _ hweight lower).
    pose proof (Rmult_le_compat_l _ _ _ hweight upper).
    lra.
Qed.

Theorem local_bound (trials : list local_trial)
    (nonnegative : Forall (fun trial => 0 <= probability trial) trials)
    (normalized : total_weight trials = 1) : Rabs (local_average trials) <= 2.
Proof.
  pose proof (local_average_bounds trials nonnegative).
  unfold Rabs. destruct (Rcase_abs (local_average trials)); lra.
Qed.

Definition bell_amplitude (i j : bool) : R := if Bool.eqb i j then 1 / sqrt 2 else 0.
Definition analyzer (z x : R) (i j : bool) : R :=
  if Bool.eqb i j then (if i then -z else z) else x.
Definition sum2 (f : bool -> R) : R := f false + f true.

Theorem analyzer_symmetric (z x : R) (i j : bool) : analyzer z x i j = analyzer z x j i.
Proof. destruct i, j; reflexivity. Qed.

Theorem analyzer_sq (z x : R) (h : z^2 + x^2 = 1) (i j : bool) :
  sum2 (fun k => analyzer z x i k * analyzer z x k j) = if Bool.eqb i j then 1 else 0.
Proof. destruct i, j; unfold sum2, analyzer; cbn [Bool.eqb]; nra. Qed.

(** Expectation of the tensor product of two observables in the Bell state. *)
Definition correlation (a b : bool -> bool -> R) : R :=
  sum2 (fun i => sum2 (fun j => sum2 (fun k => sum2 (fun l =>
    bell_amplitude i j * a i k * b j l * bell_amplitude k l)))).

Local Lemma amplitude_sq : (1 / sqrt 2) ^ 2 = 1 / 2.
Proof.
  assert (hp : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  assert (hsq : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  replace ((1 / sqrt 2) ^ 2) with (1 / (sqrt 2 * sqrt 2)) by (field; lra).
  now rewrite hsq.
Qed.

Theorem bell_amplitude_normalized : sum2 (fun i => sum2 (fun j => bell_amplitude i j ^ 2)) = 1.
Proof.
  unfold sum2, bell_amplitude. cbn [Bool.eqb]. rewrite !amplitude_sq. lra.
Qed.

Theorem correlation_analyzers (az ax bz bx : R) :
  correlation (analyzer az ax) (analyzer bz bx) = az * bz + ax * bx.
Proof.
  transitivity ((az * bz + ax * bx) * (2 * (1 / sqrt 2) ^ 2)).
  - unfold correlation, sum2, analyzer, bell_amplitude. cbn [Bool.eqb].
    set (amplitude := 1 / sqrt 2). ring.
  - rewrite amplitude_sq. field.
Qed.

Definition quantum_score : R :=
  let z := analyzer 1 0 in
  let x := analyzer 0 1 in
  let plus := analyzer (1 / sqrt 2) (1 / sqrt 2) in
  let minus := analyzer (1 / sqrt 2) (-1 / sqrt 2) in
  correlation z plus + correlation z minus + correlation x plus - correlation x minus.

Theorem quantum_score_eq : quantum_score = 2 * sqrt 2.
Proof.
  unfold quantum_score. rewrite !correlation_analyzers.
  assert (hp : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  assert (hsq : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  transitivity (4 / sqrt 2).
  - field. lra.
  - apply (Rmult_eq_reg_r (sqrt 2)).
    + replace (4 / sqrt 2 * sqrt 2) with 4 by (field; lra). nra.
    + lra.
Qed.

Theorem quantum_score_violates_local_bound : 2 < quantum_score.
Proof.
  rewrite quantum_score_eq.
  assert (hp : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  assert (hsq : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  nra.
Qed.

Theorem quantum_score_no_local_model (trials : list local_trial)
    (nonnegative : Forall (fun trial => 0 <= probability trial) trials)
    (normalized : total_weight trials = 1) : local_average trials <> quantum_score.
Proof.
  intro heq.
  pose proof (local_bound trials nonnegative normalized) as bound.
  rewrite heq in bound.
  pose proof (Rle_abs quantum_score).
  pose proof quantum_score_violates_local_bound.
  lra.
Qed.
