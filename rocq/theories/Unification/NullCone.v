From Stdlib Require Import Reals Lra Psatz ZArith.

Open Scope R_scope.

(** Positive affine changes of the null generator parameter preserve the
    cap-normalized clock. *)
Theorem cap_clock_affine_invariant : forall slope start finish shift scale : R,
  0 < scale ->
  (slope / scale) * ((scale * finish + shift) - (scale * start + shift)) =
  slope * (finish - start).
Proof.
  intros slope start finish shift scale Hscale.
  field; lra.
Qed.

(** Classical area bound (5.21) from the moment inequalities. *)
Theorem area_bound : forall A a eps L : R,
  0 <= A -> 0 < a -> eps < 1 -> 0 <= L ->
  a ^ 2 <= 4 * PI * A -> (1 - eps) * A / a <= L ->
  A <= 4 * PI * L ^ 2 / (1 - eps) ^ 2.
Proof.
  intros A a eps L HA Ha Heps HL Hmoment Hclock.
  assert (Hgap : 0 < 1 - eps) by lra.
  assert (Hstep : (1 - eps) * A <= L * a).
  { apply (Rmult_le_reg_r (/ a)); [apply Rinv_0_lt_compat; exact Ha|].
    replace (L * a * / a) with L by (field; lra).
    exact Hclock. }
  assert (Hsq : ((1 - eps) * A) ^ 2 <= (L * a) ^ 2).
  { apply pow_incr; nra. }
  assert (Hmoment' : L ^ 2 * a ^ 2 <= L ^ 2 * (4 * PI * A)).
  { apply Rmult_le_compat_l; nra. }
  apply (Rmult_le_reg_r ((1 - eps) ^ 2)); [nra|].
  replace (4 * PI * L ^ 2 / (1 - eps) ^ 2 * (1 - eps) ^ 2)
    with (4 * PI * L ^ 2) by (field; lra).
  destruct (Req_dec A 0) as [-> | Hne].
  - pose proof PI_RGT_0. nra.
  - apply (Rmult_le_reg_r A); nra.
Qed.

(** A scalar resolvent estimate from Appendix C. *)
Theorem resolvent_energy_bound : forall L x : R,
  0 < L -> 0 <= x -> x * (L / (L + x)) ^ 2 <= L / 4.
Proof.
  intros L x HL Hx.
  assert (Hsum : 0 < L + x) by lra.
  apply (Rmult_le_reg_r ((L + x) ^ 2)); [nra|].
  replace (x * (L / (L + x)) ^ 2 * (L + x) ^ 2)
    with (x * L ^ 2) by (field; lra).
  pose proof (Rmult_le_pos L ((L - x) ^ 2) (Rlt_le _ _ HL) (pow2_ge_0 (L - x))).
  nra.
Qed.

(** Bound the normalized clock resolvent by a two-valued function on the
    spectral windows [0, cutoff] and (cutoff, infinity). *)
Theorem clock_resolvent_window : forall L cutoff reading : R,
  0 < L -> 0 <= cutoff -> 0 <= reading ->
  (reading <= cutoff -> L / (L + cutoff) <= L / (L + reading) <= 1) /\
  (cutoff < reading -> 0 <= L / (L + reading) <= L / (L + cutoff)).
Proof.
  intros L cutoff reading HL Hcutoff Hreading.
  assert (HreadingDenom : 0 < L + reading) by lra.
  assert (HcutoffDenom : 0 < L + cutoff) by lra.
  assert (Hreg : forall x y : R, 0 < L + x -> x <= y ->
    L / (L + y) <= L / (L + x)).
  { intros x y Hx Hxy.
    unfold Rdiv.
    apply Rmult_le_compat_l; [lra|].
    apply Rinv_le_contravar; lra. }
  split; intro Hwindow.
  - split.
    + apply Hreg; assumption.
    + replace 1 with (L / (L + 0)) by (field; lra).
      apply Hreg; lra.
  - split.
    + apply Rlt_le, Rdiv_lt_0_compat; assumption.
    + apply Hreg; lra.
Qed.

(** An exponential lower bound on a commuting clock gives a Laplace upper
    bound on its normalized resolvent. *)
Theorem resolvent_le_clock_laplace : forall L floor clock focusing : R,
  0 < L -> 0 < floor -> floor * exp focusing <= clock ->
  L / (L + clock) <= (L / floor) * exp (- focusing).
Proof.
  intros L floor clock focusing HL Hfloor Hclock.
  pose proof (exp_pos focusing) as Hexp.
  pose proof (Rmult_lt_0_compat _ _ Hfloor Hexp) as Hproduct.
  assert (Hsum : 0 < L + clock) by lra.
  rewrite exp_Ropp.
  apply (Rmult_le_reg_r ((L + clock) * (floor * exp focusing))).
  - apply Rmult_lt_0_compat; assumption.
  - replace (L / (L + clock) * ((L + clock) * (floor * exp focusing)))
      with (L * (floor * exp focusing)) by (field; lra).
    replace (L / floor * / exp focusing * ((L + clock) * (floor * exp focusing)))
      with (L * (L + clock)) by (field; lra).
    apply Rmult_le_compat_l; lra.
Qed.

(** Positive lower bounds on replica purity imply trace bounds when the
    cyclic numerator is bounded by the trace of the cut. *)
Theorem trace_bound_from_purity : forall trace cyclic p : R,
  0 < trace -> 0 < p -> cyclic <= trace ->
  p <= cyclic / trace ^ 2 -> trace <= 1 / p.
Proof.
  intros trace cyclic p Htrace Hp Hcyclic Hpurity.
  assert (Hscaled : p * trace ^ 2 <= cyclic).
  { apply (Rmult_le_reg_r (/ trace ^ 2)).
    - apply Rinv_0_lt_compat. nra.
    - replace (p * trace ^ 2 * / trace ^ 2) with p by (field; lra).
      exact Hpurity. }
  apply (Rmult_le_reg_r p); [exact Hp|].
  replace (1 / p * p) with 1 by (field; lra).
  apply (Rmult_le_reg_r trace); nra.
Qed.

Fixpoint diagonal_sum (diagonal : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => diagonal_sum diagonal k + diagonal k
  end.

(** Uniformly positive diagonals have divergent finite traces. *)
Theorem finite_trace_lower_bound : forall (diagonal : nat -> R) c,
  (forall k, c <= diagonal k) -> forall n, INR n * c <= diagonal_sum diagonal n.
Proof.
  intros diagonal c H n.
  induction n as [|n IH].
  - simpl. lra.
  - rewrite S_INR. simpl diagonal_sum. specialize (H n). nra.
Qed.

Theorem positive_diagonal_unbounded : forall (diagonal : nat -> R) c,
  0 < c -> (forall k, c <= diagonal k) -> forall bound,
  exists n, bound < diagonal_sum diagonal n.
Proof.
  intros diagonal c Hc H bound.
  destruct (archimed (Rabs (bound / c))) as [Hup _].
  pose proof (Rle_abs (bound / c)).
  pose proof (Rabs_pos (bound / c)).
  assert (Hz : (0 <= up (Rabs (bound / c)))%Z).
  { apply le_IZR. simpl. lra. }
  exists (Z.to_nat (up (Rabs (bound / c)))).
  assert (Hbelow : bound < INR (Z.to_nat (up (Rabs (bound / c)))) * c).
  { rewrite INR_IZR_INZ, Z2Nat.id by exact Hz.
    apply (Rmult_lt_reg_r (/ c)); [apply Rinv_0_lt_compat; exact Hc|].
    replace (IZR (up (Rabs (bound / c))) * c * / c)
      with (IZR (up (Rabs (bound / c)))) by (field; lra).
    lra. }
  eapply Rlt_le_trans; [exact Hbelow|].
  apply finite_trace_lower_bound. exact H.
Qed.

(** The boost mismatch suppression factor in (5.29). *)
Theorem boost_factor_lt_one : forall r : R,
  0 < r -> r <> 1 -> 4 * r / (1 + r) ^ 2 < 1.
Proof.
  intros r Hr Hne.
  apply (Rmult_lt_reg_r ((1 + r) ^ 2)); [nra|].
  replace (4 * r / (1 + r) ^ 2 * (1 + r) ^ 2) with (4 * r) by (field; lra).
  assert (0 < (r - 1) ^ 2) by nra.
  nra.
Qed.

Theorem one_loop_coefficient :
  (257 / 302) / (2 * (1 - 257 / 302)) - 1 / 2 = 106 / 45.
Proof. field. Qed.
