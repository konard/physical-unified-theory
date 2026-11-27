From Stdlib Require Import Reals Lra.
From PhysicalUnifiedTheory.Unification Require Import NullCone.

Open Scope R_scope.

Example bounded_positive_weights_have_unbounded_trace : forall bound : R,
  exists n, bound < diagonal_sum (fun _ => 2 / 3) n.
Proof.
  intro bound.
  apply (positive_diagonal_unbounded _ (2 / 3)).
  - lra.
  - intro k. apply Rle_refl.
Qed.

Example trace_128_lower_bound : 128 * (2 / 3) <= diagonal_sum (fun _ => 2 / 3) 128.
Proof.
  replace 128 with (INR 128) by (simpl; lra).
  apply finite_trace_lower_bound. intro k. apply Rle_refl.
Qed.

Example boost_mismatch_at_double_scale : 4 * 2 / (1 + 2) ^ 2 < 1.
Proof. apply boost_factor_lt_one; lra. Qed.
