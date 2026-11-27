From Stdlib Require Import Reals Lra.
From PhysicalUnifiedTheory.Foundations Require Import HilbertSpaces.
Open Scope R_scope.

(* The vector (1, -1) has a strictly negative quadratic form. *)
Example indefinite_density_rejected (rho : DensityMatrix2D) :
  ~ (rho.(d00) = 1/2 /\ rho.(d01) = 1 /\ rho.(d11) = 1/2).
Proof.
  intros [h00 [h01 h11]].
  pose proof (density_positive rho 1 (-1)).
  lra.
Qed.
