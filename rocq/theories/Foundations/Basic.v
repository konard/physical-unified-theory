(** * Mathematical Foundations

    This module establishes the mathematical infrastructure required for formalizing
    quantum mechanics and general relativity.

    Contents:
    - Real numbers and basic structures
    - Physical constants in natural units

    Note: Complex number support requires the Coquelicot library.
    For CI purposes, we use the standard library only.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

(** ** Physical Constants (Natural Units) *)

(** In natural units, we set c = ℏ = 1.
    This simplifies equations and makes dimensional analysis clearer. *)

(** Reduced Planck constant ℏ = h/(2π) *)
Definition hbar : R := 1.

(** Speed of light c *)
Definition speed_of_light : R := 1.

(** Gravitational constant G
    In natural units with c = ℏ = 1, we have G = ℓ_P²
    where ℓ_P is the Planck length *)
Definition gravitational_constant : R := 1.

(** Planck length ℓ_P = √(ℏG/c³) = √G in natural units *)
Definition planck_length : R := sqrt gravitational_constant.

(** Planck mass m_P = √(ℏc/G) = 1/√G in natural units *)
Definition planck_mass : R := 1 / sqrt gravitational_constant.

(** Planck energy E_P = m_P c² = m_P in natural units *)
Definition planck_energy : R := planck_mass.

(** ** Basic Lemmas *)

Lemma hbar_positive : hbar > 0.
Proof.
  unfold hbar. lra.
Qed.

Lemma speed_of_light_positive : speed_of_light > 0.
Proof.
  unfold speed_of_light. lra.
Qed.
