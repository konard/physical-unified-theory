(** * Mathematical Foundations

    This module establishes the mathematical infrastructure required for formalizing
    quantum mechanics and general relativity.

    Contents:
    - Complex numbers and vector spaces
    - Basic linear algebra structures
    - Physical constants in natural units
*)

Require Import Reals.
Require Import Coquelicot.Complex.
Open Scope R_scope.

(** ** Complex Numbers and Hilbert Spaces *)

(** In quantum mechanics, we work with complex Hilbert spaces.
    For a two-dimensional system (qubit), the state space is ℂ². *)

(** A complex 2D vector (qubit state representation) *)
Definition C2 := (C * C)%type.

(** The zero vector *)
Definition c2_zero : C2 := (RtoC 0, RtoC 0).

(** Standard basis vectors *)
Definition basis_0 : C2 := (RtoC 1, RtoC 0).
Definition basis_1 : C2 := (RtoC 0, RtoC 1).

(** Complex inner product for C2 *)
Definition inner_product (v w : C2) : C :=
  Cplus (Cmult (Cconj (fst v)) (fst w))
        (Cmult (Cconj (snd v)) (snd w)).

(** The norm squared of a vector *)
Definition norm_sq (v : C2) : R :=
  Cre (inner_product v v).

(** Basis vectors are orthogonal *)
Lemma basis_orthogonal : inner_product basis_0 basis_1 = RtoC 0.
Proof.
  unfold inner_product, basis_0, basis_1.
  unfold Cconj, Cmult, Cplus. simpl.
  f_equal; ring.
Qed.

(** Basis vectors are normalized *)
Lemma basis_0_normalized : norm_sq basis_0 = 1.
Proof.
  unfold norm_sq, inner_product, basis_0.
  unfold Cconj, Cmult, Cplus, Cre. simpl.
  ring.
Qed.

Lemma basis_1_normalized : norm_sq basis_1 = 1.
Proof.
  unfold norm_sq, inner_product, basis_1.
  unfold Cconj, Cmult, Cplus, Cre. simpl.
  ring.
Qed.

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
