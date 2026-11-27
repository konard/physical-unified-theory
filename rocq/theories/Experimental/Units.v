(** * Dimensions and coherent unit systems

    The seven base dimensions and coherent units follow the BIPM SI Brochure,
    https://www.bipm.org/en/publications/si-brochure.
*)
From Stdlib Require Import Reals ZArith.
Open Scope R_scope.

Inductive base_dimension :=
| Length | Mass | Time | Current | Temperature | Amount | LuminousIntensity.

Definition base_dimension_eq_dec :
  forall a b : base_dimension, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition dimension := base_dimension -> Z.
Definition dimensionless : dimension := fun _ => 0%Z.
Definition base_dim (b : base_dimension) : dimension :=
  fun a => if base_dimension_eq_dec a b then 1%Z else 0%Z.

Definition dim_mul (d e : dimension) : dimension := fun b => (d b + e b)%Z.
Definition dim_div (d e : dimension) : dimension := fun b => (d b - e b)%Z.

Definition length_dim := base_dim Length.
Definition mass_dim := base_dim Mass.
Definition time_dim := base_dim Time.
Definition current_dim := base_dim Current.
Definition temperature_dim := base_dim Temperature.
Definition amount_dim := base_dim Amount.
Definition luminous_intensity_dim := base_dim LuminousIntensity.

Definition velocity_dim := dim_div length_dim time_dim.
Definition energy_dim :=
  dim_div (dim_mul (dim_mul mass_dim length_dim) length_dim) (dim_mul time_dim time_dim).
Definition action_dim := dim_mul energy_dim time_dim.
Definition gravitation_dim :=
  dim_div (dim_mul (dim_mul length_dim length_dim) length_dim)
    (dim_mul (dim_mul mass_dim time_dim) time_dim).
Definition charge_dim := dim_mul current_dim time_dim.

(** The magnitude in coherent SI units, indexed by its dimension. *)
Record quantity (d : dimension) := { si_value : R }.
Arguments Build_quantity {d} _.
Arguments si_value {d} _.

Definition add_quantity {d} (x y : quantity d) : quantity d :=
  Build_quantity (si_value x + si_value y).

Definition sub_quantity {d} (x y : quantity d) : quantity d :=
  Build_quantity (si_value x - si_value y).

Definition mul_quantity {d e} (x : quantity d) (y : quantity e) : quantity (dim_mul d e) :=
  Build_quantity (si_value x * si_value y).

Definition div_quantity {d e} (x : quantity d) (y : quantity e) : quantity (dim_div d e) :=
  Build_quantity (si_value x / si_value y).

Definition sqrt_quantity {d} (x : quantity (dim_mul d d)) : quantity d :=
  Build_quantity (sqrt (si_value x)).

(** Coherent multiplicative systems give the SI magnitude of each base unit. *)
Record unit_system := {
  base_scale : base_dimension -> R;
  base_scale_pos : forall b, 0 < base_scale b;
}.

Definition si : unit_system :=
  {| base_scale := fun _ => 1; base_scale_pos := fun _ => Rlt_0_1 |}.

Definition scale (u : unit_system) (d : dimension) : R :=
  powerRZ (base_scale u Length) (d Length) *
  powerRZ (base_scale u Mass) (d Mass) *
  powerRZ (base_scale u Time) (d Time) *
  powerRZ (base_scale u Current) (d Current) *
  powerRZ (base_scale u Temperature) (d Temperature) *
  powerRZ (base_scale u Amount) (d Amount) *
  powerRZ (base_scale u LuminousIntensity) (d LuminousIntensity).

Lemma scale_pos (u : unit_system) (d : dimension) : 0 < scale u d.
Proof.
  unfold scale. repeat apply Rmult_lt_0_compat; apply powerRZ_lt, base_scale_pos.
Qed.

Definition in_units (u : unit_system) (d : dimension) (value : R) : quantity d :=
  Build_quantity (value * scale u d).

Definition magnitude (u : unit_system) {d} (x : quantity d) : R :=
  si_value x / scale u d.

Lemma magnitude_in_units (u : unit_system) (d : dimension) (value : R) :
  magnitude u (in_units u d value) = value.
Proof.
  unfold magnitude, in_units. simpl. field. apply Rgt_not_eq, scale_pos.
Qed.

Lemma in_units_magnitude (u : unit_system) {d} (x : quantity d) :
  in_units u d (magnitude u x) = x.
Proof.
  destruct x as [value]. unfold magnitude, in_units. simpl. f_equal.
  field. apply Rgt_not_eq, scale_pos.
Qed.

Definition convert (source target : unit_system) (d : dimension) (value : R) : R :=
  magnitude target (in_units source d value).

Lemma convert_trans (source intermediate target : unit_system) (d : dimension) (value : R) :
  convert intermediate target d (convert source intermediate d value) =
  convert source target d value.
Proof. unfold convert. rewrite in_units_magnitude. reflexivity. Qed.

Lemma convert_self (u : unit_system) (d : dimension) (value : R) :
  convert u u d value = value.
Proof. apply magnitude_in_units. Qed.
