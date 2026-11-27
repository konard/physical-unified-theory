(** * Physical constants in SI units

    Exact constants follow the SI Brochure. Estimates and standard
    uncertainties follow https://physics.nist.gov/cuu/Constants/Table/allascii.txt
    (2022 CODATA).
*)
From Stdlib Require Import Reals Lra.
From PhysicalUnifiedTheory.Experimental Require Import Units.
Open Scope R_scope.

Local Ltac positive_decimal :=
  apply Rdiv_lt_0_compat; [lra | repeat apply Rmult_lt_0_compat; lra].

Definition speed_of_light_si : quantity velocity_dim := Build_quantity 299792458.
Definition planck_constant_si : quantity action_dim := Build_quantity (662607015 / 10^42).
Definition reduced_planck_constant_si : quantity action_dim :=
  Build_quantity (si_value planck_constant_si / (2 * PI)).
Definition elementary_charge_si : quantity charge_dim := Build_quantity (1602176634 / 10^28).
Definition boltzmann_constant_si : quantity (dim_div energy_dim temperature_dim) :=
  Build_quantity (1380649 / 10^29).
Definition avogadro_constant_si : quantity (dim_div dimensionless amount_dim) :=
  Build_quantity (602214076 * 10^15).

(** Luminous efficacy at the SI defining frequency of 540 THz, in lumens per watt. *)
Definition luminous_efficacy_si : quantity
  (dim_div luminous_intensity_dim (dim_div energy_dim time_dim)) := Build_quantity 683.

Record measured_constant (d : dimension) := {
  estimate : quantity d;
  standard_uncertainty : quantity d;
  uncertainty_pos : 0 < si_value standard_uncertainty;
}.
Arguments Build_measured_constant {d} _ _ _.
Arguments estimate {d} _.
Arguments standard_uncertainty {d} _.

Definition gravitational_constant_si : measured_constant gravitation_dim.
Proof.
  refine (Build_measured_constant (Build_quantity (667430 / 10^16))
    (Build_quantity (15 / 10^16)) _). simpl. positive_decimal.
Defined.

Definition fine_structure_constant : measured_constant dimensionless.
Proof.
  refine (Build_measured_constant (Build_quantity (72973525643 / 10^13))
    (Build_quantity (11 / 10^13)) _). simpl. positive_decimal.
Defined.

Definition electron_mass : measured_constant mass_dim.
Proof.
  refine (Build_measured_constant (Build_quantity (91093837139 / 10^41))
    (Build_quantity (28 / 10^41)) _). simpl. positive_decimal.
Defined.

Definition muon_mass : measured_constant mass_dim.
Proof.
  refine (Build_measured_constant (Build_quantity (1883531627 / 10^37))
    (Build_quantity (42 / 10^37)) _). simpl. positive_decimal.
Defined.

Definition tau_mass : measured_constant mass_dim.
Proof.
  refine (Build_measured_constant (Build_quantity (316754 / 10^32))
    (Build_quantity (21 / 10^32)) _). simpl. positive_decimal.
Defined.

Definition proton_mass : measured_constant mass_dim.
Proof.
  refine (Build_measured_constant (Build_quantity (167262192595 / 10^38))
    (Build_quantity (52 / 10^38)) _). simpl. positive_decimal.
Defined.

Definition neutron_mass : measured_constant mass_dim.
Proof.
  refine (Build_measured_constant (Build_quantity (167492750056 / 10^38))
    (Build_quantity (85 / 10^38)) _). simpl. positive_decimal.
Defined.

Definition weak_mixing_angle_squared : measured_constant dimensionless.
Proof.
  refine (Build_measured_constant (Build_quantity (22305 / 10^5))
    (Build_quantity (23 / 10^5)) _). simpl. positive_decimal.
Defined.

Definition electronvolt : quantity energy_dim := Build_quantity (si_value elementary_charge_si).

(** CODATA quotes this convention in inverse square GeV with hbar = c = 1. *)
Definition fermi_coupling : measured_constant
  (dim_div dimensionless (dim_mul energy_dim energy_dim)).
Proof.
  refine (Build_measured_constant
    (Build_quantity ((11663787 / 10^12) / (10^9 * si_value electronvolt)^2))
    (Build_quantity ((6 / 10^12) / (10^9 * si_value electronvolt)^2)) _).
  change (0 < (6 / 10^12) / (10^9 * (1602176634 / 10^28))^2).
  apply Rdiv_lt_0_compat.
  - positive_decimal.
  - apply pow_lt, Rmult_lt_0_compat.
    + apply pow_lt. lra.
    + positive_decimal.
Defined.

Local Lemma light_pos : 0 < si_value speed_of_light_si.
Proof. unfold speed_of_light_si. simpl. lra. Qed.

Local Lemma hbar_si_pos : 0 < si_value reduced_planck_constant_si.
Proof.
  change (0 < (662607015 / 10^42) / (2 * PI)).
  apply Rdiv_lt_0_compat.
  - positive_decimal.
  - apply Rmult_lt_0_compat; [lra | exact PI_RGT_0].
Qed.

Local Lemma boltzmann_pos : 0 < si_value boltzmann_constant_si.
Proof. unfold boltzmann_constant_si. simpl. positive_decimal. Qed.

Local Lemma charge_pos : 0 < si_value elementary_charge_si.
Proof. unfold elementary_charge_si. simpl. positive_decimal. Qed.

Local Lemma gravitation_pos : 0 < si_value (estimate gravitational_constant_si).
Proof. simpl. positive_decimal. Qed.

(** Natural units parameterized by the energy unit. *)
Definition natural_units (energy : quantity energy_dim) (he : 0 < si_value energy) : unit_system.
Proof.
  refine {| base_scale := fun b =>
    match b with
    | Length => si_value reduced_planck_constant_si * si_value speed_of_light_si / si_value energy
    | Mass => si_value energy / si_value speed_of_light_si ^ 2
    | Time => si_value reduced_planck_constant_si / si_value energy
    | Current => si_value elementary_charge_si * si_value energy / si_value reduced_planck_constant_si
    | Temperature => si_value energy / si_value boltzmann_constant_si
    | Amount | LuminousIntensity => 1
    end |}.
  intros []; try exact Rlt_0_1; apply Rdiv_lt_0_compat.
  - apply Rmult_lt_0_compat; [exact hbar_si_pos | exact light_pos].
  - exact he.
  - exact he.
  - apply pow_lt, light_pos.
  - exact hbar_si_pos.
  - exact he.
  - apply Rmult_lt_0_compat; [exact charge_pos | exact he].
  - exact hbar_si_pos.
  - exact he.
  - exact boltzmann_pos.
Defined.

Definition planck_energy : quantity energy_dim :=
  Build_quantity (sqrt (si_value reduced_planck_constant_si * si_value speed_of_light_si ^ 5 /
    si_value (estimate gravitational_constant_si))).

Lemma planck_energy_pos : 0 < si_value planck_energy.
Proof.
  apply sqrt_lt_R0, Rdiv_lt_0_compat.
  - apply Rmult_lt_0_compat; [exact hbar_si_pos | apply pow_lt, light_pos].
  - exact gravitation_pos.
Qed.

(** Planck mechanical and temperature scales, with the elementary charge
    setting the electrical scale. *)
Definition planck_units : unit_system := natural_units planck_energy planck_energy_pos.
