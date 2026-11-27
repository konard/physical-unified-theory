From Stdlib Require Import Reals Lra.
From PhysicalUnifiedTheory.Experimental Require Import Units Constants.
Open Scope R_scope.

Fail Check (fun (distance : quantity length_dim) (duration : quantity time_dim) =>
  add_quantity distance duration).

Example speed_of_light_exact : si_value speed_of_light_si = 299792458.
Proof. reflexivity. Qed.

Example planck_constant_exact : si_value planck_constant_si = 662607015 / 10^42.
Proof. reflexivity. Qed.

Example luminous_efficacy_exact : si_value luminous_efficacy_si = 683.
Proof. reflexivity. Qed.

Example gravitation_uncertainty :
  si_value (standard_uncertainty gravitational_constant_si) = 15 / 10^16.
Proof. reflexivity. Qed.

Example planck_length_conversion (value : R) :
  convert planck_units si length_dim (convert si planck_units length_dim value) = value.
Proof. rewrite convert_trans, convert_self. reflexivity. Qed.

Example planck_length_positive : 0 < base_scale planck_units Length.
Proof. apply base_scale_pos. Qed.

Example natural_light_and_action (energy : quantity energy_dim) (he : 0 < si_value energy) :
  let units := natural_units energy he in
  base_scale units Length / base_scale units Time = si_value speed_of_light_si /\
  base_scale units Mass * base_scale units Length ^ 2 / base_scale units Time =
    si_value reduced_planck_constant_si.
Proof.
  cbn [natural_units base_scale].
  set (c := si_value speed_of_light_si).
  set (h := si_value reduced_planck_constant_si).
  assert (hc : 0 < c) by (change (0 < 299792458); lra).
  assert (hh : 0 < h).
  { change (0 < (662607015 / 10^42) / (2 * PI)).
    apply Rdiv_lt_0_compat; [|apply Rmult_lt_0_compat; [lra | exact PI_RGT_0]].
    apply Rdiv_lt_0_compat; [lra | apply pow_lt; lra]. }
  split; field; repeat split; lra.
Qed.
