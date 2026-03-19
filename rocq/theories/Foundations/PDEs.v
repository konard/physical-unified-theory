(** * Partial Differential Equations (A.6)

    This module formalizes PDE concepts relevant to physics.

    Contents:
    - A.6.1: Classification of linear PDEs
    - A.6.1: Klein-Gordon equation (dispersion relation)
    - A.6.1: Particle in a box (energy levels)
    - A.6.3: Geometric PDEs (qualitative model)

    References:
    - Evans, "Partial Differential Equations"
    - Taylor, "Partial Differential Equations I-III"
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Psatz.
Require Import PhysicalUnifiedTheory.Foundations.Basic.
Open Scope R_scope.

(** ** A.6.1: Classification of Linear PDEs

    Second-order linear PDEs in two variables are classified by:
    - Elliptic (b² - 4ac < 0): Laplace equation
    - Parabolic (b² - 4ac = 0): heat equation
    - Hyperbolic (b² - 4ac > 0): wave equation *)

(** The discriminant of a second-order PDE determines its type. *)
Definition pde_discriminant (a b c : R) : R := b * b - 4 * a * c.

(** The Laplace equation (Δu = 0) is elliptic: discriminant < 0. *)
Lemma laplace_is_elliptic :
    pde_discriminant 1 0 1 < 0.
Proof.
  unfold pde_discriminant. lra.
Qed.

(** The heat equation is parabolic: discriminant = 0. *)
Lemma heat_is_parabolic :
    pde_discriminant 0 0 (-1) = 0.
Proof.
  unfold pde_discriminant. lra.
Qed.

(** The wave equation (u_tt - c²u_xx = 0) is hyperbolic: discriminant > 0.
    With a=1, b=0, c=-1 (wave speed c=1). *)
Lemma wave_is_hyperbolic :
    pde_discriminant 1 0 (-1) > 0.
Proof.
  unfold pde_discriminant. lra.
Qed.

(** ** Klein-Gordon Equation

    The Klein-Gordon equation (□ + m²)φ = 0 describes a free massive scalar field.
    Dispersion relation: ω² = k² + m². *)

(** Klein-Gordon dispersion relation: ω² = k² + m². *)
Definition klein_gordon_dispersion (k m : R) : R := k * k + m * m.

(** For massless particles (m=0), reduces to the wave equation: ω² = k². *)
Lemma massless_dispersion (k : R) :
    klein_gordon_dispersion k 0 = k * k.
Proof.
  unfold klein_gordon_dispersion. ring.
Qed.

(** Energy of a Klein-Gordon quantum: E = √(k² + m²) (natural units). *)
Definition klein_gordon_energy (k m : R) : R :=
  sqrt (klein_gordon_dispersion k m).

(** Energy is always non-negative. *)
Lemma klein_gordon_energy_nonneg (k m : R) :
    0 <= klein_gordon_energy k m.
Proof.
  unfold klein_gordon_energy.
  apply sqrt_pos.
Qed.

(** For zero momentum, the energy equals the rest mass: E = m. *)
Lemma rest_energy (m : R) (hm : 0 <= m) :
    klein_gordon_energy 0 m = m.
Proof.
  unfold klein_gordon_energy, klein_gordon_dispersion.
  assert (h : 0 * 0 + m * m = m * m) by ring.
  rewrite h.
  fold (Rsqr m). apply sqrt_Rsqr. exact hm.
Qed.

(** ** Particle in a Box (Schrödinger Equation)

    Energy levels of a particle in a 1D infinite square well of length L.
    Time-independent Schrödinger equation: Hψ = Eψ.
    In natural units with m=1, L=π: E_n = n²/2. *)

(** Energy levels: E_n = n²π²/2 (standard box with L=1, m=1/2). *)
Definition particle_in_box_energy (n : nat) : R :=
  INR n * INR n * (PI * PI) / 2.

(** Ground state energy (n=1): E₁ = π²/2. *)
Lemma ground_state_energy :
    particle_in_box_energy 1 = PI * PI / 2.
Proof.
  unfold particle_in_box_energy. simpl.
  lra.
Qed.

(** Energy levels are non-negative. *)
Lemma energy_nonneg (n : nat) : 0 <= particle_in_box_energy n.
Proof.
  unfold particle_in_box_energy.
  assert (hPI : 0 < PI) by (apply PI_RGT_0).
  assert (hINR : 0 <= INR n) by (apply pos_INR).
  nra.
Qed.

(** Ground state has less energy than first excited state. *)
Lemma ground_lt_first_excited :
    particle_in_box_energy 1 < particle_in_box_energy 2.
Proof.
  unfold particle_in_box_energy. simpl.
  assert (hPI : 0 < PI) by (apply PI_RGT_0).
  nra.
Qed.

(** ** A.6.3: Geometric PDEs (Qualitative Model)

    Ricci flow: ∂_t g_μν = -2 R_μν deforms a metric toward constant curvature.
    A simple ODE model: ∂_t u = -u (exponential decay, analogous to curvature decay). *)

(** Simplified Ricci flow model: exponential decay of curvature. *)
Definition ricci_flow_model (u0 t : R) : R := u0 * exp (- t).

(** The Ricci flow model is positive when the initial curvature is positive. *)
Lemma ricci_flow_positive (u0 : R) (hu0 : 0 < u0) (t : R) :
    0 < ricci_flow_model u0 t.
Proof.
  unfold ricci_flow_model.
  apply Rmult_pos; [exact hu0 | apply exp_pos].
Qed.

(** The Ricci flow model is strictly decreasing for positive initial curvature. *)
Lemma ricci_flow_decreasing (u0 : R) (hu0 : 0 < u0) (t : R) (ht : 0 < t) :
    ricci_flow_model u0 t < u0.
Proof.
  unfold ricci_flow_model.
  assert (hexp : exp (- t) < 1).
  { assert (h : - t < 0) by lra.
    rewrite <- exp_0.
    apply exp_increasing.
    lra. }
  assert (hpos : 0 < exp (- t)) by apply exp_pos.
  nra.
Qed.
