(** * Differential Geometry (A.2)

    This module formalizes differential geometry concepts required for
    general relativity and gauge theories.

    Contents:
    - A.2.2: Tensor algebra (4-vectors and the Minkowski metric)
    - A.2.4: Curvature tensors (Ricci scalar in flat spacetime)
    - A.2.5: Geodesics in flat spacetime
    - A.2.6: Lorentzian geometry and causal structure

    Note: Coordinates and the basic spacetime interval are defined in
    GeneralRelativity/Basic.v. This module provides Track A foundations
    with additional mathematical structure.

    References:
    - Lee, "Introduction to Smooth Manifolds"
    - O'Neill, "Semi-Riemannian Geometry"
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz.
Require Import PhysicalUnifiedTheory.Foundations.Basic.
Open Scope R_scope.

(** ** A.2.2: Minkowski Metric and 4-Vectors

    The Minkowski metric η_μν = diag(-1, +1, +1, +1) is the metric tensor
    of flat spacetime. It defines the spacetime interval and causal structure. *)

(** A 4-vector in Minkowski spacetime (t, x, y, z components). *)
Record FourVector : Type := mkFourVector {
  v_t : R;
  v_x : R;
  v_y : R;
  v_z : R
}.

(** The zero 4-vector. *)
Definition zero_fourvector : FourVector := {|
  v_t := 0; v_x := 0; v_y := 0; v_z := 0
|}.

(** The Minkowski inner product: η(u, v) = -u_t v_t + u_x v_x + u_y v_y + u_z v_z. *)
Definition minkowski_inner (u v : FourVector) : R :=
  - u.(v_t) * v.(v_t) + u.(v_x) * v.(v_x) + u.(v_y) * v.(v_y) + u.(v_z) * v.(v_z).

(** The Minkowski norm squared of a 4-vector. *)
Definition minkowski_norm_sq (v : FourVector) : R :=
  minkowski_inner v v.

(** The Minkowski norm of the zero vector is zero. *)
Lemma zero_minkowski_norm : minkowski_norm_sq zero_fourvector = 0.
Proof.
  unfold minkowski_norm_sq, minkowski_inner, zero_fourvector. simpl. ring.
Qed.

(** Scalar multiplication of a 4-vector. *)
Definition scale_fourvector (c : R) (v : FourVector) : FourVector := {|
  v_t := c * v.(v_t);
  v_x := c * v.(v_x);
  v_y := c * v.(v_y);
  v_z := c * v.(v_z)
|}.

(** The Minkowski inner product scales quadratically: η(cv, cv) = c² η(v,v). *)
Lemma minkowski_scaling (c : R) (v : FourVector) :
    minkowski_norm_sq (scale_fourvector c v) = c * c * minkowski_norm_sq v.
Proof.
  unfold minkowski_norm_sq, minkowski_inner, scale_fourvector. simpl. ring.
Qed.

(** ** A.2.6: Causal Structure

    4-vectors are classified by the sign of their Minkowski norm:
    - Timelike: η(v,v) < 0 (worldlines of massive particles)
    - Lightlike: η(v,v) = 0 (worldlines of massless particles, photons)
    - Spacelike: η(v,v) > 0 (spacelike-separated events) *)

Definition is_timelike_vec (v : FourVector) : Prop := minkowski_norm_sq v < 0.
Definition is_lightlike_vec (v : FourVector) : Prop := minkowski_norm_sq v = 0.
Definition is_spacelike_vec (v : FourVector) : Prop := minkowski_norm_sq v > 0.

(** A purely temporal 4-vector is timelike for nonzero time component. *)
Lemma temporal_timelike (tau : R) (h : tau <> 0) :
    is_timelike_vec {| v_t := tau; v_x := 0; v_y := 0; v_z := 0 |}.
Proof.
  unfold is_timelike_vec, minkowski_norm_sq, minkowski_inner. simpl.
  nra.
Qed.

(** A null vector represents a photon worldline: light speed = 1. *)
Lemma photon_lightlike :
    is_lightlike_vec {| v_t := 1; v_x := 1; v_y := 0; v_z := 0 |}.
Proof.
  unfold is_lightlike_vec, minkowski_norm_sq, minkowski_inner. simpl. lra.
Qed.

(** A purely spatial 4-vector is spacelike for nonzero spatial component. *)
Lemma spatial_spacelike (r : R) (h : r <> 0) :
    is_spacelike_vec {| v_t := 0; v_x := r; v_y := 0; v_z := 0 |}.
Proof.
  unfold is_spacelike_vec, minkowski_norm_sq, minkowski_inner. simpl.
  nra.
Qed.

(** Causal types are mutually exclusive. *)
Lemma timelike_not_lightlike (v : FourVector) :
    is_timelike_vec v -> ~ is_lightlike_vec v.
Proof.
  unfold is_timelike_vec, is_lightlike_vec, minkowski_norm_sq. lra.
Qed.

Lemma lightlike_not_spacelike (v : FourVector) :
    is_lightlike_vec v -> ~ is_spacelike_vec v.
Proof.
  unfold is_lightlike_vec, is_spacelike_vec, minkowski_norm_sq. lra.
Qed.

(** ** A.2.4: Curvature in Flat Spacetime

    In flat Minkowski spacetime, all curvature tensors vanish.
    The Riemann tensor R^ρ_{σμν} = 0, Ricci tensor R_μν = 0,
    and Ricci scalar R = 0.

    Full curvature formalization requires smooth manifold structure
    and connection coefficients (Christoffel symbols). *)

Definition flat_ricci_scalar : R := 0.

Lemma flat_vacuum_consistent : flat_ricci_scalar = 0.
Proof. reflexivity. Qed.

(** ** A.2.5: Geodesics in Flat Spacetime

    In flat Minkowski spacetime, geodesics are straight lines.
    A straight worldline has constant 4-velocity. *)

(** A straight worldline: position at parameter λ is p₀ + λ * v. *)
Definition straight_worldline (p0 v : FourVector) (lambda : R) : FourVector := {|
  v_t := p0.(v_t) + lambda * v.(v_t);
  v_x := p0.(v_x) + lambda * v.(v_x);
  v_y := p0.(v_y) + lambda * v.(v_y);
  v_z := p0.(v_z) + lambda * v.(v_z)
|}.

(** At parameter λ=0, the worldline starts at p₀. *)
Lemma worldline_at_origin (p0 v : FourVector) :
    straight_worldline p0 v 0 = p0.
Proof.
  unfold straight_worldline.
  destruct p0. simpl.
  f_equal; ring.
Qed.
