import PhysicalUnifiedTheory.Unification.NullCone

open PhysicalUnifiedTheory.Unification.NullCone
open scoped InnerProductSpace Topology
open Filter

example (p : ℝ) : p = p * Real.exp (-(0 : ℝ)) := by
  exact focused_slope (fun _ => p) (fun _ => 0) (fun _ => 0) 0 1 rfl
    (fun _ _ => by simpa using hasDerivAt_const _ p)
    (fun _ _ => hasDerivAt_const _ 0) 1 (by norm_num [Set.mem_Icc])

-- The classical shear-free, constant-density example saturates the bound.
example (r ε : ℝ) (hε : ε < 1) :
    4 * Real.pi * ((1 - ε) * r) ^ 2 / (1 - ε) ^ 2 = 4 * Real.pi * r ^ 2 := by
  field_simp [sub_ne_zero.mpr hε.ne']

-- Positive clock resolvents can have zero weight after the cutoff is removed.
example : Tendsto (fun n : ℕ => (3 : ℝ) / (3 + n)) atTop (𝓝 0) :=
  cutoff_resolvent_vanishes 3

example : 1 - (3 : ℝ) / (3 + 2) ≤ 2 / 3 := by
  simpa using finite_clock_resolvent_error ({0} : Finset ℕ) (fun _ => 1) (fun _ => 2)
    3 (by norm_num) (by simp) (by simp) (by simp)

example : (1 : ℝ) / (2 + 1) + 2 / (2 + 1) ^ 2 * (2 - 1) - 2 / (2 + 2) = 1 / 18 := by
  convert resolvent_tangent_deficit 2 2 1 (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num

-- Every absolute open gluing sum is bounded even in this divergent trace model.
example : ∃ b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2),
    ∃ W : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2,
      ‖W‖ ≤ 1 ∧
      (∀ x, 0 ≤ (⟪x, W x⟫_ℂ).re) ∧
      (∀ x y, Summable (fun k => ‖⟪x, b k⟫_ℂ * ⟪b k, W y⟫_ℂ‖) ∧
        (∑' k, ‖⟪x, b k⟫_ℂ * ⟪b k, W y⟫_ℂ‖) ≤ ‖x‖ * ‖y‖) ∧
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (⟪b k, W (b k)⟫_ℂ).re) atTop atTop :=
  open_gluing_with_divergent_closed_trace (2 / 3) (by norm_num) (by norm_num)

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ℕ → E) (hv : Orthonormal ℂ v) : ¬ ∃ x : E, ∀ k, (2 / 3 : ℝ) ≤ ‖⟪v k, x⟫_ℂ‖ ^ 2 :=
  no_normalizable_cap_with_uniform_weights v hv (2 / 3) (by norm_num)

example : (∑ _k ∈ Finset.range 128, (2 / 3 : ℝ) ^ 2) /
    (∑ _k ∈ Finset.range 128, (2 / 3 : ℝ)) ^ 2 = 1 / 128 :=
  constant_weight_purity (2 / 3) (by norm_num) 128 (by decide)

example : ‖radialTerm 2 0‖ = (1 / 8 : ℝ) := by
  rw [norm_radialTerm]
  norm_num
