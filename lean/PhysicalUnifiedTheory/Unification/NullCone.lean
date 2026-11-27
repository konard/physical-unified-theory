module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PhysicalUnifiedTheory.Unification.NullCone

open scoped InnerProductSpace Topology
open Filter Set

/-- The integrating factor in (3.26) on a null generator. Here `f` is the
focusing rate and `Xi` is its primitive normalized at the cap. -/
theorem focused_slope (p Xi f : ℝ → ℝ) (a b : ℝ) (hcap : Xi a = 0)
    (hp : ∀ v ∈ Icc a b, HasDerivAt p (-(f v * p v)) v)
    (hXi : ∀ v ∈ Icc a b, HasDerivAt Xi (f v) v) (v : ℝ) (hv : v ∈ Icc a b) :
    p v = p a * Real.exp (-Xi v) := by
  have hcont : ContinuousOn (fun w => p w * Real.exp (Xi w)) (Icc a b) :=
    fun w hw => ((hp w hw).mul (hXi w hw).exp).continuousAt.continuousWithinAt
  have hzero (w : ℝ) (hw : w ∈ Ico a b) :
      HasDerivWithinAt (fun u => p u * Real.exp (Xi u)) 0 (Ici w) w := by
    have hw' : w ∈ Icc a b := ⟨hw.1, hw.2.le⟩
    convert ((hp w hw').mul (hXi w hw').exp).hasDerivWithinAt using 1
    ring
  have hprod := constant_of_has_deriv_right_zero hcont hzero v hv
  rw [hcap, Real.exp_zero, mul_one] at hprod
  rw [Real.exp_neg, ← hprod, mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _), mul_one]

/-- Cap-normalized elapsed time is unchanged by a positive affine rescaling. -/
theorem cap_clock_affine_invariant (slope start finish shift scale : ℝ) (hs : 0 < scale) :
    (slope / scale) * ((scale * finish + shift) - (scale * start + shift)) =
      slope * (finish - start) := by
  field_simp [hs.ne']
  ring

/-- The classical version of (5.21), given the two moment inequalities. -/
theorem area_bound (A a ε L : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hε : ε < 1)
    (hmoment : a ^ 2 ≤ 4 * Real.pi * A)
    (hclock : (1 - ε) * A / a ≤ L) : A ≤ 4 * Real.pi * L ^ 2 / (1 - ε) ^ 2 := by
  have hgap : 0 < 1 - ε := sub_pos.mpr hε
  have hfirst := (div_le_iff₀ ha).1 hclock
  have hsquare : ((1 - ε) * A) ^ 2 ≤ (L * a) ^ 2 := by
    gcongr
  have hsecond := mul_le_mul_of_nonneg_left hmoment (sq_nonneg L)
  apply (le_div_iff₀ (sq_pos_of_pos hgap)).2
  rcases hA.eq_or_lt with rfl | hA
  · rw [zero_mul]
    positivity
  · apply le_of_mul_le_mul_right _ hA
    calc
      A * (1 - ε) ^ 2 * A = ((1 - ε) * A) ^ 2 := by ring
      _ ≤ (L * a) ^ 2 := hsquare
      _ = L ^ 2 * a ^ 2 := by ring
      _ ≤ L ^ 2 * (4 * Real.pi * A) := hsecond
      _ = (4 * Real.pi * L ^ 2) * A := by ring

/-- Open gluing over any Hilbert basis, equations (4.29)–(4.30). The evolution and
cut projections may be absorbed into the two Hilbert vectors. -/
theorem open_gluing {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b : HilbertBasis ι ℂ E) (x y : E) :
    HasSum (fun i => ⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ) ⟪x, y⟫_ℂ ∧
    Summable (fun i => ‖⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ‖) ∧
    (∑' i, ‖⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ‖) ≤ ‖x‖ * ‖y‖ := by
  refine ⟨b.hasSum_inner_mul_inner x y, ?_⟩
  have h₂ : (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  simpa only [norm_mul, norm_inner_symm x (b _), ← b.repr_apply_apply, b.repr.norm_map] using
    lp.tsum_mul_le_mul_norm h₂ (b.repr x) (b.repr y)

/-- Restoring finitely many cuts gives the norm estimate underlying (4.31).
Unitary evolutions and orthogonal projections are special cases of contractions. -/
theorem multiple_cut_error_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U P : ℕ → E →L[ℂ] E) (full truncated : ℕ → E)
    (hU : ∀ j, ‖U j‖ ≤ 1) (hP : ∀ j, ‖P j‖ ≤ 1) (hstart : full 0 = truncated 0)
    (hfull : ∀ j, full (j + 1) = U j (full j))
    (htruncated : ∀ j, truncated (j + 1) = P j (U j (truncated j))) (n : ℕ) :
    ‖full n - truncated n‖ ≤ ∑ j ∈ Finset.range n, ‖full (j + 1) - P j (full (j + 1))‖ := by
  have contract (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) (x : E) : ‖T x‖ ≤ ‖x‖ :=
    (T.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg x) hT)
  induction n with
  | zero => simp [hstart]
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have hsplit : full (j + 1) - truncated (j + 1) =
        (P j (U j (full j - truncated j))) + (full (j + 1) - P j (full (j + 1))) := by
      rw [hfull j, htruncated j, map_sub, map_sub]
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add
      ((contract (P j) (hP j) _).trans ((contract (U j) (hU j) _).trans ih)) le_rfl)

/-- The `k+1` term in (4.33) for one fixed angular harmonic and polarization. -/
noncomputable def radialTerm (s : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (((-2 * ((k : ℝ) + 1) / s : ℝ) : ℂ) * Complex.I) *
    ((1 / (2 * s ^ 2 * ((k : ℝ) + 1) ^ 2) : ℝ) : ℂ)

theorem norm_radialTerm (s : ℝ) (k : ℕ) :
    ‖radialTerm s k‖ = 1 / (2 * s ^ 2 * ((k : ℝ) + 1) ^ 2) := by
  rw [radialTerm, norm_mul, Complex.norm_exp, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, Real.exp_zero, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  positivity

/-- Absolute cutoff convergence at fixed area parameter. -/
theorem radial_absolute_convergence (s : ℝ) : Summable (fun k => ‖radialTerm s k‖) := by
  have h : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    exact_mod_cast (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2
      (Real.summable_one_div_nat_pow.2 (by decide : 1 < (2 : ℕ)))
  refine (h.mul_left (1 / (2 * s ^ 2))).congr fun k => ?_
  rw [norm_radialTerm, div_mul_div_comm, one_mul]

/-- The harmonic coefficient in the cutoff expansion (4.34) diverges. -/
theorem radial_harmonic_coefficient_diverges :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) atTop atTop :=
  Real.tendsto_sum_range_one_div_nat_succ_atTop

/-- A uniform lower bound on the diagonal gives a linear lower bound on every
finite diagonal trace. -/
theorem finite_trace_lower_bound (c : ℝ) (diagonal : ℕ → ℝ) (h : ∀ k, c ≤ diagonal k)
    (n : ℕ) : (n : ℝ) * c ≤ ∑ k ∈ Finset.range n, diagonal k := by
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    (Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => h k)

/-- The positive scalar weight on an infinite orthonormal basis gives a
counterexample to deriving finite closed traces from bounded weights. -/
theorem constant_weight_trace_diverges (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => ∑ _k ∈ Finset.range n, c) atTop atTop := by
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hc

/-- A bounded positive scalar operator on ℓ² has all open gluing bounds and
divergent closed trace in its canonical basis. -/
theorem open_gluing_with_divergent_closed_trace (c : ℝ) (hc : 0 < c) (hc' : c ≤ 1) :
    ∃ b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2),
    ∃ W : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2,
      ‖W‖ ≤ 1 ∧
      (∀ x, 0 ≤ (⟪x, W x⟫_ℂ).re) ∧
      (∀ x y, Summable (fun k => ‖⟪x, b k⟫_ℂ * ⟪b k, W y⟫_ℂ‖) ∧
        (∑' k, ‖⟪x, b k⟫_ℂ * ⟪b k, W y⟫_ℂ‖) ≤ ‖x‖ * ‖y‖) ∧
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (⟪b k, W (b k)⟫_ℂ).re) atTop atTop := by
  let b := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (lp (fun _ : ℕ => ℂ) 2))
  let W : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
    (c : ℂ) • ContinuousLinearMap.id ℂ _
  have hW (x : lp (fun _ : ℕ => ℂ) 2) : W x = (c : ℂ) • x := rfl
  have hnorm : ‖W‖ ≤ 1 := by
    dsimp only [W]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hc.le).trans (by simpa)
  refine ⟨b, W, hnorm, fun x => ?_, fun x y => ?_, ?_⟩
  · rw [hW, inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    change 0 ≤ c * RCLike.re ⟪x, x⟫_ℂ
    rw [inner_self_eq_norm_sq]
    positivity
  · obtain ⟨_, hsum, hbound⟩ := open_gluing b x (W y)
    refine ⟨hsum, hbound.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg x))⟩
    exact (W.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg y) hnorm)
  · have hdiag (k : ℕ) : (⟪b k, W (b k)⟫_ℂ).re = c := by
      rw [hW, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 k]
      change ((c : ℂ) * (1 : ℂ) ^ 2).re = c
      simp
    simpa only [hdiag] using constant_weight_trace_diverges c hc

/-- Purity of the normalized constant weight on a nonempty finite cut. -/
theorem constant_weight_purity (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 0 < n) :
    (∑ _k ∈ Finset.range n, c ^ 2) / (∑ _k ∈ Finset.range n, c) ^ 2 = 1 / (n : ℝ) := by
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hc.ne']

/-- Positive normalized replica purity forces an exact finite trace bound if the
cut weights obey `λ² ≤ λ` and the amplitude equals the cut replica ratio. -/
theorem trace_bound_from_purity (trace cyclic p : ℝ) (htrace : 0 < trace) (hp : 0 < p)
    (hcyclic : cyclic ≤ trace) (hpurity : p ≤ cyclic / trace ^ 2) : trace ≤ 1 / p := by
  have h := (le_div_iff₀ (sq_pos_of_pos htrace)).1 hpurity
  apply (le_div_iff₀ hp).2
  apply le_of_mul_le_mul_right _ htrace
  calc
    trace * p * trace = p * trace ^ 2 := by ring
    _ ≤ cyclic := h
    _ ≤ trace := hcyclic
    _ = 1 * trace := by ring

/-- An exact positive replica limit supplies an eventual uniform trace bound. -/
theorem trace_bound_from_replica_limit {ι : Type*} (cuts : Filter ι)
    (trace cyclic : ι → ℝ) (p : ℝ) (hp : 0 < p) (htrace : ∀ i, 0 < trace i)
    (hcyclic : ∀ i, cyclic i ≤ trace i)
    (hlimit : Tendsto (fun i => cyclic i / trace i ^ 2) cuts (𝓝 p)) :
    ∀ᶠ i in cuts, trace i ≤ 2 / p := by
  filter_upwards [(tendsto_order.1 hlimit).1 (p / 2) (by linarith)] with i hi
  have h := trace_bound_from_purity (trace i) (cyclic i) (p / 2) (htrace i)
    (by positivity) (hcyclic i) hi.le
  simpa only [div_div_eq_mul_div, one_mul] using h

/-- If the finite closed-cut amplitudes converge to the exact uncut one,
the sign pattern in (5.38) is impossible. -/
theorem no_positive_closed_gluing_limit {ι : Type*} (cuts : Filter ι) [NeBot cuts]
    (amplitude : ι → ℝ) (uncut : ℝ) (hpos : 0 < uncut)
    (hcuts : ∀ᶠ i in cuts, amplitude i ≤ 0) : ¬ Tendsto amplitude cuts (𝓝 uncut) :=
  fun hlimit => hpos.not_ge (le_of_tendsto hlimit hcuts)

/-- Scalar positive cut forms can have zero limiting resolvent weight. -/
theorem cutoff_resolvent_vanishes (L : ℝ) :
    Tendsto (fun n : ℕ => L / (L + (n : ℝ))) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ L tendsto_natCast_atTop_atTop)

/-- Scalar resolvent cutoff bound underlying the form-domain argument in Appendix C. -/
theorem resolvent_energy_bound (L x : ℝ) (hL : 0 < L) (hx : 0 ≤ x) :
    x * (L / (L + x)) ^ 2 ≤ L / 4 := by
  have hsum : 0 < L + x := by linarith
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hsum)]
  nlinarith [mul_nonneg hL.le (sq_nonneg (L - x))]

/-- The strict tangent deficit of `x / (L + x)` used in the Wigner check. -/
theorem resolvent_tangent_deficit (L x m : ℝ) (hL : 0 < L) (hx : 0 ≤ x) (hm : 0 ≤ m) :
    m / (L + m) + L / (L + m) ^ 2 * (x - m) - x / (L + x) =
      L * (x - m) ^ 2 / ((L + m) ^ 2 * (L + x)) := by
  have hxm : L + x ≠ 0 := by linarith
  have hmm : L + m ≠ 0 := by linarith
  field_simp
  ring

/-- The boost mismatch factor in (5.29) is strictly suppressed away from matching. -/
theorem boost_mismatch (r : ℝ) (hr : 0 < r) :
    1 - 4 * r / (1 + r) ^ 2 = (r - 1) ^ 2 / (r + 1) ^ 2 := by
  have h : 1 + r ≠ 0 := by linarith
  have h' : r + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem boost_factor_lt_one (r : ℝ) (hr : 0 < r) (hmismatch : r ≠ 1) :
    4 * r / (1 + r) ^ 2 < 1 := by
  have h : 0 < (r - 1) ^ 2 / (r + 1) ^ 2 :=
    div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hmismatch)) (by positivity)
  linarith [boost_mismatch r hr]

/-- Equation (5.50) for a finite nonempty spectrum. -/
theorem finite_gibbs_entropy {ι : Type*} (cut : Finset ι) (hcut : cut.Nonempty)
    (entropy : ι → ℝ) :
    let Z := ∑ i ∈ cut, Real.exp (-entropy i)
    let p := fun i => Real.exp (-entropy i) / Z
    (∑ i ∈ cut, -(p i * Real.log (p i))) = (∑ i ∈ cut, p i * entropy i) + Real.log Z := by
  dsimp only
  let Z := ∑ i ∈ cut, Real.exp (-entropy i)
  have hZ : 0 < Z := Finset.sum_pos (fun i _ => Real.exp_pos (-entropy i)) hcut
  change (∑ i ∈ cut, -(Real.exp (-entropy i) / Z * Real.log (Real.exp (-entropy i) / Z))) =
    (∑ i ∈ cut, Real.exp (-entropy i) / Z * entropy i) + Real.log Z
  simp_rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  simp_rw [show ∀ a b c : ℝ, -(a * (-b - c)) = a * b + a * c by intros; ring]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div, div_self hZ.ne', one_mul]

/-- One-loop arithmetic in (5.69) at the pure-gravity value of `q`. -/
theorem one_loop_coefficient :
    (257 / 302 : ℝ) / (2 * (1 - 257 / 302)) - 1 / 2 = 106 / 45 := by
  norm_num

/-- The covariance contraction (6.12)–(6.13) for a finite family, given the
second variation of the Einstein equation. -/
theorem finite_backreaction_contraction {ι E F : Type*} (modes : Finset ι)
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (covariance : ι → ℝ) (secondMetricVariation : ι → E) (linearized : E →ₗ[ℝ] F)
    (quadraticSource : ι → F)
    (hvar : ∀ i ∈ modes, linearized (secondMetricVariation i) = (-2 : ℝ) • quadraticSource i) :
    linearized (∑ i ∈ modes, (covariance i / 2) • secondMetricVariation i) =
      -(∑ i ∈ modes, covariance i • quadraticSource i) := by
  rw [map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, hvar i hi, smul_smul, ← neg_smul]
  congr 1
  ring

end PhysicalUnifiedTheory.Unification.NullCone
