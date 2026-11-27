module

/-
# Measure Theory and Probability (A.5)

This module formalizes measure theory and probability as needed for quantum mechanics
(Born rule, density matrices) and quantum field theory (path integrals).

## Contents

- A.5.1: Measure spaces and integration
- A.5.2: Probability theory foundations
- A.5.3: Functional integration (path integrals) — stub
- A.5.4: Stochastic processes — stub

## Dependencies

- `Mathlib.MeasureTheory.Measure.MeasureSpace` for measure spaces
- `Mathlib.MeasureTheory.Integral.Lebesgue.Basic` for Lebesgue integration
- `Mathlib.MeasureTheory.Measure.ProbabilityMeasure` for probability measures

## References

- Rudin, "Real and Complex Analysis"
- Glimm & Jaffe, "Quantum Physics: A Functional Integral Point of View"

## Hypothesis

Rigorous path integrals can be constructed in 4D via constructive QFT methods
(Osterwalder-Schrader axioms + Wightman reconstruction theorem).
-/

public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

namespace PhysicalUnifiedTheory.Foundations.MeasureTheory

open scoped ComplexOrder

/-!
## A.5.1: Measure Spaces and Integration

A measure space (X, Σ, μ) consists of:
- A set X (sample space)
- A σ-algebra Σ (measurable subsets)
- A measure μ: Σ → [0, ∞] (non-negative, countably additive)

The Lebesgue measure on ℝⁿ is the canonical example.
-/

/- The L² space: square-integrable functions on a measure space.
    In quantum mechanics, wave functions live in L²(ℝⁿ, ℂ).
    L² is a Hilbert space with inner product ⟨φ|ψ⟩ = ∫ φ*(x) ψ(x) dx. -/
-- L²(X, μ) is available as MeasureTheory.Lp E 2 μ in Mathlib

/- The L² inner product of two functions: ⟨φ|ψ⟩ = ∫ conj(φ(x)) ψ(x) dx. -/
-- This is the inner product making wave functions in quantum mechanics.
-- For ψ ∈ L²(ℝ, ℂ): the norm ‖ψ‖² = ∫|ψ(x)|² dx = 1 for normalized states.

/- A density operator (density matrix) represents a mixed quantum state.
    ρ: H → H with ρ ≥ 0 (positive semidefinite), Tr(ρ) = 1.
    Pure states: ρ = |ψ⟩⟨ψ| (rank-1 projector). -/
-- In finite dimensions: ρ is a positive semidefinite Hermitian matrix with trace 1.

/-- For finite-dimensional systems, a density matrix is a Hermitian positive
    semidefinite matrix with trace 1. -/
structure DensityMatrix (n : ℕ) where
  /-- The matrix representing the quantum state -/
  mat : Matrix (Fin n) (Fin n) ℂ
  /-- The quadratic form is nonnegative on all vectors. This also implies Hermiticity. -/
  posSemidef : mat.PosSemidef
  /-- Trace equals 1: Tr(ρ) = 1 -/
  trace_one : mat.trace = 1

/-- A density matrix equals its conjugate transpose. -/
theorem DensityMatrix.hermitian {n : ℕ} (ρ : DensityMatrix n) : ρ.mat.IsHermitian :=
  ρ.posSemidef.isHermitian

/-- Born probability for an outcome in the computational basis. -/
def DensityMatrix.basisProbability {n : ℕ} (ρ : DensityMatrix n) (i : Fin n) : ℝ :=
  (ρ.mat i i).re

theorem DensityMatrix.basisProbability_nonneg {n : ℕ} (ρ : DensityMatrix n) (i : Fin n) :
    0 ≤ ρ.basisProbability i :=
  (Complex.nonneg_iff.mp (ρ.posSemidef.diag_nonneg (i := i))).1

theorem DensityMatrix.sum_basisProbability {n : ℕ} (ρ : DensityMatrix n) :
    ∑ i, ρ.basisProbability i = 1 := by
  simpa [Matrix.trace, basisProbability] using congrArg Complex.re ρ.trace_one

/-- The outer product of ψ with its conjugate dual. Its trace is one when ψ is normalized. -/
noncomputable def pureStateDensityMatrix {n : ℕ} (ψ : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ψ i * star (ψ j)

/-- The outer product of a vector with its conjugate dual is positive semidefinite. -/
theorem pureState_posSemidef {n : ℕ} (ψ : Fin n → ℂ) :
    (pureStateDensityMatrix ψ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star ψ

/-- The trace of the pure state density matrix is 1 when ψ is normalized. -/
theorem pureState_trace_one {n : ℕ} (ψ : Fin n → ℂ) (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    (pureStateDensityMatrix ψ).trace = 1 := by
  calc
    (pureStateDensityMatrix ψ).trace = ∑ i, (Complex.normSq (ψ i) : ℂ) := by
      simp only [Matrix.trace, Matrix.diag_apply, pureStateDensityMatrix]
      apply Finset.sum_congr rfl
      intro i _
      exact (Complex.normSq_eq_conj_mul_self.trans (mul_comm _ _)).symm
    _ = 1 := by
      rw [← Complex.ofReal_sum, hψ, Complex.ofReal_one]

/-- A normalized state vector determines a positive trace-one density matrix. -/
noncomputable def DensityMatrix.ofPureState {n : ℕ} (ψ : Fin n → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1) : DensityMatrix n where
  mat := pureStateDensityMatrix ψ
  posSemidef := pureState_posSemidef ψ
  trace_one := pureState_trace_one ψ hψ

/-!
## A.5.2: Probability Theory

A probability measure is a measure P with P(X) = 1.
In quantum mechanics, the Born rule gives the probability measure:
P(measured in set A) = ∫_A |ψ(x)|² dx for position measurement.
-/

section PositionMeasurement

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The squared-amplitude measure of a wave function. For position in Euclidean
    space, take `μ` to be Lebesgue measure. -/
noncomputable def positionMeasure (ψ : Lp ℂ 2 μ) : Measure Ω :=
  μ.withDensity fun x => ‖ψ x‖ₑ ^ (2 : ℕ)

/-- A region of zero reference measure has zero position probability. -/
theorem positionMeasure_absolutelyContinuous (ψ : Lp ℂ 2 μ) :
    (positionMeasure ψ).AbsolutelyContinuous μ :=
  withDensity_absolutelyContinuous μ _

/-- A measurable region has squared-amplitude mass computed with any
    representative of the `L²` wave function. -/
theorem positionMeasure_apply_of_ae_eq (ψ : Lp ℂ 2 μ) {f : Ω → ℂ}
    (hf : (ψ : Ω → ℂ) =ᵐ[μ] f) {s : Set Ω} (hs : MeasurableSet s) :
    positionMeasure ψ s = ∫⁻ x in s, ‖f x‖ₑ ^ (2 : ℕ) ∂μ := by
  have hd : (fun x => ‖ψ x‖ₑ ^ (2 : ℕ)) =ᵐ[μ] (fun x => ‖f x‖ₑ ^ (2 : ℕ)) :=
    hf.mono fun _ hx => congrArg (fun z : ℂ => ‖z‖ₑ ^ (2 : ℕ)) hx
  rw [positionMeasure, withDensity_congr_ae hd, withDensity_apply _ hs]

/-- A normalized wave function gives a probability measure on position space. -/
noncomputable def positionProbability (ψ : Lp ℂ 2 μ) (hψ : ‖ψ‖ = 1) : ProbabilityMeasure Ω := by
  refine ⟨positionMeasure ψ, ⟨?_⟩⟩
  rw [positionMeasure_apply_of_ae_eq ψ Filter.EventuallyEq.rfl MeasurableSet.univ,
    Measure.restrict_univ]
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by simp) (Lp.aestronglyMeasurable ψ)
  change eLpNorm (ψ : Ω → ℂ) 2 μ ^ (2 : ℝ) = _ at h
  rw [← Lp.enorm_def ψ] at h
  have hψ' : ‖ψ‖ₑ = 1 := by
    rw [← ofReal_norm, hψ, ENNReal.ofReal_one]
  simpa [ENNReal.rpow_two, hψ'] using h.symm

end PositionMeasurement

section ProjectiveMeasurement

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (K : Submodule ℂ H) [K.HasOrthogonalProjection]

/-- The squared norm of the projection onto a measurement subspace. -/
noncomputable def projectionWeight (ψ : H) : ℝ := ‖K.orthogonalProjectionOnto ψ‖ ^ 2

theorem projectionWeight_nonneg (ψ : H) : 0 ≤ projectionWeight K ψ := sq_nonneg _

/-- A normalized input gives total probability one for the two complementary outcomes. -/
theorem projectionWeights_sum (ψ : H) (hψ : ‖ψ‖ = 1) :
    projectionWeight K ψ + projectionWeight Kᗮ ψ = 1 := by
  simpa [projectionWeight, hψ] using (K.norm_sq_eq_add_norm_sq_projection ψ).symm

/-- Condition a pure state on a positive-probability outcome by projecting and normalizing. -/
noncomputable def projectedState (ψ : H) (h : 0 < projectionWeight K ψ) : {φ : K // ‖φ‖ = 1} := by
  have hNorm : ‖K.orthogonalProjectionOnto ψ‖ ≠ 0 := by
    intro hz
    simp [projectionWeight, hz] at h
  refine ⟨(↑(‖K.orthogonalProjectionOnto ψ‖⁻¹) : ℂ) • K.orthogonalProjectionOnto ψ, ?_⟩
  rw [norm_smul, Complex.norm_real, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ hNorm

/-- Immediately repeating the chosen measurement produces that outcome with certainty. -/
theorem projectedState_weight (ψ : H) (h : 0 < projectionWeight K ψ) :
    projectionWeight K (((projectedState K ψ h).val : K) : H) = 1 := by
  rw [projectionWeight, K.norm_orthogonalProjectionOnto_apply (projectedState K ψ h).val.prop]
  change ‖(projectedState K ψ h).val‖ ^ 2 = 1
  simp [(projectedState K ψ h).property]

end ProjectiveMeasurement

/- Entropy of a quantum state (von Neumann entropy).
    S(ρ) = -Tr(ρ log ρ).
    For pure states: S = 0.
    For maximally mixed state: S = log(n). -/
-- TODO (A.5.2): Formalize von Neumann entropy using matrix logarithm

/- The Heisenberg uncertainty principle: ΔA · ΔB ≥ (1/2)|⟨[A,B]⟩|.
    For position and momentum: Δx · Δp ≥ ℏ/2.
    In natural units (ℏ=1): Δx · Δp ≥ 1/2. -/
-- TODO (A.5.2): Formalize uncertainty relations from commutators

/-!
## A.5.3: Path Integrals (Functional Integration)

The path integral formulation of quantum mechanics sums over all paths:
⟨x_f|e^{-iHt}|x_i⟩ = ∫ D[x(t)] exp(iS[x]/ℏ)

where S[x] = ∫₀ᵗ L(x, ẋ) dt is the classical action.

**Hypothesis**: Rigorous path integrals can be constructed in 4D via
constructive QFT methods (Euclidean continuation → Wiener measure).
-/

-- TODO (A.5.3): Formalize Wiener measure on path space
-- The Euclidean path integral uses the heat kernel / Wiener process:
-- ⟨x_f|e^{-Ht}|x_i⟩ = ∫_{x(0)=x_i}^{x(t)=x_f} D[x] exp(-S_E[x])
-- This is rigorously defined as the Wiener measure on C([0,t], ℝ).

-- TODO (A.5.3): Osterwalder-Schrader axioms for Euclidean QFT
-- These axioms guarantee the existence of a corresponding Minkowski QFT.

/-!
## A.5.4: Stochastic Processes

Stochastic processes model quantum systems coupled to environments
(open quantum systems, decoherence, Brownian motion).
-/

-- TODO (A.5.4): Formalize Brownian motion and Itô calculus
-- Key connection to physics: Nelson's stochastic mechanics interprets
-- quantum mechanics as a classical diffusion process.

end PhysicalUnifiedTheory.Foundations.MeasureTheory
