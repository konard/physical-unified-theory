module

import PhysicalUnifiedTheory.Foundations.MeasureTheory

open MeasureTheory PhysicalUnifiedTheory.Foundations.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

private theorem unitWave_memLp : MemLp (fun _ : Ω => (1 : ℂ)) 2 μ :=
  memLp_const _

private noncomputable def unitWave : Lp ℂ 2 μ := (unitWave_memLp μ).toLp _

private theorem unitWave_norm : ‖unitWave μ‖ = 1 := by
  rw [unitWave, Lp.norm_toLp, eLpNorm_const' _ (by simp) (by simp)]
  simp

/-- A constant unit wave function on a probability space gives back the
    reference measure on every measurable region. -/
example : (positionProbability (unitWave μ) (unitWave_norm μ)).toMeasure = μ := by
  ext s hs
  change positionMeasure (unitWave μ) s = μ s
  rw [positionMeasure_apply_of_ae_eq (unitWave μ) (unitWave_memLp μ).coeFn_toLp hs]
  simp
