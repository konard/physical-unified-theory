module

import PhysicalUnifiedTheory.Experimental.Constants
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace PhysicalUnifiedTheory.Experimental

-- Adding a time to a length must fail at elaboration.
#check_failure (fun (distance : Quantity lengthDim) (duration : Quantity timeDim) =>
  distance + duration)

example : speedOfLightSI.siValue = 299792458 := rfl
example : planckConstantSI.siValue = 6.62607015e-34 := rfl
example : luminousEfficacySI.siValue = 683 := rfl
example : gravitationalConstantSI.standardUncertainty.siValue = 0.00015e-11 := rfl

noncomputable def electronvoltUnits : UnitSystem :=
  naturalUnits electronvolt (by norm_num [electronvolt, elementaryChargeSI])

private theorem light_pos : 0 < speedOfLightSI.siValue := by norm_num [speedOfLightSI]
private theorem hbar_pos : 0 < reducedPlanckConstantSI.siValue := by
  have hp := Real.pi_pos
  have hplanck : 0 < planckConstantSI.siValue := by norm_num [planckConstantSI]
  change 0 < planckConstantSI.siValue / (2 * Real.pi)
  positivity

example : UnitSystem.convert electronvoltUnits UnitSystem.si energyDim 1 =
    electronvolt.siValue := by
  have hc := light_pos
  have hh := hbar_pos
  have he : 0 < electronvolt.siValue := by norm_num [electronvolt, elementaryChargeSI]
  simp [UnitSystem.convert, UnitSystem.magnitude, UnitSystem.quantity, UnitSystem.scale,
    UnitSystem.si, electronvoltUnits, naturalUnits, energyDim, baseDimension,
    massDim, lengthDim, timeDim]
  field_simp

example (energy : Quantity energyDim) (he : 0 < energy.siValue) :
    (naturalUnits energy he).magnitude speedOfLightSI = 1 ∧
      (naturalUnits energy he).magnitude reducedPlanckConstantSI = 1 := by
  have hc := light_pos
  have hh := hbar_pos
  constructor <;>
    simp [UnitSystem.magnitude, UnitSystem.scale, naturalUnits, velocityDim, actionDim,
      energyDim, baseDimension, massDim, lengthDim, timeDim] <;> field_simp

example (value : ℝ) :
    UnitSystem.convert electronvoltUnits UnitSystem.si lengthDim
      (UnitSystem.convert UnitSystem.si electronvoltUnits lengthDim value) = value := by
  simp

example : 0 < planckUnits.baseScale .length := planckUnits.baseScale_pos _

end PhysicalUnifiedTheory.Experimental
