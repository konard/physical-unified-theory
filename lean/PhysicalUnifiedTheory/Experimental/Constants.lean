module

public import PhysicalUnifiedTheory.Experimental.Units
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Physical constants in SI units

The [BIPM SI Brochure](https://www.bipm.org/en/publications/si-brochure)
supplies the exact defining constants. The
[2022 CODATA table](https://physics.nist.gov/cuu/Constants/Table/allascii.txt)
supplies the measured estimates and standard uncertainties below.
-/

@[expose] public section

noncomputable section

namespace PhysicalUnifiedTheory.Experimental

def speedOfLightSI : Quantity velocityDim := ⟨299792458⟩
def planckConstantSI : Quantity actionDim := ⟨6.62607015e-34⟩
def reducedPlanckConstantSI : Quantity actionDim :=
  ⟨planckConstantSI.siValue / (2 * Real.pi)⟩
def elementaryChargeSI : Quantity chargeDim := ⟨1.602176634e-19⟩
def boltzmannConstantSI : Quantity (energyDim - temperatureDim) := ⟨1.380649e-23⟩
def avogadroConstantSI : Quantity (-amountDim) := ⟨6.02214076e23⟩

/-- Luminous efficacy at the SI defining frequency of 540 THz, in lumens per watt. -/
def luminousEfficacySI : Quantity (luminousIntensityDim - (energyDim - timeDim)) := ⟨683⟩

/-- A published estimate and its standard uncertainty, in the same dimension. -/
structure MeasuredConstant (d : Dimension) where
  estimate : Quantity d
  standardUncertainty : Quantity d
  uncertainty_pos : 0 < standardUncertainty.siValue

def gravitationalConstantSI : MeasuredConstant gravitationDim :=
  ⟨⟨6.67430e-11⟩, ⟨0.00015e-11⟩, by norm_num⟩

def fineStructureConstant : MeasuredConstant 0 :=
  ⟨⟨7.2973525643e-3⟩, ⟨0.0000000011e-3⟩, by norm_num⟩

def electronMass : MeasuredConstant massDim :=
  ⟨⟨9.1093837139e-31⟩, ⟨0.0000000028e-31⟩, by norm_num⟩
def muonMass : MeasuredConstant massDim :=
  ⟨⟨1.883531627e-28⟩, ⟨0.000000042e-28⟩, by norm_num⟩
def tauMass : MeasuredConstant massDim :=
  ⟨⟨3.16754e-27⟩, ⟨0.00021e-27⟩, by norm_num⟩
def protonMass : MeasuredConstant massDim :=
  ⟨⟨1.67262192595e-27⟩, ⟨0.00000000052e-27⟩, by norm_num⟩
def neutronMass : MeasuredConstant massDim :=
  ⟨⟨1.67492750056e-27⟩, ⟨0.00000000085e-27⟩, by norm_num⟩

def weakMixingAngleSquared : MeasuredConstant 0 :=
  ⟨⟨0.22305⟩, ⟨0.00023⟩, by norm_num⟩

/-- Exact conversion factor for an electronvolt, expressed in joules. -/
def electronvolt : Quantity energyDim := ⟨elementaryChargeSI.siValue⟩

/-- CODATA quotes this convention in inverse square GeV with ℏ = c = 1. -/
def fermiCoupling : MeasuredConstant (-(energyDim + energyDim)) :=
  ⟨⟨1.1663787e-5 / (1e9 * electronvolt.siValue)^2⟩,
   ⟨0.0000006e-5 / (1e9 * electronvolt.siValue)^2⟩,
   by norm_num [electronvolt, elementaryChargeSI]⟩

private theorem light_pos : 0 < speedOfLightSI.siValue := by norm_num [speedOfLightSI]
private theorem hbar_pos : 0 < reducedPlanckConstantSI.siValue := by
  have h := Real.pi_pos
  have hh : 0 < planckConstantSI.siValue := by norm_num [planckConstantSI]
  change 0 < planckConstantSI.siValue / (2 * Real.pi)
  positivity
private theorem boltzmann_pos : 0 < boltzmannConstantSI.siValue := by
  norm_num [boltzmannConstantSI]
private theorem charge_pos : 0 < elementaryChargeSI.siValue := by
  norm_num [elementaryChargeSI]
private theorem gravitation_pos : 0 < gravitationalConstantSI.estimate.siValue := by
  norm_num [gravitationalConstantSI]

/-- Natural units parameterized by the energy unit. The other scales set
ℏ, c, k_B and the elementary charge to one. Amount and luminous intensity
retain their SI base units. -/
def naturalUnits (energy : Quantity energyDim) (hEnergy : 0 < energy.siValue) : UnitSystem where
  baseScale
    | .length => reducedPlanckConstantSI.siValue * speedOfLightSI.siValue / energy.siValue
    | .mass => energy.siValue / speedOfLightSI.siValue ^ 2
    | .time => reducedPlanckConstantSI.siValue / energy.siValue
    | .current => elementaryChargeSI.siValue * energy.siValue / reducedPlanckConstantSI.siValue
    | .temperature => energy.siValue / boltzmannConstantSI.siValue
    | .amount | .luminousIntensity => 1
  baseScale_pos b := by
    have hc := light_pos
    have hh := hbar_pos
    have hk := boltzmann_pos
    have he := charge_pos
    cases b <;> dsimp <;> positivity

/-- Planck energy derived using the CODATA central estimate of G. -/
def planckEnergy : Quantity energyDim :=
  ⟨Real.sqrt (reducedPlanckConstantSI.siValue * speedOfLightSI.siValue ^ 5 /
    gravitationalConstantSI.estimate.siValue)⟩

theorem planckEnergy_pos : 0 < planckEnergy.siValue := by
  have hc := light_pos
  have hh := hbar_pos
  have hg := gravitation_pos
  change 0 < Real.sqrt _
  positivity

/-- Planck mechanical and temperature scales. The electrical scale uses
the elementary charge, and the remaining scales follow the SI. -/
def planckUnits : UnitSystem := naturalUnits planckEnergy planckEnergy_pos

/-- Newton's constant has magnitude one in Planck units when its central
estimate sets the unit scales. -/
theorem planckUnits_gravitation : planckUnits.magnitude gravitationalConstantSI.estimate = 1 := by
  have hh := hbar_pos.ne'
  have hc := light_pos.ne'
  have hg := gravitation_pos.ne'
  have he := planckEnergy_pos.ne'
  have hScale : planckUnits.scale gravitationDim =
      reducedPlanckConstantSI.siValue * speedOfLightSI.siValue ^ 5 / planckEnergy.siValue ^ 2 := by
    simp [UnitSystem.scale, planckUnits, naturalUnits, gravitationDim,
      lengthDim, massDim, timeDim, baseDimension]
    field_simp
  have hEnergy : planckEnergy.siValue ^ 2 =
      reducedPlanckConstantSI.siValue * speedOfLightSI.siValue ^ 5 /
        gravitationalConstantSI.estimate.siValue :=
    Real.sq_sqrt (div_nonneg (mul_nonneg hbar_pos.le (pow_nonneg light_pos.le _)) gravitation_pos.le)
  rw [UnitSystem.magnitude, hScale, hEnergy]
  field_simp

end PhysicalUnifiedTheory.Experimental
