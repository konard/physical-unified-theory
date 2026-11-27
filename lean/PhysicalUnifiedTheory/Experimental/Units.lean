module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Dimensions and coherent unit systems

A quantity carries the seven SI base-dimension exponents in its type.
[The SI Brochure](https://www.bipm.org/en/publications/si-brochure) defines the
base dimensions and the coherent derived units.
-/

@[expose] public section

noncomputable section

namespace PhysicalUnifiedTheory.Experimental

/-- The seven base dimensions of the SI. -/
inductive BaseDimension
  | length | mass | time | current | temperature | amount | luminousIntensity
  deriving DecidableEq

/-- Integer exponents of the base dimensions. Addition composes dimensions. -/
abbrev Dimension := BaseDimension → ℤ

def baseDimension (b : BaseDimension) : Dimension := fun a => if a = b then 1 else 0

def lengthDim := baseDimension .length
def massDim := baseDimension .mass
def timeDim := baseDimension .time
def currentDim := baseDimension .current
def temperatureDim := baseDimension .temperature
def amountDim := baseDimension .amount
def luminousIntensityDim := baseDimension .luminousIntensity

def velocityDim := lengthDim - timeDim
def energyDim := massDim + lengthDim + lengthDim - timeDim - timeDim
def actionDim := energyDim + timeDim
def gravitationDim := lengthDim + lengthDim + lengthDim - massDim - timeDim - timeDim
def chargeDim := currentDim + timeDim

/-- The magnitude in coherent SI units, with the dimension carried in the type. -/
structure Quantity (d : Dimension) where
  siValue : ℝ

namespace Quantity

instance (d : Dimension) : Add (Quantity d) where
  add x y := ⟨x.siValue + y.siValue⟩

instance (d : Dimension) : Sub (Quantity d) where
  sub x y := ⟨x.siValue - y.siValue⟩

def mul {d e : Dimension} (x : Quantity d) (y : Quantity e) : Quantity (d + e) :=
  ⟨x.siValue * y.siValue⟩

def div {d e : Dimension} (x : Quantity d) (y : Quantity e) : Quantity (d - e) :=
  ⟨x.siValue / y.siValue⟩

def sqrt {d : Dimension} (x : Quantity (d + d)) : Quantity d :=
  ⟨Real.sqrt x.siValue⟩

end Quantity

/-- A coherent multiplicative system gives the SI magnitude of each base unit.
Affine scales such as degrees Celsius require a separate origin. -/
structure UnitSystem where
  baseScale : BaseDimension → ℝ
  baseScale_pos : ∀ b, 0 < baseScale b

namespace UnitSystem

def si : UnitSystem := ⟨fun _ => 1, fun _ => zero_lt_one⟩

def scale (u : UnitSystem) (d : Dimension) : ℝ :=
  u.baseScale .length ^ d .length * u.baseScale .mass ^ d .mass *
  u.baseScale .time ^ d .time * u.baseScale .current ^ d .current *
  u.baseScale .temperature ^ d .temperature * u.baseScale .amount ^ d .amount *
  u.baseScale .luminousIntensity ^ d .luminousIntensity

theorem scale_pos (u : UnitSystem) (d : Dimension) : 0 < u.scale d := by
  unfold scale
  repeat apply mul_pos
  all_goals exact zpow_pos (u.baseScale_pos _) _

@[simp] theorem si_scale (d : Dimension) : si.scale d = 1 := by
  simp [scale, si]

/-- Interpret a number in the given unit system. -/
def quantity (u : UnitSystem) (d : Dimension) (value : ℝ) : Quantity d :=
  ⟨value * u.scale d⟩

/-- Express a quantity numerically in the given unit system. -/
def magnitude (u : UnitSystem) {d : Dimension} (x : Quantity d) : ℝ :=
  x.siValue / u.scale d

@[simp] theorem magnitude_quantity (u : UnitSystem) (d : Dimension) (value : ℝ) :
    u.magnitude (u.quantity d value) = value := by
  exact mul_div_cancel_right₀ value (u.scale_pos d).ne'

@[simp] theorem quantity_magnitude (u : UnitSystem) {d : Dimension} (x : Quantity d) :
    u.quantity d (u.magnitude x) = x := by
  cases x with
  | mk val =>
    change Quantity.mk (val / u.scale d * u.scale d) = Quantity.mk val
    rw [div_mul_cancel₀ _ (u.scale_pos d).ne']

/-- Convert a magnitude while preserving its dimension. -/
def convert (source target : UnitSystem) (d : Dimension) (value : ℝ) : ℝ :=
  target.magnitude (source.quantity d value)

@[simp] theorem convert_trans (source intermediate target : UnitSystem) (d : Dimension)
    (value : ℝ) :
    convert intermediate target d (convert source intermediate d value) =
      convert source target d value := by
  simp [convert]

@[simp] theorem convert_self (u : UnitSystem) (d : Dimension) (value : ℝ) :
    convert u u d value = value := by
  simp [convert]

end UnitSystem

end PhysicalUnifiedTheory.Experimental
