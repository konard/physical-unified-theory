module

import PhysicalUnifiedTheory.Foundations.MeasureTheory
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

open PhysicalUnifiedTheory.Foundations.MeasureTheory
open Matrix
open scoped ComplexOrder

-- Positive diagonal entries and trace one cannot certify this matrix as a state.
example (ρ : DensityMatrix 2) : ρ.mat ≠ !![(1 / 2 : ℂ), 1; 1, 1 / 2] := by
  intro h
  have hPositive := ρ.posSemidef
  rw [h] at hPositive
  have hNegativeDirection := hPositive.dotProduct_mulVec_nonneg ![1, -1]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.nonneg_iff] at hNegativeDirection
