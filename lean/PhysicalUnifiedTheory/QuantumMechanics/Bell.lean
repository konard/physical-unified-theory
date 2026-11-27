module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The CHSH Bell inequality

Local responses take values in `{-1, 1}` and use a common distribution of the
hidden variable that is independent of the settings. The quantum model uses
the real amplitudes of the Bell state `(|00⟩ + |11⟩) / √2` and measurements in
the plane spanned by the Pauli X and Z observables.
-/

@[expose] public section

noncomputable section

namespace PhysicalUnifiedTheory.QuantumMechanics.Bell

def response (outcome : Bool) : ℝ := if outcome then 1 else -1

def localScore (a₀ a₁ b₀ b₁ : Bool) : ℝ :=
  response a₀ * (response b₀ + response b₁) +
    response a₁ * (response b₀ - response b₁)

theorem abs_localScore (a₀ a₁ b₀ b₁ : Bool) : |localScore a₀ a₁ b₀ b₁| = 2 := by
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> norm_num [localScore, response]

/-- The CHSH bound for a finite local hidden-variable distribution. -/
theorem localBound {Λ : Type*} [Fintype Λ] (weight : Λ → ℝ)
    (nonnegative : ∀ state, 0 ≤ weight state) (total : ∑ state, weight state = 1)
    (a₀ a₁ b₀ b₁ : Λ → Bool) :
    |∑ state, weight state * localScore (a₀ state) (a₁ state) (b₀ state) (b₁ state)| ≤ 2 := by
  calc
    _ ≤ ∑ state, |weight state * localScore (a₀ state) (a₁ state) (b₀ state) (b₁ state)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = 2 := by
      simp [abs_mul, abs_of_nonneg, nonnegative, abs_localScore, ← Finset.sum_mul, total]

/-- Coordinates of the Bell state in the computational product basis. -/
def bellAmplitude (i j : Fin 2) : ℝ := if i = j then 1 / Real.sqrt 2 else 0

/-- Matrix for the observable `z Z + x X`. A unit vector in this plane gives outcomes ±1. -/
def analyzer (z x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![z, x; x, -z]

theorem analyzer_symmetric (z x : ℝ) : (analyzer z x).transpose = analyzer z x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [analyzer]

theorem analyzer_sq (z x : ℝ) (h : z ^ 2 + x ^ 2 = 1) :
    analyzer z x * analyzer z x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [analyzer, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

/-- Expectation of the tensor product of two observables in the Bell state. -/
def correlation (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, bellAmplitude i j * A i k * B j l * bellAmplitude k l

private theorem amplitude_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem bellAmplitude_normalized : ∑ i, ∑ j, bellAmplitude i j ^ 2 = 1 := by
  norm_num [Fin.sum_univ_two, bellAmplitude, amplitude_sq]

theorem correlation_analyzers (az ax bz bx : ℝ) :
    correlation (analyzer az ax) (analyzer bz bx) = az * bz + ax * bx := by
  calc
    _ = (az * bz + ax * bx) * (2 * (1 / Real.sqrt 2) ^ 2) := by
      conv_lhs => simp [correlation, analyzer, bellAmplitude, Fin.sum_univ_two]
      ring
    _ = _ := by rw [amplitude_sq]; ring

/-- The CHSH score for Z and X measured against `(Z + X)/√2` and `(Z - X)/√2`. -/
def quantumScore : ℝ :=
  let z := analyzer 1 0
  let x := analyzer 0 1
  let plus := analyzer (1 / Real.sqrt 2) (1 / Real.sqrt 2)
  let minus := analyzer (1 / Real.sqrt 2) (-1 / Real.sqrt 2)
  correlation z plus + correlation z minus + correlation x plus - correlation x minus

theorem quantumScore_eq : quantumScore = 2 * Real.sqrt 2 := by
  have h : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp [quantumScore, correlation_analyzers]
  field_simp
  nlinarith

theorem quantumScore_violates_localBound : 2 < quantumScore := by
  rw [quantumScore_eq]
  linarith [Real.one_lt_sqrt_two]

theorem quantumScore_noLocalModel {Λ : Type*} [Fintype Λ] (weight : Λ → ℝ)
    (nonnegative : ∀ state, 0 ≤ weight state) (total : ∑ state, weight state = 1)
    (a₀ a₁ b₀ b₁ : Λ → Bool) :
    (∑ state, weight state * localScore (a₀ state) (a₁ state) (b₀ state) (b₁ state)) ≠
      quantumScore := by
  intro eq
  have bound := localBound weight nonnegative total a₀ a₁ b₀ b₁
  rw [eq] at bound
  exact (not_le_of_gt quantumScore_violates_localBound) ((le_abs_self _).trans bound)

end PhysicalUnifiedTheory.QuantumMechanics.Bell
