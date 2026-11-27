module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Schwartz functions and tempered distributions

The Schwartz space embeds densely in the `L²` Hilbert space for Lebesgue
measure, which embeds into the continuous dual of the Schwartz space. The
distribution pairing uses the complex bilinear convention.
-/

@[expose] public section

noncomputable section

namespace PhysicalUnifiedTheory.Foundations.Distributions

open MeasureTheory

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

abbrev TestFunctions := SchwartzMap E ℂ
abbrev Wavefunctions := Lp (α := E) ℂ 2 volume
abbrev TemperedDistributions := TemperedDistribution E ℂ

/-- Realize a Schwartz function as a square-integrable wavefunction. -/
def testToWavefunction : TestFunctions E →L[ℂ] Wavefunctions E :=
  SchwartzMap.toLpCLM ℂ ℂ 2 volume

theorem testToWavefunction_injective : Function.Injective (testToWavefunction E) :=
  SchwartzMap.injective_toLp 2 volume

theorem testToWavefunction_dense : DenseRange (testToWavefunction E) :=
  SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top

/-- Realize an `L²` equivalence class as a distribution by integration. -/
def wavefunctionToDistribution : Wavefunctions E →L[ℂ] TemperedDistributions E :=
  Lp.toTemperedDistributionCLM ℂ volume 2

theorem wavefunctionToDistribution_injective :
    Function.Injective (wavefunctionToDistribution E) :=
  LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot

theorem wavefunctionToDistribution_apply (ψ : Wavefunctions E) (f : TestFunctions E) :
    wavefunctionToDistribution E ψ f = ∫ x, f x * ψ x :=
  Lp.toTemperedDistribution_apply ψ f

theorem distribution_of_test (f : TestFunctions E) :
    wavefunctionToDistribution E (testToWavefunction E f) =
      SchwartzMap.toTemperedDistributionCLM E ℂ volume f :=
  Lp.toTemperedDistribution_toLp_eq f

end PhysicalUnifiedTheory.Foundations.Distributions
