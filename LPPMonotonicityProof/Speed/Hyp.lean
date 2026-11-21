module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Standing offspring hypotheses

The single home of `OffspringHyp` and `mean`, shared by the interface and the
escape modules.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LPPMonotonicityProof.Speed

/-- Standing offspring hypotheses, using the measure-based RTL convention:
no mass at `0` and mean `1 < m < ∞`. -/
structure OffspringHyp (μ : Measure ℕ) [IsProbabilityMeasure μ] : Prop where
  zero : μ {0} = 0
  mean_lt_top : ∫⁻ k, (k : ℝ≥0∞) ∂μ < ⊤
  one_lt_mean : 1 < ∫⁻ k, (k : ℝ≥0∞) ∂μ

/-- The real-valued offspring mean. -/
noncomputable def mean (μ : Measure ℕ) : ℝ := (∫⁻ k, (k : ℝ≥0∞) ∂μ).toReal

end LPPMonotonicityProof.Speed
