module

public import LPPMonotonicityProof.Speed.Signed.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-! # The two-copy denominator and numerator

The quantities `N` and `Z` of Section 2.2, defined with two independent escapes. -/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The escape law on the real interval. -/
noncomputable def escLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) : Measure ℝ :=
  (bienaymeLaw μ).map (escape l)

/-- The two-copy denominator. -/
def Dfun (l b b' : ℝ) : ℝ := l - 1 + b + b' - b * b'

/-- The two-copy numerator in `N/Z`. -/
noncomputable def Nval (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) : ℝ :=
  ∫ p, p.1 * p.2 / Dfun l p.1 p.2 ∂(escLaw μ l).prod (escLaw μ l)

/-- The two-copy denominator in `N/Z`. -/
noncomputable def Zval (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) : ℝ :=
  ∫ p, (p.1 + p.2 - p.1 * p.2) / Dfun l p.1 p.2 ∂(escLaw μ l).prod (escLaw μ l)

instance (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) :
    IsProbabilityMeasure (escLaw μ l) := by
  unfold escLaw
  infer_instance


end LPPMonotonicityProof.Speed
