module

public import LPPMonotonicity.Model.Defs
public import LPPMonotonicityProof.Speed.Hyp
public import LPPMonotonicityProof.RTL.LocallyFinite.Law

/-!
# Interface with the public offspring model

This module identifies the PMF-based public model of `LPPMonotonicity/Model/Defs.lean`
with the measure-based RTL conventions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicityProof.RTL.LocallyFinite

@[simp] theorem treeLaw_eq (μ' : PMF ℕ) :
    treeLaw μ' = offspringFieldLaw μ'.toMeasure := rfl

@[simp] theorem offspringMean_eq (μ' : PMF ℕ) :
    offspringMean μ' = ∫⁻ k, (k : ℝ≥0∞) ∂μ'.toMeasure := by
  rw [lintegral_countable']
  simp_rw [μ'.toMeasure_apply_singleton _ (measurableSet_singleton _)]
  rfl

/-- Convert the public hypotheses to the bundled RTL hypotheses. -/
theorem offspringHyp_of (μ' : PMF ℕ) (hμ0 : μ' 0 = 0)
    (hm1 : 1 < offspringMean μ') (hmfin : offspringMean μ' < ⊤) :
    OffspringHyp μ'.toMeasure where
  zero := by
    rw [μ'.toMeasure_apply_singleton _ (measurableSet_singleton _)]
    exact hμ0
  mean_lt_top := by simpa only [← offspringMean_eq] using hmfin
  one_lt_mean := by simpa only [← offspringMean_eq] using hm1

@[simp] theorem mean_eq (μ' : PMF ℕ) :
    mean μ'.toMeasure = (offspringMean μ').toReal := by
  rw [mean, offspringMean_eq]

end LPPMonotonicityProof.Speed
