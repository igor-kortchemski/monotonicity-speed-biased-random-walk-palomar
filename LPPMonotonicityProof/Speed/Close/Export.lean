module

public import LPPMonotonicityProof.Speed.Close.RestartExport

/-!
# The exported quenched speed clause
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState
open LPPMonotonicityProof.RTL.LocallyFinite

/-- At positive admissible bias, nullity of `Bad` is precisely the pruned-tree
quenched speed statement. -/
theorem ae_pruned_speed_limit (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ) :
    ∀ᵐ T ∂bienaymeLaw μ, ∀ᵐ X ∂walkLaw T.val l.toNNReal,
      Tendsto (fun n : ℕ => (height (X n) : ℝ) / n) atTop (𝓝 (speedValue μ l)) := by
  filter_upwards [ae_bad_null μ hl hμ hlm] with T hT
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hT] with X hX
  exact not_not.mp hX

/-- The positive-bias pruned statement pulled back to raw offspring fields. -/
theorem ae_offspringField_speed_limit (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ) :
    ∀ᵐ ω ∂offspringFieldLaw μ, ∀ᵐ X ∂walkLaw ω l.toNNReal,
      Tendsto (fun n : ℕ => (height (X n) : ℝ) / n) atTop (𝓝 (speedValue μ l)) := by
  have hraw : ∀ᵐ ω ∂offspringFieldLaw μ,
      ∀ᵐ X ∂walkLaw (prune ω).val l.toNNReal,
        Tendsto (fun n : ℕ => (height (X n) : ℝ) / n) atTop (𝓝 (speedValue μ l)) := by
    exact MeasureTheory.ae_of_ae_map measurable_prune.aemeasurable
      (ae_pruned_speed_limit μ hμ hl hlm)
  filter_upwards [hraw] with ω hω
  rw [walkLaw_prune ω l.toNNReal]
  exact hω

/-- **Almost-sure speed.**  The first clause of
`LPPMonotonicity.speed_monotone_of_interval_certificates` (the almost-sure limit in
Theorem 2.2, and `v(0) = 1`), with its speed chosen to be `speedValue μ'.toMeasure`. -/
theorem speed_limit (μ' : PMF ℕ) (hμ0 : μ' 0 = 0)
    (hm1 : 1 < offspringMean μ') (hmfin : offspringMean μ' < ∞) :
    ∀ l ∈ Set.Ico (0 : ℝ) (offspringMean μ').toReal,
      ∀ᵐ ω ∂treeLaw μ', ∀ᵐ X ∂walkLaw ω l.toNNReal,
        Tendsto (fun n : ℕ => (height (X n) : ℝ) / n) atTop
          (𝓝 (speedValue μ'.toMeasure l)) := by
  have hμ : OffspringHyp μ'.toMeasure := offspringHyp_of μ' hμ0 hm1 hmfin
  intro l hl
  by_cases hl0 : l = 0
  · subst l
    simpa using ae_treeWalk_zero_bias_speed μ' hμ0
  have hlpos : 0 < l := lt_of_le_of_ne hl.1 (Ne.symm hl0)
  have hlm : l < mean μ'.toMeasure := by simpa only [mean_eq] using hl.2
  rw [treeLaw_eq]
  exact ae_offspringField_speed_limit μ'.toMeasure hμ hlpos hlm

end LPPMonotonicityProof.Speed
