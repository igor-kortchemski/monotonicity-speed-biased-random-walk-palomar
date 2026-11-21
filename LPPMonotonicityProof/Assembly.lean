module

public import LPPMonotonicityProof.Analytic.CostExport
public import LPPMonotonicity.Model.Defs

/-!
# Conditional assembly of Theorem 1.1

This module assembles the proved positivity, regularity,
almost-sure speed, and right-endpoint clauses.  Strict decrease and the full
statement of Theorem 1.1 are conditional on the global derivative-sign cover, which
`AssemblyCert.lean` supplies.
No certificate proposition or proof hole is introduced here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LPPMonotonicity
open LPPMonotonicityProof.Speed

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- **Strict decrease, conditional on the sign cover.**  Negative derivative on `(0, m)`
forces the speed to be strictly decreasing on `[0, m)` (the mean value theorem, as at
the end of the proof of Theorem 1.1). -/
theorem strictAntiOn_speedValue_of_deriv_neg (h : OffspringHyp μ)
    (hneg : ∀ l ∈ Set.Ioo 0 (mean μ), deriv (Speed.speedValue μ) l < 0) :
    StrictAntiOn (Speed.speedValue μ) (Set.Ico 0 (mean μ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 (mean μ)) (continuousOn_speedValue h)
  simpa only [interior_Ico] using hneg

/-- The positivity clause (second clause) of Theorem 1.1 as stated in
`LPPMonotonicity.speed_monotone_of_interval_certificates`, for the actual almost-sure
speed. -/
theorem speedValue_pos_pmf (μ' : PMF ℕ) (hμ0 : μ' 0 = 0)
    (hm1 : 1 < offspringMean μ') (hmfin : offspringMean μ' < ∞) :
    ∀ l ∈ Set.Ico 0 (offspringMean μ').toReal, 0 < Speed.speedValue μ'.toMeasure l := by
  rw [← mean_eq μ']
  intro l hl
  rw [speedValue_eq_speedValueProv]
  exact speedValue_pos μ'.toMeasure (offspringHyp_of μ' hμ0 hm1 hmfin) l hl

/-- **Clauses 2--6 of Theorem 1.1, conditional on the sign cover**, as stated in
`LPPMonotonicity.speed_monotone_of_interval_certificates`, for the actual almost-sure
speed. -/
theorem analytic_clauses_of_sign (μ' : PMF ℕ) (hμ0 : μ' 0 = 0)
    (hm1 : 1 < offspringMean μ') (hmfin : offspringMean μ' < ∞)
    (hneg : ∀ l ∈ Set.Ioo 0 (offspringMean μ').toReal,
      deriv (Speed.speedValue μ'.toMeasure) l < 0) :
    let v := Speed.speedValue μ'.toMeasure
    let m := (offspringMean μ').toReal
    (∀ l ∈ Set.Ico (0 : ℝ) m, 0 < v l) ∧
      ContDiffOn ℝ 1 v (Set.Ico 0 m) ∧
      StrictAntiOn v (Set.Ico 0 m) ∧
      (∀ l ∈ Set.Ioo (0 : ℝ) m, deriv v l < 0) ∧
      HasDerivWithinAt v (-2 * inverseMean μ') (Set.Ici 0) 0 := by
  dsimp only
  have hμ : OffspringHyp μ'.toMeasure := offspringHyp_of μ' hμ0 hm1 hmfin
  have hneg' : ∀ l ∈ Set.Ioo 0 (mean μ'.toMeasure),
      deriv (Speed.speedValue μ'.toMeasure) l < 0 := by
    simpa only [mean_eq] using hneg
  have hanti : StrictAntiOn (Speed.speedValue μ'.toMeasure)
      (Set.Ico 0 (offspringMean μ').toReal) := by
    simpa only [mean_eq] using strictAntiOn_speedValue_of_deriv_neg hμ hneg'
  exact ⟨speedValue_pos_pmf μ' hμ0 hm1 hmfin,
    contDiffOn_speedValue_pmf μ' hμ0 hm1 hmfin,
    hanti, hneg,
    hasDerivWithinAt_speedValue_zero_pmf μ' hμ0 hm1 hmfin⟩

/-- Theorem 1.1, conditional only on the global derivative-sign
cover.  Its conclusion is verbatim that of
`LPPMonotonicity.speed_monotone_of_interval_certificates`. -/
theorem speed_monotone_of_sign
    (hsign : ∀ μ' : PMF ℕ, μ' 0 = 0 → 1 < offspringMean μ' → offspringMean μ' < ∞ →
      ∀ l ∈ Set.Ioo 0 (offspringMean μ').toReal,
        deriv (Speed.speedValue μ'.toMeasure) l < 0)
    (μ : PMF ℕ) (hμ0 : μ 0 = 0)
    (hm1 : 1 < offspringMean μ) (hmfin : offspringMean μ < ∞) :
    ∃ v : ℝ → ℝ,
      (∀ l ∈ Set.Ico (0 : ℝ) (offspringMean μ).toReal,
        ∀ᵐ ω ∂treeLaw μ, ∀ᵐ X ∂walkLaw ω l.toNNReal,
          Tendsto (fun n : ℕ => (height (X n) : ℝ) / n) atTop (𝓝 (v l))) ∧
      (∀ l ∈ Set.Ico (0 : ℝ) (offspringMean μ).toReal, 0 < v l) ∧
      ContDiffOn ℝ 1 v (Set.Ico 0 (offspringMean μ).toReal) ∧
      StrictAntiOn v (Set.Ico 0 (offspringMean μ).toReal) ∧
      (∀ l ∈ Set.Ioo (0 : ℝ) (offspringMean μ).toReal, deriv v l < 0) ∧
      HasDerivWithinAt v (-2 * inverseMean μ) (Set.Ici 0) 0 := by
  refine ⟨Speed.speedValue μ.toMeasure, Speed.speed_limit μ hμ0 hm1 hmfin, ?_⟩
  exact analytic_clauses_of_sign μ hμ0 hm1 hmfin (hsign μ hμ0 hm1 hmfin)

/-- The conditional theorem has exactly the input hypotheses and the six-clause
conclusion of `LPPMonotonicity.speed_monotone_of_interval_certificates` once the sign cover
is supplied. -/
example
    (hsign : ∀ μ' : PMF ℕ, μ' 0 = 0 → 1 < offspringMean μ' → offspringMean μ' < ∞ →
      ∀ l ∈ Set.Ioo 0 (offspringMean μ').toReal,
        deriv (Speed.speedValue μ'.toMeasure) l < 0) :
    ∀ (μ : PMF ℕ), μ 0 = 0 → 1 < offspringMean μ → offspringMean μ < ∞ →
      ∃ v : ℝ → ℝ,
        (∀ l ∈ Set.Ico (0 : ℝ) (offspringMean μ).toReal,
          ∀ᵐ ω ∂treeLaw μ, ∀ᵐ X ∂walkLaw ω l.toNNReal,
            Tendsto (fun n : ℕ => (height (X n) : ℝ) / n) atTop (𝓝 (v l))) ∧
        (∀ l ∈ Set.Ico (0 : ℝ) (offspringMean μ).toReal, 0 < v l) ∧
        ContDiffOn ℝ 1 v (Set.Ico 0 (offspringMean μ).toReal) ∧
        StrictAntiOn v (Set.Ico 0 (offspringMean μ).toReal) ∧
        (∀ l ∈ Set.Ioo (0 : ℝ) (offspringMean μ).toReal, deriv v l < 0) ∧
        HasDerivWithinAt v (-2 * inverseMean μ) (Set.Ici 0) 0 :=
  speed_monotone_of_sign hsign

end LPPMonotonicityProof.Analytic
