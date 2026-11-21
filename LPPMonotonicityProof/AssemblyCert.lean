module

public import LPPMonotonicityProof.Assembly
public import LPPMonotonicityProof.Analytic.SignCover

/-!
# Theorem 1.1 from the two certificates and the large-finite statement

This module plugs the derivative-sign cover `deriv_speedValue_neg` (the case analysis
in the proof of Theorem 1.1) into the conditional assembly of the six clauses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LPPMonotonicity
open LPPMonotonicityProof.Speed

namespace LPPMonotonicityProof.Analytic

/-- Theorem 1.1, conditional on the two interval certificates and
on the large-finite consequence for every admissible offspring law. -/
theorem speed_monotone_of_certificates (hA : CertACovers) (hB : CertBCovers)
    (hLF : ∀ μ : Measure ℕ, [IsProbabilityMeasure μ] →
      OffspringHyp μ → LargeFiniteStmt μ)
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
  apply speed_monotone_of_sign ?_ μ hμ0 hm1 hmfin
  intro μ' hμ0' hm1' hmfin' l hl
  have h : OffspringHyp μ'.toMeasure := offspringHyp_of μ' hμ0' hm1' hmfin'
  have hl' : l ∈ Set.Ioo 0 (mean μ'.toMeasure) := by
    simpa only [mean_eq] using hl
  exact deriv_speedValue_neg h hA hB (hLF μ'.toMeasure h) l hl'

end LPPMonotonicityProof.Analytic
