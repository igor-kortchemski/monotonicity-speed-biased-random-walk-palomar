module

public import LPPMonotonicityProof.AssemblyCert
public import LPPMonotonicityProof.Analytic.LargeFinite

/-!
# Theorem 1.1 from the two interval certificates

`speed_monotone_of_two_certificates` proves the conclusion of
`LPPMonotonicity.speed_monotone_of_interval_certificates` (all six clauses, verbatim) from the two
certificate propositions `CertACovers` and `CertBCovers` alone: the third input of
`speed_monotone_of_certificates`, the large-finite step `LargeFiniteStmt`, is
discharged by `large_finite` (`Analytic/LargeFinite.lean`), which derives the positivity
in Lemma A.1 (`lem:large-finite`) from `CertACovers`.

The two certificate propositions are hypotheses here: they state what the interval
verifications of Lemmas A.1 and A.2 check, and the development derives the two lemmas
from them at the actual law. They are proved in a separate companion repository, not in
this one.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LPPMonotonicity
open LPPMonotonicityProof.Speed

namespace LPPMonotonicityProof.Analytic

/-- `large_finite` (Lemma A.1, `lem:large-finite`, from `CertACovers`) gives the
large-finite step for every admissible offspring law. -/
theorem largeFiniteStmt_of_hyp (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h : OffspringHyp μ) : LargeFiniteStmt μ :=
  fun _l hA hl hlm hx ha hw => large_finite h hA hl hlm hx ha hw

/-- **Theorem 1.1** (`thm:main`) from the two interval certificates. -/
theorem speed_monotone_of_two_certificates (hA : CertACovers) (hB : CertBCovers)
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
      HasDerivWithinAt v (-2 * inverseMean μ) (Set.Ici 0) 0 :=
  speed_monotone_of_certificates hA hB (fun μ' _ h => largeFiniteStmt_of_hyp μ' h)
    μ hμ0 hm1 hmfin

end LPPMonotonicityProof.Analytic
