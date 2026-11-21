module

public import LPPMonotonicity.Model.Defs
public import LPPMonotonicityProof.AssemblyFinal

/-!
# Theorem 1.1 from the interval verifications of Appendix A

`speed_monotone_of_interval_certificates` is Theorem 1.1 (`thm:main`), with the positivity
of the speed, assuming the closed propositions `CertACovers` and `CertBCovers` that
the interval verifications of Lemmas A.1 and A.2 check. Its proof is
`speed_monotone_of_two_certificates` (`LPPMonotonicityProof/AssemblyFinal.lean`),
which derives the two lemmas from these propositions at the actual law. The two
propositions are not proved in this repository.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LPPMonotonicity

/-- **Theorem 1.1** (`thm:main`) assuming the interval verifications of Appendix A,
together with the positivity of the speed. `CertACovers` and `CertBCovers` are closed
statements about real numbers and laws on `ℝ`: what the verifications of Lemma A.1
(`lem:large-finite`) and Lemma A.2 (`lem:joint-finite`) check, for all feasible data.
The proof derives the two lemmas from them at the actual law. For an offspring law
with no mass at `0` and mean `1 < m < ∞`, there is a function `v` such that: for every
`λ ∈ [0, m)`, for almost every tree and almost every path of the `λ`-biased walk,
`|X_n|/n → v(λ)` (the null sets may depend on `λ`; `|X_n|` is `height (X n)`, whose
value `-1` at `rootParent` does not affect the limit); `v(λ) > 0`; `v` is `C¹` on
`[0, m)` and strictly decreasing there, with `v'(λ) < 0` for `0 < λ < m` and right
derivative `v'₊(0) = -2 E[1/ν]`. -/
theorem speed_monotone_of_interval_certificates
    (hA : LPPMonotonicityProof.Analytic.CertACovers)
    (hB : LPPMonotonicityProof.Analytic.CertBCovers)
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
  LPPMonotonicityProof.Analytic.speed_monotone_of_two_certificates hA hB μ hμ0 hm1 hmfin

end LPPMonotonicity
