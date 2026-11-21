module

public import LPPMonotonicityProof.Analytic.BelowOneTheorem
public import LPPMonotonicityProof.Analytic.AboveTwo
public import LPPMonotonicityProof.Analytic.LowWindowTheorem
public import LPPMonotonicityProof.Analytic.JointFinite
public import LPPMonotonicityProof.Analytic.UpperBands

/-!
# The global derivative-sign cover

This module covers `(0, mean μ)` by Theorems 2.7 (`thm:below-one`), 3.7
(`thm:above-two`), 4.3 (`thm:low-window`), 5.1 (`thm:joint`) and 4.8
(`thm:upper-bands`), as in the final range cover of the proof of Theorem 1.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open LPPMonotonicityProof.Speed

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- **`v' < 0` on `(0, m)`.**  The two lemmas of Appendix A (`CertACovers`, `CertBCovers`)
and the large-finite statement `LargeFiniteStmt` cover every transient positive bias with a strictly
negative speed derivative. -/
theorem deriv_speedValue_neg (h : OffspringHyp μ) (hA : CertACovers)
    (hB : CertBCovers) (hLF : LargeFiniteStmt μ) :
    ∀ l ∈ Set.Ioo 0 (mean μ), deriv (speedValue μ) l < 0 := by
  intro l hl
  by_cases hl1 : l ≤ 1
  · exact deriv_neg_of_le_one h hl.1 hl1
  have hl1' : 1 < l := lt_of_not_ge hl1
  by_cases hhigh : 9 / 5 ≤ l
  · exact deriv_neg_of_ge μ h hhigh hl.2
  have h95 : l ≤ 9 / 5 := (lt_of_not_ge hhigh).le
  by_cases hslow : (l - 1) / pBr μ ≤ 1 / 8
  · exact deriv_neg_low_window h hl1' hl.2 hslow
  by_cases hsmid : (l - 1) / pBr μ ≤ 4
  · exact deriv_neg_joint h hB hl1' hl.2 h95 ⟨(lt_of_not_ge hslow).le, hsmid⟩
  · exact deriv_neg_upper_bands h hA hLF hl1' hl.2 h95 (lt_of_not_ge hsmid).le

end LPPMonotonicityProof.Analytic
