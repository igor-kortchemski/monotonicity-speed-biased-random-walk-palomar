module

public import LPPMonotonicityProof.Analytic.SmallTerminal
public import LPPMonotonicityProof.Analytic.Certificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The upper scaled-bias bands

This module proves Theorem 4.8 (`thm:upper-bands`) from Corollary 4.6
(`cor:small-terminal`), the large-finite statement of Lemma A.1, and the scaled
derivative identity `∂ₓV = -s² v'`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open LPPMonotonicityProof.Speed

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- The consequence of Lemma A.1 (`lem:large-finite`) needed by Theorem 4.8. It is
stated here as a proposition and proved from `CertACovers` by `large_finite`
(`Analytic/LargeFinite.lean`). -/
def LargeFiniteStmt (μ : Measure ℕ) [IsProbabilityMeasure μ] : Prop :=
  ∀ l, CertACovers → 1 < l → l < mean μ → xS μ l ≤ 1 / 4 →
    l - 1 ≤ 4 / 5 → 4 / 9 < wbar μ l → 0 < dx μ (Vsc μ) l

/-- **Theorem 4.8** (`thm:upper-bands`).  In the upper scaled-bias bands, either
the terminal mean `w` is at most `4/9`, or Lemma A.1 gives the required positivity. -/
theorem deriv_neg_upper_bands (h : OffspringHyp μ) (hA : CertACovers)
    (hLF : LargeFiniteStmt μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (h95 : l ≤ 9 / 5) (hs : 4 ≤ (l - 1) / pBr μ) :
    deriv (speedValue μ) l < 0 := by
  by_cases hw : wbar μ l ≤ (4 / 9 : ℝ)
  · exact deriv_neg_of_wbar_le h hl hlm hw
  · have hx_eq : xS μ l = ((l - 1) / pBr μ)⁻¹ := by
      unfold xS
      field_simp [(pBr_pos h).ne', (by linarith : l - 1 ≠ 0)]
    have hx : xS μ l ≤ 1 / 4 := by
      rw [hx_eq]
      simpa only [one_div] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hs
    have ha : l - 1 ≤ 4 / 5 := by
      norm_num at h95 ⊢
      linarith
    have hdxV : 0 < dx μ (Vsc μ) l :=
      hLF l hA hl hlm hx ha (lt_of_not_ge hw)
    rw [dx_Vsc] at hdxV
    have hspos : 0 < sS μ l := div_pos (by linarith) (pBr_pos h)
    have hder : deriv (speedValueProv μ) l < 0 := by
      nlinarith [sq_pos_of_pos hspos]
    change deriv (speedValueProv μ) l < 0
    exact hder

end LPPMonotonicityProof.Analytic
