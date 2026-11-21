module

public import LPPMonotonicityProof.Analytic.NormalizedDerivative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma A.1: the large-finite region

This module derives the conclusion of Lemma A.1 (`lem:large-finite`) from the retained
lower bound of `NormalizedDerivative.lean` and the hypothesis `CertACovers`, which states
that this lower bound is strictly positive on the whole region. `CertACovers` is
verified in a companion repository; here it is a hypothesis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open LPPMonotonicityProof.Speed

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- **Lemma A.1** (`lem:large-finite`). Under `CertACovers`, the scaled derivative is
strictly positive in the large-finite region. -/
theorem large_finite (h : OffspringHyp μ) (hA : CertACovers) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hx : xS μ l ≤ 1 / 4) (ha : l - 1 ≤ 4 / 5)
    (hw : 4 / 9 < wbar μ l) : 0 < dx μ (Vsc μ) l := by
  have hD := actual_scaledDomain h hl hlm hx ha hw
  have hLB : 0 < scaledLowerBound (xS μ l) (l - 1) (tW μ l) (wbar μ l)
      (fun n => etaW μ l n / wbar μ l) (tailR μ l) (tailT μ l) :=
    hA _ _ _ _ _ _ _ hD
  have hge := normalized_derivative_ge h hl hlm hw
  dsimp only at hge
  have hpos : 0 < 2 * hsc μ l ^ 2 * dx μ (Vsc μ) l / wbar μ l ^ 3 := hLB.trans_le hge
  have hw0 := wbar_pos_f10 h hl hlm
  have hh0 : 0 < hsc μ l :=
    (div_pos (mMom_one_pos_f10 h hl hlm) (by norm_num)).trans_le (hsc_bounds h hl hlm).1
  have hfac : 0 < 2 * hsc μ l ^ 2 / wbar μ l ^ 3 := by positivity
  have hform : 2 * hsc μ l ^ 2 * dx μ (Vsc μ) l / wbar μ l ^ 3 =
      (2 * hsc μ l ^ 2 / wbar μ l ^ 3) * dx μ (Vsc μ) l := by ring
  rw [hform] at hpos
  exact (mul_pos_iff_of_pos_left hfac).mp hpos

/-- The consequence of Lemma A.1 for the speed derivative, through `dx_Vsc`
(`∂ₓV = -s² v'`). -/
theorem deriv_neg_large_finite (h : OffspringHyp μ) (hA : CertACovers) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (hx : xS μ l ≤ 1 / 4) (ha : l - 1 ≤ 4 / 5)
    (hw : 4 / 9 < wbar μ l) : deriv (speedValue μ) l < 0 := by
  have hdx := large_finite h hA hl hlm hx ha hw
  rw [dx_Vsc] at hdx
  have hspos : 0 < sS μ l := div_pos (by linarith) (pBr_pos h)
  change deriv (speedValueProv μ) l < 0
  nlinarith [sq_pos_of_pos hspos]

end LPPMonotonicityProof.Analytic
