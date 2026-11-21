module

public import LPPMonotonicityProof.Analytic.ScaledTwoChildren
public import LPPMonotonicityProof.Analytic.ScaledMark
public import LPPMonotonicityProof.Analytic.Terminal

/-!
# The small-terminal condition

This module proves Corollary 4.6 (`cor:small-terminal`) for the speed
`Speed.speedValue`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- Corollary 4.6 (`cor:small-terminal`): a terminal mean `w` at most `4/9` gives
`v' < 0`. -/
theorem deriv_neg_of_wbar_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hw : wbar μ l ≤ (4 / 9 : ℝ)) : deriv (speedValue μ) l < 0 := by
  have hM_ge := Mstar_ge μ h hl hlm
  have hM : 1 ≤ Mstar μ l := by nlinarith
  have hterm (n : ℕ) : 0 ≤ Dcoef μ l (n + 1) *
      dx μ (fun y => mMom μ y (n + 1)) l :=
    mul_nonneg (Dcoef_mem μ h hl hlm (Nat.succ_pos n)).1
      (dx_mn_nonneg h hl hlm hM (Nat.succ_pos n))
  have hsum : 0 ≤ ∑' n : ℕ, Dcoef μ l (n + 1) *
      dx μ (fun y => mMom μ y (n + 1)) l := tsum_nonneg hterm
  obtain ⟨-, hmark⟩ := scaled_mark μ h hl hlm
  have hV : 0 < Vsc μ l :=
    div_pos (speedValue_pos μ h l ⟨(by linarith : 0 ≤ l), hlm⟩) (pBr_pos h)
  obtain ⟨hgap_lower, hS⟩ := S_sub_gamT μ h hl hlm
  have hleft : 0 < (l - 1) * Ssc μ l / (2 * l) := by positivity
  have hgap : 0 < Ssc μ l - gamS l * Tsc μ l := hleft.trans_le hgap_lower
  have hH : 0 < hsc μ l :=
    (half_pos (mMom_one_pos_f10 h hl hlm)).trans_le (hsc_bounds (μ := μ) h hl hlm).1
  have hHdx : 0 < hsc μ l * dx μ (Vsc μ) l := by
    rw [hmark]
    exact add_pos_of_pos_of_nonneg (mul_pos hV hgap) hsum
  have hdxV : 0 < dx μ (Vsc μ) l := by
    by_contra hn
    have hn' : dx μ (Vsc μ) l ≤ 0 := le_of_not_gt hn
    have := mul_nonpos_of_nonneg_of_nonpos hH.le hn'
    linarith
  rw [dx_Vsc] at hdxV
  have hs : 0 < sS μ l := div_pos (by linarith) (pBr_pos h)
  have hder : deriv (speedValueProv μ) l < 0 := by nlinarith [sq_pos_of_pos hs]
  change deriv (speedValueProv μ) l < 0
  exact hder

/-- Corollary 4.6 (`cor:small-terminal`): the sufficient condition
`(m - λ) E J ≤ (4/5) m (λ - 1)` on the mean split degree. -/
theorem deriv_neg_of_meanJ (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ)
    (hc : (mean μ - l) * meanJ μ ≤ (4 / 5 : ℝ) * mean μ * (l - 1)) :
    deriv (speedValue μ) l < 0 :=
  deriv_neg_of_wbar_le h hl hlm (wbar_le_of_meanJ h hl hlm hc)

end LPPMonotonicityProof.Analytic
