module

public import LPPMonotonicityProof.Analytic.AboveTwo
public import LPPMonotonicityProof.Analytic.ScaledTwoChildren
public import LPPMonotonicityProof.Analytic.ScaledMark
public import LPPMonotonicityProof.Analytic.Terminal

/-!
# The three analytic exits

These are the three analytic tests of the proof of Lemma A.2 (`lem:joint-finite`)
that settle a moment box without Ward summation, each giving `v'(λ) < 0`.  The
high-bias and source exits are Theorem 3.7 (`thm:above-two`) and Corollary 3.6
(`cor:ward-source`); the two-child exit `2dη ≥ 1` combines the child-response
recursion of Lemma 4.5 (`lem:scaled-two-children`) with the scaled series and
equation (4.2) (`eq:scaled-mark`) of Lemma 4.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- The two-child exit `2 d η ≥ 1`. -/
theorem exit_M (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (hM : 1 ≤ 2 * dW μ l * etaD μ l) : deriv (speedValue μ) l < 0 := by
  have hd : dW μ l ≠ 0 := (dW_pos h hl hlm).ne'
  have hMtwo : Mtwo μ l = 2 * dW μ l * etaD μ l := by
    unfold Mtwo etaD
    field_simp [hd]
  rw [← hMtwo] at hM
  have hMstar : 1 ≤ Mstar μ l := hM.trans (Mtwo_le_Mstar h hl hlm)
  have hterm (n : ℕ) : 0 ≤ Dcoef μ l (n + 1) *
      dx μ (fun y => mMom μ y (n + 1)) l :=
    mul_nonneg (Dcoef_mem μ h hl hlm (Nat.succ_pos n)).1
      (dx_mn_nonneg h hl hlm hMstar (Nat.succ_pos n))
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

/-- The explicit high-bias exit, exactly Theorem 3.7 (`thm:above-two`). -/
theorem exit_highBias (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (hb : 8 ≤ 24 * peff μ l + 10 * (l - 1)) : deriv (speedValue μ) l < 0 :=
  deriv_neg_above_two μ h hl hlm hb

/-- Admissibility at `θ = 1`, exactly the last clause of Corollary 3.6 (`cor:ward-source`). -/
theorem exit_theta_one (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (h1 : Admissible μ l 1) : deriv (speedValue μ) l < 0 :=
  deriv_neg_of_admissible_one μ h hl hlm h1

end LPPMonotonicityProof.Analytic
