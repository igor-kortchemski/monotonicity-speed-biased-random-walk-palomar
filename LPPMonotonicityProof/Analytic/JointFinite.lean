module

public import LPPMonotonicityProof.Analytic.AnalyticExits
public import LPPMonotonicityProof.Analytic.SmallTerminal
public import LPPMonotonicityProof.Analytic.TerminalSpeed
public import LPPMonotonicityProof.Analytic.WardExit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma A.2 and the intermediate range (Theorem 5.1, `thm:joint`)

The interval verification of Lemma A.2 (`lem:joint-finite`) enters as the hypothesis
`CertBCovers`, the closed statement it checks; that statement is not proved in this
repository.  This module derives Lemma A.2 from it: it instantiates `CertBCovers` at
the pushforward law of `1 - W` and turns each of its four exits into `v'(λ) < 0`.
Theorem 5.1 follows, with Corollary 4.6 (`cor:small-terminal`) when `w ≤ 4/9`.  No
certificate computation is assumed beyond the named hypothesis `CertBCovers`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private lemma integral_map_one_sub_Wt (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ X, f X ∂(splitLaw μ).map (fun T => 1 - Wt l T)) =
      ∫ T, f (1 - Wt l T) ∂splitLaw μ := by
  exact integral_map (measurable_const.sub (measurable_Wt l)).aemeasurable
    hf.aestronglyMeasurable

/-- Lemma A.2 (`lem:joint-finite`), assuming `CertBCovers`: every feasible law admitted
by `CertBCovers` has one of the four exits, and each gives `v'(λ) < 0`. -/
theorem joint_finite (h : OffspringHyp μ) (hB : CertBCovers) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ)
    (hx : 1 / 4 ≤ xS μ l ∧ xS μ l ≤ 8) (ha : l - 1 ≤ 4 / 5)
    (hw : 4 / 9 < wbar μ l) : deriv (speedValue μ) l < 0 := by
  letI := splitLaw_prob h
  let ρ : Measure ℝ := (splitLaw μ).map (fun T => 1 - Wt l T)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  have hWi : Integrable (Wt l) (splitLaw μ) := by
    apply Integrable.of_bound (measurable_Wt l).aestronglyMeasurable 1
    filter_upwards with T
    obtain ⟨hW0, hW1⟩ := Wt_mem_Icc' hl T
    simpa [Real.norm_of_nonneg hW0] using hW1
  have hd : dMean ρ = dW μ l := by
    calc
      dMean ρ = ∫ T, (1 - Wt l T) ∂splitLaw μ := by
        unfold dMean
        exact integral_map_one_sub_Wt μ l measurable_id
      _ = 1 - ∫ T, Wt l T ∂splitLaw μ := by
        rw [integral_sub (integrable_const 1) hWi]
        simp
      _ = dW μ l := by simp [dW, wbar, etaW]
  have heta : etaMean ρ = etaD μ l := by
    unfold etaMean etaD
    rw [hd]
    congr 1
    exact integral_map_one_sub_Wt μ l (measurable_id.pow_const 2)
  have hμ : muBox (xS μ l) (dMean ρ) = muY μ l := by
    unfold muBox
    rw [hd]
    exact (muY_eq_box h hl hlm).symm
  have hρmem : ∀ᵐ X ∂ρ, X ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [ρ]
    apply (ae_map_iff (measurable_const.sub (measurable_Wt l)).aemeasurable
      measurableSet_Icc).2
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    exact ⟨sub_nonneg.mpr hT.2.le, by change 1 - Wt l T ≤ 1; linarith [hT.1]⟩
  have hax : (l - 1) * xS μ l ≤ 1 := by
    have hp : pBr μ ≤ 1 := by
      have hpq := p1_add_pBr h
      have hp0 : 0 ≤ p1 μ := measureReal_nonneg
      linarith
    calc
      (l - 1) * xS μ l = pBr μ := by
        unfold xS
        field_simp [(by linarith : l - 1 ≠ 0)]
      _ ≤ 1 := hp
  have hdx : dMean ρ * xS μ l ≤ 1 := by
    rw [hd]
    have hxpos : 0 < xS μ l := xS_pos (μ := μ) h hl
    calc
      dW μ l * xS μ l ≤ sS μ l * xS μ l :=
        mul_le_mul_of_nonneg_right (dW_le h hl hlm).2 hxpos.le
      _ = 1 := by
        unfold sS xS
        field_simp [(pBr_pos h).ne', (by linarith : l - 1 ≠ 0)]
  have hbin : binaryConstraint (xS μ l) (l - 1) (dMean ρ) (etaMean ρ) := by
    unfold binaryConstraint muBox m2Box
    rw [hd, heta]
    have hL : lMoment (xS μ l) (l - 1) 2 = xS μ l * iota μ l 2 := by
      unfold lMoment certIota certQ iota Qgeo
      congr 2
      ring
    rw [hL, ← muY_eq_box h hl hlm, ← momY2_eq_box h hl hlm]
    exact scaled_binary h hl hlm
  have hP (j : ℕ) : rankP (xS μ l) (l - 1) ρ j = PJ μ l j := by
    unfold rankP
    rw [integral_map_one_sub_Wt μ l (by unfold rankPolyP rankQuad; fun_prop)]
    exact (rank_factors_poly μ h hl hlm (r := rr μ l) (θ := 0) j).1.symm
  have hF (θ : ℝ) (j : ℕ) :
      rankF (xS μ l) (l - 1) ρ (rr μ l) θ j = muJ μ l j (fθ l (rr μ l) θ) := by
    unfold rankF
    rw [integral_map_one_sub_Wt μ l (by unfold rankPolyF rankQuad; fun_prop)]
    exact (rank_factors_poly μ h hl hlm j).2.1.symm
  have hG (θ : ℝ) (j : ℕ) :
      rankG (xS μ l) (l - 1) ρ (rr μ l) θ j = muJ μ l j (gθ l (rr μ l) θ) := by
    unfold rankG
    rw [integral_map_one_sub_Wt μ l (by unfold rankPolyG rankQuad; fun_prop)]
    exact (rank_factors_poly μ h hl hlm j).2.2.1.symm
  have hFJ (j : ℕ) : rankFJ (xS μ l) (l - 1) ρ j = FJ μ l j := by
    unfold rankFJ
    rw [integral_map_one_sub_Wt μ l (by unfold rankPolyFJ; fun_prop)]
    exact (rank_factors_poly μ h hl hlm (r := rr μ l) (θ := 0) j).2.2.2.symm
  have hadm_iff (θ : ℝ) :
      thetaAdmissible (xS μ l) (l - 1) ρ (rr μ l) θ ↔ Admissible μ l θ := by
    unfold thetaAdmissible Admissible
    rw [hF θ 0]
    simp only [muJ, pow_zero, one_mul]
  have hfeas : JointFeasible (xS μ l) (l - 1) ρ (rr μ l) := {
    x_ge := hx.1
    x_le := hx.2
    a_pos := by linarith
    a_le := ha
    ax_le := hax
    prob := inferInstance
    support := hρmem
    d_pos := by rw [hd]; exact dW_pos h hl hlm
    d_lt := by rw [hd]; unfold dW; norm_num at hw ⊢; linarith
    d_mul_x_le := hdx
    d_le_eta := by rw [hd, heta]; exact (dW_le_etaD h hl hlm).1
    eta_le := by rw [heta]; exact (dW_le_etaD h hl hlm).2
    binary := hbin
    r_nonneg := (rr_pos μ h hl hlm).le
    r_le_mean := by
      rw [hμ]
      have hc := speed_le_ceiling μ h hl hlm
      have hspeed : speedValue μ l ≤ peff μ l :=
        hc.2.1.trans (hc.2.2.1.trans hc.2.2.2.le)
      calc
        rr μ l = speedValue μ l / (l - 1) := by rw [rr, speedValue_eq_speedValueProv]
        _ ≤ peff μ l / (l - 1) := div_le_div_of_nonneg_right hspeed (by linarith)
        _ = muY μ l / (1 - muY μ l) := by
          unfold peff
          field_simp [(by linarith : l - 1 ≠ 0)]
    r_le_twoPoint := by
      intro d₀ η₀ hd₀ hd₀d hη₀ hη₁
      rw [hd] at hd₀d
      rw [heta] at hη₀
      exact rr_le_twoPoint h hl hlm ⟨hd₀, hd₀d⟩ ⟨hη₀, hη₁⟩
    theta_zero := (hadm_iff 0).2 ⟨by norm_num, by
      have hf := (f0_rank_pos μ h hl hlm 0).le
      simpa only [pow_zero, one_mul] using hf⟩
    P_nonneg := by
      intro j
      rw [hP]
      unfold PJ muJ
      apply integral_nonneg_of_ae
      filter_upwards [ae_escape_mem_Ioo h (by linarith) hlm] with T hT
      have hy := Yt_mem hl hT.1
      have hy1 : Yt l T ≤ 1 := hy.2.le.trans ((div_le_one (by linarith)).mpr hl.le)
      exact mul_nonneg (pow_nonneg (mul_nonneg (kS_pos hl).le hy.1.le) _)
        (mul_nonneg hy.1.le (sub_nonneg.mpr hy1))
    FJ_nonneg := by intro j; rw [hFJ]; exact FJ_nonneg μ h hl hlm j
    F_nonneg := by
      intro θ hθ j
      rw [hF]
      exact muJ_fθ_nonneg μ h hl hlm ((hadm_iff θ).1 hθ) j
    G_persist := by
      intro θ hθ K j hKj hK
      rw [hG]
      exact muJ_gθ_persist μ h hl hlm ((hadm_iff θ).1 hθ) hKj (by rwa [← hG] )
  }
  rcases hB (xS μ l) (l - 1) ρ (rr μ l) hfeas with hM | hb | h1 | hward
  · exact exit_M h hl hlm (by simpa only [hd, heta] using hM)
  · apply exit_highBias h hl hlm
    rw [hμ] at hb
    simpa only [peff] using hb
  · exact exit_theta_one h hl hlm ((hadm_iff 1).1 h1)
  · obtain ⟨θ, hθ, K, Jm, hKJ, hK, hpos⟩ := hward
    apply deriv_neg_of_ward_partial μ h hl hlm ((hadm_iff θ).1 hθ) hKJ
    · rw [← hG θ K]
      exact hK
    · have hsumeq : wardPartialSum (xS μ l) (l - 1) ρ (rr μ l) θ Jm =
          ∑ j ∈ Finset.range (Jm + 1), wardTerm μ l θ j := by
        unfold wardPartialSum wardTerm
        apply Finset.sum_congr rfl
        intro j hj
        rw [hP, hG, hFJ, hF]
      rw [← hsumeq]
      exact hpos

/-- **Theorem 5.1** (`thm:joint`), assuming `CertBCovers`: the intermediate range
`1/8 ≤ s ≤ 4`. -/
theorem deriv_neg_joint (h : OffspringHyp μ) (hB : CertBCovers) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (h95 : l ≤ 9 / 5)
    (hs : 1 / 8 ≤ (l - 1) / pBr μ ∧ (l - 1) / pBr μ ≤ 4) :
    deriv (speedValue μ) l < 0 := by
  by_cases hw : wbar μ l ≤ (4 / 9 : ℝ)
  · exact deriv_neg_of_wbar_le h hl hlm hw
  · apply joint_finite h hB hl hlm ?_ ?_ (lt_of_not_ge hw)
    · have hx_eq : xS μ l = ((l - 1) / pBr μ)⁻¹ := by
        unfold xS
        field_simp [(pBr_pos h).ne', (by linarith : l - 1 ≠ 0)]
      rw [hx_eq]
      have hspos : 0 < (l - 1) / pBr μ :=
        (by norm_num : (0 : ℝ) < 1 / 8).trans_le hs.1
      constructor
      · simpa only [one_div] using one_div_le_one_div_of_le hspos hs.2
      · simpa only [one_div, inv_inv] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 8) hs.1
    · norm_num at h95 ⊢
      linarith

end LPPMonotonicityProof.Analytic
