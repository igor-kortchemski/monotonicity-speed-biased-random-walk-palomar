module

public import LPPMonotonicityProof.Analytic.WardRanks2
public import LPPMonotonicityProof.Analytic.Certificates
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Ward finite-rank criterion

This module proves the finite-rank box criterion in the proof of Theorem 5.1
(`thm:joint`): a strictly positive partial sum of the rank expansion of
Proposition 5.2 (`prop:ward-ranks`) forces `v' < 0`. The statement of Lemma A.2
(`CertBCovers`) uses the four explicit polynomials `rankPoly*` of
`LPPMonotonicity/Model/Defs.lean`; the identities below prove that they are exactly
the averaged rank factors.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

private lemma PJ_nonneg_exit (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) : 0 ≤ PJ μ l j := by
  unfold PJ muJ
  apply integral_nonneg_of_ae
  filter_upwards [ae_escape_mem_Ioo h (by linarith) hlm] with T hb
  have hy := Yt_mem hl hb.1
  have hy1 : Yt l T ≤ 1 := hy.2.le.trans ((div_le_one (by linarith)).mpr hl.le)
  exact mul_nonneg (pow_nonneg (mul_nonneg (kS_pos hl).le hy.1.le) _)
    (mul_nonneg hy.1.le (sub_nonneg.mpr hy1))

/-- **Finite-rank criterion: a positive initial Ward sum forces the speed derivative
to be negative.** -/
theorem deriv_neg_of_ward_partial (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {θ : ℝ} (hθ : Admissible μ l θ) {K Jm : ℕ} (hKJ : K ≤ Jm)
    (hK : 0 ≤ muJ μ l K (gθ l (rr μ l) θ))
    (hpos : 0 < ∑ j ∈ Finset.range (Jm + 1), wardTerm μ l θ j) :
    deriv (speedValue μ) l < 0 := by
  obtain ⟨hsum, hbound⟩ := ward_ranks μ h hl hlm hθ
  have htail : 0 ≤ ∑' i : ℕ, wardTerm μ l θ (i + (Jm + 1)) := by
    apply tsum_nonneg
    intro i
    have hg : 0 ≤ muJ μ l (i + (Jm + 1)) (gθ l (rr μ l) θ) :=
      muJ_gθ_persist μ h hl hlm hθ (by omega) hK
    have hf := muJ_fθ_nonneg μ h hl hlm hθ (i + (Jm + 1))
    have hF := FJ_nonneg μ h hl hlm (i + (Jm + 1))
    have hP := PJ_nonneg_exit μ h hl hlm (i + (Jm + 1))
    dsimp [wardTerm]
    positivity
  have hpartial : (∑ j ∈ Finset.range (Jm + 1), wardTerm μ l θ j) ≤
      ∑' j, wardTerm μ l θ j := by
    rw [← hsum.sum_add_tsum_nat_add (Jm + 1)]
    exact le_add_of_nonneg_right htail
  have hcost : 0 < cost μ l := hpos.trans_le (hpartial.trans hbound)
  change 0 < -l * Zval μ l * deriv (speedValue μ) l at hcost
  exact neg_of_mul_pos_right hcost
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by linarith : 0 ≤ l))
      (Speed.Zval_pos μ (by linarith) h hlm).le)

/-- **A quadratic lower bound integrates against the first two moments.** -/
theorem quadratic_minorant {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐ X ∂ρ, X ∈ Set.Icc 0 1)
    {P : ℝ → ℝ} {c₀ c₁ c₂ : ℝ}
    (hP : ∀ u ∈ Set.Icc 0 1, c₀ + c₁ * u + c₂ * u ^ 2 ≤ P u)
    (hPi : Integrable P ρ) :
    c₀ + c₁ * ∫ X, X ∂ρ + c₂ * ∫ X, X ^ 2 ∂ρ ≤ ∫ X, P X ∂ρ := by
  have hXi : Integrable (fun X : ℝ => X) ρ := by
    apply Integrable.of_bound measurable_id.aestronglyMeasurable 1
    filter_upwards [hρ] with X hX
    simpa [Real.norm_of_nonneg hX.1] using hX.2
  have hX2i : Integrable (fun X : ℝ => X ^ 2) ρ := by
    apply Integrable.of_bound (measurable_id.pow_const 2).aestronglyMeasurable 1
    filter_upwards [hρ] with X hX
    change ‖X ^ 2‖ ≤ 1
    rw [Real.norm_of_nonneg (sq_nonneg X)]
    exact pow_le_one₀ hX.1 hX.2
  have hlow : Integrable (fun X : ℝ => c₀ + c₁ * X + c₂ * X ^ 2) ρ :=
    ((integrable_const c₀).add (hXi.const_mul c₁)).add (hX2i.const_mul c₂)
  calc
    c₀ + c₁ * ∫ X, X ∂ρ + c₂ * ∫ X, X ^ 2 ∂ρ =
        ∫ X, (c₀ + c₁ * X + c₂ * X ^ 2) ∂ρ := by
      symm
      calc
        (∫ X, (c₀ + c₁ * X + c₂ * X ^ 2) ∂ρ) =
            (∫ X, c₀ + c₁ * X ∂ρ) + ∫ X, c₂ * X ^ 2 ∂ρ :=
          integral_add ((integrable_const c₀).add (hXi.const_mul c₁)) (hX2i.const_mul c₂)
        _ = ((∫ _X : ℝ, c₀ ∂ρ) + ∫ X, c₁ * X ∂ρ) + ∫ X, c₂ * X ^ 2 ∂ρ := by
          congr 1
          exact integral_add (integrable_const c₀) (hXi.const_mul c₁)
        _ = _ := by
          rw [integral_const_mul, integral_const_mul]
          simp
    _ ≤ ∫ X, P X ∂ρ := by
      apply integral_mono_ae hlow hPi
      filter_upwards [hρ] with X hX
      exact hP X hX

/-- **Both quadratic profiles are antitone in the speed ratio.** -/
theorem fθ_gθ_antitone_r {l θ y : ℝ} (hl : 1 < l) (hy : y ∈ Set.Icc 0 (1 / l)) :
    Antitone (fun r => fθ l r θ y) ∧ Antitone (fun r => gθ l r θ y) := by
  have hl0 : 0 < l := by linarith
  have hly : l * y ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hy.2 hl0.le
    have hid : l * (1 / l) = 1 := by field_simp [hl0.ne']
    exact hh.trans_eq hid
  have hy1 : y ≤ 1 := hy.2.trans ((div_le_one hl0).mpr hl.le)
  have hA : 0 ≤ (1 - y) * (1 - l * y) :=
    mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hly)
  have hB : 0 ≤ l * (1 - y) * (2 - (1 + l) * y) := by
    have hq : 0 ≤ 2 - (1 + l) * y := by nlinarith
    positivity
  constructor <;> intro r s hrs
  · have hn := mul_nonneg (sub_nonneg.mpr hrs) hA
    unfold fθ
    nlinarith
  · have hn := mul_nonneg (sub_nonneg.mpr hrs) hB
    unfold gθ
    nlinarith

private lemma integrable_Y_pow_exit (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : Integrable (fun T => Yt l T ^ n) (GW μ) := by
  apply Integrable.of_bound ((measurable_Yt l).pow_const n).aestronglyMeasurable 1
  filter_upwards [ae_escape_mem_Ioo h (by linarith) hlm] with T hb
  have hy := Yt_mem hl hb.1
  have hy1 : Yt l T ≤ 1 := hy.2.le.trans ((div_le_one (by linarith)).mpr hl.le)
  rw [Real.norm_of_nonneg (pow_nonneg hy.1.le _)]
  exact pow_le_one₀ hy.1.le hy1

private lemma integrable_W_pow_exit (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : Integrable (fun T => Wt l T ^ n) (splitLaw μ) := by
  letI := splitLaw_prob h
  apply Integrable.of_bound ((measurable_Wt l).pow_const n).aestronglyMeasurable 1
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  rw [Real.norm_of_nonneg (pow_nonneg hT.1.le _)]
  exact pow_le_one₀ hT.1.le hT.2.le

private lemma cert_lMoment_eq (l : ℝ) (n : ℕ) :
    lMoment (xS μ l) (l - 1) n = xS μ l * iota μ l n := by
  unfold lMoment certIota certQ iota Qgeo
  congr 2
  ring

private lemma muJ_quad_eq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) (c₀ c₁ c₂ : ℝ) :
    (∫ T, (kS l * Yt l T) ^ j * (c₀ + c₁ * Yt l T + c₂ * Yt l T ^ 2) ∂GW μ) =
      ∫ T, rankQuad (xS μ l) (l - 1) j c₀ c₁ c₂ (1 - Wt l T) ∂splitLaw μ := by
  letI := splitLaw_prob h
  have hY0 := integrable_Y_pow_exit μ h hl hlm j
  have hY1 := integrable_Y_pow_exit μ h hl hlm (j + 1)
  have hY2 := integrable_Y_pow_exit μ h hl hlm (j + 2)
  have hW0 := integrable_W_pow_exit μ h hl hlm j
  have hW1 := integrable_W_pow_exit μ h hl hlm (j + 1)
  have hW2 := integrable_W_pow_exit μ h hl hlm (j + 2)
  have hk : certK (l - 1) = kS l := by unfold certK kS; congr 1; ring
  have hleft : (fun T => (kS l * Yt l T) ^ j *
      (c₀ + c₁ * Yt l T + c₂ * Yt l T ^ 2)) =
      (fun T => (kS l ^ j * c₀) * Yt l T ^ j +
        (kS l ^ j * c₁) * Yt l T ^ (j + 1) +
        (kS l ^ j * c₂) * Yt l T ^ (j + 2)) := by
    funext T
    rw [mul_pow, pow_add, pow_add]
    ring
  have hAdd : (∫ T, (kS l ^ j * c₀) * Yt l T ^ j +
      (kS l ^ j * c₁) * Yt l T ^ (j + 1) + (kS l ^ j * c₂) * Yt l T ^ (j + 2) ∂GW μ) =
      ((∫ T, (kS l ^ j * c₀) * Yt l T ^ j ∂GW μ) +
        (∫ T, (kS l ^ j * c₁) * Yt l T ^ (j + 1) ∂GW μ)) +
        ∫ T, (kS l ^ j * c₂) * Yt l T ^ (j + 2) ∂GW μ := by
    calc
      (∫ T, (kS l ^ j * c₀) * Yt l T ^ j + (kS l ^ j * c₁) * Yt l T ^ (j + 1) +
          (kS l ^ j * c₂) * Yt l T ^ (j + 2) ∂GW μ) =
        (∫ T, (kS l ^ j * c₀) * Yt l T ^ j + (kS l ^ j * c₁) * Yt l T ^ (j + 1)
          ∂GW μ) + ∫ T, (kS l ^ j * c₂) * Yt l T ^ (j + 2) ∂GW μ :=
        integral_add ((hY0.const_mul _).add (hY1.const_mul _)) (hY2.const_mul _)
      _ = _ := by
        congr 1
        exact integral_add (hY0.const_mul _) (hY1.const_mul _)
  rw [hleft, hAdd, integral_const_mul, integral_const_mul, integral_const_mul]
  change kS l ^ j * c₀ * momY μ l j + kS l ^ j * c₁ * momY μ l (j + 1) +
      kS l ^ j * c₂ * momY μ l (j + 2) = _
  rw [momY_eq h hl hlm j, momY_eq h hl hlm (j + 1), momY_eq h hl hlm (j + 2)]
  unfold rankQuad
  rw [hk, cert_lMoment_eq μ, cert_lMoment_eq μ, cert_lMoment_eq μ]
  simp only [sub_sub_cancel]
  unfold etaW
  have hrw (T : Tree) : c₀ * Wt l T ^ j * (xS μ l * iota μ l j) +
      c₁ * Wt l T ^ (j + 1) * (xS μ l * iota μ l (j + 1)) +
      c₂ * Wt l T ^ (j + 2) * (xS μ l * iota μ l (j + 2)) =
      (c₀ * (xS μ l * iota μ l j)) * Wt l T ^ j +
        (c₁ * (xS μ l * iota μ l (j + 1))) * Wt l T ^ (j + 1) +
        (c₂ * (xS μ l * iota μ l (j + 2))) * Wt l T ^ (j + 2) := by ring
  simp_rw [hrw]
  have hAdd : (∫ T, (c₀ * (xS μ l * iota μ l j)) * Wt l T ^ j +
      (c₁ * (xS μ l * iota μ l (j + 1))) * Wt l T ^ (j + 1) +
      (c₂ * (xS μ l * iota μ l (j + 2))) * Wt l T ^ (j + 2) ∂splitLaw μ) =
      ((∫ T, (c₀ * (xS μ l * iota μ l j)) * Wt l T ^ j ∂splitLaw μ) +
        (∫ T, (c₁ * (xS μ l * iota μ l (j + 1))) * Wt l T ^ (j + 1) ∂splitLaw μ)) +
        ∫ T, (c₂ * (xS μ l * iota μ l (j + 2))) * Wt l T ^ (j + 2) ∂splitLaw μ := by
    calc
      (∫ T, (c₀ * (xS μ l * iota μ l j)) * Wt l T ^ j +
          (c₁ * (xS μ l * iota μ l (j + 1))) * Wt l T ^ (j + 1) +
          (c₂ * (xS μ l * iota μ l (j + 2))) * Wt l T ^ (j + 2) ∂splitLaw μ) =
        (∫ T, (c₀ * (xS μ l * iota μ l j)) * Wt l T ^ j +
          (c₁ * (xS μ l * iota μ l (j + 1))) * Wt l T ^ (j + 1) ∂splitLaw μ) +
          ∫ T, (c₂ * (xS μ l * iota μ l (j + 2))) * Wt l T ^ (j + 2) ∂splitLaw μ :=
        integral_add ((hW0.const_mul _).add (hW1.const_mul _)) (hW2.const_mul _)
      _ = _ := by
        congr 1
        exact integral_add (hW0.const_mul _) (hW1.const_mul _)
  have hAddC := congrArg (fun z : ℝ => kS l ^ j * z) hAdd
  rw [integral_const_mul, hAddC, integral_const_mul, integral_const_mul, integral_const_mul]
  ring

/-- **The four polynomials `rankPoly*` are the exact rank factors.** -/
theorem rank_factors_poly (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {r θ : ℝ} (j : ℕ) :
    PJ μ l j = ∫ T, rankPolyP (xS μ l) (l - 1) j (1 - Wt l T) ∂splitLaw μ ∧
    muJ μ l j (fθ l r θ) = ∫ T, rankPolyF (xS μ l) (l - 1) r θ j (1 - Wt l T) ∂splitLaw μ ∧
    muJ μ l j (gθ l r θ) = ∫ T, rankPolyG (xS μ l) (l - 1) r θ j (1 - Wt l T) ∂splitLaw μ ∧
    FJ μ l j = ∫ T, rankPolyFJ (xS μ l) (l - 1) j (1 - Wt l T) ∂splitLaw μ := by
  have hP : PJ μ l j = ∫ T, rankPolyP (xS μ l) (l - 1) j (1 - Wt l T) ∂splitLaw μ := by
    unfold PJ muJ rankPolyP
    convert muJ_quad_eq μ h hl hlm j 0 1 (-1) using 1 <;> ring
  have hF : muJ μ l j (fθ l r θ) =
      ∫ T, rankPolyF (xS μ l) (l - 1) r θ j (1 - Wt l T) ∂splitLaw μ := by
    unfold muJ rankPolyF
    have hq := muJ_quad_eq μ h hl hlm j (-r) (1 + r * (2 + (l - 1)))
      (-θ - r * (1 + (l - 1)))
    calc
      (∫ T, (kS l * Yt l T) ^ j * fθ l r θ (Yt l T) ∂GW μ) =
          ∫ T, (kS l * Yt l T) ^ j *
            (-r + (1 + r * (2 + (l - 1))) * Yt l T +
              (-θ - r * (1 + (l - 1))) * Yt l T ^ 2) ∂GW μ := by
        apply integral_congr_ae
        filter_upwards with T
        unfold fθ
        ring
      _ = _ := hq
  have hG : muJ μ l j (gθ l r θ) =
      ∫ T, rankPolyG (xS μ l) (l - 1) r θ j (1 - Wt l T) ∂splitLaw μ := by
    unfold muJ rankPolyG
    have hq := muJ_quad_eq μ h hl hlm j (-2 * (1 + (l - 1)) * r)
      ((1 + (l - 1)) + 2 * θ + (1 + (l - 1)) * r * (4 + (l - 1)))
      (-(1 + (l - 1)) - 2 * θ * (1 + (l - 1)) - (1 + (l - 1)) * r * (2 + (l - 1)))
    calc
      (∫ T, (kS l * Yt l T) ^ j * gθ l r θ (Yt l T) ∂GW μ) =
          ∫ T, (kS l * Yt l T) ^ j *
            (-2 * (1 + (l - 1)) * r +
              (1 + (l - 1) + 2 * θ + (1 + (l - 1)) * r * (4 + (l - 1))) * Yt l T +
              (-(1 + (l - 1)) - 2 * θ * (1 + (l - 1)) -
                (1 + (l - 1)) * r * (2 + (l - 1))) * Yt l T ^ 2) ∂GW μ := by
        apply integral_congr_ae
        filter_upwards with T
        unfold gθ
        ring
      _ = _ := hq
  have hFJ : FJ μ l j = ∫ T, rankPolyFJ (xS μ l) (l - 1) j (1 - Wt l T) ∂splitLaw μ := by
    have hpq : p1 μ = 1 - (l - 1) * xS μ l := by
      have hp := p1_add_pBr h
      unfold xS
      field_simp [(by linarith : l - 1 ≠ 0)]
      nlinarith
    unfold FJ rankPolyFJ
    rw [hpq, cert_lMoment_eq μ]
    have hk : certK (l - 1) = kS l := by unfold certK kS; congr 1; ring
    rw [hk]
    have hi₁ : certIota (xS μ l) (l - 1) (j + 1) = iota μ l (j + 1) := by
      unfold certIota certQ iota Qgeo
      congr 2
      ring
    have hi₂ : certIota (xS μ l) (l - 1) (j + 2) = iota μ l (j + 2) := by
      unfold certIota certQ iota Qgeo
      congr 2
      ring
    rw [hi₁, hi₂]
    simp only [sub_sub_cancel]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with T
    ring
  exact ⟨hP, hF, hG, hFJ⟩

end LPPMonotonicityProof.Analytic
