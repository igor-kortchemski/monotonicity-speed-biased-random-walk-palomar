module

public import LPPMonotonicityProof.Analytic.WardSource
public import LPPMonotonicityProof.Analytic.Comparison3
public import LPPMonotonicityProof.Analytic.Ceiling
public import LPPMonotonicityProof.Analytic.HighBias
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The high-bias sign test

This module proves Theorem 3.7 (`thm:above-two`).
All clearing identities are kept on plain real variables before the analytic
moment and speed estimates are instantiated.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

private lemma integrable_Yt_above (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : Integrable (Yt l) (GW μ) := by
  apply Integrable.of_bound (measurable_Yt l).aestronglyMeasurable (1 / l)
  filter_upwards [ae_escape_pos h (by linarith) hlm] with T hT
  have hy := Yt_mem hl hT
  rw [Real.norm_eq_abs, abs_of_pos hy.1]
  exact hy.2.le

private lemma integrable_Yt_sq_above (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : Integrable (fun T => Yt l T ^ 2) (GW μ) := by
  apply Integrable.of_bound ((measurable_Yt l).pow_const 2).aestronglyMeasurable 1
  filter_upwards [ae_escape_pos h (by linarith) hlm] with T hT
  have hy := Yt_mem hl hT
  have hy1 : Yt l T < 1 := hy.2.trans ((div_lt_one (by linarith)).2 (by linarith))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [mul_pos hy.1 (sub_pos.mpr hy1)]

private lemma muY_sq_le_momY_two (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : muY μ l ^ 2 ≤ momY μ l 2 := by
  let m := muY μ l
  have hY := integrable_Yt_above μ h hl hlm
  have hY2 := integrable_Yt_sq_above μ h hl hlm
  have hnon : 0 ≤ ∫ T, (Yt l T - m) ^ 2 ∂GW μ :=
    integral_nonneg fun T => sq_nonneg (Yt l T - m)
  have hrew : (∫ T, (Yt l T - m) ^ 2 ∂GW μ) = momY μ l 2 - m ^ 2 := by
    calc
      (∫ T, (Yt l T - m) ^ 2 ∂GW μ) =
          ∫ T, Yt l T ^ 2 - 2 * m * Yt l T + m ^ 2 ∂GW μ := by
        apply integral_congr_ae
        filter_upwards with T
        ring
      _ = momY μ l 2 - m ^ 2 := by
        rw [integral_add (f := fun T => Yt l T ^ 2 - 2 * m * Yt l T)
            (g := fun _ => m ^ 2) (hY2.sub (hY.const_mul (2 * m))) (integrable_const _),
          integral_sub (f := fun T => Yt l T ^ 2) (g := fun T => 2 * m * Yt l T)
            hY2 (hY.const_mul (2 * m)), integral_const_mul, integral_const]
        simp [Measure.real]
        change (∫ T, Yt l T ^ 2 ∂GW μ) - 2 * m * (∫ T, Yt l T ∂GW μ) + m ^ 2 =
          (∫ T, Yt l T ^ 2 ∂GW μ) - m ^ 2
        rw [show (∫ T, Yt l T ∂GW μ) = m from rfl]
        ring
  rw [hrew] at hnon
  exact sub_nonneg.mp hnon

/-- The bracket multiplying `r` in the two-moment Ward test. -/
private noncomputable def sourceBracket (l m c : ℝ) : ℝ :=
  2 / m - 2 * (1 + l) + (1 + l) * c + (l - 1) * l * c ^ 2

private noncomputable def sourceQ (l m c r : ℝ) : ℝ :=
  2 - c - l * c ^ 2 - r * sourceBracket l m c

private lemma sourceBracket_at_mean (l m : ℝ) (hm : m ≠ 0) :
    m * sourceBracket l m m = (1 - l * m) * (2 - 2 * m - (l - 1) * m ^ 2) := by
  simp only [sourceBracket]
  field_simp [hm]
  ring

private lemma sourceBracket_mono {l m c : ℝ} (hl : 1 < l)
    (hm : 0 < m) (hmc : m ≤ c) :
    sourceBracket l m m ≤ sourceBracket l m c := by
  have hc : 0 ≤ c := hm.le.trans hmc
  have hfactor : 0 ≤ (c - m) * ((1 + l) + (l - 1) * l * (c + m)) :=
    mul_nonneg (sub_nonneg.mpr hmc) (by positivity)
  have hid : sourceBracket l m c - sourceBracket l m m =
      (c - m) * ((1 + l) + (l - 1) * l * (c + m)) := by
    simp only [sourceBracket]
    ring
  linarith

private lemma sourceBracket_pos {l m c : ℝ} (hl : 1 < l)
    (hm : 0 < m) (hlm : l * m < 1) (hmc : m ≤ c) : 0 < sourceBracket l m c := by
  have hm1 : m < 1 := by nlinarith [mul_pos (by linarith : 0 < l) hm]
  have hprod : 0 < (1 - l * m) * (1 - m) * (2 - m) :=
    mul_pos (mul_pos (sub_pos.mpr hlm) (sub_pos.mpr hm1)) (by linarith)
  have hlast : (1 - l * m) * (2 - 2 * m - (l - 1) * m ^ 2) =
      (1 - l * m) * ((1 - m) * (2 - m) + m * (1 - l * m)) := by ring
  have hother : 0 ≤ (1 - l * m) * (m * (1 - l * m)) := by positivity
  have hmean : 0 < sourceBracket l m m := by
    apply (mul_pos_iff_of_pos_left hm).mp
    rw [sourceBracket_at_mean l m hm.ne', hlast]
    nlinarith
  exact hmean.trans_le (sourceBracket_mono hl hm hmc)

private lemma sourceQ_cap_le {l m c C r R : ℝ} (hl : 1 < l)
    (hm : 0 < m) (hlm : l * m < 1) (hmc : m ≤ c) (hc : 0 ≤ c) (hcC : c ≤ C)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hrR : r ≤ R) :
    sourceQ l m C R ≤ sourceQ l m c r := by
  have hmC : m ≤ C := hmc.trans hcC
  have hBC : 0 < sourceBracket l m C := sourceBracket_pos hl hm hlm hmC
  have hfactor : 0 ≤ (C - c) *
      (1 + l * (c + C) + r * ((1 + l) + (l - 1) * l * (c + C))) := by
    apply mul_nonneg (sub_nonneg.mpr hcC)
    positivity
  have hid₁ : sourceQ l m c r - sourceQ l m C r = (C - c) *
      (1 + l * (c + C) + r * ((1 + l) + (l - 1) * l * (c + C))) := by
    simp only [sourceQ, sourceBracket]
    ring
  have hid₂ : sourceQ l m C r - sourceQ l m C R =
      (R - r) * sourceBracket l m C := by
    simp only [sourceQ]
    ring
  have hsecond : 0 ≤ (R - r) * sourceBracket l m C :=
    mul_nonneg (sub_nonneg.mpr hrR) hBC.le
  linarith

private lemma mean_peff_identity {l m b q : ℝ} (hm : 1 - m ≠ 0)
    (hb : b = (l - 1) * m / (1 - m)) (hq : q = 1 - b)
    (hlq : l - q ≠ 0) : m = b / (l - q) := by
  apply (eq_div_iff hlq).2
  subst q
  subst b
  field_simp [hm]
  ring

private lemma cap_identity {l m b q : ℝ} (hm : 1 - m ≠ 0)
    (hb : b = (l - 1) * m / (1 - m)) (hq : q = 1 - b)
    (_hlq : l - q ≠ 0) (hv : l ^ 2 - q ≠ 0) :
    (1 + l * (1 - m))⁻¹ = (l - q) / (l ^ 2 - q) := by
  subst q
  subst b
  have hid : (1 + l * (1 - m)) * (l - (1 - (l - 1) * m / (1 - m))) =
      l ^ 2 - (1 - (l - 1) * m / (1 - m)) := by
    field_simp [hm]
    ring
  have hden : 1 + l * (1 - m) ≠ 0 := by
    intro hzero
    apply hv
    rw [← hid, hzero, zero_mul]
  rw [inv_eq_one_div]
  apply (div_eq_div_iff hden hv).2
  field_simp [hm]
  ring

private lemma q_cap_identity {l b q S : ℝ}
    (hb : b = 1 - q) (hq : 1 - q ≠ 0) (_hlq : l - q ≠ 0) (hv : l ^ 2 - q ≠ 0)
    (hd : 2 * l - (1 + l) * b * S ≠ 0) :
    (l ^ 2 - q) ^ 2 * (2 * l - (1 + l) * b * S) *
        sourceQ l (b / (l - q)) ((l - q) / (l ^ 2 - q))
          (b * S / (2 * l - (1 + l) * b * S)) =
      2 * (l - 1) * HighBias.FReal l q S := by
  subst b
  have hDR : (2 * l - (1 + l) * (1 - q) * S) *
      ((1 - q) * S / (2 * l - (1 + l) * (1 - q) * S)) = (1 - q) * S := by
    field_simp [hd]
  have hWB : (1 - q) * sourceBracket l ((1 - q) / (l - q)) ((l - q) / (l ^ 2 - q)) =
      2 * (l - q) + (1 - q) *
        (-2 * (1 + l) + (1 + l) * ((l - q) / (l ^ 2 - q)) +
          (l - 1) * l * ((l - q) / (l ^ 2 - q)) ^ 2) := by
    simp only [sourceBracket]
    field_simp [_hlq, hv, hq]
    ring
  calc
    (l ^ 2 - q) ^ 2 * (2 * l - (1 + l) * (1 - q) * S) *
        sourceQ l ((1 - q) / (l - q)) ((l - q) / (l ^ 2 - q))
          ((1 - q) * S / (2 * l - (1 + l) * (1 - q) * S)) =
      (l ^ 2 - q) ^ 2 * (2 * l - (1 + l) * (1 - q) * S) *
        (2 - (l - q) / (l ^ 2 - q) - l * ((l - q) / (l ^ 2 - q)) ^ 2) -
        (l ^ 2 - q) ^ 2 * ((2 * l - (1 + l) * (1 - q) * S) *
          ((1 - q) * S / (2 * l - (1 + l) * (1 - q) * S))) *
          sourceBracket l ((1 - q) / (l - q)) ((l - q) / (l ^ 2 - q)) := by
        simp only [sourceQ]
        ring
    _ = (l ^ 2 - q) ^ 2 * (2 * l - (1 + l) * (1 - q) * S) *
        (2 - (l - q) / (l ^ 2 - q) - l * ((l - q) / (l ^ 2 - q)) ^ 2) -
        (l ^ 2 - q) ^ 2 * ((1 - q) * S) *
          sourceBracket l ((1 - q) / (l - q)) ((l - q) / (l ^ 2 - q)) := by rw [hDR]
    _ = (l ^ 2 - q) ^ 2 * (2 * l - (1 + l) * (1 - q) * S) *
        (2 - (l - q) / (l ^ 2 - q) - l * ((l - q) / (l ^ 2 - q)) ^ 2) -
        (l ^ 2 - q) ^ 2 * S * ((1 - q) *
          sourceBracket l ((1 - q) / (l - q)) ((l - q) / (l ^ 2 - q))) := by ring
    _ = (l ^ 2 - q) ^ 2 * (2 * l - (1 + l) * (1 - q) * S) *
        (2 - (l - q) / (l ^ 2 - q) - l * ((l - q) / (l ^ 2 - q)) ^ 2) -
        (l ^ 2 - q) ^ 2 * S * (2 * (l - q) + (1 - q) *
          (-2 * (1 + l) + (1 + l) * ((l - q) / (l ^ 2 - q)) +
            (l - 1) * l * ((l - q) / (l ^ 2 - q)) ^ 2)) := by rw [hWB]
    _ = 2 * (l - 1) * HighBias.FReal l q S := by
      simp only [HighBias.FReal]
      field_simp [hv]
      ring

private lemma q_cap_pos {l b q S : ℝ} (hl : 1 < l) (hb : b = 1 - q)
    (hq : 1 - q ≠ 0) (hlq : 0 < l - q) (hv : 0 < l ^ 2 - q)
    (hd : 0 < 2 * l - (1 + l) * b * S) (hF : 0 < HighBias.FReal l q S) :
    0 < sourceQ l (b / (l - q)) ((l - q) / (l ^ 2 - q))
      (b * S / (2 * l - (1 + l) * b * S)) := by
  have hfactor : 0 < (l ^ 2 - q) ^ 2 * (2 * l - (1 + l) * b * S) :=
    mul_pos (sq_pos_of_pos hv) hd
  apply (mul_pos_iff_of_pos_left hfactor).mp
  rw [q_cap_identity hb hq hlq.ne' hv.ne' hd.ne']
  exact mul_pos (by linarith) hF

private lemma F_pos_of_le {l q S T : ℝ} (hl : 1 < l)
    (hq : 0 ≤ q) (hq1 : q < 1) (hST : S ≤ T)
    (hT : 0 < HighBias.FReal l q T) : 0 < HighBias.FReal l q S := by
  have hq2 : q ^ 2 ≤ q := by nlinarith [mul_nonneg hq (sub_nonneg.mpr hq1.le)]
  have hlq : l * q ≤ l := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ l) (sub_nonneg.mpr hq1.le)]
  have hlcube : l ^ 2 < l ^ 2 * (l + 1) := by
    nlinarith [mul_pos (sq_pos_of_pos (by linarith : 0 < l)) (by linarith : 0 < l)]
  have hK : 0 < (l - q) * (l ^ 2 * (l + 1) - l * q - q ^ 2) := by
    apply mul_pos (by linarith)
    nlinarith
  have hid : HighBias.FReal l q S - HighBias.FReal l q T =
      (l - q) * (l ^ 2 * (l + 1) - l * q - q ^ 2) * (T - S) := by
    simp only [HighBias.FReal]
    ring
  have hnon : 0 ≤ (l - q) * (l ^ 2 * (l + 1) - l * q - q ^ 2) * (T - S) :=
    mul_nonneg hK.le (sub_nonneg.mpr hST)
  linarith

/-- **Theorem 3.7** (`thm:above-two`): the explicit high-bias criterion. -/
theorem deriv_neg_above_two (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ)
    (hab : 8 ≤ 24 * peff μ l + 10 * (l - 1)) : deriv (speedValue μ) l < 0 := by
  apply deriv_neg_of_Qtest_pos μ h hl hlm
  let m := muY μ l
  let b := peff μ l
  let q := 1 - b
  let S := Sgeo l q
  let c := momY μ l 2 / m
  let r := rr μ l
  let C := (l - q) / (l ^ 2 - q)
  let d := 2 * l - (1 + l) * b * S
  let R := b * S / d
  change 0 < sourceQ l m c r
  have hm : 0 < m := (muY_mem μ h hl hlm).1
  have hml : m < 1 / l := (muY_mem μ h hl hlm).2
  have hlm' : l * m < 1 := by
    have := mul_lt_mul_of_pos_left hml (by linarith : 0 < l)
    rw [mul_one_div, div_self (by linarith : l ≠ 0)] at this
    exact this
  have hbmem : 0 < b ∧ b < 1 := peff_mem μ h hl hlm
  have hq : 0 ≤ q ∧ q < 1 := by dsimp [q]; constructor <;> linarith [hbmem.1, hbmem.2]
  have hlq : 0 < l - q := by dsimp [q]; linarith [hbmem.1, hl]
  have hv : 0 < l ^ 2 - q := by nlinarith [mul_pos (sub_pos.mpr hl) (by linarith : 0 < l + 1)]
  have hm1 : 1 - m ≠ 0 := by
    have hm1' : m < 1 := by nlinarith [hlm', mul_pos (sub_pos.mpr hl) hm]
    exact sub_ne_zero.mpr hm1'.ne'
  have hbdef : b = (l - 1) * m / (1 - m) := by rfl
  have hqdef : q = 1 - b := by rfl
  have hmform : m = b / (l - q) := mean_peff_identity hm1 hbdef hqdef hlq.ne'
  have hsq : m ^ 2 ≤ momY μ l 2 := muY_sq_le_momY_two μ h hl hlm
  have hc : 0 ≤ c := div_nonneg ((sq_nonneg m).trans hsq) hm.le
  have hmc : m ≤ c := by
    dsimp [c]
    exact (le_div_iff₀ hm).2 (by nlinarith [hsq])
  have hcC : c ≤ C := by
    have hbound := momY_two_div_le μ h hl hlm
    change c ≤ (1 + l * (1 - m))⁻¹ at hbound
    exact hbound.trans_eq (cap_identity hm1 hbdef hqdef hlq.ne' hv.ne')
  have hC : 0 ≤ C := (div_pos hlq hv).le
  have hceil := speed_le_ceiling μ h hl hlm
  have hd : 0 < d := hceil.1
  have hr : 0 ≤ r := (rr_pos μ h hl hlm).le
  have hrR : r ≤ R := by
    have hvceil : speedValue μ l ≤ (l - 1) * b * S / d := hceil.2.1
    dsimp [r, R]
    unfold rr
    rw [← speedValue_eq_speedValueProv]
    calc
      speedValue μ l / (l - 1) ≤ ((l - 1) * b * S / d) / (l - 1) :=
        div_le_div_of_nonneg_right hvceil (by linarith)
      _ = b * S / d := by field_simp [show l - 1 ≠ 0 by linarith]
  have hqb : 1 - q = b := by dsimp [q]; ring
  have hSS2 : S ≤ HighBias.S2Real (l - 1) b := by
    dsimp [S]
    rw [← hqb]
    exact Sgeo_le_S2 hl hq
  have hF2 : 0 < HighBias.FReal l q (HighBias.S2Real (l - 1) b) := by
    have hpos := F_S2_pos (a := l - 1) (b := b) (by linarith) hbmem.1.le hbmem.2 hab
    have hLa : 1 + (l - 1) = l := by ring
    have hqb : 1 - b = q := by rfl
    simpa only [hLa, hqb] using hpos
  have hF : 0 < HighBias.FReal l q S := F_pos_of_le hl hq.1 hq.2 hSS2 hF2
  have hcap : 0 < sourceQ l m C R := by
    dsimp [C, R, d]
    rw [hmform]
    exact q_cap_pos hl (by dsimp [q]; ring) (sub_ne_zero.mpr hq.2.ne') hlq hv hd hF
  exact hcap.trans_le (sourceQ_cap_le hl hm hlm' hmc hc hcC hC hr hrR)

/-- **Theorem 3.7, second clause:** bias at least `9/5` suffices on its own. -/
theorem deriv_neg_of_ge (h : OffspringHyp μ) {l : ℝ}
    (hl : 9 / 5 ≤ l) (hlm : l < mean μ) : deriv (speedValue μ) l < 0 := by
  have hl1 : 1 < l := by norm_num at hl ⊢; linarith
  apply deriv_neg_above_two μ h hl1 hlm
  have hb : 0 ≤ peff μ l := (peff_mem μ h hl1 hlm).1.le
  norm_num at hl ⊢
  nlinarith

end LPPMonotonicityProof.Analytic
