module

public import LPPMonotonicityProof.Analytic.FirstSplit
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# First split: moments and deficit estimates

This module proves the moment identities of Lemma 4.1 (`lem:prefix-terminal`):
`E Lⁿ = x ιₙ`, `E Yⁿ = x ιₙ E Wⁿ` and `E Y = w / (1 + s)`.  It also proves the basic
facts on the split: `0 < W < 1` almost surely, `d = 1 - w > 0`,
`0 < e = E[1/J] ≤ 1/2`, and `d ≤ η ≤ 1` (the Jensen step of Lemma 5.4,
`lem:terminal-speed`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private lemma ae_splitLaw_of_ae {P : Tree → Prop} (hP : ∀ᵐ T ∂GW μ, P T) :
    ∀ᵐ T ∂splitLaw μ, P T := by
  exact (ae_restrict_of_ae hP).filter_mono (Measure.ae_smul_measure_le _)

private lemma ae_split_degree' : ∀ᵐ T ∂splitLaw μ, 2 ≤ degree T := by
  exact (ae_restrict_mem (continuous_degree.measurable measurableSet_Ici)).filter_mono
    (Measure.ae_smul_measure_le _)

/-- At a transient bias, the split response lies strictly between zero and one. -/
theorem ae_Wt_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    ∀ᵐ T ∂splitLaw μ, 0 < Wt l T ∧ Wt l T < 1 := by
  have hesc : ∀ᵐ T ∂splitLaw μ, ∀ v, Present T v →
      0 < escape l (subtree T v) := ae_splitLaw_of_ae (ae_escape_pos_subtrees h
    (by positivity) hlm)
  filter_upwards [hesc, ae_split_degree' (μ := μ)] with T hT hdeg
  have hpos (i : Fin (degree T)) : 0 < escape l (child T (i.val + 1)) := by
    have hi := hT [i.val + 1] (by simp only [present_cons, present_nil, and_true]; omega)
    simpa [subtree_cons] using hi
  have hsum : 0 < childSum l T := by
    apply Finset.sum_pos (fun i _ => hpos i)
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hden : 0 < l - 1 + childSum l T := by linarith
  constructor
  · exact div_pos hsum hden
  · exact (div_lt_one hden).2 (by linarith)

private lemma ae_Wt_mem_Icc (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : ∀ᵐ T ∂splitLaw μ, Wt l T ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  exact ⟨hT.1.le, hT.2.le⟩

private lemma integrable_Wt_pow (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : Integrable (fun T => Wt l T ^ n) (splitLaw μ) := by
  letI := splitLaw_prob h
  apply (integrable_const (1 : ℝ)).mono' ((measurable_Wt l).pow_const n).aestronglyMeasurable
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hT.1.le _)]
  exact pow_le_one₀ hT.1.le hT.2.le

private lemma integrable_one_sub_Wt (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : Integrable (fun T => 1 - Wt l T) (splitLaw μ) := by
  letI := splitLaw_prob h
  exact (integrable_const (1 : ℝ)).sub ((by simpa only [pow_one] using integrable_Wt_pow h hl hlm 1))

private lemma dW_eq_integral (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : dW μ l = ∫ T, (1 - Wt l T) ∂splitLaw μ := by
  letI := splitLaw_prob h
  have hW : Integrable (fun T => Wt l T) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow h hl hlm 1
  rw [integral_sub (integrable_const (1 : ℝ)) hW]
  simp [dW, wbar, etaW]

/-- The mean deficit is positive. -/
theorem dW_pos (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    0 < dW μ l := by
  letI := splitLaw_prob h
  rw [dW_eq_integral h hl hlm]
  have hi := integrable_one_sub_Wt h hl hlm
  have hnonneg : 0 ≤ᵐ[splitLaw μ] (fun T => 1 - Wt l T) := by
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    exact sub_nonneg.mpr hT.2.le
  rw [integral_pos_iff_support_of_nonneg_ae hnonneg hi]
  have hsupport : Function.support (fun T => 1 - Wt l T) =ᵐ[splitLaw μ] Set.univ := by
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    simp [Function.support, ne_of_gt (sub_pos.mpr hT.2)]
  rw [measure_congr hsupport]
  simp

/-- The reciprocal split degree has mean in `(0, 1/2]`. -/
theorem eJ_mem (h : OffspringHyp μ) : 0 < eJ μ ∧ eJ μ ≤ 1 / 2 := by
  letI := splitLaw_prob h
  have hnonneg : 0 ≤ᵐ[splitLaw μ] (fun T => ((degree T : ℝ))⁻¹) := by
    filter_upwards with T
    positivity
  have hi : Integrable (fun T => ((degree T : ℝ))⁻¹) (splitLaw μ) := by
    apply (integrable_const (1 / 2 : ℝ)).mono'
      ((measurable_of_countable (fun k : ℕ => ((k : ℝ))⁻¹)).comp
      continuous_degree.measurable).aestronglyMeasurable
    filter_upwards [ae_split_degree' (μ := μ)] with T hT
    change ‖((degree T : ℝ))⁻¹‖ ≤ 1 / 2
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    simpa only [one_div] using one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≤ degree T by exact_mod_cast hT)
  constructor
  · unfold eJ
    rw [integral_pos_iff_support_of_nonneg_ae hnonneg hi]
    have hsupport : Function.support (fun T : Tree => ((degree T : ℝ))⁻¹) =ᵐ[splitLaw μ]
        Set.univ := by
      filter_upwards [ae_split_degree' (μ := μ)] with T hT
      have hdeg : degree T ≠ 0 := by omega
      simp [Function.support, hdeg]
    rw [measure_congr hsupport]
    simp
  · unfold eJ
    calc
      (∫ T, ((degree T : ℝ))⁻¹ ∂splitLaw μ) ≤ ∫ _T : Tree, (1 / 2 : ℝ) ∂splitLaw μ := by
        apply integral_mono_ae hi (integrable_const _)
        filter_upwards [ae_split_degree' (μ := μ)] with T hT
        change ((degree T : ℝ))⁻¹ ≤ 1 / 2
        simpa only [one_div] using one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num)
          (show (2 : ℝ) ≤ degree T by exact_mod_cast hT)
      _ = 1 / 2 := by simp

private lemma integrable_deficit_sq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : Integrable (fun T => (1 - Wt l T) ^ 2) (splitLaw μ) := by
  letI := splitLaw_prob h
  apply (integrable_const (1 : ℝ)).mono'
    (((integrable_one_sub_Wt h hl hlm).1.pow 2))
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hd : 0 ≤ 1 - Wt l T := sub_nonneg.mpr hT.2.le
  have hd' : 1 - Wt l T ≤ 1 := by linarith [hT.1]
  exact pow_le_one₀ hd hd'

/-- Jensen under the deficit tilt, together with `0 ≤ 1 - W ≤ 1`. -/
theorem dW_le_etaD (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    dW μ l ≤ etaD μ l ∧ etaD μ l ≤ 1 := by
  letI := splitLaw_prob h
  have hdpos := dW_pos h hl hlm
  have hX := integrable_one_sub_Wt h hl hlm
  have hX2 := integrable_deficit_sq h hl hlm
  have hmem : ∀ᵐ T ∂splitLaw μ, 1 - Wt l T ∈ Set.Ici (0 : ℝ) := by
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    exact sub_nonneg.mpr hT.2.le
  have hJensen := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le (continuousOn_pow 2)
      isClosed_Ici hmem hX hX2
  have hJ : dW μ l ^ 2 ≤ ∫ T, (1 - Wt l T) ^ 2 ∂splitLaw μ := by
    rw [dW_eq_integral h hl hlm]
    exact hJensen
  constructor
  · unfold etaD
    apply (le_div_iff₀ hdpos).2
    nlinarith
  · unfold etaD
    apply (div_le_one hdpos).2
    rw [dW_eq_integral h hl hlm]
    apply integral_mono_ae hX2 hX
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    have hd0 : 0 ≤ 1 - Wt l T := sub_nonneg.mpr hT.2.le
    have hd1 : 1 - Wt l T ≤ 1 := by linarith [hT.1]
    nlinarith

private lemma p1_nonneg (μ : Measure ℕ) [IsProbabilityMeasure μ] : 0 ≤ p1 μ := by
  exact measureReal_nonneg

private lemma pBr_le_one (h : OffspringHyp μ) : pBr μ ≤ 1 := by
  have hp := p1_add_pBr h
  have hq := p1_nonneg μ
  linarith

private lemma geomY_prob (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) :
    IsProbabilityMeasure (geomY l (pBr μ)) := by
  have hp0 := pBr_pos h
  have hp1 := pBr_le_one h
  have hr0 : 0 ≤ 1 - pBr μ := by linarith
  have hr1 : 1 - pBr μ < 1 := by linarith
  have hsum : Summable (fun g : ℕ => pBr μ * (1 - pBr μ) ^ g) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine ⟨?_⟩
  rw [geomY, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun g => mul_nonneg hp0.le (pow_nonneg hr0 _)) hsum]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hpne : pBr μ ≠ 0 := ne_of_gt hp0
  rw [sub_sub_cancel, mul_inv_cancel₀ hpne, ENNReal.ofReal_one]

private lemma ae_geomY_mem_Icc (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) :
    ∀ᵐ y ∂geomY l (pBr μ), y ∈ Set.Icc (0 : ℝ) 1 := by
  rw [geomY, Measure.ae_sum_iff]
  intro g
  apply Filter.Eventually.filter_mono (Measure.ae_smul_measure_le _)
  refine (mem_ae_dirac_iff (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc).2 ⟨?_, ?_⟩
  · exact (zpow_pos (show 0 < l by positivity) (-((g : ℤ) + 1))).le
  · exact zpow_le_one_of_nonpos₀ hl.le (by omega)

private lemma integrable_geomY_pow (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (n : ℕ) : Integrable (fun y => y ^ n) (geomY l (pBr μ)) := by
  letI := geomY_prob h hl
  apply (integrable_const (1 : ℝ)).mono' (measurable_id.pow_const n).aestronglyMeasurable
  filter_upwards [ae_geomY_mem_Icc h hl] with y hy
  change ‖y ^ n‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy.1 _)]
  exact pow_le_one₀ hy.1 hy.2

private lemma xS_mul_iota (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) :
    xS μ l * iota μ l n = pBr μ / (pBr μ + l ^ n - 1) := by
  have hp := pBr_pos h
  have ha : 0 < l - 1 := by linarith
  have hn : 0 < l ^ n := pow_pos (by positivity) _
  have hQ : Qgeo l n * (l - 1) = l ^ n - 1 := geom_sum_mul_of_one_le hl.le n
  have hden : xS μ l + Qgeo l n = (pBr μ + l ^ n - 1) / (l - 1) := by
    unfold xS
    field_simp [ha.ne']
    nlinarith [hQ]
  have hln1 : 1 ≤ l ^ n := one_le_pow₀ hl.le
  have hbase : pBr μ + l ^ n - 1 ≠ 0 := by linarith
  rw [xS, iota, hden]
  field_simp [ha.ne', hp.ne', hbase]

private lemma geomY_moment_series (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (n : ℕ) : (∫ y, y ^ n ∂geomY l (pBr μ)) =
      ∑' g : ℕ, pBr μ * (1 - pBr μ) ^ g * (l ^ (-((g : ℤ) + 1))) ^ n := by
  have hp := pBr_pos h
  have hp1 := pBr_le_one h
  have hr0 : 0 ≤ 1 - pBr μ := by linarith
  have hInt := integrable_geomY_pow h hl n
  unfold geomY
  rw [integral_sum_measure hInt]
  apply tsum_congr
  intro g
  rw [integral_smul_measure, integral_dirac]
  rw [ENNReal.toReal_ofReal (mul_nonneg hp.le (pow_nonneg hr0 _))]
  rfl

/-- Lemma 4.1 (`lem:prefix-terminal`): the moments of the geometric prefix law. -/
theorem Llaw_moment (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) :
    ∫ y, y ^ n ∂geomY l (pBr μ) = xS μ l * iota μ l n := by
  have hp := pBr_pos h
  have hp1 := pBr_le_one h
  have hn : 0 < l ^ n := pow_pos (by positivity) _
  have hr0 : 0 ≤ 1 - pBr μ := by linarith
  have hr1 : 1 - pBr μ < 1 := by linarith
  rw [geomY_moment_series h hl n]
  have hterm (g : ℕ) :
      pBr μ * (1 - pBr μ) ^ g * (l ^ (-((g : ℤ) + 1))) ^ n =
        pBr μ * (l ^ n)⁻¹ * ((1 - pBr μ) * (l ^ n)⁻¹) ^ g := by
    have hg : -((g : ℤ) + 1) = -(((g + 1 : ℕ) : ℤ)) := by push_cast; ring
    rw [hg, zpow_neg, zpow_natCast, inv_pow, mul_pow]
    have hpow : ((l ^ (g + 1)) ^ n)⁻¹ = (l ^ n)⁻¹ * ((l ^ n) ^ g)⁻¹ := by
      calc
        ((l ^ (g + 1)) ^ n)⁻¹ = (l ^ ((g + 1) * n))⁻¹ := by rw [pow_mul]
        _ = (l ^ (n + n * g))⁻¹ := by congr 2; push_cast; ring
        _ = ((l ^ n) * (l ^ (n * g)))⁻¹ := by rw [pow_add]
        _ = (l ^ n)⁻¹ * ((l ^ n) ^ g)⁻¹ := by rw [pow_mul, mul_inv]
    rw [hpow]
    ring
  simp_rw [hterm]
  have hr'0 : 0 ≤ (1 - pBr μ) * (l ^ n)⁻¹ := mul_nonneg hr0 (inv_nonneg.mpr hn.le)
  have hr'1 : (1 - pBr μ) * (l ^ n)⁻¹ < 1 := by
    have hi : (l ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hl.le)
    have hi0 : 0 ≤ (l ^ n)⁻¹ := inv_nonneg.mpr hn.le
    calc
      (1 - pBr μ) * (l ^ n)⁻¹ ≤ (1 - pBr μ) * 1 := mul_le_mul_of_nonneg_left hi hr0
      _ < 1 := by simpa using hr1
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr'0 hr'1, xS_mul_iota h hl]
  field_simp [hp.ne', hn.ne']
  ring

private lemma ae_Yt_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : ∀ᵐ T ∂GW μ, 0 < Yt l T ∧ Yt l T < 1 := by
  filter_upwards [ae_escape_pos h (by positivity) hlm] with T hT
  have hden : 0 < l - 1 + escape l T := by linarith
  constructor
  · exact div_pos hT hden
  · exact (div_lt_one hden).2 (by linarith)

/-- Independence of the unary prefix and the split, at the level of moments. -/
theorem momY_eq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (n : ℕ) : momY μ l n = xS μ l * iota μ l n * etaW μ l n := by
  let F : ℕ → Tree → ℝ := fun g T => (l ^ (-(g : ℤ)) * Wt l T) ^ n
  have hFm : Measurable (Function.uncurry F) := by
    apply measurable_from_prod_countable_right
    intro g
    simpa only [F, Function.uncurry, Pi.mul_apply] using
      (measurable_const.mul (measurable_Wt l)).pow_const n
  have hYi : Integrable (fun T => Yt l T ^ n) (GW μ) := by
    apply (integrable_const (1 : ℝ)).mono' ((measurable_Yt l).pow_const n).aestronglyMeasurable
    filter_upwards [ae_Yt_mem h hl hlm] with T hT
    change ‖Yt l T ^ n‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hT.1.le _)]
    exact pow_le_one₀ hT.1.le hT.2.le
  have hInt : Integrable (fun T => F (Gt T) (splitTree T)) (GW μ) := by
    apply hYi.congr
    filter_upwards [ae_split_degree h] with T hT
    exact congrArg (fun y : ℝ => y ^ n) (Yt_eq_prefix hl T hT)
  unfold momY
  calc
    (∫ T, Yt l T ^ n ∂GW μ) = ∫ T, F (Gt T) (splitTree T) ∂GW μ := by
      apply integral_congr_ae
      filter_upwards [ae_split_degree h] with T hT
      exact congrArg (fun y : ℝ => y ^ n) (Yt_eq_prefix hl T hT)
    _ = ∑' g : ℕ, (p1 μ ^ g * pBr μ) * ∫ T, F (g + 1) T ∂splitLaw μ :=
      integral_firstSplit h hFm hInt
    _ = ∑' g : ℕ, (pBr μ * (1 - pBr μ) ^ g *
        (l ^ (-((g : ℤ) + 1))) ^ n) * etaW μ l n := by
      apply tsum_congr
      intro g
      have hpq : p1 μ = 1 - pBr μ := by linarith [p1_add_pBr h]
      simp only [F, mul_pow]
      rw [integral_const_mul]
      unfold etaW
      push_cast
      rw [hpq]
      ring
    _ = (∑' g : ℕ, pBr μ * (1 - pBr μ) ^ g *
        (l ^ (-((g : ℤ) + 1))) ^ n) * etaW μ l n := by rw [tsum_mul_right]
    _ = xS μ l * iota μ l n * etaW μ l n := by
      rw [← geomY_moment_series h hl n, Llaw_moment h hl n]

/-- The transformed moment normalization `E Yⁿ = x k^(1-n) mₙ`. -/
theorem momY_eq_mMom (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (n : ℕ) (hn : 1 ≤ n) : momY μ l n = xS μ l * kS l ^ (1 - (n : ℤ)) * mMom μ l n := by
  rw [momY_eq h hl hlm n, mMom, if_neg (by omega), Acoef]
  have hk : 0 < kS l := Real.sqrt_pos.mpr (by positivity)
  have hpow : kS l ^ (1 - (n : ℤ)) * kS l ^ (n - 1) = 1 := by
    calc
      kS l ^ (1 - (n : ℤ)) * kS l ^ (n - 1) =
          kS l ^ (1 - (n : ℤ)) * kS l ^ (((n - 1 : ℕ) : ℤ)) := by rw [zpow_natCast]
      _ = kS l ^ ((1 - (n : ℤ)) + ((n - 1 : ℕ) : ℤ)) := by
        rw [← zpow_add₀ hk.ne']
      _ = 1 := by
        have he : (1 - (n : ℤ)) + ((n - 1 : ℕ) : ℤ) = 0 := by omega
        rw [he, zpow_zero]
  calc
    xS μ l * iota μ l n * etaW μ l n =
        (kS l ^ (1 - (n : ℤ)) * kS l ^ (n - 1)) *
          (xS μ l * iota μ l n * etaW μ l n) := by rw [hpow, one_mul]
    _ = xS μ l * kS l ^ (1 - (n : ℤ)) *
        (kS l ^ (n - 1) * iota μ l n * etaW μ l n) := by ring

/-- Lemma 4.1 (`lem:prefix-terminal`): the mean of `Y`. -/
theorem muY_eq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    muY μ l = wbar μ l / (1 + sS μ l) := by
  have hm : muY μ l = momY μ l 1 := by simp [muY, momY]
  rw [hm, momY_eq h hl hlm, xS_mul_iota h hl]
  have hp := pBr_pos h
  have ha : 0 < l - 1 := by linarith
  have hdenpos : 0 < pBr μ + l ^ (1 : ℕ) - 1 := by nlinarith
  have hden' : -1 + pBr μ + l ≠ 0 := by nlinarith
  have hscalar : pBr μ / (pBr μ + l ^ (1 : ℕ) - 1) =
      1 / (1 + (l - 1) / pBr μ) := by
    field_simp [hp.ne', ha.ne', hdenpos.ne', hden']
    convert div_self hdenpos.ne' using 1 <;> ring
  unfold wbar etaW sS
  rw [hscalar]
  ring

/-- The differentiated geometric-prefix moment. -/
theorem GL_moment (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) (hn1 : 1 ≤ n) :
    (l - 1) / l * ∑' g : ℕ, (g + 1) * p1 μ ^ g * pBr μ *
      l ^ (-((g : ℤ) + 1) * (n : ℤ)) = xS μ l * Acoef μ l n ^ 2 := by
  have hp := pBr_pos h
  have ha : 0 < l - 1 := by linarith
  have hl0 : 0 < l := by positivity
  have hn : 0 < l ^ n := pow_pos hl0 _
  have hpq : p1 μ = 1 - pBr μ := by linarith [p1_add_pBr h]
  have hq0 := p1_nonneg μ
  have hq1 : p1 μ < 1 := by linarith [p1_add_pBr h]
  let D : ℝ := pBr μ + l ^ n - 1
  have hD : D ≠ 0 := by dsimp [D]; nlinarith [one_le_pow₀ hl.le (n := n)]
  have hQ : Qgeo l n * (l - 1) = l ^ n - 1 := geom_sum_mul_of_one_le hl.le n
  have hden : xS μ l + Qgeo l n = D / (l - 1) := by
    unfold xS
    dsimp [D]
    field_simp [ha.ne']
    nlinarith [hQ]
  have hi : iota μ l n = (l - 1) / D := by rw [iota, hden, inv_div]
  have hsquare : (Real.sqrt l ^ (n - 1)) ^ 2 = l ^ (n - 1) := by
    rw [← pow_mul, Nat.mul_comm (n - 1) 2, pow_mul, Real.sq_sqrt hl0.le]
  have hA : Acoef μ l n ^ 2 = l ^ (n - 1) * (l - 1) ^ 2 / D ^ 2 := by
    rw [Acoef, hi, mul_pow]
    change (Real.sqrt l ^ (n - 1)) ^ 2 * ((l - 1) / D) ^ 2 = _
    rw [hsquare]
    ring
  have hi0 : (l ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hl.le)
  have hr0 : 0 ≤ p1 μ * (l ^ n)⁻¹ := mul_nonneg hq0 (inv_nonneg.mpr hn.le)
  have hr1 : p1 μ * (l ^ n)⁻¹ < 1 := by
    calc
      p1 μ * (l ^ n)⁻¹ ≤ p1 μ * 1 := mul_le_mul_of_nonneg_left hi0 hq0
      _ < 1 := by simpa using hq1
  have hnorm : ‖p1 μ * (l ^ n)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hgeo : (∑' g : ℕ, (g + 1 : ℝ) * (p1 μ * (l ^ n)⁻¹) ^ g) =
      1 / (1 - p1 μ * (l ^ n)⁻¹) ^ 2 := by
    simpa using (tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hnorm)
  have hseries : (∑' g : ℕ, (g + 1) * p1 μ ^ g * pBr μ *
        l ^ (-((g : ℤ) + 1) * (n : ℤ))) =
      pBr μ * (l ^ n)⁻¹ * (1 / (1 - p1 μ * (l ^ n)⁻¹) ^ 2) := by
    calc
      _ = ∑' g : ℕ, pBr μ * (l ^ n)⁻¹ *
          ((g + 1 : ℝ) * (p1 μ * (l ^ n)⁻¹) ^ g) := by
        apply tsum_congr
        intro g
        have hpowg : l ^ (-((g : ℤ) + 1) * (n : ℤ)) =
            (l ^ (-((g : ℤ) + 1))) ^ n := by rw [zpow_mul, zpow_natCast]
        rw [hpowg]
        have hg : -((g : ℤ) + 1) = -(((g + 1 : ℕ) : ℤ)) := by push_cast; ring
        rw [hg, zpow_neg, zpow_natCast, inv_pow, mul_pow]
        have hpow : ((l ^ (g + 1)) ^ n)⁻¹ = (l ^ n)⁻¹ * ((l ^ n) ^ g)⁻¹ := by
          calc
            ((l ^ (g + 1)) ^ n)⁻¹ = (l ^ ((g + 1) * n))⁻¹ := by rw [pow_mul]
            _ = (l ^ (n + n * g))⁻¹ := by congr 2; push_cast; ring
            _ = ((l ^ n) * (l ^ (n * g)))⁻¹ := by rw [pow_add]
            _ = (l ^ n)⁻¹ * ((l ^ n) ^ g)⁻¹ := by rw [pow_mul, mul_inv]
        rw [hpow]
        ring
      _ = pBr μ * (l ^ n)⁻¹ *
          (∑' g : ℕ, (g + 1 : ℝ) * (p1 μ * (l ^ n)⁻¹) ^ g) := by rw [tsum_mul_left]
      _ = _ := by rw [hgeo]
  rw [hseries, hA, xS]
  have hratio : 1 - p1 μ * (l ^ n)⁻¹ = D / l ^ n := by
    dsimp [D]
    field_simp [hn.ne']
    rw [hpq]
    ring
  rw [hratio]
  simp only [inv_eq_one_div]
  have hln : l ^ (n - 1) * l = l ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn1]
  field_simp [hp.ne', ha.ne', hl0.ne', hn.ne', hD]
  nlinarith [hln]

end LPPMonotonicityProof.Analytic
