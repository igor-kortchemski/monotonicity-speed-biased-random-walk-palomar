module

public import LPPMonotonicityProof.Analytic.WardRanks
public import LPPMonotonicityProof.Analytic.FirstSplit3
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Ward coefficient `FJ`

This module proves the part of Proposition 5.2 (`prop:ward-ranks`) concerning the
explicit coefficient `F_j`: it is nonnegative, it dominates the exact rank moment, and
Ward's inequality holds with it. The private helpers whose names end in `Prov` are
local copies of private facts about `geomY` from `Analytic/FirstSplit2.lean`; they
make the weighted geometric average needed here explicit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

/-- The summand retained in Ward's rank inequality. -/
noncomputable def wardTerm (l θ : ℝ) (j : ℕ) : ℝ :=
  (j + 1) * (PJ μ l j * muJ μ l j (gθ l (rr μ l) θ) +
    2 * FJ μ l j * muJ μ l j (fθ l (rr μ l) θ))

private lemma p1_nonnegProv (μ : Measure ℕ) [IsProbabilityMeasure μ] : 0 ≤ p1 μ :=
  measureReal_nonneg

private lemma pBr_le_oneProv {μ : Measure ℕ} [IsProbabilityMeasure μ]
    (h : OffspringHyp μ) : pBr μ ≤ 1 := by
  have hp := p1_add_pBr h
  have hq := p1_nonnegProv μ
  linarith

/-- Local copy of the private lemma `geomY_prob` of `Analytic/FirstSplit2.lean`. -/
private lemma geomY_probProv (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) :
    IsProbabilityMeasure (geomY l (pBr μ)) := by
  have hp0 := pBr_pos h
  have hp1 := pBr_le_oneProv h
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
  rw [sub_sub_cancel, mul_inv_cancel₀ hp0.ne', ENNReal.ofReal_one]

/-- Local copy of the private support lemma for `geomY`. -/
private lemma ae_geomY_posProv (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) :
    ∀ᵐ y ∂geomY l (pBr μ), 0 < y ∧ y ≤ 1 := by
  rw [geomY, Measure.ae_sum_iff]
  intro g
  apply Filter.Eventually.filter_mono (Measure.ae_smul_measure_le _)
  refine (mem_ae_dirac_iff (s := Set.Ioc (0 : ℝ) 1) measurableSet_Ioc).2 ⟨?_, ?_⟩
  · exact zpow_pos (show 0 < l by positivity) (-((g : ℤ) + 1))
  · exact zpow_le_one_of_nonpos₀ hl.le (by omega)

private lemma integrable_geomY_powProv (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (n : ℕ) : Integrable (fun y => y ^ n) (geomY l (pBr μ)) := by
  letI := geomY_probProv μ h hl
  apply (integrable_const (1 : ℝ)).mono' (measurable_id.pow_const n).aestronglyMeasurable
  filter_upwards [ae_geomY_posProv μ h hl] with y hy
  change ‖y ^ n‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy.1.le _)]
  exact pow_le_one₀ hy.1.le hy.2

private lemma integrable_geomY_pow_logProv (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun y => y ^ n * Real.log y) (geomY l (pBr μ)) := by
  letI := geomY_probProv μ h hl
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_id.pow_const n).mul Real.measurable_log).aestronglyMeasurable
  filter_upwards [ae_geomY_posProv μ h hl] with y hy
  have hlog : Real.log y ≤ 0 := Real.log_nonpos hy.1.le hy.2
  have hpow : y ^ n ≤ y := pow_le_of_le_one hy.1.le hy.2 (by omega)
  have hmul : |Real.log y * y| < 1 := Real.abs_log_mul_self_lt y hy.1 hy.2
  change |y ^ n * Real.log y| ≤ 1
  rw [abs_mul, abs_of_nonneg (pow_nonneg hy.1.le _), abs_of_nonpos hlog]
  have hnonneg : 0 ≤ -Real.log y := neg_nonneg.mpr hlog
  calc
    y ^ n * -Real.log y ≤ y * -Real.log y :=
      mul_le_mul_of_nonneg_right hpow hnonneg
    _ = |Real.log y * y| := by rw [abs_mul, abs_of_nonpos hlog, abs_of_pos hy.1]; ring
    _ ≤ 1 := hmul.le

/-- Sum form of the weighted geometric logarithmic moment. -/
private lemma geomY_log_momentProv (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (n : ℕ) (hn : 1 ≤ n) :
    (∫ y, y ^ n * (-((l - 1) / Real.log l) * Real.log y) ∂geomY l (pBr μ)) =
      l * xS μ l * Acoef μ l n ^ 2 := by
  letI := geomY_probProv μ h hl
  have hInt : Integrable (fun y : ℝ => y ^ n * Real.log y) (geomY l (pBr μ)) :=
    integrable_geomY_pow_logProv μ h hl n hn
  have hser : (∫ y, y ^ n * Real.log y ∂geomY l (pBr μ)) =
      ∑' g : ℕ, pBr μ * (1 - pBr μ) ^ g *
        ((l ^ (-((g : ℤ) + 1))) ^ n * Real.log (l ^ (-((g : ℤ) + 1)))) := by
    unfold geomY
    rw [integral_sum_measure hInt]
    apply tsum_congr
    intro g
    rw [integral_smul_measure, integral_dirac]
    rw [ENNReal.toReal_ofReal (mul_nonneg (pBr_pos h).le
      (pow_nonneg (by linarith [pBr_le_oneProv h] : 0 ≤ 1 - pBr μ) _))]
    rfl
  have hq : p1 μ = 1 - pBr μ := by linarith [p1_add_pBr h]
  have hterm (g : ℕ) :
      pBr μ * (1 - pBr μ) ^ g *
          ((l ^ (-((g : ℤ) + 1))) ^ n * Real.log (l ^ (-((g : ℤ) + 1)))) =
        (-Real.log l) * ((g + 1 : ℝ) * p1 μ ^ g * pBr μ *
          l ^ (-((g : ℤ) + 1) * (n : ℤ))) := by
    rw [Real.log_zpow]
    have hpow : (l ^ (-((g : ℤ) + 1))) ^ n =
        l ^ (-((g : ℤ) + 1) * (n : ℤ)) := by rw [zpow_mul, zpow_natCast]
    rw [hpow, hq]
    push_cast
    ring
  have hGL := GL_moment h hl n hn
  have hla : 0 < l := by linarith
  have ha : 0 < l - 1 := by linarith
  have hlog : 0 < Real.log l := Real.log_pos hl
  have hrewrite : (fun y : ℝ => y ^ n * (-((l - 1) / Real.log l) * Real.log y)) =
      (fun y => ((l - 1) / Real.log l) * -(y ^ n * Real.log y)) := by
    funext y
    ring
  rw [hrewrite, integral_const_mul, integral_neg, hser]
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hfactor : (l - 1) / Real.log l * Real.log l = l - 1 := by
    field_simp [hlog.ne']
  calc
    (l - 1) / Real.log l * -(-Real.log l * ∑' g : ℕ,
        ((g + 1 : ℝ) * p1 μ ^ g * pBr μ * l ^ (-((g : ℤ) + 1) * (n : ℤ)))) =
      ((l - 1) / Real.log l * Real.log l) * ∑' g : ℕ,
        ((g + 1 : ℝ) * p1 μ ^ g * pBr μ * l ^ (-((g : ℤ) + 1) * (n : ℤ))) := by ring
    _ =
      (l - 1) * ∑' g : ℕ, (g + 1 : ℝ) * p1 μ ^ g * pBr μ *
        l ^ (-((g : ℤ) + 1) * (n : ℤ)) := by rw [hfactor]
    _ = l * ((l - 1) / l * ∑' g : ℕ, (g + 1 : ℝ) * p1 μ ^ g * pBr μ *
        l ^ (-((g : ℤ) + 1) * (n : ℤ))) := by
      have hf : l * ((l - 1) / l) = l - 1 := by field_simp [hla.ne']
      calc
        (l - 1) * ∑' g : ℕ, (g + 1 : ℝ) * p1 μ ^ g * pBr μ *
            l ^ (-((g : ℤ) + 1) * (n : ℤ)) =
          (l * ((l - 1) / l)) * ∑' g : ℕ, (g + 1 : ℝ) * p1 μ ^ g * pBr μ *
            l ^ (-((g : ℤ) + 1) * (n : ℤ)) := by rw [hf]
        _ = _ := by ring
    _ = l * (xS μ l * Acoef μ l n ^ 2) := by rw [hGL]
    _ = _ := by ring

private lemma iota_den_posProv (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) :
    0 < xS μ l + Qgeo l n := by
  have hp := pBr_pos h
  have ha : 0 < l - 1 := by linarith
  have hx : 0 < xS μ l := div_pos hp ha
  exact add_pos_of_pos_of_nonneg hx (Qgeo_nonneg (by linarith) n)

private lemma iota_posProv (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) :
    0 < iota μ l n := inv_pos.mpr (iota_den_posProv μ h hl n)

private lemma iota_recurrenceProv (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (n : ℕ) :
    l * iota μ l (n + 1) = (1 - p1 μ * iota μ l (n + 1)) * iota μ l n := by
  have hn := iota_den_posProv μ h hl n
  have hn1 := iota_den_posProv μ h hl (n + 1)
  have hQ : Qgeo l n * (l - 1) = l ^ n - 1 := geom_sum_mul_of_one_le hl.le n
  have hQ1 : Qgeo l (n + 1) = Qgeo l n + l ^ n := by
    simp [Qgeo, Finset.sum_range_succ]
  have hpq : p1 μ + pBr μ = 1 := p1_add_pBr h
  have ha : 0 < l - 1 := by linarith
  have hx : pBr μ = xS μ l * (l - 1) := by unfold xS; field_simp [ha.ne']
  unfold iota
  field_simp [hn.ne', hn1.ne']
  rw [hQ1]
  nlinarith

private lemma Acoef_sqProv (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ)
    (hn : 1 ≤ n) :
    l * Acoef μ l n ^ 2 = l ^ n * iota μ l n ^ 2 := by
  unfold Acoef
  have hk := kS_sq hl
  have hpow : (kS l ^ (n - 1)) ^ 2 = l ^ (n - 1) := by
    rw [← pow_mul, Nat.mul_comm (n - 1) 2, pow_mul, hk]
  rw [mul_pow, hpow]
  have hnp : l ^ (n - 1) * l = l ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  nlinarith

private lemma iota_prefixProv (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) :
    (l ^ n - p1 μ) * iota μ l n = l - 1 := by
  have hn := iota_den_posProv μ h hl n
  have hQ : Qgeo l n * (l - 1) = l ^ n - 1 := geom_sum_mul_of_one_le hl.le n
  have hpq : p1 μ + pBr μ = 1 := p1_add_pBr h
  have ha : 0 < l - 1 := by linarith
  have hx : pBr μ = xS μ l * (l - 1) := by unfold xS; field_simp [ha.ne']
  unfold iota
  field_simp [hn.ne']
  nlinarith

private lemma FJ_integrand_nonnegProv (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (j : ℕ) (T : Tree) (hW : 0 ≤ Wt l T) (hW1 : Wt l T ≤ 1) :
    0 ≤ p1 μ * l ^ (j + 1) * iota μ l (j + 1) * iota μ l (j + 2) +
      ((l - 1) / (l + 1) + p1 μ * iota μ l (j + 2)) * (1 - Wt l T) +
      (1 - Wt l T) ^ 2 / 2 := by
  have hp : 0 ≤ p1 μ := p1_nonnegProv μ
  have hi1 := (iota_posProv μ h hl (j + 1)).le
  have hi2 := (iota_posProv μ h hl (j + 2)).le
  have hl0 : 0 ≤ l := by linarith
  have hlin : 0 ≤ (l - 1) / (l + 1) := div_nonneg (by linarith) (by linarith)
  have hd : 0 ≤ 1 - Wt l T := sub_nonneg.mpr hW1
  positivity

/-- **Proposition 5.2, nonnegativity of the explicit rank coefficient.** -/
theorem FJ_nonneg (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) : 0 ≤ FJ μ l j := by
  letI := splitLaw_prob h
  have hk : 0 ≤ kS l ^ j := pow_nonneg (kS_pos hl).le _
  have hx : 0 ≤ xS μ l := (div_pos (pBr_pos h) (by linarith)).le
  have hi := (iota_posProv μ h hl (j + 1)).le
  apply mul_nonneg (mul_nonneg (mul_nonneg hk hx) hi)
  apply integral_nonneg_of_ae
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  exact mul_nonneg (pow_nonneg hT.1.le _)
    (FJ_integrand_nonnegProv μ h hl j T hT.1.le hT.2.le)

/-- The logarithmic form of the rank density after `phiResp_identity`. -/
private noncomputable def rankY (l : ℝ) (j : ℕ) (y : ℝ) : ℝ :=
  kS l ^ j * y ^ (j + 1) *
    (-((l - 1) / Real.log l) * Real.log y - l * (1 - y))

private lemma measurable_rankY (l : ℝ) (j : ℕ) : Measurable (rankY l j) := by
  unfold rankY
  fun_prop

private lemma rankY_eq_tree {l : ℝ} (hl : 1 < l) (j : ℕ) (T : Tree)
    (hb : escape l T ∈ Set.Ioo 0 1) :
    rankY l j (Yt l T) = (kS l * Yt l T) ^ j * (1 - Yt l T) ^ 2 *
      phiResp l (escape l T) := by
  have hid := phiResp_identity hl hb
  change (1 - Yt l T) ^ 2 * phiResp l (escape l T) =
    Yt l T * (-((l - 1) / Real.log l) * Real.log (Yt l T) -
      l * (1 - Yt l T)) at hid
  unfold rankY
  rw [mul_pow, pow_succ]
  calc
    kS l ^ j * (Yt l T ^ j * Yt l T) *
        (-((l - 1) / Real.log l) * Real.log (Yt l T) - l * (1 - Yt l T)) =
      kS l ^ j * Yt l T ^ j * ((1 - Yt l T) ^ 2 * phiResp l (escape l T)) := by
        rw [hid]
        ring
    _ = _ := by ring

private lemma integrable_rankY_tree (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) :
    Integrable (fun T => rankY l j (Yt l T)) (GW μ) := by
  have hEq : ∀ᵐ T ∂GW μ,
      (kS l * Yt l T) ^ j * (1 - Yt l T) ^ 2 * phiResp l (escape l T) =
        rankY l j (Yt l T) := by
    filter_upwards [ae_escape_mem_Ioo h (by linarith) hlm] with T hb
    exact (rankY_eq_tree hl j T hb).symm
  have hm : AEStronglyMeasurable
      (fun T => (kS l * Yt l T) ^ j * (1 - Yt l T) ^ 2 * phiResp l (escape l T))
      (GW μ) := by
    apply ((measurable_rankY l j).comp (measurable_Yt l)).aestronglyMeasurable.congr
    filter_upwards [hEq] with T hT
    exact hT.symm
  have hi : Integrable
      (fun T => (kS l * Yt l T) ^ j * (1 - Yt l T) ^ 2 * phiResp l (escape l T))
      (GW μ) := by
    apply ((integrable_resp h ⟨by linarith, hlm⟩).const_mul (kS l ^ j)).mono' hm
    filter_upwards [ae_regTree h, ae_escape_mem_Ioo h (by linarith) hlm] with T hT hb
    have hy := Yt_mem hl hb.1
    have hp0 : 0 ≤ phiResp l (escape l T) := phiResp_nonneg hl ⟨hb.1, hb.2.le⟩
    have hpr : phiResp l (escape l T) ≤ resp l T := phiResp_le_resp h hT hl hlm
    have hr : 0 ≤ resp l T := hp0.trans hpr
    have hu1 : 1 / l ≤ 1 := (div_le_one (by linarith)).mpr hl.le
    have hy1 : Yt l T ≤ 1 := hy.2.le.trans hu1
    have hd0 : 0 ≤ 1 - Yt l T := sub_nonneg.mpr hy1
    have hd1 : 1 - Yt l T ≤ 1 := by linarith [hy.1]
    have hyj0 : 0 ≤ Yt l T ^ j := pow_nonneg hy.1.le _
    have hyj1 : Yt l T ^ j ≤ 1 := pow_le_one₀ hy.1.le hy1
    have hs0 : 0 ≤ (1 - Yt l T) ^ 2 := sq_nonneg _
    have hs1 : (1 - Yt l T) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Yt l T)]
    have hk : 0 ≤ kS l ^ j := pow_nonneg (kS_pos hl).le _
    rw [mul_pow, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hk hyj0) hs0) hp0)]
    calc
      kS l ^ j * Yt l T ^ j * (1 - Yt l T) ^ 2 * phiResp l (escape l T) ≤
          kS l ^ j * 1 * 1 * resp l T := by gcongr
      _ = kS l ^ j * resp l T := by ring
  exact hi.congr hEq

private lemma integrable_rankY_Ylaw (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) : Integrable (rankY l j) (Ylaw μ l) := by
  unfold Ylaw
  apply (integrable_map_measure (measurable_rankY l j).aestronglyMeasurable
    (measurable_Yt l).aemeasurable).2
  exact integrable_rankY_tree μ h hl hlm j

private lemma phiRank_eq_rankY (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) :
    phiRank μ l j = ∫ y, rankY l j y ∂Ylaw μ l := by
  unfold phiRank
  calc
    (∫ T, (kS l * Yt l T) ^ j * (1 - Yt l T) ^ 2 * phiResp l (escape l T) ∂GW μ) =
        ∫ T, rankY l j (Yt l T) ∂GW μ := by
      apply integral_congr_ae
      filter_upwards [ae_escape_mem_Ioo h (by linarith) hlm] with T hb
      exact (rankY_eq_tree hl j T hb).symm
    _ = ∫ y, rankY l j y ∂Ylaw μ l := by
      unfold Ylaw
      rw [integral_map (measurable_Yt l).aemeasurable
        (measurable_rankY l j).aestronglyMeasurable]

private lemma integrable_rankY_prod (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) :
    Integrable (fun p : ℝ × Tree => rankY l j (p.1 * Wt l p.2))
      ((geomY l (pBr μ)).prod (splitLaw μ)) := by
  letI := splitLaw_prob h
  letI := geomY_probProv μ h hl
  have hmul : Measurable (fun q : ℝ × ℝ => q.1 * q.2) := by fun_prop
  have hprod : AEMeasurable (Prod.map id (Wt l))
      ((geomY l (pBr μ)).prod (splitLaw μ)) :=
    (measurable_id.prodMap (measurable_Wt l)).aemeasurable
  have hmeasure : (geomY l (pBr μ)).prod ((splitLaw μ).map (Wt l)) =
      ((geomY l (pBr μ)).prod (splitLaw μ)).map (Prod.map id (Wt l)) := by
    rw [← Measure.map_prod_map (geomY l (pBr μ)) (splitLaw μ) measurable_id
      (measurable_Wt l)]
    simp
  have hi := integrable_rankY_Ylaw μ h hl hlm j
  rw [Ylaw_eq_prod h hl hlm] at hi
  have hp : Integrable (fun q : ℝ × ℝ => rankY l j (q.1 * q.2))
      ((geomY l (pBr μ)).prod ((splitLaw μ).map (Wt l))) := by
    simpa only [Function.comp_def] using
      (integrable_map_measure (measurable_rankY l j).aestronglyMeasurable hmul.aemeasurable).1 hi
  rw [hmeasure] at hp
  have hp' := (integrable_map_measure
    (g := fun q : ℝ × ℝ => rankY l j (q.1 * q.2))
    (((measurable_rankY l j).comp hmul).aestronglyMeasurable) hprod).1 hp
  exact hp'

private lemma phiRank_eq_prod (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) :
    phiRank μ l j = ∫ p : ℝ × Tree, rankY l j (p.1 * Wt l p.2)
      ∂(geomY l (pBr μ)).prod (splitLaw μ) := by
  letI := splitLaw_prob h
  letI := geomY_probProv μ h hl
  have hmul : Measurable (fun q : ℝ × ℝ => q.1 * q.2) := by fun_prop
  have hprod : AEMeasurable (Prod.map id (Wt l))
      ((geomY l (pBr μ)).prod (splitLaw μ)) :=
    (measurable_id.prodMap (measurable_Wt l)).aemeasurable
  have hmeasure : (geomY l (pBr μ)).prod ((splitLaw μ).map (Wt l)) =
      ((geomY l (pBr μ)).prod (splitLaw μ)).map (Prod.map id (Wt l)) := by
    rw [← Measure.map_prod_map (geomY l (pBr μ)) (splitLaw μ) measurable_id
      (measurable_Wt l)]
    simp
  calc
    phiRank μ l j = ∫ y, rankY l j y ∂Ylaw μ l := phiRank_eq_rankY μ h hl hlm j
    _ = ∫ y, rankY l j y ∂((geomY l (pBr μ)).prod ((splitLaw μ).map (Wt l))).map
        (fun p => p.1 * p.2) := by rw [Ylaw_eq_prod h hl hlm]
    _ = ∫ q : ℝ × ℝ, rankY l j (q.1 * q.2)
        ∂(geomY l (pBr μ)).prod ((splitLaw μ).map (Wt l)) :=
      integral_map hmul.aemeasurable (measurable_rankY l j).aestronglyMeasurable
    _ = ∫ q : ℝ × ℝ, rankY l j (q.1 * q.2)
        ∂((geomY l (pBr μ)).prod (splitLaw μ)).map (Prod.map id (Wt l)) := by
      rw [← hmeasure]
    _ = ∫ p : ℝ × Tree, (fun q : ℝ × ℝ => rankY l j (q.1 * q.2))
        (Prod.map id (Wt l) p) ∂(geomY l (pBr μ)).prod (splitLaw μ) := by
      apply integral_map hprod
      exact ((measurable_rankY l j).comp hmul).aestronglyMeasurable
    _ = _ := rfl

private lemma integral_geom_rankY (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (j : ℕ) {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    (∫ L, rankY l j (L * w) ∂geomY l (pBr μ)) =
      kS l ^ j * xS μ l * iota μ l (j + 1) * w ^ (j + 1) *
        (l ^ (j + 1) * iota μ l (j + 1) - (l - 1) / Real.log l * Real.log w - l +
          (1 - p1 μ * iota μ l (j + 2)) * w) := by
  letI := geomY_probProv μ h hl
  let n := j + 1
  let d₀ := (l - 1) / Real.log l
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hn1 : n + 1 = j + 2 := by dsimp [n]
  have hpow := integrable_geomY_powProv μ h hl n
  have hnext : Integrable (fun y => y ^ (n + 1)) (geomY l (pBr μ)) :=
    integrable_geomY_powProv μ h hl (n + 1)
  have hlog : Integrable (fun y => y ^ n * Real.log y) (geomY l (pBr μ)) :=
    integrable_geomY_pow_logProv μ h hl n hn
  have hA : Integrable (fun y => y ^ n * (-d₀ * Real.log y)) (geomY l (pBr μ)) := by
    have heq : (fun y : ℝ => y ^ n * (-d₀ * Real.log y)) =
        (fun y => -d₀ * (y ^ n * Real.log y)) := by
      funext y
      ring
    rw [heq]
    exact hlog.const_mul (-d₀)
  have hB : Integrable (fun y => (-d₀ * Real.log w) * y ^ n) (geomY l (pBr μ)) :=
    hpow.const_mul _
  have hC : Integrable (fun y => (-l) * y ^ n) (geomY l (pBr μ)) := hpow.const_mul _
  have hD : Integrable (fun y => (l * w) * y ^ (n + 1)) (geomY l (pBr μ)) :=
    hnext.const_mul _
  have hrewrite : (fun L => rankY l j (L * w)) = fun L => kS l ^ j * w ^ n *
      (L ^ n * (-d₀ * Real.log L) + (-d₀ * Real.log w) * L ^ n +
        (-l) * L ^ n + (l * w) * L ^ (n + 1)) := by
    funext L
    by_cases hL : L = 0
    · subst L
      simp [rankY, n, pow_succ]
    · unfold rankY
      rw [Real.log_mul hL hw.ne', mul_pow, pow_succ]
      change kS l ^ j * (L ^ n * w ^ n) *
        (-d₀ * (Real.log L + Real.log w) - l * (1 - L * w)) = _
      ring
  have hAdd : (∫ L, L ^ n * (-d₀ * Real.log L) + (-d₀ * Real.log w) * L ^ n +
      (-l) * L ^ n + (l * w) * L ^ (n + 1) ∂geomY l (pBr μ)) =
      (∫ L, L ^ n * (-d₀ * Real.log L) ∂geomY l (pBr μ)) +
      (∫ L, (-d₀ * Real.log w) * L ^ n ∂geomY l (pBr μ)) +
      (∫ L, (-l) * L ^ n ∂geomY l (pBr μ)) +
      ∫ L, (l * w) * L ^ (n + 1) ∂geomY l (pBr μ) := by
    calc
      (∫ L, L ^ n * (-d₀ * Real.log L) + (-d₀ * Real.log w) * L ^ n +
          (-l) * L ^ n + (l * w) * L ^ (n + 1) ∂geomY l (pBr μ)) =
        (∫ L, L ^ n * (-d₀ * Real.log L) + (-d₀ * Real.log w) * L ^ n +
          (-l) * L ^ n ∂geomY l (pBr μ)) +
          ∫ L, (l * w) * L ^ (n + 1) ∂geomY l (pBr μ) :=
        integral_add ((hA.add hB).add hC) hD
      _ = ((∫ L, L ^ n * (-d₀ * Real.log L) ∂geomY l (pBr μ)) +
          (∫ L, (-d₀ * Real.log w) * L ^ n ∂geomY l (pBr μ))) +
          (∫ L, (-l) * L ^ n ∂geomY l (pBr μ)) +
          ∫ L, (l * w) * L ^ (n + 1) ∂geomY l (pBr μ) := by
        congr 1
        calc
          (∫ L, L ^ n * (-d₀ * Real.log L) + (-d₀ * Real.log w) * L ^ n +
              (-l) * L ^ n ∂geomY l (pBr μ)) =
            (∫ L, L ^ n * (-d₀ * Real.log L) + (-d₀ * Real.log w) * L ^ n
              ∂geomY l (pBr μ)) + ∫ L, (-l) * L ^ n ∂geomY l (pBr μ) :=
            integral_add (hA.add hB) hC
          _ = _ := by
            congr 1
            exact integral_add hA hB
  rw [hrewrite, integral_const_mul, hAdd,
    integral_const_mul, integral_const_mul, integral_const_mul]
  rw [geomY_log_momentProv μ h hl n hn, Llaw_moment h hl n,
    Llaw_moment h hl (n + 1)]
  have hAcoef : l * xS μ l * Acoef μ l n ^ 2 =
      xS μ l * iota μ l n * (l ^ n * iota μ l n) := by
    calc
      l * xS μ l * Acoef μ l n ^ 2 = xS μ l * (l * Acoef μ l n ^ 2) := by ring
      _ = xS μ l * (l ^ n * iota μ l n ^ 2) := by rw [Acoef_sqProv μ h hl n hn]
      _ = _ := by ring
  have hiratio : 1 - p1 μ * iota μ l (n + 1) =
      l * iota μ l (n + 1) / iota μ l n :=
    (eq_div_iff (iota_posProv μ h hl n).ne').2 (iota_recurrenceProv μ h hl n).symm
  rw [hAcoef, hiratio, hn1]
  dsimp only [n, d₀]
  field_simp [(iota_posProv μ h hl (j + 1)).ne']
  <;> ring

private lemma phiRank_eq_average (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) :
    phiRank μ l j = kS l ^ j * xS μ l * iota μ l (j + 1) *
      ∫ T, Wt l T ^ (j + 1) *
        (p1 μ * l ^ (j + 1) * iota μ l (j + 1) * iota μ l (j + 2) -
          (1 - p1 μ * iota μ l (j + 2)) * (1 - Wt l T) -
          (l - 1) / Real.log l * Real.log (Wt l T)) ∂splitLaw μ := by
  letI := splitLaw_prob h
  letI := geomY_probProv μ h hl
  rw [phiRank_eq_prod μ h hl hlm j,
    integral_prod_symm _ (integrable_rankY_prod μ h hl hlm j)]
  calc
    (∫ T, ∫ L, rankY l j (L * Wt l T) ∂geomY l (pBr μ) ∂splitLaw μ) =
        ∫ T, kS l ^ j * xS μ l * iota μ l (j + 1) * Wt l T ^ (j + 1) *
          (l ^ (j + 1) * iota μ l (j + 1) - (l - 1) / Real.log l * Real.log (Wt l T) -
            l + (1 - p1 μ * iota μ l (j + 2)) * Wt l T) ∂splitLaw μ := by
      apply integral_congr_ae
      filter_upwards [ae_Wt_mem h hl hlm] with T hT
      exact integral_geom_rankY μ h hl j hT.1 hT.2.le
    _ = ∫ T, kS l ^ j * xS μ l * iota μ l (j + 1) * Wt l T ^ (j + 1) *
        (p1 μ * l ^ (j + 1) * iota μ l (j + 1) * iota μ l (j + 2) -
          (1 - p1 μ * iota μ l (j + 2)) * (1 - Wt l T) -
          (l - 1) / Real.log l * Real.log (Wt l T)) ∂splitLaw μ := by
      apply integral_congr_ae
      filter_upwards with T
      have hr := iota_recurrenceProv μ h hl (j + 1)
      have hrN := congrArg (fun z : ℝ => l ^ (j + 1) * z) hr
      have hp := iota_prefixProv μ h hl (j + 2)
      rw [pow_succ] at hp
      linear_combination (kS l ^ j * xS μ l * iota μ l (j + 1) * Wt l T ^ (j + 1)) *
        (hp - hrN)
    _ = kS l ^ j * xS μ l * iota μ l (j + 1) *
        ∫ T, Wt l T ^ (j + 1) *
          (p1 μ * l ^ (j + 1) * iota μ l (j + 1) * iota μ l (j + 2) -
            (1 - p1 μ * iota μ l (j + 2)) * (1 - Wt l T) -
            (l - 1) / Real.log l * Real.log (Wt l T)) ∂splitLaw μ := by
      have hc : (fun T => kS l ^ j * xS μ l * iota μ l (j + 1) * Wt l T ^ (j + 1) *
          (p1 μ * l ^ (j + 1) * iota μ l (j + 1) * iota μ l (j + 2) -
            (1 - p1 μ * iota μ l (j + 2)) * (1 - Wt l T) -
            (l - 1) / Real.log l * Real.log (Wt l T))) =
        (fun T => (kS l ^ j * xS μ l * iota μ l (j + 1)) *
          (Wt l T ^ (j + 1) *
            (p1 μ * l ^ (j + 1) * iota μ l (j + 1) * iota μ l (j + 2) -
              (1 - p1 μ * iota μ l (j + 2)) * (1 - Wt l T) -
              (l - 1) / Real.log l * Real.log (Wt l T)))) := by
        funext T
        ring
      rw [hc, integral_const_mul]

private lemma log_le_sqrt_ratio {l : ℝ} (hl : 1 < l) :
    Real.log l ≤ (l - 1) / kS l := by
  let s := kS l
  let u := Real.log s
  let A := 1 + u + u ^ 2 / 2
  have hs0 : 0 < s := kS_pos hl
  have hs1 : 1 < s := one_lt_kS hl
  have hs2 : s ^ 2 = l := kS_sq hl
  have hu0 : 0 ≤ u := Real.log_nonneg hs1.le
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hAs : A ≤ Real.exp u := Real.quadratic_le_exp_of_nonneg hu0
  have hexp : Real.exp u = s := by dsimp [u]; exact Real.exp_log hs0
  rw [hexp] at hAs
  have hinv : s⁻¹ ≤ A⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hA0 hAs
  have htwo : 2 * u ≤ A - A⁻¹ := by
    have hid : A - A⁻¹ = (A ^ 2 - 1) / A := by field_simp [hA0.ne']
    rw [hid, le_div_iff₀ hA0]
    dsimp [A]
    nlinarith [sq_nonneg (u ^ 2)]
  have hlog : Real.log l = 2 * u := by
    dsimp [u, s]
    rw [kS, Real.log_sqrt (by linarith : 0 ≤ l)]
    ring
  calc
    Real.log l = 2 * u := hlog
    _ ≤ A - A⁻¹ := htwo
    _ ≤ s - s⁻¹ := sub_le_sub hAs hinv
    _ = (l - 1) / s := by field_simp [hs0.ne']; nlinarith

private lemma sqrt_ratio_bounds {l : ℝ} (hl : 1 < l) :
    1 ≤ (l - 1) / Real.log l ∧ 2 * l / (l + 1) ≤ (l - 1) / Real.log l := by
  have hlog : 0 < Real.log l := Real.log_pos hl
  have hs0 : 0 < kS l := kS_pos hl
  have hs1 : 1 < kS l := one_lt_kS hl
  have hs2 : kS l ^ 2 = l := kS_sq hl
  have hmul : kS l * Real.log l ≤ l - 1 := by
    have hb := mul_le_mul_of_nonneg_left (log_le_sqrt_ratio hl) hs0.le
    have hcancel : kS l * ((l - 1) / kS l) = l - 1 := by field_simp [hs0.ne']
    calc
      kS l * Real.log l ≤ kS l * ((l - 1) / kS l) := hb
      _ = l - 1 := hcancel
  have hsqrt : kS l ≤ (l - 1) / Real.log l := (le_div_iff₀ hlog).2 hmul
  refine ⟨hs1.le.trans hsqrt, ?_⟩
  refine (show 2 * l / (l + 1) ≤ kS l from ?_).trans hsqrt
  apply (div_le_iff₀ (by linarith : 0 < l + 1)).2
  have hid : kS l * (l + 1) - 2 * l = kS l * (kS l - 1) ^ 2 := by
    nlinarith [hs2]
  have hn : 0 ≤ kS l * (kS l - 1) ^ 2 :=
    mul_nonneg hs0.le (sq_nonneg _)
  nlinarith

private lemma neg_log_quadratic {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    (1 - w) + (1 - w) ^ 2 / 2 ≤ -Real.log w := by
  let X := 1 - w
  have hX0 : 0 ≤ X := sub_nonneg.mpr hw1
  have hz0 : 0 ≤ X / w := div_nonneg hX0 hw.le
  have hz := Real.le_log_one_add_of_nonneg hz0
  have hlog : 2 * (X / w) / (X / w + 2) ≤ -Real.log w := by
    calc
      2 * (X / w) / (X / w + 2) ≤ Real.log (1 + X / w) := hz
      _ = -Real.log w := by
        have heq : 1 + X / w = w⁻¹ := by dsimp [X]; field_simp [hw.ne']; ring
        rw [heq, Real.log_inv]
  have hratio : 2 * (X / w) / (X / w + 2) = 2 * X / (1 + w) := by
    field_simp [hw.ne']
    <;> ring
  have hXw : 0 < 1 + w := by linarith
  have hid : 2 * X / (1 + w) - (X + X ^ 2 / 2) = X ^ 3 / (2 * (1 + w)) := by
    field_simp [hXw.ne']
    ring
  have hn : 0 ≤ X ^ 3 / (2 * (1 + w)) := div_nonneg (pow_nonneg hX0 _) (by positivity)
  dsimp [X] at hlog hratio hid hn
  rw [hratio] at hlog
  linarith

private lemma integrable_FJ_avg (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) :
    Integrable (fun T => Wt l T ^ (j + 1) *
      (p1 μ * l ^ (j + 1) * iota μ l (j + 1) * iota μ l (j + 2) +
        ((l - 1) / (l + 1) + p1 μ * iota μ l (j + 2)) * (1 - Wt l T) +
        (1 - Wt l T) ^ 2 / 2)) (splitLaw μ) := by
  letI := splitLaw_prob h
  let A := p1 μ * l ^ (j + 1) * iota μ l (j + 1) * iota μ l (j + 2)
  let B := (l - 1) / (l + 1) + p1 μ * iota μ l (j + 2)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hp := p1_nonnegProv μ
    have hi₁ := (iota_posProv μ h hl (j + 1)).le
    have hi₂ := (iota_posProv μ h hl (j + 2)).le
    have hl0 : 0 ≤ l := by linarith
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    have h₁ := p1_nonnegProv μ
    have h₂ := (iota_posProv μ h hl (j + 2)).le
    have hl0 : 0 ≤ l := by linarith
    positivity
  have hm : AEStronglyMeasurable (fun T => Wt l T ^ (j + 1) *
      (A + B * (1 - Wt l T) + (1 - Wt l T) ^ 2 / 2)) (splitLaw μ) := by
    have hlin : Measurable (fun T => B * (1 - Wt l T)) :=
      measurable_const.mul (measurable_const.sub (measurable_Wt l))
    have hsq : Measurable (fun T => (1 - Wt l T) ^ 2 / 2) :=
      ((measurable_const.sub (measurable_Wt l)).pow_const 2).div_const 2
    exact ((measurable_Wt l).pow_const (j + 1) |>.mul
      ((measurable_const.add hlin).add hsq)).aestronglyMeasurable
  apply Integrable.of_bound hm (A + B + 1 / 2)
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  have hp : 0 ≤ Wt l T ^ (j + 1) := pow_nonneg hT.1.le _
  have hp1 : Wt l T ^ (j + 1) ≤ 1 := pow_le_one₀ hT.1.le hT.2.le
  have hd : 0 ≤ 1 - Wt l T := sub_nonneg.mpr hT.2.le
  have hd1 : 1 - Wt l T ≤ 1 := by linarith [hT.1]
  have hb0 : 0 ≤ A + B * (1 - Wt l T) + (1 - Wt l T) ^ 2 / 2 := by positivity
  have hb : A + B * (1 - Wt l T) + (1 - Wt l T) ^ 2 / 2 ≤ A + B + 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hd1 hB
    have hs : (1 - Wt l T) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Wt l T)]
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp hb0)]
  calc
    Wt l T ^ (j + 1) * (A + B * (1 - Wt l T) + (1 - Wt l T) ^ 2 / 2) ≤
        1 * (A + B + 1 / 2) := mul_le_mul hp1 hb hb0 zero_le_one
    _ = A + B + 1 / 2 := one_mul _

private lemma integrable_phi_avg (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) :
    Integrable (fun T => Wt l T ^ (j + 1) *
      (p1 μ * l ^ (j + 1) * iota μ l (j + 1) * iota μ l (j + 2) -
        (1 - p1 μ * iota μ l (j + 2)) * (1 - Wt l T) -
        (l - 1) / Real.log l * Real.log (Wt l T))) (splitLaw μ) := by
  letI := splitLaw_prob h
  letI := geomY_probProv μ h hl
  let C := kS l ^ j * xS μ l * iota μ l (j + 1)
  have hC : 0 < C := by
    dsimp [C]
    have hx : 0 < xS μ l := div_pos (pBr_pos h) (by linarith)
    have hk : 0 < kS l ^ j := pow_pos (kS_pos hl) _
    have hi := iota_posProv μ h hl (j + 1)
    positivity
  have hi := (integrable_rankY_prod μ h hl hlm j).integral_prod_right.const_mul C⁻¹
  apply hi.congr
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  rw [integral_geom_rankY μ h hl j hT.1 hT.2.le]
  change C⁻¹ * (C * Wt l T ^ (j + 1) *
    (l ^ (j + 1) * iota μ l (j + 1) - (l - 1) / Real.log l * Real.log (Wt l T) - l +
      (1 - p1 μ * iota μ l (j + 2)) * Wt l T)) = _
  have hcancel : C⁻¹ * (C * Wt l T ^ (j + 1)) = Wt l T ^ (j + 1) := by
    rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
  rw [← mul_assoc, hcancel]
  have hr := iota_recurrenceProv μ h hl (j + 1)
  have hrN := congrArg (fun z : ℝ => l ^ (j + 1) * z) hr
  have hp := iota_prefixProv μ h hl (j + 2)
  rw [pow_succ] at hp
  linear_combination Wt l T ^ (j + 1) * (hp - hrN)

/-- **Proposition 5.2, domination of the exact rank moment by the explicit
coefficient.** -/
theorem FJ_le_phiRank (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) : FJ μ l j ≤ phiRank μ l j := by
  letI := splitLaw_prob h
  rw [phiRank_eq_average μ h hl hlm j]
  unfold FJ
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (pow_nonneg (kS_pos hl).le _)
    (div_pos (pBr_pos h) (by linarith)).le) (iota_posProv μ h hl (j + 1)).le)
  apply integral_mono_ae (integrable_FJ_avg μ h hl hlm j) (integrable_phi_avg μ h hl hlm j)
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  have hlog := neg_log_quadratic hT.1 hT.2.le
  have hd0 := (sqrt_ratio_bounds hl).1
  have hd1 := (sqrt_ratio_bounds hl).2
  have hq : 0 ≤ p1 μ * iota μ l (j + 2) :=
    mul_nonneg (p1_nonnegProv μ) (iota_posProv μ h hl (j + 2)).le
  have hd : 0 ≤ 1 - Wt l T := sub_nonneg.mpr hT.2.le
  have hdnonneg : 0 ≤ (l - 1) / Real.log l := zero_le_one.trans hd0
  have hlin : (l - 1) / (l + 1) + p1 μ * iota μ l (j + 2) ≤
      (l - 1) / Real.log l - (1 - p1 μ * iota μ l (j + 2)) := by
    have hid : 2 * l / (l + 1) - 1 = (l - 1) / (l + 1) := by
      field_simp [(by linarith : l + 1 ≠ 0)]
      ring
    linarith
  have hquad : (1 - Wt l T) ^ 2 / 2 ≤
      (l - 1) / Real.log l * ((1 - Wt l T) ^ 2 / 2) := by
    have hs : 0 ≤ (1 - Wt l T) ^ 2 / 2 := by positivity
    nlinarith
  have hmain :
      ((l - 1) / (l + 1) + p1 μ * iota μ l (j + 2)) * (1 - Wt l T) +
        (1 - Wt l T) ^ 2 / 2 ≤
      -(1 - p1 μ * iota μ l (j + 2)) * (1 - Wt l T) -
        (l - 1) / Real.log l * Real.log (Wt l T) := by
    have hlin' := mul_le_mul_of_nonneg_right hlin hd
    calc
      ((l - 1) / (l + 1) + p1 μ * iota μ l (j + 2)) * (1 - Wt l T) +
          (1 - Wt l T) ^ 2 / 2 ≤
        ((l - 1) / Real.log l - (1 - p1 μ * iota μ l (j + 2))) * (1 - Wt l T) +
          (l - 1) / Real.log l * ((1 - Wt l T) ^ 2 / 2) := add_le_add hlin' hquad
      _ = (l - 1) / Real.log l * ((1 - Wt l T) + (1 - Wt l T) ^ 2 / 2) -
          (1 - p1 μ * iota μ l (j + 2)) * (1 - Wt l T) := by ring
      _ ≤ (l - 1) / Real.log l * (-Real.log (Wt l T)) -
          (1 - p1 μ * iota μ l (j + 2)) * (1 - Wt l T) := by
        nlinarith [mul_le_mul_of_nonneg_left hlog hdnonneg]
      _ = _ := by ring
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hT.1.le _)
  nlinarith [hmain]

private lemma muJ_norm_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y ∈ Set.Ioo 0 (1 / l), ‖f y‖ ≤ C) (j : ℕ) :
    ‖muJ μ l j f‖ ≤ C * (kS l)⁻¹ ^ j := by
  let r := (kS l)⁻¹
  have hr : 0 ≤ r := inv_nonneg.mpr (kS_pos hl).le
  have hY : ∀ᵐ T ∂GW μ, Yt l T ∈ Set.Ioo 0 (1 / l) := by
    filter_upwards [ae_escape_mem_Ioo h (by linarith) hlm] with T hb
    exact Yt_mem hl hb.1
  have hpoint : ∀ᵐ T ∂GW μ, ‖(kS l * Yt l T) ^ j * f (Yt l T)‖ ≤ C * r ^ j := by
    filter_upwards [hY] with T hy
    have hk0 : 0 ≤ kS l * Yt l T := mul_nonneg (kS_pos hl).le hy.1.le
    have hk : kS l * Yt l T ≤ r := by
      have hh := mul_le_mul_of_nonneg_left hy.2.le (kS_pos hl).le
      have hid : kS l * (1 / l) = r := by
        dsimp [r]
        field_simp [(kS_pos hl).ne', (by linarith : l ≠ 0)]
        nlinarith [kS_sq hl]
      exact hh.trans_eq hid
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hk0]
    simpa [mul_comm] using mul_le_mul (pow_le_pow_left₀ hk0 hk j) (hC _ hy)
      (norm_nonneg _) (pow_nonneg hr _)
  have hm : AEStronglyMeasurable (fun T => (kS l * Yt l T) ^ j * f (Yt l T)) (GW μ) := by
    exact (((measurable_const.mul (measurable_Yt l)).pow_const j).mul
      (hf.measurable.comp (measurable_Yt l))).aestronglyMeasurable
  have hi : Integrable (fun T => (kS l * Yt l T) ^ j * f (Yt l T)) (GW μ) :=
    Integrable.of_bound hm (C * r ^ j) hpoint
  calc
    ‖muJ μ l j f‖ = ‖∫ T, (kS l * Yt l T) ^ j * f (Yt l T) ∂GW μ‖ := rfl
    _ ≤ ∫ T, ‖(kS l * Yt l T) ^ j * f (Yt l T)‖ ∂GW μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _T : Tree, C * r ^ j ∂GW μ := integral_mono_ae hi.norm (integrable_const _) hpoint
    _ = C * r ^ j := by simp

private lemma summable_static_rank (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (θ : ℝ) :
    Summable (fun j : ℕ => (j + 1 : ℝ) *
      (PJ μ l j * muJ μ l j (gθ l (rr μ l) θ))) := by
  have hg : Continuous (gθ l (rr μ l) θ) := by unfold gθ; fun_prop
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) (1 / l)) hg.continuousOn
  have hCg0 : 0 ≤ Cg := by
    exact (norm_nonneg (gθ l (rr μ l) θ 0)).trans
      (hCg 0 ⟨le_rfl, div_nonneg (by linarith) (by linarith)⟩)
  have hP := muJ_norm_le μ h hl hlm (f := fun y => y * (1 - y)) (by fun_prop)
    zero_le_one (fun y hy => by
      have hy1 : y ≤ 1 := hy.2.le.trans ((div_le_one (by linarith)).mpr hl.le)
      rw [Real.norm_of_nonneg (mul_nonneg hy.1.le (sub_nonneg.mpr hy1))]
      calc
        y * (1 - y) ≤ 1 * (1 - y) := mul_le_mul_of_nonneg_right hy1 (sub_nonneg.mpr hy1)
        _ ≤ 1 := by simp only [one_mul]; linarith [hy.1]) 
  have hG := muJ_norm_le μ h hl hlm hg hCg0 (fun y hy =>
    hCg y ⟨hy.1.le, hy.2.le⟩)
  have hP' (j : ℕ) : ‖PJ μ l j‖ ≤ 1 * (kS l)⁻¹ ^ j := by
    unfold PJ
    exact hP j
  let C : ℝ := Cg
  have hnorm : ‖(l : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (by linarith : 0 ≤ l))]
    exact inv_lt_one_of_one_lt₀ hl
  have hbase : Summable (fun j : ℕ => (j + 1 : ℝ) * (l⁻¹) ^ j) := by
    simpa using (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm)
  apply (hbase.mul_left C).of_norm_bounded
  intro j
  have hPj := hP j
  have hGj := hG j
  have hk : (kS l)⁻¹ ^ j * (kS l)⁻¹ ^ j = (l⁻¹) ^ j := by
    rw [← mul_pow, ← mul_inv, show kS l * kS l = l by nlinarith [kS_sq hl]]
  have hn : ‖(j + 1 : ℝ) * (PJ μ l j * muJ μ l j (gθ l (rr μ l) θ))‖ ≤
      (j + 1 : ℝ) * (C * (l⁻¹) ^ j) := by
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ j + 1)]
    have hprod := mul_le_mul (hP' j) hGj (norm_nonneg _) (mul_nonneg zero_le_one (pow_nonneg
      (inv_nonneg.mpr (kS_pos hl).le) _))
    dsimp [C]
    calc
      (j + 1 : ℝ) * (‖PJ μ l j‖ * ‖muJ μ l j (gθ l (rr μ l) θ)‖) ≤
          (j + 1 : ℝ) * ((1 * (kS l)⁻¹ ^ j) * (Cg * (kS l)⁻¹ ^ j)) := by gcongr
      _ = (j + 1 : ℝ) * (Cg * ((kS l)⁻¹ ^ j * (kS l)⁻¹ ^ j)) := by ring
      _ = (j + 1 : ℝ) * (Cg * (l⁻¹) ^ j) := by rw [hk]
  convert hn using 1 <;> ring

/-- **Proposition 5.2** (`prop:ward-ranks`), Ward's inequality with the explicit
coefficient `FJ`. -/
theorem ward_ranks (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {θ : ℝ} (hθ : Admissible μ l θ) :
    Summable (wardTerm μ l θ) ∧ ∑' j, wardTerm μ l θ j ≤ cost μ l := by
  obtain ⟨horig, hbound⟩ := cost_ge_rank_series μ h hl hlm hθ
  let S : ℕ → ℝ := fun j => (j + 1 : ℝ) *
    (PJ μ l j * muJ μ l j (gθ l (rr μ l) θ))
  let R : ℕ → ℝ := fun j => (j + 1 : ℝ) * (2 * phiRank μ l j * muJ μ l j (fθ l (rr μ l) θ))
  let RF : ℕ → ℝ := fun j => (j + 1 : ℝ) * (2 * FJ μ l j * muJ μ l j (fθ l (rr μ l) θ))
  have hS : Summable S := by
    apply (summable_static_rank μ h hl hlm θ).congr
    intro j
    dsimp [S]
  have hR : Summable R := by
    have hs := horig.sub hS
    apply hs.congr
    intro j
    dsimp [S, R]
    ring
  have hRF : Summable RF := by
    apply hR.of_norm_bounded
    intro j
    have hf := muJ_fθ_nonneg μ h hl hlm hθ j
    have hF0 := FJ_nonneg μ h hl hlm j
    have hFle := FJ_le_phiRank μ h hl hlm j
    have hp0 : 0 ≤ phiRank μ l j := hF0.trans hFle
    have hRF0 : 0 ≤ RF j := by dsimp [RF]; positivity
    have hR0 : 0 ≤ R j := by dsimp [R]; positivity
    rw [Real.norm_of_nonneg hRF0]
    dsimp [RF, R]
    have hd : 0 ≤ 2 * (phiRank μ l j - FJ μ l j) * muJ μ l j (fθ l (rr μ l) θ) := by
      exact mul_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hFle)) hf
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ j + 1 by positivity) hd]
  have hward : Summable (wardTerm μ l θ) := by
    apply (hS.add hRF).congr
    intro j
    dsimp [wardTerm, S, RF]
    ring
  refine ⟨hward, ?_⟩
  calc
    ∑' j : ℕ, wardTerm μ l θ j ≤ ∑' j : ℕ, (S j + R j) := by
      apply hward.tsum_le_tsum _ (hS.add hR)
      intro j
      have hf := muJ_fθ_nonneg μ h hl hlm hθ j
      have hFle := FJ_le_phiRank μ h hl hlm j
      dsimp [wardTerm, S, R]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ j + 1 by positivity)
        (mul_nonneg (sub_nonneg.mpr hFle) hf)]
    _ = ∑' j : ℕ, (j + 1 : ℝ) *
        (PJ μ l j * muJ μ l j (gθ l (rr μ l) θ) +
          2 * phiRank μ l j * muJ μ l j (fθ l (rr μ l) θ)) := by
      apply tsum_congr
      intro j
      dsimp [S, R]
      ring
    _ ≤ cost μ l := hbound

end LPPMonotonicityProof.Analytic
