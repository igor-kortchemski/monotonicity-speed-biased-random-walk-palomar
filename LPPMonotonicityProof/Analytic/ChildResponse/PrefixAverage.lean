module

public import LPPMonotonicityProof.Analytic.ChildResponse.ChildMoment

/-!
# Averaging one child response over the unary prefix

This module averages the two terms of one child's response over the geometric
unary prefix of Lemma 4.1 (`lem:prefix-terminal`), giving
`E[Y^(n-1) (response of Y)] = x (ιₙ Bₙ + Aₙ² ηₙ)` for the child-response recursion in
the proof of Lemma 4.5 (`lem:scaled-two-children`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem measurable_prefixResponse_uncurry (l : ℝ) (n : ℕ) :
    Measurable (Function.uncurry (childPrefixResponse l n)) := by
  apply measurable_from_prod_countable_right
  intro g
  change Measurable (childPrefixResponse l n g)
  unfold childPrefixResponse
  exact ((measurable_const.mul ((measurable_Wt l).pow_const (n - 1))).mul
    (measurable_Wresp l))

private theorem measurable_prefixEscape_uncurry (l : ℝ) (n : ℕ) :
    Measurable (Function.uncurry (childPrefixEscape l n)) := by
  apply measurable_from_prod_countable_right
  intro g
  change Measurable (childPrefixEscape l n g)
  unfold childPrefixEscape
  exact ((measurable_const.mul measurable_const).mul ((measurable_Wt l).pow_const n))

private lemma geomY_probability_prefix (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) :
    IsProbabilityMeasure (geomY l (pBr μ)) := by
  have hp0 := pBr_pos h
  have hp1 := pBr_le_one' h
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

private lemma ae_geomY_mem_prefix (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) :
    ∀ᵐ y ∂geomY l (pBr μ), y ∈ Set.Icc (0 : ℝ) 1 := by
  rw [geomY, Measure.ae_sum_iff]
  intro g
  apply Filter.Eventually.filter_mono (Measure.ae_smul_measure_le _)
  refine (mem_ae_dirac_iff (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc).2 ⟨?_, ?_⟩
  · exact (zpow_pos (show 0 < l by positivity) (-((g : ℤ) + 1))).le
  · exact zpow_le_one_of_nonpos₀ hl.le (by omega)

private lemma geomY_moment_series_prefix (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (n : ℕ) : (∫ y, y ^ n ∂geomY l (pBr μ)) =
      ∑' g : ℕ, pBr μ * (1 - pBr μ) ^ g * (l ^ (-((g : ℤ) + 1))) ^ n := by
  have hp := pBr_pos h
  have hp1 := pBr_le_one' h
  have hr0 : 0 ≤ 1 - pBr μ := by linarith
  letI := geomY_probability_prefix h hl
  have hInt : Integrable (fun y : ℝ => y ^ n) (geomY l (pBr μ)) := by
    apply (integrable_const (1 : ℝ)).mono' (measurable_id.pow_const n).aestronglyMeasurable
    filter_upwards [ae_geomY_mem_prefix h hl] with y hy
    simp only [id_eq, Real.norm_eq_abs]
    rw [abs_of_nonneg (pow_nonneg hy.1 _)]
    exact pow_le_one₀ hy.1 hy.2
  unfold geomY
  rw [integral_sum_measure hInt]
  apply tsum_congr
  intro g
  rw [integral_smul_measure, integral_dirac]
  rw [ENNReal.toReal_ofReal (mul_nonneg hp.le (pow_nonneg hr0 _))]
  rfl

-- The two global measurability/integrability obligations are elaboration-heavy.
set_option maxHeartbeats 800000 in
private theorem prefix_integrability (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun T => childPrefixResponse l n (Gt T) (splitTree T)) (GW μ) ∧
      Integrable (fun T => childPrefixEscape l n (Gt T) (splitTree T)) (GW μ) := by
  have hsum : Integrable (fun T => childPrefixResponse l n (Gt T) (splitTree T) +
      childPrefixEscape l n (Gt T) (splitTree T)) (GW μ) := by
    apply (integrable_childTerm h hl hlm n).congr
    filter_upwards [ae_regTree h, ae_split_degree h] with T hT hs
    exact childTerm_eq_prefix h hT hl hlm hs n hn
  have hGt : Measurable (Gt : Tree → ℕ) := measurable_prefixLen.add_const 1
  have hmr : AEStronglyMeasurable (fun T => childPrefixResponse l n (Gt T) (splitTree T))
      (GW μ) := ((measurable_prefixResponse_uncurry l n).comp
    (hGt.prodMk measurable_splitTree)).aestronglyMeasurable
  have hme : AEStronglyMeasurable (fun T => childPrefixEscape l n (Gt T) (splitTree T))
      (GW μ) := ((measurable_prefixEscape_uncurry l n).comp
    (hGt.prodMk measurable_splitTree)).aestronglyMeasurable
  have hnonneg : ∀ᵐ T ∂GW μ, 0 ≤ childPrefixResponse l n (Gt T) (splitTree T) ∧
      0 ≤ childPrefixEscape l n (Gt T) (splitTree T) := by
    filter_upwards [ae_regTree h, ae_split_degree h] with T hT hs
    have hreg := regTree_splitTree hT
    have hW := (Wt_mem_Icc' hl (splitTree T)).1
    have hr := Wresp_nonneg hreg h hl hlm
    have hL : 0 ≤ l ^ (-(Gt T : ℤ)) := (zpow_pos (by positivity) _).le
    constructor
    · exact mul_nonneg (mul_nonneg (pow_nonneg hL _) (pow_nonneg hW _)) hr
    · exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (by linarith) (by positivity))
      (Nat.cast_nonneg _)) (pow_nonneg hL _)) (pow_nonneg hW _)
  refine ⟨hsum.mono' hmr ?_, hsum.mono' hme ?_⟩
  · filter_upwards [hnonneg] with T hT
    rw [Real.norm_of_nonneg hT.1]
    linarith
  · filter_upwards [hnonneg] with T hT
    rw [Real.norm_of_nonneg hT.2]
    linarith

private theorem integral_prefixResponse_series (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ T, childPrefixResponse l n (Gt T) (splitTree T) ∂GW μ) =
      ∑' g : ℕ, (p1 μ ^ g * pBr μ) *
        ∫ T, childPrefixResponse l n (g + 1) T ∂splitLaw μ :=
  integral_firstSplit h (measurable_prefixResponse_uncurry l n) (prefix_integrability h hl hlm n hn).1

private theorem integral_prefixEscape_series (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ T, childPrefixEscape l n (Gt T) (splitTree T) ∂GW μ) =
      ∑' g : ℕ, (p1 μ ^ g * pBr μ) *
        ∫ T, childPrefixEscape l n (g + 1) T ∂splitLaw μ :=
  integral_firstSplit h (measurable_prefixEscape_uncurry l n) (prefix_integrability h hl hlm n hn).2

/-- The response part of one child's average. -/
theorem integral_prefixResponse (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ T, childPrefixResponse l n (Gt T) (splitTree T) ∂GW μ) =
      xS μ l * iota μ l n * BnMeasurable μ l n := by
  rw [integral_prefixResponse_series h hl hlm n hn]
  have hpq : p1 μ = 1 - pBr μ := by linarith [p1_add_pBr h]
  calc
    _ = ∑' g : ℕ, (pBr μ * (1 - pBr μ) ^ g *
        (l ^ (-((g : ℤ) + 1))) ^ n) * BnMeasurable μ l n := by
      apply tsum_congr
      intro g
      unfold childPrefixResponse BnMeasurable
      have hg : -((g + 1 : ℕ) : ℤ) = -((g : ℤ) + 1) := by push_cast; ring
      rw [hg]
      simp only [hpq, mul_assoc]
      rw [integral_const_mul]
      ring
    _ = (∑' g : ℕ, pBr μ * (1 - pBr μ) ^ g *
        (l ^ (-((g : ℤ) + 1))) ^ n) * BnMeasurable μ l n := by rw [tsum_mul_right]
    _ = _ := by rw [← geomY_moment_series_prefix h hl n, Llaw_moment h hl n]

/-- The prefix-length response part of one child's average. -/
theorem integral_prefixEscape (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ T, childPrefixEscape l n (Gt T) (splitTree T) ∂GW μ) =
      xS μ l * Acoef μ l n ^ 2 * etaW μ l n := by
  rw [integral_prefixEscape_series h hl hlm n hn]
  have hpq : p1 μ = 1 - pBr μ := by linarith [p1_add_pBr h]
  calc
    _ = (∑' g : ℕ, (g + 1) * p1 μ ^ g * pBr μ *
        l ^ (-((g : ℤ) + 1) * (n : ℤ))) * ((l - 1) / l) * etaW μ l n := by
      rw [← tsum_mul_right, ← tsum_mul_right]
      apply tsum_congr
      intro g
      have hg : -((g + 1 : ℕ) : ℤ) = -((g : ℤ) + 1) := by push_cast; ring
      have hpow : l ^ (-((g : ℤ) + 1) * (n : ℤ)) =
          (l ^ (-((g : ℤ) + 1))) ^ n := by rw [zpow_mul, zpow_natCast]
      unfold childPrefixEscape etaW
      rw [hg, hpow]
      simp only [Nat.cast_add, Nat.cast_one, mul_assoc]
      rw [integral_const_mul, integral_const_mul, integral_const_mul]
      ring
    _ = ((l - 1) / l * ∑' g : ℕ, (g + 1) * p1 μ ^ g * pBr μ *
        l ^ (-((g : ℤ) + 1) * (n : ℤ))) * etaW μ l n := by ring
    _ = _ := by rw [GL_moment h hl n hn]

/-- The child-response recursion averaged over one child: the exact two-term identity. -/
theorem integral_childTerm_eq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ T, childTerm l n T ∂GW μ) =
      xS μ l * (iota μ l n * BnMeasurable μ l n + Acoef μ l n ^ 2 * etaW μ l n) := by
  have hi := prefix_integrability h hl hlm n hn
  calc
    _ = ∫ T, (childPrefixResponse l n (Gt T) (splitTree T) +
        childPrefixEscape l n (Gt T) (splitTree T)) ∂GW μ := by
      apply integral_congr_ae
      filter_upwards [ae_regTree h, ae_split_degree h] with T hT hs
      exact childTerm_eq_prefix h hT hl hlm hs n hn
    _ = (∫ T, childPrefixResponse l n (Gt T) (splitTree T) ∂GW μ) +
        ∫ T, childPrefixEscape l n (Gt T) (splitTree T) ∂GW μ := integral_add hi.1 hi.2
    _ = _ := by
      rw [integral_prefixResponse h hl hlm n hn, integral_prefixEscape h hl hlm n hn]
      ring

end LPPMonotonicityProof.Analytic
