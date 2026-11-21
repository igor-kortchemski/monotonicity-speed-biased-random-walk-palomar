module

public import LPPMonotonicityProof.Analytic.BelowOne2
public import LPPMonotonicityProof.Analytic.HalfResponse
public import LPPMonotonicityProof.Analytic.RegularityExport
import Mathlib.Tactic.FunProp

/-!
# Strict negativity of the speed derivative at bias at most one

This module proves Theorem 2.7 (`thm:below-one`) for the speed `Speed.speedValue`,
the almost-sure limit of `|X_n|/n` of Theorem 2.2 (`thm:speed-formula`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

private theorem pol_nonneg_below_one {l c b : ℝ} (hl1 : l ≤ 1) (hc : 0 ≤ c)
    (hb : b ∈ Set.Ioc 0 1) (hbl : 1 - l ≤ b) : 0 ≤ Pol l c b := by
  rw [show Pol l c b = b * (b - (1 - l)) + (1 - l) * c * (1 - b) by
    unfold Pol
    ring]
  exact add_nonneg (mul_nonneg hb.1.le (sub_nonneg.mpr hbl))
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hl1) hc) (sub_nonneg.mpr hb.2))

private theorem escape_ratio_monotone_below_one {l y : ℝ} (hl : 0 < l)
    (hy : y ∈ Set.Ioc 0 1) (hyl : 1 - l ≤ y) :
    MonotoneOn (fun b => b / DfunProv l b y) (Set.Ioc 0 1 ∩ Set.Ici (1 - l)) := by
  have hD {b : ℝ} (hb : b ∈ Set.Ioc 0 1 ∩ Set.Ici (1 - l)) :
      0 < DfunProv l b y := by
    have hbound := (Dfun_bounds hl hb.1 hy (fun _ => ⟨hb.2, hyl⟩)).1
    exact (mul_pos (lt_min zero_lt_one hl) (hb.1.1.trans_le (le_max_left _ _))).trans_le hbound
  intro x hx z hz hxz
  apply (div_le_div_iff₀ (hD hx) (hD hz)).2
  calc
    x * DfunProv l z y ≤ x * DfunProv l z y + (z - x) * (y - (1 - l)) :=
      le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hxz) (sub_nonneg.mpr hyl))
    _ = z * DfunProv l x y := by unfold DfunProv; ring

private theorem kernel_gap_pos {c k₀ k₁ A : ℝ} (hc : 0 ≤ c)
    (hcA : c < A⁻¹) (hk₁ : 0 < k₁) (hk₀ : k₀ ≤ k₁ * A) :
    0 < k₁ - c * k₀ := by
  have hA := inv_pos.mp (hc.trans_lt hcA)
  have hcA' : c * A < 1 := by
    apply (lt_div_iff₀ hA).mp
    rwa [one_div]
  apply sub_pos.mpr
  calc
    c * k₀ ≤ c * (k₁ * A) := mul_le_mul_of_nonneg_left hk₀ hc
    _ = k₁ * (c * A) := by ring
    _ < k₁ * 1 := mul_lt_mul_of_pos_left hcA' hk₁
    _ = k₁ := mul_one _

variable {μ : Measure ℕ}

private theorem escape_mem_below_one {T : Tree} (hT : RegTree μ T)
    {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) (hl1 : l ≤ 1) :
    escape l T ∈ Set.Ioc 0 1 ∩ Set.Ici (1 - l) := by
  have hb := escape_mem_Ioc_of_regTree hT hl
  refine ⟨hb, ?_⟩
  rcases hl1.lt_or_eq with hlt | rfl
  · exact escape_ge hl.1 hlt T (fun v hv => hT.1.1 v hv)
  · simpa only [Set.mem_Ici, sub_self] using hb.1.le

variable [IsProbabilityMeasure μ]

private theorem K0_le_K1_mul_inv_escape (h : OffspringHyp μ)
    {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) (hl1 : l ≤ 1)
    (hiInv : Integrable (fun T => (escape l T)⁻¹) (GW μ)) :
    K0 μ l ≤ K1 μ l * ∫ T, (escape l T)⁻¹ ∂GW μ := by
  let F : Tree × Tree → ℝ := fun p => escape l p.1 / DfunProv l (escape l p.1) (escape l p.2)
  let G : Tree × Tree → ℝ := fun p => 1 / DfunProv l (escape l p.1) (escape l p.2)
  have hiG : Integrable G ((GW μ).prod (GW μ)) := integrable_inv_D h hl
  have hiF : Integrable F ((GW μ).prod (GW μ)) := by
    have he := measurable_escape l
    have hm : Measurable F := by
      unfold F DfunProv
      fun_prop
    apply hiG.mono' hm.aestronglyMeasurable
    have hpair : ∀ᵐ p : Tree × Tree ∂(GW μ).prod (GW μ), RegTree μ p.1 ∧ RegTree μ p.2 :=
      (Measure.quasiMeasurePreserving_fst.ae (ae_regTree h)).and
        (Measure.quasiMeasurePreserving_snd.ae (ae_regTree h))
    filter_upwards [hpair] with p hp
    have hb := escape_mem_Ioc_of_regTree hp.1 hl
    have hD := DfunProv_pos_of_regTrees hp.1 hp.2 hl
    dsimp only [F, G]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hb.1.le hD.le)]
    exact div_le_div_of_nonneg_right hb.2 hD.le
  have hs : ∀ᵐ T ∂GW μ, escape l T ∈ Set.Ioc 0 1 ∩ Set.Ici (1 - l) :=
    (ae_regTree h).mono fun _ hT => escape_mem_below_one hT hl hl1
  change (∫ p, G p ∂(GW μ).prod (GW μ)) ≤
    (∫ p, F p ∂(GW μ).prod (GW μ)) * ∫ T, (escape l T)⁻¹ ∂GW μ
  rw [integral_prod_symm G hiG, integral_prod_symm F hiF, ← integral_mul_const]
  apply integral_mono_ae hiG.integral_prod_right (hiF.integral_prod_right.mul_const _)
  filter_upwards [hs, hiF.prod_left_ae, hiG.prod_left_ae] with T' hT' hF hG
  have heq : (fun T => F (T, T') * (escape l T)⁻¹) =ᵐ[GW μ] fun T => G (T, T') := by
    filter_upwards [hs] with T hT
    dsimp only [F, G]
    rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hT.1.1.ne', one_mul, one_div]
  have hc := integral_mul_le_of_monotone_antitone
    (f := fun b => b / DfunProv l b (escape l T')) (g := fun b : ℝ => b⁻¹) _ hs
    (escape_ratio_monotone_below_one hl.1 hT'.1 hT'.2)
    (fun _ hb _ hc hbc => (inv_le_inv₀ hc.1.1 hb.1.1).2 hbc)
    hF hiInv (hG.congr heq.symm)
  exact (integral_congr_ae heq).ge.trans hc

private theorem K1_sub_speed_mul_K0_pos (h : OffspringHyp μ)
    {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) (hl1 : l ≤ 1) :
    0 < K1 μ l - speedValue μ l * K0 μ l := by
  have hv : 0 < speedValue μ l := speedValue_pos μ h l ⟨hl.1.le, hl.2⟩
  have hvInv : speedValue μ l < (∫ T, (escape l T)⁻¹ ∂GW μ)⁻¹ :=
    ((speed_le_mean_drift h hl.1 hl1).trans_lt (mean_drift_lt h hl.1 hl1)).trans_le
      (one_sub_le_inv_mean_inv_escape h hl.1 hl1)
  have hUn : 0 ≤ invMean μ :=
    (div_nonneg zero_le_one (zero_lt_one.trans (one_lt_mean_of_hyp h)).le).trans
      (invMean_bounds h).1
  have hU : l * invMean μ < 1 := by
    calc
      l * invMean μ ≤ 1 * invMean μ := mul_le_mul_of_nonneg_right hl1 hUn
      _ = invMean μ := one_mul _
      _ < 1 := (invMean_bounds h).2
  exact kernel_gap_pos hv.le hvInv (K1_pos h hl)
    (K0_le_K1_mul_inv_escape h hl hl1 (integrable_inv_escape h hl.1 hU).2)

private theorem half_response_le_cost (h : OffspringHyp μ)
    {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) (hl1 : l ≤ 1) :
    K1 μ l - speedValue μ l * K0 μ l ≤ cost μ l := by
  have hv := (speedValue_pos μ h l ⟨hl.1.le, hl.2⟩).le
  have hGam (b : ℝ) : 0 ≤ Gam μ l b := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_regTree h] with T hT
    have hb := escape_mem_below_one hT hl hl1
    exact div_nonneg (pol_nonneg_below_one hl1 hv hb.1 hb.2) (sq_nonneg _)
  have hmeas : Measurable (fun T => Gam μ l (escape l T)) := by
    have he := measurable_escape l
    have hm : Measurable (fun p : Tree × Tree => Pol l (speedValueProv μ l) (escape l p.2) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2) := by
      unfold Pol DfunProv
      fun_prop
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := GW μ)).measurable
  have hresp := (integrable_resp_Gam h hl).const_mul 2
  have hle : ∀ᵐ T ∂GW μ, (1 - escape l T) * Gam μ l (escape l T) ≤
      2 * (resp l T * Gam μ l (escape l T)) := by
    filter_upwards [ae_regTree h] with T hT
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (two_resp_ge hT hl hl1) (hGam _)
  have hi : Integrable (fun T => (1 - escape l T) * Gam μ l (escape l T)) (GW μ) := by
    apply hresp.mono' ((measurable_const.sub (measurable_escape l)).mul hmeas).aestronglyMeasurable
    filter_upwards [hle] with T hT
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hT
    · exact mul_nonneg (sub_nonneg.mpr (escape_mem_Icc hl.1 T).2) (hGam _)
  have hcompare := integral_mono_ae hi hresp hle
  rw [integral_const_mul] at hcompare
  rw [← half_response h hl, cost_eq h hl]
  exact add_le_add (le_refl _) hcompare

/-- **Theorem 2.7** (`thm:below-one`). The speed derivative is strictly negative at
every bias in `(0, 1]` under the standing offspring hypotheses. -/
theorem deriv_neg_of_le_one (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    deriv (speedValue μ) l < 0 := by
  have hlt : l ∈ Set.Ioo 0 (mean μ) := ⟨hl, hl1.trans_lt (one_lt_mean_of_hyp h)⟩
  have hcost := (K1_sub_speed_mul_K0_pos h hlt hl1).trans_le (half_response_le_cost h hlt hl1)
  change 0 < -l * Zval μ l * deriv (speedValue μ) l at hcost
  exact neg_of_mul_pos_right hcost
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl.le) (Speed.Zval_pos μ hl h hlt.2).le)

end LPPMonotonicityProof.Analytic
