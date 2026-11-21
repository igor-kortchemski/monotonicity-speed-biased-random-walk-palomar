module

public import LPPMonotonicityProof.Analytic.Critical
public import LPPMonotonicityProof.Analytic.FirstSplit
public import LPPMonotonicityProof.Analytic.Interface2
public import LPPMonotonicityProof.Analytic.LowWindowScalar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Speed estimates at the lower edge of the first-split window

This module proves the first step of the proof of Theorem 4.3 (`thm:low-window`): the
speed at bias one, `v(1) = E[(ν-1)/(ν+1)]`, and the bound `V ≤ 1 - 4e/3` when
`v(1+ps) ≤ v(1)`. The bias-one formula is obtained from the Aïdékon quotient (2.1) and
exchangeability of the `k+1` escape coordinates in each root-degree fiber.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private lemma one_lt_mean_real (h : OffspringHyp μ) : 1 < mean μ :=
  (ENNReal.toReal_lt_toReal ENNReal.one_ne_top h.mean_lt_top.ne).2 h.one_lt_mean

private lemma integrable_offspring_ratio (f : ℕ → ℝ)
    (hf : ∀ k, |f k| ≤ 1) : Integrable f μ := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable 1
  filter_upwards with k
  simpa only [Real.norm_eq_abs] using hf k

private lemma integrable_aidFiber_one (h : OffspringHyp μ) (k : ℕ) :
    Integrable (fun q : ℝ × (Fin k → ℝ) => q.1 / Hfun 1 q.1 (∑ j, q.2 j))
      ((escLaw μ 1).prod (Measure.pi fun _ : Fin k => escLaw μ 1)) := by
  refine (integrable_const (1 : ℝ)).mono ?_ ?_
  exact (measurable_fst.div (((measurable_const.sub measurable_const).add measurable_fst).add
    (Finset.univ.measurable_sum fun j _ => (measurable_pi_apply j).comp measurable_snd))).aestronglyMeasurable
  filter_upwards [ae_iid_good μ zero_lt_one h (one_lt_mean_real h) k] with q hq
  have hS : 0 ≤ ∑ j, q.2 j := Finset.sum_nonneg fun j _ => (hq.2 j).1.le
  have hH : 0 < Hfun 1 q.1 (∑ j, q.2 j) := by
    by_cases hk : k = 0
    · subst k
      simpa [Hfun] using hq.1.1
    · exact Hfun_pos hk hq.1 hq.2
  have hle : q.1 ≤ Hfun 1 q.1 (∑ j, q.2 j) := by
    simp only [Hfun]
    linarith
  change ‖q.1 / Hfun 1 q.1 (∑ j, q.2 j)‖ ≤ ‖(1 : ℝ)‖
  rw [Real.norm_eq_abs, norm_one, abs_div, abs_of_pos hH,
    abs_of_nonneg hq.1.1.le]
  exact (div_le_one hH).2 hle

/-- The root decomposition of an Aïdékon expectation. -/
private lemma aidE_eq_tsum (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) (g : ℕ → ℝ) (hg : ∃ C, ∀ k, |g k| ≤ C * (k + 1))
    (hprod : ∀ k, Integrable (fun q : ℝ × (Fin k → ℝ) =>
      g k * q.1 / Hfun l q.1 (∑ i, q.2 i))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l))) :
    aidE μ l g = ∑' k, (μ {k}).toReal * ∫ q : ℝ × (Fin k → ℝ),
      g k * q.1 / Hfun l q.1 (∑ i, q.2 i)
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) := by
  have hint := integrable_aid h hl hlm g hg
  let G : Tree → ℝ := fun T => ∫ U, g (degree T) * escape l U /
    (l - 1 + escape l U + childSum l T) ∂GW μ
  calc
    aidE μ l g = ∫ T, G T ∂GW μ := integral_prod _ hint
    _ = ∑' k, (μ {k}).toReal * ∫ ts, G (nodeFin k ts)
        ∂Measure.pi (fun _ : Fin k => GW μ) := integral_GW_eq_tsum G hint.integral_prod_left
    _ = _ := by
      apply tsum_congr
      intro k
      congr 1
      let piEsc := Measure.pi fun _ : Fin k => escLaw μ l
      let H : (Fin k → ℝ) → ℝ := fun bs =>
        ∫ b, g k * b / Hfun l b (∑ i, bs i) ∂escLaw μ l
      have hvec : (Measure.pi fun _ : Fin k => GW μ).map
          (fun ts i => escape l (ts i)) = piEsc :=
        Measure.pi_map_pi fun _ => (measurable_escape l).aemeasurable
      have hH : AEStronglyMeasurable H piEsc :=
        (hprod k).aestronglyMeasurable.prod_swap.integral_prod_right'
      calc
        (∫ ts, G (nodeFin k ts) ∂Measure.pi fun _ : Fin k => GW μ) =
            ∫ ts, H (fun i => escape l (ts i)) ∂Measure.pi (fun _ : Fin k => GW μ) := by
          apply integral_congr_ae
          filter_upwards with ts
          dsimp only [G, H]
          rw [degree_nodeFin, childSum_nodeFin, escLaw,
            integral_map (measurable_escape l).aemeasurable]
          · rfl
          · exact ((measurable_const.mul measurable_id).div
              (((measurable_const.sub measurable_const).add measurable_id).add
                measurable_const)).aestronglyMeasurable
        _ = ∫ bs, H bs ∂piEsc := by
          rw [← hvec] at hH ⊢
          exact (integral_map
            (Measurable.of_eval fun i => (measurable_escape l).comp
              (measurable_pi_apply i)).aemeasurable hH).symm
        _ = ∫ q : (Fin k → ℝ) × ℝ, g k * q.2 / Hfun l q.2 (∑ i, q.1 i)
            ∂piEsc.prod (escLaw μ l) := (integral_prod _ (hprod k).swap).symm
        _ = _ := by
          simpa only [Prod.swap, piEsc] using
            (integral_prod_swap (μ := escLaw μ l) (ν := piEsc)
              (fun q : ℝ × (Fin k → ℝ) => g k * q.1 / Hfun l q.1 (∑ i, q.2 i)))

/-- Exchangeability identifies the common escape-coordinate quotient at bias one. -/
private lemma integral_escape_quotient_one (h : OffspringHyp μ) (k : ℕ) :
    (∫ q : ℝ × (Fin k → ℝ), q.1 / Hfun 1 q.1 (∑ j, q.2 j)
      ∂(escLaw μ 1).prod (Measure.pi fun _ : Fin k => escLaw μ 1)) = ((k : ℝ) + 1)⁻¹ := by
  by_cases hk : k = 0
  · subst k
    have heq : (fun q : ℝ × (Fin 0 → ℝ) => q.1 / Hfun 1 q.1 (∑ j, q.2 j)) =ᵐ[
        (escLaw μ 1).prod (Measure.pi fun _ : Fin 0 => escLaw μ 1)] fun _ => 1 := by
      filter_upwards [ae_iid_good μ zero_lt_one h (one_lt_mean_real h) 0] with q hq
      have hb := hq.1.1.ne'
      simp only [Hfun, Finset.univ_eq_empty, Finset.sum_empty, sub_self, zero_add, add_zero]
      exact div_self hb
    rw [integral_congr_ae heq, integral_const, probReal_univ]
    simp
  · have hint := integrable_aidFiber_one h k
    have hsum := integrable_sum_ratio μ zero_lt_one h (one_lt_mean_real h) hk
    have hdiff : (∫ q : ℝ × (Fin k → ℝ), (∑ j, q.2 j) / Hfun 1 q.1 (∑ j, q.2 j)
        ∂(escLaw μ 1).prod (Measure.pi fun _ : Fin k => escLaw μ 1)) =
        1 - ∫ q : ℝ × (Fin k → ℝ), q.1 / Hfun 1 q.1 (∑ j, q.2 j)
          ∂(escLaw μ 1).prod (Measure.pi fun _ : Fin k => escLaw μ 1) := by
      calc
        _ = ∫ q : ℝ × (Fin k → ℝ), (1 - q.1 / Hfun 1 q.1 (∑ j, q.2 j))
            ∂(escLaw μ 1).prod (Measure.pi fun _ : Fin k => escLaw μ 1) := by
          apply integral_congr_ae
          filter_upwards [ae_iid_good μ zero_lt_one h (one_lt_mean_real h) k] with q hq
          have hH := Hfun_pos hk hq.1 hq.2
          simp only [Hfun] at hH ⊢
          field_simp
          ring
        _ = _ := by
          rw [integral_sub (integrable_const 1) hint, integral_const, probReal_univ]
          simp
    have hexch := integral_degree_exchange μ zero_lt_one h (one_lt_mean_real h) hk
    rw [hdiff] at hexch
    have hconst : (∫ q : ℝ × (Fin k → ℝ), (k : ℝ) * q.1 / Hfun 1 q.1 (∑ j, q.2 j)
        ∂(escLaw μ 1).prod (Measure.pi fun _ : Fin k => escLaw μ 1)) =
        (k : ℝ) * ∫ q : ℝ × (Fin k → ℝ), q.1 / Hfun 1 q.1 (∑ j, q.2 j)
          ∂(escLaw μ 1).prod (Measure.pi fun _ : Fin k => escLaw μ 1) := by
      simpa only [mul_div_assoc] using integral_const_mul (k : ℝ)
        (fun q : ℝ × (Fin k → ℝ) => q.1 / Hfun 1 q.1 (∑ j, q.2 j))
    rw [hconst] at hexch
    rw [← one_div]
    apply (eq_div_iff (by positivity : (k : ℝ) + 1 ≠ 0)).2
    nlinarith

private lemma aidE_one_eq_tsum (h : OffspringHyp μ) (g : ℕ → ℝ)
    (hg : ∃ C, ∀ k, |g k| ≤ C * (k + 1)) :
    aidE μ 1 g = ∑' k, (μ {k}).toReal * (g k * ((k : ℝ) + 1)⁻¹) := by
  have hprod (k : ℕ) : Integrable (fun q : ℝ × (Fin k → ℝ) =>
      g k * q.1 / Hfun 1 q.1 (∑ i, q.2 i))
      ((escLaw μ 1).prod (Measure.pi fun _ : Fin k => escLaw μ 1)) := by
    simpa only [mul_div_assoc] using (integrable_aidFiber_one h k).const_mul (g k)
  rw [aidE_eq_tsum h zero_lt_one (one_lt_mean_real h) g hg hprod]
  apply tsum_congr
  intro k
  rw [show (∫ q : ℝ × (Fin k → ℝ), g k * q.1 / Hfun 1 q.1 (∑ i, q.2 i)
      ∂(escLaw μ 1).prod (Measure.pi fun _ : Fin k => escLaw μ 1)) =
      g k * ∫ q : ℝ × (Fin k → ℝ), q.1 / Hfun 1 q.1 (∑ i, q.2 i)
        ∂(escLaw μ 1).prod (Measure.pi fun _ : Fin k => escLaw μ 1) by
    simpa only [mul_div_assoc] using integral_const_mul (g k)
      (fun q : ℝ × (Fin k → ℝ) => q.1 / Hfun 1 q.1 (∑ i, q.2 i)),
    integral_escape_quotient_one h k]

/-- **Speed at bias one.**  At bias one the speed `Speed.speedValue` is the classical
offspring expectation `E[(ν-1)/(ν+1)]`. -/
theorem speedValue_one (h : OffspringHyp μ) :
    Speed.speedValue μ 1 = ∫ k, ((k : ℝ) - 1) / (k + 1) ∂μ := by
  let f : ℕ → ℝ := fun k => ((k : ℝ) - 1) / (k + 1)
  let D : ℝ := aidE μ 1 (fun k : ℕ => (k : ℝ) + 1)
  have hf : Integrable f μ := by
    apply integrable_offspring_ratio
    intro k
    dsimp only [f]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    apply (div_le_one (by positivity)).2
    simpa using abs_sub (k : ℝ) 1
  have hD : 0 < D := aidE_pos h zero_lt_one (one_lt_mean_real h)
  have hgminus : ∃ C, ∀ k : ℕ, |(k : ℝ) - 1| ≤ C * (k + 1) := by
    refine ⟨1, fun k => ?_⟩
    simpa using abs_sub (k : ℝ) 1
  have hgplus : ∃ C, ∀ k : ℕ, |(k : ℝ) + 1| ≤ C * (k + 1) := by
    refine ⟨2, fun k => ?_⟩
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  have hmass : (∑' k : ℕ, (μ {k}).toReal) = 1 := by
    have hi := integral_countable (μ := μ) (f := fun _ : ℕ => (1 : ℝ)) (integrable_const 1)
    simpa [Measure.real] using hi.symm
  have hDone : D = 1 := by
    dsimp only [D]
    rw [aidE_one_eq_tsum h _ hgplus]
    calc
      _ = ∑' k : ℕ, (μ {k}).toReal := by
        apply tsum_congr
        intro k
        have hk : (k : ℝ) + 1 ≠ 0 := by positivity
        field_simp
      _ = 1 := hmass
  have hN : aidE μ 1 (fun k : ℕ => (k : ℝ) - 1) = ∫ k, f k ∂μ := by
    rw [aidE_one_eq_tsum h _ hgminus, integral_countable hf]
    apply tsum_congr
    intro k
    simp only [Measure.real, smul_eq_mul, f, div_eq_mul_inv]
  rw [speedValue_eq_speedValueProv, speedValue_eq_aid h zero_lt_one (one_lt_mean_real h)]
  change _ / D = _
  rw [hN, hDone, div_one]

private lemma ae_splitLaw_degree_two : ∀ᵐ T ∂splitLaw μ, 2 ≤ degree T := by
  exact (ae_restrict_mem (continuous_degree.measurable measurableSet_Ici)).filter_mono
    (Measure.ae_smul_measure_le _)

private lemma integrable_invDegree_split (h : OffspringHyp μ) : Integrable (fun T : Tree => ((degree T : ℝ))⁻¹)
    (splitLaw μ) := by
  letI := splitLaw_prob (μ := μ) h
  apply Integrable.of_bound
    (((measurable_of_countable fun k : ℕ => (k : ℝ)⁻¹).comp
      continuous_degree.measurable).aestronglyMeasurable) 1
  filter_upwards [ae_splitLaw_degree_two (μ := μ)] with T hT
  change |(degree T : ℝ)⁻¹| ≤ 1
  rw [abs_of_nonneg (by positivity)]
  apply inv_le_one_of_one_le₀
  exact_mod_cast (show 1 ≤ degree T by omega)

private lemma integrable_splitRatio (h : OffspringHyp μ) : Integrable
    (fun T : Tree => ((degree T : ℝ) - 1) / (degree T + 1)) (splitLaw μ) := by
  letI := splitLaw_prob (μ := μ) h
  apply Integrable.of_bound
    (((measurable_of_countable fun k : ℕ => ((k : ℝ) - 1) / (k + 1)).comp
      continuous_degree.measurable).aestronglyMeasurable) 1
  filter_upwards [ae_splitLaw_degree_two (μ := μ)] with T hT
  change |((degree T : ℝ) - 1) / (degree T + 1)| ≤ 1
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < degree T + 1)]
  apply (div_le_one (by positivity)).2
  simpa using abs_sub (degree T : ℝ) 1

private lemma speedValue_one_split (h : OffspringHyp μ) :
    Speed.speedValue μ 1 = pBr μ *
      ∫ T, ((degree T : ℝ) - 1) / (degree T + 1) ∂splitLaw μ := by
  let f : ℕ → ℝ := fun k => ((k : ℝ) - 1) / (k + 1)
  have hf : Integrable f μ := by
    apply integrable_offspring_ratio
    intro k
    dsimp only [f]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    apply (div_le_one (by positivity)).2
    simpa using abs_sub (k : ℝ) 1
  have hsplit : (∫ k, f k ∂μ) = ∫ k in Set.Ici 2, f k ∂μ := by
    calc
      (∫ k, f k ∂μ) = (∫ k in {1}, f k ∂μ) + ∫ k in ({1} : Set ℕ)ᶜ, f k ∂μ := by
        conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ)
          (measurableSet_singleton 1)]
        rw [integral_add_measure (hf.mono_measure Measure.restrict_le_self)
          (hf.mono_measure Measure.restrict_le_self)]
      _ = ∫ k in Set.Ici 2, f k ∂μ := by
        rw [integral_singleton]
        simp only [f, Nat.cast_one, sub_self, zero_div, smul_zero, zero_add]
        have hc : ({1} : Set ℕ)ᶜ =ᵐ[μ] Set.Ici 2 := by
          rw [ae_eq_set]
          constructor
          · have hs : ({1} : Set ℕ)ᶜ \ Set.Ici 2 = {0} := by
              ext k
              simp only [Set.mem_sdiff, Set.mem_compl_iff, Set.mem_singleton_iff,
                Set.mem_Ici, not_le]
              omega
            rw [hs]
            exact h.zero
          · have hs : Set.Ici 2 \ ({1} : Set ℕ)ᶜ = ∅ := by ext k; simp
            rw [hs, measure_empty]
        rw [Measure.restrict_congr_set hc]
  have hmap : (∫ T, f (degree T) ∂splitLaw μ) =
      (pBr μ)⁻¹ * ∫ k in Set.Ici 2, f k ∂μ := by
    calc
      _ = ∫ k, f k ∂(splitLaw μ).map degree := by
        symm
        exact integral_map continuous_degree.measurable.aemeasurable
          (measurable_of_countable f).aestronglyMeasurable
      _ = _ := by
        rw [splitLaw_map_degree h]
        simp only [integral_smul_measure, smul_eq_mul, pBr, Measure.real,
          ENNReal.toReal_inv]
  rw [speedValue_one h, hsplit, hmap]
  change _ = pBr μ * ((pBr μ)⁻¹ * _)
  rw [← mul_assoc, mul_inv_cancel₀ (pBr_pos h).ne', one_mul]

private lemma splitRatio_le (h : OffspringHyp μ) :
    (∫ T, ((degree T : ℝ) - 1) / (degree T + 1) ∂splitLaw μ) ≤ 1 - 4 * eJ μ / 3 := by
  letI := splitLaw_prob h
  calc
    _ ≤ ∫ T, 1 - 4 / 3 * ((degree T : ℝ))⁻¹ ∂splitLaw μ := by
      apply integral_mono_ae (integrable_splitRatio h)
        ((integrable_const 1).sub ((integrable_invDegree_split h).const_mul (4 / 3 : ℝ)))
      filter_upwards [ae_splitLaw_degree_two (μ := μ)] with T hT
      have hk : (2 : ℝ) ≤ degree T := by exact_mod_cast hT
      change ((degree T : ℝ) - 1) / (degree T + 1) ≤ 1 - 4 / 3 * (degree T : ℝ)⁻¹
      have hk0 : (0 : ℝ) < degree T := by linarith
      have hk1 : (0 : ℝ) < degree T + 1 := by linarith
      rw [div_le_iff₀ hk1]
      have hkne : (degree T : ℝ) ≠ 0 := hk0.ne'
      field_simp
      nlinarith
    _ = 1 - 4 * eJ μ / 3 := by
      rw [integral_sub (integrable_const 1) ((integrable_invDegree_split h).const_mul (4 / 3 : ℝ)),
        integral_const, probReal_univ, integral_const_mul]
      simp only [probReal_univ, one_smul]
      unfold eJ
      ring

/-- **First-split bound.**  Below the bias-one speed, the scaled speed is at
most `1 - 4e/3`. -/
theorem Vsc_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (hv : Speed.speedValue μ l ≤ Speed.speedValue μ 1) :
    Vsc μ l ≤ 1 - 4 * eJ μ / 3 := by
  have hp := pBr_pos h
  have hv' : speedValueProv μ l ≤ speedValueProv μ 1 := by
    simpa only [← speedValue_eq_speedValueProv] using hv
  calc
    Vsc μ l = speedValueProv μ l / pBr μ := rfl
    _ ≤ speedValueProv μ 1 / pBr μ := div_le_div_of_nonneg_right hv' hp.le
    _ = ∫ T, ((degree T : ℝ) - 1) / (degree T + 1) ∂splitLaw μ := by
      rw [← speedValue_eq_speedValueProv, speedValue_one_split h]
      field_simp
    _ ≤ 1 - 4 * eJ μ / 3 := splitRatio_le h

end LPPMonotonicityProof.Analytic
