module

public import LPPMonotonicityProof.Analytic.Regularity.InverseMoment
public import LPPMonotonicityProof.Speed.Close.S4

/-!
# Root-drift comparison at bias at most one

This module proves two scalar steps of the root-drift comparison in the proof of
Theorem 2.7 (`thm:below-one`): the strict drift estimate
`E[(ν - λ)/(ν + λ)] < 1 - λ E[1/ν]`, and the reciprocal-moment comparison
`1 - λ E[1/ν] ≤ 1 / E[1/β]` obtained from Lemma 2.4 (`lem:inverse-moment`).  The
weighted Aïdékon comparison `speed_le_mean_drift` is proved in
`LPPMonotonicityProof.Analytic.BelowOne2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem ae_nat_one_le_B1 (h : OffspringHyp μ) : ∀ᵐ k : ℕ ∂μ, 1 ≤ k := by
  rw [ae_iff]
  have hs : {k : ℕ | ¬1 ≤ k} = {0} := by ext k; simp
  rw [hs]
  exact h.zero

private theorem integrable_nat_inv_B1 : Integrable (fun k : ℕ => (k : ℝ)⁻¹) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  filter_upwards with k
  cases k with
  | zero => simp
  | succ k =>
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((k + 1 : ℕ) : ℝ)⁻¹)]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_pos k)

private theorem integrable_root_drift {l : ℝ} (hl : 0 < l) :
    Integrable (fun k : ℕ => ((k : ℝ) - l) / (k + l)) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  filter_upwards with k
  have hp : 0 < (k : ℝ) + l := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hp]
  apply (div_le_one hp).2
  rw [abs_le]
  constructor <;> linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]

private theorem integrable_shifted_inv {l : ℝ} (hl : 0 < l) :
    Integrable (fun k : ℕ => ((k : ℝ) + l)⁻¹) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable l⁻¹
  filter_upwards with k
  have hp : 0 < (k : ℝ) + l := by positivity
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  apply (inv_le_inv₀ hp hl).2
  exact le_add_of_nonneg_left (Nat.cast_nonneg k)

private theorem root_drift_integral_formula {l : ℝ} (hl : 0 < l) :
    (∫ k, ((k : ℝ) - l) / (k + l) ∂μ) =
      1 - 2 * l * ∫ k, ((k : ℝ) + l)⁻¹ ∂μ := by
  have hi := (integrable_shifted_inv (μ := μ) hl).const_mul (2 * l)
  have heq : (fun k : ℕ => ((k : ℝ) - l) / (k + l)) =
      (fun k : ℕ => 1 - 2 * l * ((k : ℝ) + l)⁻¹) := by
    funext k
    have hk : (k : ℝ) + l ≠ 0 := by positivity
    field_simp [hk]
    ring
  rw [heq, integral_sub (integrable_const 1) hi, integral_const_mul,
    integral_const, probReal_univ, one_smul]

/-- The expected root drift is strictly below `1-lU`. -/
theorem mean_drift_lt (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    (∫ k, ((k : ℝ) - l) / (k + l) ∂μ) < 1 - l * invMean μ := by
  let A : ℝ := ∫ k, ((k : ℝ) + l)⁻¹ ∂μ
  let d : ℕ → ℝ := fun k => 2 * l * ((k : ℝ) + l)⁻¹ - l * (k : ℝ)⁻¹
  have hdint : Integrable d μ :=
    ((integrable_shifted_inv (μ := μ) hl).const_mul (2 * l)).sub
      (integrable_nat_inv_B1.const_mul l)
  have hdnonneg : 0 ≤ᵐ[μ] d := by
    filter_upwards [ae_nat_one_le_B1 h] with k hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hkl : (k : ℝ) + l ≠ 0 := by positivity
    have hn : 0 ≤ l * ((k : ℝ) - l) / ((k : ℝ) * ((k : ℝ) + l)) :=
      div_nonneg (mul_nonneg hl.le (sub_nonneg.mpr (hl1.trans hkR))) (by positivity)
    have heq : d k = l * ((k : ℝ) - l) / ((k : ℝ) * ((k : ℝ) + l)) := by
      dsimp only [d]
      field_simp [hk0, hkl]
      ring
    rw [heq]
    exact hn
  obtain ⟨k, hk, hμk⟩ := exists_degree_ge_two h
  have hkd : 0 < d k := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hkl : (k : ℝ) + l ≠ 0 := by positivity
    have heq : d k = l * ((k : ℝ) - l) / ((k : ℝ) * ((k : ℝ) + l)) := by
      dsimp only [d]
      field_simp [hk0, hkl]
      ring
    rw [heq]
    exact div_pos (mul_pos hl (sub_pos.mpr (hl1.trans_lt (by linarith)))) (by positivity)
  have hm : 0 < μ (Function.support d) := by
    apply lt_of_lt_of_le (pos_iff_ne_zero.mpr hμk)
    apply measure_mono
    intro j hj
    rw [Set.mem_singleton_iff] at hj
    subst j
    exact ne_of_gt hkd
  have hdpos : 0 < ∫ k, d k ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hdnonneg hdint).2 hm
  rw [root_drift_integral_formula hl]
  have hdform : (∫ k, d k ∂μ) = 2 * l * A - l * invMean μ := by
    dsimp only [d, A, invMean]
    rw [integral_sub ((integrable_shifted_inv (μ := μ) hl).const_mul (2 * l))
      (integrable_nat_inv_B1.const_mul l), integral_const_mul, integral_const_mul]
  rw [hdform] at hdpos
  linarith

/-- The reciprocal inverse-escape moment is at least `1-lU`. -/
theorem one_sub_le_inv_mean_inv_escape (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hl1 : l ≤ 1) :
    1 - l * invMean μ ≤ (∫ T, (escape l T)⁻¹ ∂GW μ)⁻¹ := by
  have hUn : 0 ≤ invMean μ := by
    apply integral_nonneg_of_ae
    exact ae_of_all _ fun k => inv_nonneg.mpr (Nat.cast_nonneg k)
  have hU : l * invMean μ < 1 := by
    calc
      l * invMean μ ≤ 1 * invMean μ := mul_le_mul_of_nonneg_right hl1 hUn
      _ = invMean μ := one_mul _
      _ < 1 := (invMean_bounds h).2
  obtain ⟨hpos, hint⟩ := integrable_inv_escape h hl hU
  let M : ℝ := ∫ T, (escape l T)⁻¹ ∂GW μ
  have hone : 1 ≤ M := by
    calc
      1 = ∫ _T : Tree, (1 : ℝ) ∂GW μ := by simp
      _ ≤ M := by
        apply integral_mono_ae (integrable_const 1) hint
        filter_upwards [hpos] with T hT
        exact (one_le_inv₀ hT).2 (escape_mem_Icc hl T).2
  have hMp : 0 < M := zero_lt_one.trans_le hone
  have heq : ENNReal.ofReal M = ∫⁻ T, (ENNReal.ofReal (escape l T))⁻¹ ∂GW μ := by
    have he : (fun T => ENNReal.ofReal ((escape l T)⁻¹)) =ᵐ[GW μ]
        (fun T => (ENNReal.ofReal (escape l T))⁻¹) :=
      hpos.mono fun T hT => ENNReal.ofReal_inv_of_pos hT
    dsimp only [M]
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (hpos.mono fun T hT => inv_nonneg.mpr hT.le), lintegral_congr_ae he]
  have hbound : ENNReal.ofReal M ≤ ENNReal.ofReal (1 - l * invMean μ)⁻¹ := by
    rw [heq]
    exact lintegral_inv_escape_le h hl hU
  have hi := ENNReal.inv_le_inv.mpr hbound
  rw [ENNReal.ofReal_inv_of_pos (sub_pos.mpr hU), inv_inv,
    ← ENNReal.ofReal_inv_of_pos hMp] at hi
  exact (ENNReal.ofReal_le_ofReal_iff (inv_nonneg.mpr hMp.le)).mp hi

end LPPMonotonicityProof.Analytic
