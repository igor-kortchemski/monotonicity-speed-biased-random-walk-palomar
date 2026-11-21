module

public import LPPMonotonicityProof.Analytic.Kernel2
public import LPPMonotonicityProof.Analytic.Regularity.Mean
public import LPPMonotonicityProof.Analytic.Tools
public import LPPMonotonicityProof.Speed.Close.Export
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The critical-bias remark

This module proves Remark 2.3 (`rem:critical-bias`) for the speed
`Speed.speedValue`.  It also records that `Speed.speedValue` is definitionally equal
to its copy `speedValueProv`, used by the analytic modules.  All extended second
moments remain in `ℝ≥0∞`, so the infinite-moment case needs no real-valued moment
integral.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- The speed `Speed.speedValue` and its copy `speedValueProv` are definitionally equal. -/
theorem speedValue_eq_speedValueProv (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) :
    Speed.speedValue μ l = speedValueProv μ l := rfl

private lemma mean_pos_critical (h : OffspringHyp μ) : 0 < mean μ := by
  have hm : (1 : ℝ≥0∞) < ∫⁻ k, (k : ℝ≥0∞) ∂μ := h.one_lt_mean
  have hr : (1 : ℝ) < mean μ :=
    (ENNReal.toReal_lt_toReal ENNReal.one_ne_top h.mean_lt_top.ne).2 hm
  exact zero_lt_one.trans hr

private lemma integrable_natCast_critical (h : OffspringHyp μ) :
    Integrable (fun k : ℕ => (k : ℝ)) μ := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun k => Nat.cast_nonneg k)).2
  simpa only [ENNReal.ofReal_natCast] using h.mean_lt_top

omit [IsProbabilityMeasure μ] in
private lemma integral_natCast_eq_mean_critical :
    (∫ k : ℕ, (k : ℝ) ∂μ) = mean μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun k => Nat.cast_nonneg k)
    (measurable_of_countable _).aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast, mean]

private lemma integral_id_escLaw (l : ℝ) :
    (∫ b, b ∂Speed.escLaw μ l) = ∫ T, Speed.escape l T ∂GW μ := by
  simpa only [Speed.escLaw, id_eq] using
    (integral_map (μ := GW μ) (φ := Speed.escape l) (f := fun b : ℝ => b)
      (measurable_escape l).aemeasurable measurable_id.aestronglyMeasurable)

private lemma integrable_id_escLaw (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) : Integrable (fun b : ℝ => b) (Speed.escLaw μ l) := by
  apply (integrable_const (1 : ℝ)).mono measurable_id.aestronglyMeasurable
  filter_upwards [Speed.ae_goodEsc μ hl h hlm] with b hb
  change ‖b‖ ≤ ‖(1 : ℝ)‖
  rw [Real.norm_of_nonneg hb.1.le]
  simpa only [norm_one] using hb.2.1.le

private lemma integrable_ratio_right_critical (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    Integrable (fun p : ℝ × ℝ => p.2 / Speed.Dfun l p.1 p.2)
      ((Speed.escLaw μ l).prod (Speed.escLaw μ l)) := by
  let C : ℝ := (min 1 l)⁻¹
  have hm : 0 < min 1 l := lt_min zero_lt_one hl
  have hC : 0 ≤ C := inv_nonneg.mpr hm.le
  apply (integrable_const C).mono
    (measurable_snd.div (Speed.measurable_Dfun l)).aestronglyMeasurable
  filter_upwards [Speed.ae_pair_goodEsc μ hl h hlm] with p hp
  have hD := Speed.Dfun_pos_of_good hl hp.1 hp.2
  have hratio : 0 ≤ p.2 / Speed.Dfun l p.1 p.2 := div_nonneg hp.2.1.le hD.le
  change ‖p.2 / Speed.Dfun l p.1 p.2‖ ≤ ‖C‖
  rw [Real.norm_of_nonneg hratio, Real.norm_of_nonneg hC]
  apply (div_le_iff₀ hD).2
  calc
    p.2 = C * (min 1 l * p.2) := by
      dsimp [C]
      field_simp
    _ ≤ C * Speed.Dfun l p.1 p.2 :=
      mul_le_mul_of_nonneg_left (Speed.Dfun_ge_right hp.1 hp.2) hC

private lemma integrable_ratio_right_fixed_critical (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) {t : ℝ} (ht : Speed.GoodEsc l t) :
    Integrable (fun b : ℝ => b / Speed.Dfun l t b) (Speed.escLaw μ l) := by
  let C : ℝ := (min 1 l)⁻¹
  have hm : 0 < min 1 l := lt_min zero_lt_one hl
  have hC : 0 ≤ C := inv_nonneg.mpr hm.le
  have hDm : Measurable (fun b => Speed.Dfun l t b) :=
    (Speed.measurable_Dfun l).comp (measurable_const.prodMk measurable_id)
  apply (integrable_const C).mono (measurable_id.div hDm).aestronglyMeasurable
  filter_upwards [Speed.ae_goodEsc μ hl h hlm] with b hb
  have hD := Speed.Dfun_pos_of_good hl ht hb
  have hratio : 0 ≤ b / Speed.Dfun l t b := div_nonneg hb.1.le hD.le
  change ‖b / Speed.Dfun l t b‖ ≤ ‖C‖
  rw [Real.norm_of_nonneg hratio, Real.norm_of_nonneg hC]
  apply (div_le_iff₀ hD).2
  calc
    b = C * (min 1 l * b) := by
      dsimp [C]
      field_simp
    _ ≤ C * Speed.Dfun l t b :=
      mul_le_mul_of_nonneg_left (Speed.Dfun_ge_right ht hb) hC

private lemma integrable_ratio_left_critical (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    Integrable (fun p : ℝ × ℝ => p.1 / Speed.Dfun l p.1 p.2)
      ((Speed.escLaw μ l).prod (Speed.escLaw μ l)) := by
  let C : ℝ := (min 1 l)⁻¹
  have hm : 0 < min 1 l := lt_min zero_lt_one hl
  have hC : 0 ≤ C := inv_nonneg.mpr hm.le
  apply (integrable_const C).mono
    (measurable_fst.div (Speed.measurable_Dfun l)).aestronglyMeasurable
  filter_upwards [Speed.ae_pair_goodEsc μ hl h hlm] with p hp
  have hD := Speed.Dfun_pos_of_good hl hp.1 hp.2
  have hratio : 0 ≤ p.1 / Speed.Dfun l p.1 p.2 := div_nonneg hp.1.1.le hD.le
  change ‖p.1 / Speed.Dfun l p.1 p.2‖ ≤ ‖C‖
  rw [Real.norm_of_nonneg hratio, Real.norm_of_nonneg hC]
  apply (div_le_iff₀ hD).2
  calc
    p.1 = C * (min 1 l * p.1) := by
      dsimp [C]
      field_simp
    _ ≤ C * Speed.Dfun l p.1 p.2 :=
      mul_le_mul_of_nonneg_left (Speed.Dfun_ge_left hp.1 hp.2) hC

private lemma antitoneOn_kernel_integral_critical (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    AntitoneOn (fun t => ∫ b, b / Speed.Dfun l t b ∂Speed.escLaw μ l)
      {b | Speed.GoodEsc l b} := by
  intro t ht u hu htu
  apply integral_mono_ae (integrable_ratio_right_fixed_critical h hl hlm hu)
    (integrable_ratio_right_fixed_critical h hl hlm ht)
  filter_upwards [Speed.ae_goodEsc μ hl h hlm] with b hb
  have hDt := Speed.Dfun_pos_of_good hl ht hb
  have hDle : Speed.Dfun l t b ≤ Speed.Dfun l u b := by
    have hfac : 0 ≤ (u - t) * (1 - b) :=
      mul_nonneg (sub_nonneg.mpr htu) (sub_nonneg.mpr hb.2.1.le)
    unfold Speed.Dfun
    nlinarith
  exact div_le_div_of_nonneg_left hb.1.le hDt hDle

private lemma Nval_le_mean_mul_kernel_critical (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    Speed.Nval μ l ≤ (∫ T, Speed.escape l T ∂GW μ) *
      ∫ t, ∫ b, b / Speed.Dfun l t b ∂Speed.escLaw μ l ∂Speed.escLaw μ l := by
  let ρ := Speed.escLaw μ l
  let g : ℝ → ℝ := fun t => ∫ b, b / Speed.Dfun l t b ∂ρ
  have hK := integrable_ratio_right_critical h hl hlm
  have hprod : Integrable (fun p : ℝ × ℝ => p.1 * (p.2 / Speed.Dfun l p.1 p.2))
      (ρ.prod ρ) := by
    apply (Speed.integrable_N_kernel μ hl h hlm).congr
    exact Filter.Eventually.of_forall fun p => by
      change p.1 * p.2 / Speed.Dfun l p.1 p.2 = p.1 * (p.2 / Speed.Dfun l p.1 p.2)
      rw [mul_div_assoc]
  have hfi : Integrable ((id : ℝ → ℝ) ∘ (fun b : ℝ => b)) ρ := by
    simpa using integrable_id_escLaw h hl hlm
  have hgi : Integrable (g ∘ (fun b : ℝ => b)) ρ := by
    simpa only [Function.comp_def] using hK.integral_prod_left
  have hfgi : Integrable (fun b => id b * g b) ρ := by
    simpa only [g, integral_const_mul, id_eq] using hprod.integral_prod_left
  have hcov := integral_mul_le_of_monotone_antitone
    (P := ρ) (Z := fun b : ℝ => b) (f := id) (g := g) {b | Speed.GoodEsc l b}
    (Speed.ae_goodEsc μ hl h hlm) (fun _ _ _ _ hab => hab)
    (antitoneOn_kernel_integral_critical h hl hlm) hfi hgi hfgi
  have hN : Speed.Nval μ l = ∫ t, t * g t ∂ρ := by
    unfold Speed.Nval
    change (∫ p, p.1 * p.2 / Speed.Dfun l p.1 p.2 ∂ρ.prod ρ) = _
    simp_rw [mul_div_assoc]
    rw [integral_prod _ hprod]
    simp only [integral_const_mul, g]
  simp only [id_eq] at hcov
  rw [hN]
  change (∫ t, t * g t ∂ρ) ≤ (∫ T, Speed.escape l T ∂GW μ) * ∫ t, g t ∂ρ
  rw [← integral_id_escLaw]
  exact hcov

private lemma two_mul_kernel_integral_critical (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    2 * (∫ t, ∫ b, b / Speed.Dfun l t b ∂Speed.escLaw μ l ∂Speed.escLaw μ l) =
      Speed.Nval μ l + Speed.Zval μ l := by
  let ρ := Speed.escLaw μ l
  let A : ℝ := ∫ p, p.1 / Speed.Dfun l p.1 p.2 ∂ρ.prod ρ
  let B : ℝ := ∫ p, p.2 / Speed.Dfun l p.1 p.2 ∂ρ.prod ρ
  have hA := integrable_ratio_left_critical h hl hlm
  have hB := integrable_ratio_right_critical h hl hlm
  have hG : (∫ t, ∫ b, b / Speed.Dfun l t b ∂ρ ∂ρ) = B := by
    dsimp [B]
    exact (integral_prod _ hB).symm
  have hBA : B = A := by
    calc
      B = ∫ p : ℝ × ℝ, p.2 / Speed.Dfun l p.2 p.1 ∂ρ.prod ρ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          unfold Speed.Dfun
          ring
      _ = A := by
        dsimp [A]
        exact integral_prod_swap (fun p : ℝ × ℝ => p.1 / Speed.Dfun l p.1 p.2)
  have hsum : A + B = Speed.Nval μ l + Speed.Zval μ l := by
    calc
      A + B = ∫ p, (p.1 / Speed.Dfun l p.1 p.2 + p.2 / Speed.Dfun l p.1 p.2) ∂ρ.prod ρ :=
        (integral_add hA hB).symm
      _ = ∫ p, (p.1 * p.2 / Speed.Dfun l p.1 p.2 + tau p.1 p.2 / Speed.Dfun l p.1 p.2)
          ∂ρ.prod ρ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          change p.1 / Speed.Dfun l p.1 p.2 + p.2 / Speed.Dfun l p.1 p.2 =
            p.1 * p.2 / Speed.Dfun l p.1 p.2 + tau p.1 p.2 / Speed.Dfun l p.1 p.2
          rw [← add_div, ← add_div]
          congr 1
          unfold tau
          ring
      _ = Speed.Nval μ l + Speed.Zval μ l := by
        exact integral_add (Speed.integrable_N_kernel μ hl h hlm)
          (Speed.integrable_Z_kernel μ hl h hlm)
  rw [hG]
  nlinarith

private lemma mean_escape_lt_one_critical (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    (∫ T, Speed.escape l T ∂GW μ) < 1 := by
  have hb := (mean_escape_bounds h hl hlm).2.2.2
  have hm := mean_pos_critical h
  exact hb.trans_lt ((div_lt_one hm).2 (by linarith))

/-- Remark 2.3: Schwarzfischer's bound by the mean escape probability. -/
theorem speed_le_mean_escape (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) :
    let b := ∫ T, Speed.escape l T ∂GW μ
    Speed.speedValue μ l ≤ b / (2 - b) := by
  dsimp only
  let b : ℝ := ∫ T, Speed.escape l T ∂GW μ
  let G : ℝ := ∫ t, ∫ x, x / Speed.Dfun l t x ∂Speed.escLaw μ l ∂Speed.escLaw μ l
  have hbpos : 0 < b := (mean_escape_bounds h hl hlm).1
  have hb1 : b < 1 := mean_escape_lt_one_critical h hl hlm
  have hN := Nval_le_mean_mul_kernel_critical h hl hlm
  have hG := two_mul_kernel_integral_critical h hl hlm
  change Speed.Nval μ l ≤ b * G at hN
  change 2 * G = Speed.Nval μ l + Speed.Zval μ l at hG
  rw [Speed.speedValue_of_pos μ hl]
  apply (div_le_div_iff₀ (Speed.Zval_pos μ hl h hlm) (by linarith : 0 < 2 - b)).2
  nlinarith

/-- Remark 2.3: the elementary upper bound approaching the critical bias. -/
theorem speed_le_critical (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) :
    Speed.speedValue μ l ≤ (mean μ - l) / (mean μ + l) := by
  let b : ℝ := ∫ T, Speed.escape l T ∂GW μ
  have hbpos : 0 < b := (mean_escape_bounds h hl hlm).1
  have hb : b ≤ (mean μ - l) / mean μ := (mean_escape_bounds h hl hlm).2.2.2
  have hs := speed_le_mean_escape h hl hlm
  change Speed.speedValue μ l ≤ b / (2 - b) at hs
  have hm := mean_pos_critical h
  have hb1 : b < 1 := mean_escape_lt_one_critical h hl hlm
  have hden : 0 < 2 - b := by linarith
  have hml : 0 ≤ mean μ - l := sub_nonneg.mpr hlm.le
  have hmb : b * mean μ ≤ mean μ - l := (le_div_iff₀ hm).1 hb
  refine hs.trans ?_
  apply (div_le_div_iff₀ hden (by positivity : 0 < mean μ + l)).2
  nlinarith

private lemma integrable_offspring_second_ratio_critical (h : OffspringHyp μ) {l b : ℝ}
    (hl : 0 < l) (hb : 0 < b) :
    Integrable (fun k : ℕ => (k : ℝ) ^ 2 / (l + (k : ℝ) * b)) μ := by
  apply ((integrable_natCast_critical h).div_const b).mono
    (measurable_of_countable
      (fun k : ℕ => (k : ℝ) ^ 2 / (l + (k : ℝ) * b))).aestronglyMeasurable
  filter_upwards with k
  have hden : 0 < l + (k : ℝ) * b :=
    add_pos_of_pos_of_nonneg hl (mul_nonneg (Nat.cast_nonneg k) hb.le)
  have hratio : 0 ≤ (k : ℝ) ^ 2 / (l + (k : ℝ) * b) :=
    div_nonneg (sq_nonneg _) hden.le
  have hmajor : 0 ≤ (k : ℝ) / b := div_nonneg (Nat.cast_nonneg k) hb.le
  change ‖(k : ℝ) ^ 2 / (l + (k : ℝ) * b)‖ ≤ ‖(k : ℝ) / b‖
  rw [Real.norm_of_nonneg hratio, Real.norm_of_nonneg hmajor]
  apply (div_le_div_iff₀ hden hb).2
  nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ)) hl.le]

private lemma integrable_offspring_first_ratio_critical {μ : Measure ℕ}
    [IsProbabilityMeasure μ] {l b : ℝ} (hl : 0 < l) (hb : 0 < b) :
    Integrable (fun k : ℕ => (k : ℝ) / (l + (k : ℝ) * b)) μ := by
  apply Integrable.of_bound
    (measurable_of_countable
      (fun k : ℕ => (k : ℝ) / (l + (k : ℝ) * b))).aestronglyMeasurable b⁻¹
  filter_upwards with k
  have hden : 0 < l + (k : ℝ) * b :=
    add_pos_of_pos_of_nonneg hl (mul_nonneg (Nat.cast_nonneg k) hb.le)
  have hratio : 0 ≤ (k : ℝ) / (l + (k : ℝ) * b) :=
    div_nonneg (Nat.cast_nonneg k) hden.le
  change ‖(k : ℝ) / (l + (k : ℝ) * b)‖ ≤ b⁻¹
  rw [Real.norm_of_nonneg hratio]
  apply (div_le_iff₀ hden).2
  calc
    (k : ℝ) = b⁻¹ * ((k : ℝ) * b) := by
      field_simp
    _ ≤ b⁻¹ * (l + (k : ℝ) * b) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hb.le)

/-- The reciprocal-moment form of the first Jensen inequality in the mean-escape bound
`mean_escape_bounds`. -/
private lemma offspring_second_ratio_le_critical (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    let b := ∫ T, Speed.escape l T ∂GW μ
    (∫ k : ℕ, (k : ℝ) ^ 2 / (l + (k : ℝ) * b) ∂μ) ≤ (mean μ - l) / b := by
  dsimp only
  let b : ℝ := ∫ T, Speed.escape l T ∂GW μ
  let I : ℝ := ∫ k : ℕ, (k : ℝ) ^ 2 / (l + (k : ℝ) * b) ∂μ
  let J : ℝ := ∫ k : ℕ, (k : ℝ) / (l + (k : ℝ) * b) ∂μ
  have hb : 0 < b := (mean_escape_bounds h hl hlm).1
  have hI : Integrable (fun k : ℕ => (k : ℝ) ^ 2 / (l + (k : ℝ) * b)) μ :=
    integrable_offspring_second_ratio_critical h hl hb
  have hJ : Integrable (fun k : ℕ => (k : ℝ) / (l + (k : ℝ) * b)) μ :=
    integrable_offspring_first_ratio_critical hl hb
  have hfirst := (mean_escape_bounds h hl hlm).2.1
  change b ≤ ∫ k : ℕ, ((k : ℝ) * b) / (l + (k : ℝ) * b) ∂μ at hfirst
  have hfirst' : b ≤ b * J := by
    calc
      b ≤ ∫ k : ℕ, ((k : ℝ) * b) / (l + (k : ℝ) * b) ∂μ := hfirst
      _ = b * J := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun k => by
          dsimp [J]
          ring
  have hJone : 1 ≤ J := by
    exact (le_mul_iff_one_le_right hb).1 hfirst'
  have hident : I + (l / b) * J = mean μ / b := by
    calc
      I + (l / b) * J =
          ∫ k : ℕ, ((k : ℝ) ^ 2 / (l + (k : ℝ) * b) +
            (l / b) * ((k : ℝ) / (l + (k : ℝ) * b))) ∂μ := by
        dsimp [I, J]
        rw [← integral_const_mul]
        exact (integral_add hI (hJ.const_mul (l / b))).symm
      _ = ∫ k : ℕ, (k : ℝ) / b ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun k => by
          have hden : l + (k : ℝ) * b ≠ 0 :=
            (add_pos_of_pos_of_nonneg hl (mul_nonneg (Nat.cast_nonneg k) hb.le)).ne'
          field_simp
          ring
      _ = mean μ / b := by rw [integral_div, integral_natCast_eq_mean_critical]
  have hlb : 0 ≤ l / b := div_nonneg hl.le hb.le
  have hprod : l / b ≤ (l / b) * J := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hJone hlb
  change I ≤ (mean μ - l) / b
  calc
    I ≤ mean μ / b - l / b := by linarith
    _ = (mean μ - l) / b := by ring

private lemma tendsto_mean_escape_critical (h : OffspringHyp μ) :
    Tendsto (fun l => ∫ T, Speed.escape l T ∂GW μ) (𝓝[<] mean μ) (𝓝 0) := by
  let b : ℝ → ℝ := fun l => ∫ T, Speed.escape l T ∂GW μ
  have hm := mean_pos_critical h
  have hnonneg : ∀ᶠ l in 𝓝[<] mean μ, 0 ≤ b l := by
    filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hm), self_mem_nhdsWithin] with l hl hlm
    exact (mean_escape_bounds h hl hlm).1.le
  have hupper : ∀ᶠ l in 𝓝[<] mean μ, b l ≤ (mean μ - l) / mean μ := by
    filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hm), self_mem_nhdsWithin] with l hl hlm
    exact (mean_escape_bounds h hl hlm).2.2.2
  have hlim : Tendsto (fun l => (mean μ - l) / mean μ) (𝓝[<] mean μ) (𝓝 0) := by
    have ht : Tendsto (fun l : ℝ => mean μ - l) (𝓝[<] mean μ)
        (𝓝 (mean μ - mean μ)) :=
      tendsto_const_nhds.sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
    have ht0 : Tendsto (fun l : ℝ => mean μ - l) (𝓝[<] mean μ) (𝓝 0) := by
      simpa only [sub_self] using ht
    simpa only [zero_div] using ht0.div_const (mean μ)
  exact squeeze_zero' hnonneg hupper hlim

/-- Remark 2.3: the speed tends to zero from below the critical bias. -/
theorem tendsto_speed_critical (h : OffspringHyp μ) :
    Tendsto (Speed.speedValue μ) (𝓝[<] mean μ) (𝓝 0) := by
  let b : ℝ → ℝ := fun l => ∫ T, Speed.escape l T ∂GW μ
  have hm := mean_pos_critical h
  have hnonneg : ∀ᶠ l in 𝓝[<] mean μ, 0 ≤ Speed.speedValue μ l := by
    filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hm), self_mem_nhdsWithin] with l hl hlm
    exact le_of_lt (by
      rw [speedValue_eq_speedValueProv]
      exact speedValue_pos μ h l ⟨hl.le, hlm⟩)
  have hupper : ∀ᶠ l in 𝓝[<] mean μ,
      Speed.speedValue μ l ≤ (mean μ - l) / (mean μ + l) := by
    filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hm), self_mem_nhdsWithin] with l hl hlm
    exact speed_le_critical h hl hlm
  have hlim : Tendsto (fun l => (mean μ - l) / (mean μ + l)) (𝓝[<] mean μ) (𝓝 0) := by
    have ht : Tendsto (fun l : ℝ => mean μ - l) (𝓝[<] mean μ)
        (𝓝 (mean μ - mean μ)) :=
      tendsto_const_nhds.sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
    have hnum : Tendsto (fun l : ℝ => mean μ - l) (𝓝[<] mean μ) (𝓝 0) := by
      simpa only [sub_self] using ht
    have hd : Tendsto (fun l : ℝ => mean μ + l) (𝓝[<] mean μ)
        (𝓝 (mean μ + mean μ)) :=
      tendsto_const_nhds.add (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
    have hden : Tendsto (fun l : ℝ => mean μ + l) (𝓝[<] mean μ) (𝓝 (2 * mean μ)) := by
      simpa only [two_mul] using hd
    change Tendsto ((fun l : ℝ => mean μ - l) / (fun l => mean μ + l))
      (𝓝[<] mean μ) (𝓝 0)
    simpa only [zero_div] using hnum.div hden (by positivity : 2 * mean μ ≠ 0)
  exact squeeze_zero' hnonneg hupper hlim

private lemma lintegral_offspring_second_ratio_le_critical (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    let b := ∫ T, Speed.escape l T ∂GW μ
    (∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) ^ 2 / (l + (k : ℝ) * b)) ∂μ) ≤
      ENNReal.ofReal ((mean μ - l) / b) := by
  dsimp only
  let b : ℝ := ∫ T, Speed.escape l T ∂GW μ
  have hb : 0 < b := (mean_escape_bounds h hl hlm).1
  have hfi := integrable_offspring_second_ratio_critical h hl hb
  have hnonneg : 0 ≤ᵐ[μ] fun k : ℕ => (k : ℝ) ^ 2 / (l + (k : ℝ) * b) := by
    filter_upwards with k
    have hden : 0 < l + (k : ℝ) * b :=
      add_pos_of_pos_of_nonneg hl (mul_nonneg (Nat.cast_nonneg k) hb.le)
    exact div_nonneg (sq_nonneg _) hden.le
  calc
    (∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) ^ 2 / (l + (k : ℝ) * b)) ∂μ) =
        ENNReal.ofReal (∫ k : ℕ, (k : ℝ) ^ 2 / (l + (k : ℝ) * b) ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hfi hnonneg).symm
    _ ≤ ENNReal.ofReal ((mean μ - l) / b) :=
      ENNReal.ofReal_le_ofReal (offspring_second_ratio_le_critical h hl hlm)

private lemma secondMoment_div_mean_le_liminf_critical (h : OffspringHyp μ) :
    secondMoment μ / ENNReal.ofReal (mean μ) ≤
      liminf (fun l => ∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) ^ 2 /
        (l + (k : ℝ) * (∫ T, Speed.escape l T ∂GW μ))) ∂μ) (𝓝[<] mean μ) := by
  let b : ℝ → ℝ := fun l => ∫ T, Speed.escape l T ∂GW μ
  let F : ℝ → ℕ → ℝ≥0∞ := fun l k =>
    ENNReal.ofReal ((k : ℝ) ^ 2 / (l + (k : ℝ) * b l))
  have hm := mean_pos_critical h
  have hb := tendsto_mean_escape_critical h
  have hFmeas (l : ℝ) : Measurable (F l) :=
    ENNReal.measurable_ofReal.comp (measurable_of_countable _)
  have hpoint (k : ℕ) : Tendsto (fun l => F l k) (𝓝[<] mean μ)
      (𝓝 ((k : ℝ≥0∞) ^ 2 / ENNReal.ofReal (mean μ))) := by
    have hden : Tendsto (fun l => l + (k : ℝ) * b l) (𝓝[<] mean μ)
        (𝓝 (mean μ + (k : ℝ) * 0)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).add (tendsto_const_nhds.mul hb)
    have hden' : Tendsto (fun l => l + (k : ℝ) * b l) (𝓝[<] mean μ) (𝓝 (mean μ)) := by
      simpa only [mul_zero, add_zero] using hden
    have hr : Tendsto (fun l => (k : ℝ) ^ 2 / (l + (k : ℝ) * b l))
        (𝓝[<] mean μ) (𝓝 ((k : ℝ) ^ 2 / mean μ)) :=
      tendsto_const_nhds.div hden' hm.ne'
    simpa only [F, ENNReal.ofReal_div_of_pos hm, ENNReal.ofReal_pow (Nat.cast_nonneg k),
      ENNReal.ofReal_natCast] using ENNReal.tendsto_ofReal hr
  calc
    secondMoment μ / ENNReal.ofReal (mean μ) =
        ∫⁻ k : ℕ, (k : ℝ≥0∞) ^ 2 / ENNReal.ofReal (mean μ) ∂μ := by
      unfold secondMoment
      simp_rw [ENNReal.div_eq_inv_mul]
      exact (lintegral_const_mul (μ := μ) (f := fun k : ℕ => (k : ℝ≥0∞) ^ 2)
        (ENNReal.ofReal (mean μ))⁻¹ (measurable_of_countable _)).symm
    _ = ∫⁻ k : ℕ, liminf (fun l => F l k) (𝓝[<] mean μ) ∂μ := by
      apply lintegral_congr
      intro k
      exact (hpoint k).liminf_eq.symm
    _ ≤ liminf (fun l => ∫⁻ k : ℕ, F l k ∂μ) (𝓝[<] mean μ) :=
      lintegral_liminf_le hFmeas

private lemma ofReal_slope_le_critical (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    ENNReal.ofReal (Speed.speedValue μ l / (mean μ - l)) ≤
      ENNReal.ofReal (1 / (2 - (∫ T, Speed.escape l T ∂GW μ))) *
        (∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) ^ 2 /
          (l + (k : ℝ) * (∫ T, Speed.escape l T ∂GW μ))) ∂μ)⁻¹ := by
  let b : ℝ := ∫ T, Speed.escape l T ∂GW μ
  let I : ℝ := ∫ k : ℕ, (k : ℝ) ^ 2 / (l + (k : ℝ) * b) ∂μ
  let E : ℝ≥0∞ := ∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) ^ 2 / (l + (k : ℝ) * b)) ∂μ
  have hb : 0 < b := (mean_escape_bounds h hl hlm).1
  have hb1 : b < 1 := mean_escape_lt_one_critical h hl hlm
  have hden : 0 < 2 - b := by linarith
  have hd : 0 < mean μ - l := sub_pos.mpr hlm
  have hIle : E ≤ ENNReal.ofReal ((mean μ - l) / b) := lintegral_offspring_second_ratio_le_critical h hl hlm
  have hE : E = ENNReal.ofReal I := by
    dsimp [E, I]
    exact (ofReal_integral_eq_lintegral_ofReal
      (integrable_offspring_second_ratio_critical h hl hb) (by
        filter_upwards with k
        have hden : 0 < l + (k : ℝ) * b :=
          add_pos_of_pos_of_nonneg hl (mul_nonneg (Nat.cast_nonneg k) hb.le)
        exact div_nonneg (sq_nonneg _) hden.le)).symm
  have hv := speed_le_mean_escape h hl hlm
  change Speed.speedValue μ l ≤ b / (2 - b) at hv
  have hr : Speed.speedValue μ l / (mean μ - l) ≤
      (1 / (2 - b)) * (b / (mean μ - l)) := by
    calc
      Speed.speedValue μ l / (mean μ - l) ≤ (b / (2 - b)) / (mean μ - l) :=
        div_le_div_of_nonneg_right hv hd.le
      _ = (1 / (2 - b)) * (b / (mean μ - l)) := by ring
  have hrecip : ENNReal.ofReal (b / (mean μ - l)) =
      (ENNReal.ofReal ((mean μ - l) / b))⁻¹ := by
    rw [show b / (mean μ - l) = ((mean μ - l) / b)⁻¹ by
      field_simp]
    exact ENNReal.ofReal_inv_of_pos (div_pos hd hb)
  change ENNReal.ofReal (Speed.speedValue μ l / (mean μ - l)) ≤
    ENNReal.ofReal (1 / (2 - b)) * E⁻¹
  calc
    ENNReal.ofReal (Speed.speedValue μ l / (mean μ - l)) ≤
        ENNReal.ofReal ((1 / (2 - b)) * (b / (mean μ - l))) :=
      ENNReal.ofReal_le_ofReal hr
    _ = ENNReal.ofReal (1 / (2 - b)) * ENNReal.ofReal (b / (mean μ - l)) := by
      rw [ENNReal.ofReal_mul (div_nonneg zero_le_one hden.le)]
    _ = ENNReal.ofReal (1 / (2 - b)) * (ENNReal.ofReal ((mean μ - l) / b))⁻¹ := by rw [hrecip]
    _ ≤ ENNReal.ofReal (1 / (2 - b)) * E⁻¹ :=
      mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr hIle)

private lemma tendsto_critical_factor (h : OffspringHyp μ) :
    Tendsto (fun l => ENNReal.ofReal
      (1 / (2 - (∫ T, Speed.escape l T ∂GW μ)))) (𝓝[<] mean μ)
      (𝓝 (ENNReal.ofReal ((1 : ℝ) / 2))) := by
  let b : ℝ → ℝ := fun l => ∫ T, Speed.escape l T ∂GW μ
  have hb := tendsto_mean_escape_critical h
  have hsub : Tendsto (fun l => 2 - b l) (𝓝[<] mean μ) (𝓝 (2 - 0)) :=
    tendsto_const_nhds.sub hb
  have hsub' : Tendsto (fun l => 2 - b l) (𝓝[<] mean μ) (𝓝 2) := by
    simpa only [sub_zero] using hsub
  have hr : Tendsto (fun l => 1 / (2 - b l)) (𝓝[<] mean μ) (𝓝 ((2 : ℝ)⁻¹)) := by
    simpa only [one_div] using hsub'.inv₀ (by norm_num : (2 : ℝ) ≠ 0)
  simpa only [one_div] using ENNReal.tendsto_ofReal hr

/-- Remark 2.3: the extended-valued limsup bound at the critical bias. -/
theorem limsup_speed_critical (h : OffspringHyp μ) :
    limsup (fun l => ENNReal.ofReal (Speed.speedValue μ l / (mean μ - l)))
      (𝓝[<] mean μ) ≤ ENNReal.ofReal (mean μ) / (2 * secondMoment μ) := by
  let b : ℝ → ℝ := fun l => ∫ T, Speed.escape l T ∂GW μ
  let I : ℝ → ℝ≥0∞ := fun l => ∫⁻ k : ℕ,
    ENNReal.ofReal ((k : ℝ) ^ 2 / (l + (k : ℝ) * b l)) ∂μ
  let q : ℝ → ℝ≥0∞ := fun l => ENNReal.ofReal (1 / (2 - b l))
  let s : ℝ → ℝ≥0∞ := fun l => ENNReal.ofReal (Speed.speedValue μ l / (mean μ - l))
  have hm := mean_pos_critical h
  have hs : ∀ᶠ l in 𝓝[<] mean μ, s l ≤ q l * (I l)⁻¹ := by
    filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hm), self_mem_nhdsWithin] with l hl hlm
    exact ofReal_slope_le_critical h hl hlm
  have hq : Tendsto q (𝓝[<] mean μ) (𝓝 (ENNReal.ofReal ((1 : ℝ) / 2))) :=
    tendsto_critical_factor h
  have hI := secondMoment_div_mean_le_liminf_critical h
  change secondMoment μ / ENNReal.ofReal (mean μ) ≤ liminf I (𝓝[<] mean μ) at hI
  have hmain : limsup s (𝓝[<] mean μ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2) * (secondMoment μ / ENNReal.ofReal (mean μ))⁻¹ := by
    calc
      limsup s (𝓝[<] mean μ) ≤ limsup (fun l => q l * (I l)⁻¹) (𝓝[<] mean μ) :=
        limsup_le_limsup hs
      _ ≤ limsup q (𝓝[<] mean μ) * limsup (fun l => (I l)⁻¹) (𝓝[<] mean μ) :=
        ENNReal.limsup_mul_le'
          (Or.inl (by
            rw [hq.limsup_eq]
            exact (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).ne'))
          (Or.inl (by rw [hq.limsup_eq]; exact ENNReal.ofReal_ne_top))
      _ = ENNReal.ofReal ((1 : ℝ) / 2) * (liminf I (𝓝[<] mean μ))⁻¹ := by
        rw [hq.limsup_eq, ← ENNReal.inv_liminf]
      _ ≤ ENNReal.ofReal ((1 : ℝ) / 2) *
          (secondMoment μ / ENNReal.ofReal (mean μ))⁻¹ :=
        mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr hI)
  change limsup s (𝓝[<] mean μ) ≤ ENNReal.ofReal (mean μ) / (2 * secondMoment μ)
  refine hmain.trans_eq ?_
  have hm0 : ENNReal.ofReal (mean μ) ≠ 0 := ENNReal.ofReal_pos.mpr hm |>.ne'
  have hmt : ENNReal.ofReal (mean μ) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.inv_div (a := secondMoment μ) (b := ENNReal.ofReal (mean μ))
    (Or.inl hmt) (Or.inl hm0)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div]
  simp only [ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (a := (2 : ℝ≥0∞)) (b := secondMoment μ)
    (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  simp only [mul_assoc]

/-- Remark 2.3: with infinite offspring second moment, the critical slope tends to zero. -/
theorem tendsto_slope_critical_of_infinite (h : OffspringHyp μ)
    (h2 : secondMoment μ = ⊤) :
    Tendsto (fun l => Speed.speedValue μ l / (mean μ - l)) (𝓝[<] mean μ) (𝓝 0) := by
  let s : ℝ → ℝ≥0∞ := fun l => ENNReal.ofReal (Speed.speedValue μ l / (mean μ - l))
  have hs : limsup s (𝓝[<] mean μ) ≤ 0 := by
    have hlim := limsup_speed_critical h
    change limsup s (𝓝[<] mean μ) ≤ ENNReal.ofReal (mean μ) / (2 * secondMoment μ) at hlim
    simpa only [h2, ENNReal.mul_top (by norm_num : (2 : ℝ≥0∞) ≠ 0),
      ENNReal.div_top] using hlim
  have ht : Tendsto s (𝓝[<] mean μ) (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le bot_le hs
  have hr := (ENNReal.tendsto_toReal_zero_iff (fun l => ENNReal.ofReal_ne_top)).2 ht
  have hm := mean_pos_critical h
  have heq : (fun l => (s l).toReal) =ᶠ[𝓝[<] mean μ]
      (fun l => Speed.speedValue μ l / (mean μ - l)) := by
    filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hm), self_mem_nhdsWithin] with l hl hlm
    have hv : 0 ≤ Speed.speedValue μ l := by
      rw [speedValue_eq_speedValueProv]
      exact (speedValue_pos μ h l ⟨hl.le, hlm⟩).le
    exact ENNReal.toReal_ofReal (div_nonneg hv (sub_pos.mpr hlm).le)
  exact hr.congr' heq

end LPPMonotonicityProof.Analytic
