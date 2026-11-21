module

public import LPPMonotonicityProof.Speed.Signed.Exchange

/-! # Bounds for the two-copy kernels (equation (2.2), `eq:kernel-bounds`) -/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

lemma ae_pair_goodEsc (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) :
    ∀ᵐ p : ℝ × ℝ ∂(escLaw μ l).prod (escLaw μ l), GoodEsc l p.1 ∧ GoodEsc l p.2 := by
  have hg := ae_goodEsc μ hl hμ hlm
  filter_upwards [(measurePreserving_fst (μ := escLaw μ l)
    (ν := escLaw μ l)).quasiMeasurePreserving.ae hg,
    (measurePreserving_snd (μ := escLaw μ l)
      (ν := escLaw μ l)).quasiMeasurePreserving.ae hg] with p hp1 hp2
  exact ⟨hp1, hp2⟩

lemma Dfun_le {l b b' : ℝ} (hb : GoodEsc l b) (hb' : GoodEsc l b') : Dfun l b b' ≤ l := by
  have hp : 0 ≤ (1 - b) * (1 - b') := mul_nonneg (by linarith [hb.2.1]) (by linarith [hb'.2.1])
  unfold Dfun
  nlinarith

lemma Dfun_ge_left {l b b' : ℝ} (hb : GoodEsc l b) (hb' : GoodEsc l b') :
    min 1 l * b ≤ Dfun l b b' := by
  by_cases hl : l < 1
  · rw [min_eq_right hl.le]
    have hb'l := hb'.2.2 hl
    have hb1 := hb.2.1.le
    have hp : 0 ≤ (1 - b) * (l - 1 + b') :=
      mul_nonneg (sub_nonneg.mpr hb1) (by linarith)
    unfold Dfun
    nlinarith
  · rw [min_eq_left (by linarith)]
    have hb0 := hb.1.le
    have hb'0 := hb'.1.le
    have hb1 := hb.2.1.le
    unfold Dfun
    nlinarith

lemma Dfun_ge_right {l b b' : ℝ} (hb : GoodEsc l b) (hb' : GoodEsc l b') :
    min 1 l * b' ≤ Dfun l b b' := by
  rw [Dfun, show l - 1 + b + b' - b * b' = l - 1 + b' + b - b' * b by ring]
  exact Dfun_ge_left hb' hb

lemma Dfun_lower {l b b' : ℝ} (hb : GoodEsc l b) (hb' : GoodEsc l b') :
    min 1 l * max b b' ≤ Dfun l b b' := by
  rcases le_total b b' with h | h
  · rw [max_eq_right h]
    exact Dfun_ge_right hb hb'
  · rw [max_eq_left h]
    exact Dfun_ge_left hb hb'

lemma Dfun_pos_of_good {l : ℝ} (hl : 0 < l) {b b' : ℝ}
    (hb : GoodEsc l b) (hb' : GoodEsc l b') : 0 < Dfun l b b' := by
  have hm : 0 < min 1 l := lt_min zero_lt_one hl
  have hx : 0 < max b b' := lt_max_of_lt_left hb.1
  exact (mul_pos hm hx).trans_le (Dfun_lower hb hb')

lemma tau_pos_of_good {l b b' : ℝ} (hb : GoodEsc l b) (hb' : GoodEsc l b') :
    0 < b + b' - b * b' := by
  have h : 0 < b * (1 - b') + b' :=
    add_pos_of_pos_of_nonneg (mul_pos hb.1 (by linarith [hb'.2.1])) hb'.1.le
  nlinarith

lemma tau_le_two_max {l b b' : ℝ} (hb : GoodEsc l b) (hb' : GoodEsc l b') :
    b + b' - b * b' ≤ 2 * max b b' := by
  have hb0 := hb.1.le
  have hb'0 := hb'.1.le
  have hb1 := hb.2.1.le
  have hb'1 := hb'.2.1.le
  rcases le_total b b' with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith

lemma prod_lt_tau_of_good {l b b' : ℝ} (hb : GoodEsc l b) (hb' : GoodEsc l b') :
    b * b' < b + b' - b * b' := by
  have h : 0 < b * (1 - b') + b' * (1 - b) :=
    add_pos_of_pos_of_nonneg (mul_pos hb.1 (by linarith [hb'.2.1]))
      (mul_nonneg hb'.1.le (by linarith [hb.2.1]))
  nlinarith

lemma measurable_Dfun (l : ℝ) : Measurable fun p : ℝ × ℝ => Dfun l p.1 p.2 := by
  exact (((measurable_const.sub measurable_const).add measurable_fst).add measurable_snd).sub
    (measurable_fst.mul measurable_snd)

lemma integrable_N_kernel (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) :
    Integrable (fun p : ℝ × ℝ => p.1 * p.2 / Dfun l p.1 p.2)
      ((escLaw μ l).prod (escLaw μ l)) := by
  let C := 2 / min 1 l
  apply (integrable_const C).mono
    ((measurable_fst.mul measurable_snd).div (measurable_Dfun l)).aestronglyMeasurable
  filter_upwards [ae_pair_goodEsc μ hl hμ hlm] with p hp
  have hD := Dfun_pos_of_good hl hp.1 hp.2
  have hlo := Dfun_lower hp.1 hp.2
  have hmax0 : 0 ≤ max p.1 p.2 := (hp.1.1.trans_le (le_max_left _ _)).le
  have hprod : p.1 * p.2 ≤ max p.1 p.2 := by
    calc
      p.1 * p.2 ≤ max p.1 p.2 * p.2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hp.2.1.le
      _ ≤ max p.1 p.2 * 1 := mul_le_mul_of_nonneg_left hp.2.2.1.le hmax0
      _ = max p.1 p.2 := mul_one _
  change ‖p.1 * p.2 / Dfun l p.1 p.2‖ ≤ ‖C‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos hD,
    abs_of_pos (mul_pos hp.1.1 hp.2.1), abs_of_nonneg (by positivity : 0 ≤ C)]
  apply (div_le_iff₀ hD).2
  calc
    p.1 * p.2 ≤ max p.1 p.2 := hprod
    _ ≤ C * Dfun l p.1 p.2 := by
      have hmul := mul_le_mul_of_nonneg_left hlo (show 0 ≤ C by positivity)
      have hid : C * (min 1 l * max p.1 p.2) = 2 * max p.1 p.2 := by
        have hmin : 0 < min 1 l := lt_min zero_lt_one hl
        dsimp [C]
        field_simp
      rw [hid] at hmul
      exact (show max p.1 p.2 ≤ 2 * max p.1 p.2 by nlinarith).trans hmul


lemma integrable_Z_kernel (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) :
    Integrable (fun p : ℝ × ℝ => (p.1 + p.2 - p.1 * p.2) / Dfun l p.1 p.2)
      ((escLaw μ l).prod (escLaw μ l)) := by
  let C := 2 / min 1 l
  apply (integrable_const C).mono
    (((measurable_fst.add measurable_snd).sub (measurable_fst.mul measurable_snd)).div
      (measurable_Dfun l)).aestronglyMeasurable
  filter_upwards [ae_pair_goodEsc μ hl hμ hlm] with p hp
  have hD := Dfun_pos_of_good hl hp.1 hp.2
  have ht0 := (tau_pos_of_good hp.1 hp.2).le
  change ‖(p.1 + p.2 - p.1 * p.2) / Dfun l p.1 p.2‖ ≤ ‖C‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos hD, abs_of_nonneg ht0,
    abs_of_nonneg (by positivity : 0 ≤ C)]
  apply (div_le_iff₀ hD).2
  calc
    p.1 + p.2 - p.1 * p.2 ≤ 2 * max p.1 p.2 := tau_le_two_max hp.1 hp.2
    _ = C * (min 1 l * max p.1 p.2) := by
      have hmin : 0 < min 1 l := lt_min zero_lt_one hl
      dsimp [C]
      field_simp
    _ ≤ C * Dfun l p.1 p.2 :=
      mul_le_mul_of_nonneg_left (Dfun_lower hp.1 hp.2) (by positivity)

lemma integral_pos_of_ae_pos {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    [IsProbabilityMeasure ρ] {f : α → ℝ} (hfint : Integrable f ρ)
    (hf : ∀ᵐ x ∂ρ, 0 < f x) : 0 < ∫ x, f x ∂ρ := by
  rw [integral_pos_iff_support_of_nonneg_ae (hf.mono fun _ h => h.le) hfint]
  have heq : Function.support f =ᵐ[ρ] Set.univ := by
    filter_upwards [hf] with x hx
    simp [Function.support, ne_of_gt hx]
  rw [measure_congr heq, measure_univ]
  exact zero_lt_one

/-- Equation (2.2) and its consequence `0 < N`: the two-copy numerator is strictly
positive. -/
theorem Nval_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) : 0 < Nval μ l := by
  unfold Nval
  apply integral_pos_of_ae_pos (integrable_N_kernel μ hl hμ hlm)
  filter_upwards [ae_pair_goodEsc μ hl hμ hlm] with p hp
  exact div_pos (mul_pos hp.1.1 hp.2.1) (Dfun_pos_of_good hl hp.1 hp.2)

/-- Equation (2.2) and its consequences: the two-copy denominator is strictly
positive. -/
theorem Zval_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) : 0 < Zval μ l := by
  unfold Zval
  apply integral_pos_of_ae_pos (integrable_Z_kernel μ hl hμ hlm)
  filter_upwards [ae_pair_goodEsc μ hl hμ hlm] with p hp
  exact div_pos (tau_pos_of_good hp.1 hp.2) (Dfun_pos_of_good hl hp.1 hp.2)

/-- The exact strict ordering `0 < N < Z`, with integrability supplying the
finiteness `Z < ∞` stated after equation (2.2). -/
theorem Nval_lt_Zval (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) : Nval μ l < Zval μ l := by
  have hN := integrable_N_kernel μ hl hμ hlm
  have hZ := integrable_Z_kernel μ hl hμ hlm
  have hpos : 0 < ∫ p, ((p.1 + p.2 - p.1 * p.2) / Dfun l p.1 p.2 -
      p.1 * p.2 / Dfun l p.1 p.2) ∂(escLaw μ l).prod (escLaw μ l) := by
    apply integral_pos_of_ae_pos (hZ.sub hN)
    filter_upwards [ae_pair_goodEsc μ hl hμ hlm] with p hp
    have hD := Dfun_pos_of_good hl hp.1 hp.2
    have ht := prod_lt_tau_of_good hp.1 hp.2
    exact sub_pos.mpr (div_lt_div_of_pos_right ht hD)
  rw [integral_sub hZ hN] at hpos
  exact sub_pos.mp hpos

end LPPMonotonicityProof.Speed
