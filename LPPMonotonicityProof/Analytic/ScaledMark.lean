module

public import LPPMonotonicityProof.Analytic.ScaledSeries
public import LPPMonotonicityProof.Analytic.Ceiling2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Differentiation of the speed in its scaled moments

This module proves Lemma 4.4 (`lem:scaled-mark`) and equation (4.2) (`eq:scaled-mark`):
the scaled chain rule, the bounds for the moment coefficients, their
transformed-moment formula, and the lower bound for `S - γT`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

private lemma Vsc_pos_f7 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : 0 < Vsc μ l := by
  have hr := rr_pos μ h hl hlm
  have hx := xS_pos (μ := μ) h hl
  have hxV : xS μ l * Vsc μ l = rr μ l := by
    unfold xS Vsc rr
    field_simp [(pBr_pos h).ne', (show l - 1 ≠ 0 by linarith)]
  by_contra hn
  have hV0 : Vsc μ l ≤ 0 := le_of_not_gt hn
  have := mul_nonpos_of_nonneg_of_nonpos hx.le hV0
  linarith

private lemma mMom_one_pos_f7 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : 0 < mMom μ l 1 := by
  have hm : momY μ l 1 = xS μ l * mMom μ l 1 := by
    simpa using momY_eq_mMom (μ := μ) h hl hlm 1 le_rfl
  have hmu : 0 < momY μ l 1 := by
    simpa only [momY, pow_one, muY] using (muY_mem μ h hl hlm).1
  have hx := xS_pos (μ := μ) h hl
  by_contra hn
  have hm0 : mMom μ l 1 ≤ 0 := le_of_not_gt hn
  have := mul_nonpos_of_nonneg_of_nonpos hx.le hm0
  linarith

private lemma integrable_Yt_pow_f7 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : Integrable (fun T => Yt l T ^ n) (GW μ) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_Yt l).pow_const n).aestronglyMeasurable
  filter_upwards [ae_escape_pos h (by linarith) hlm] with T hT
  obtain ⟨hy0, hy1⟩ := Yt_mem hl hT
  have hy1' : Yt l T ≤ 1 := by
    have hy := hy1.trans ((div_lt_one (by linarith : 0 < l)).2 hl)
    exact hy.le
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy0.le _)]
  exact pow_le_one₀ hy0.le hy1'

/-- The transformed-moment formula for `Cₙ`. -/
theorem Ccoef_eq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (hn : 1 ≤ n) :
    Ccoef μ l n = kS l ^ (n - 1) *
      ∫ T, Yt l T ^ (n - 1) * (1 - Yt l T) * (1 - l * Yt l T) ∂GW μ := by
  have hk : 0 < kS l := kS_pos hl
  have hpow (j : ℕ) : Integrable (fun T => Yt l T ^ j) (GW μ) :=
    integrable_Yt_pow_f7 μ h hl hlm j
  have hint : (∫ T, Yt l T ^ (n - 1) * (1 - Yt l T) * (1 - l * Yt l T) ∂GW μ) =
      momY μ l (n - 1) - (1 + l) * momY μ l n + l * momY μ l (n + 1) := by
    unfold momY
    calc
      _ = ∫ T, (Yt l T ^ (n - 1) - (1 + l) * Yt l T ^ n) +
          l * Yt l T ^ (n + 1) ∂GW μ := by
        apply integral_congr_ae
        filter_upwards with T
        have hn1 : Yt l T ^ n = Yt l T ^ (n - 1) * Yt l T := by
          rw [← pow_succ, Nat.sub_add_cancel hn]
        have hn2 : Yt l T ^ (n + 1) = Yt l T ^ (n - 1) * Yt l T ^ 2 := by
          rw [← pow_add]
          congr 1
          omega
        rw [hn1, hn2]
        ring
      _ = _ := by
        have hleft : Integrable (fun T => Yt l T ^ (n - 1) - (1 + l) * Yt l T ^ n)
            (GW μ) := (hpow (n - 1)).sub ((hpow n).const_mul (1 + l))
        have hright : Integrable (fun T => l * Yt l T ^ (n + 1)) (GW μ) :=
          (hpow (n + 1)).const_mul l
        rw [integral_add hleft hright,
          integral_sub (hpow (n - 1)) ((hpow n).const_mul (1 + l)),
          integral_const_mul, integral_const_mul]
  rw [Ccoef, hint]
  by_cases hn1 : n = 1
  · subst n
    have hm1 : momY μ l 1 = xS μ l * mMom μ l 1 := by
      simpa using momY_eq_mMom (μ := μ) h hl hlm 1 le_rfl
    have hm2 : momY μ l 2 = xS μ l * kS l ^ (-1 : ℤ) * mMom μ l 2 := by
      simpa using momY_eq_mMom (μ := μ) h hl hlm 2 (by omega)
    have hm0 : mMom μ l 0 = 0 := by simp [mMom]
    have hY0 : momY μ l 0 = 1 := by simp [momY]
    rw [hm1, hm2]
    simp only [Nat.reduceAdd, Nat.reduceSub, pow_zero, one_mul, pow_one, hm0, hY0,
      Nat.one_ne_zero, ↓reduceIte, zero_add, zpow_neg, zpow_one]
    have hkl : l * (kS l)⁻¹ = kS l := by
      have hksq := kS_sq hl
      field_simp [hk.ne']
      nlinarith
    symm
    calc
      _ = 1 - (1 + l) * (xS μ l * mMom μ l 1) +
          xS μ l * (l * (kS l)⁻¹) * mMom μ l 2 := by ring
      _ = _ := by rw [hkl]; ring
  · have hn2 : 2 ≤ n := by omega
    have hmn : momY μ l n = xS μ l * kS l ^ (1 - (n : ℤ)) * mMom μ l n :=
      momY_eq_mMom (μ := μ) h hl hlm n hn
    have hmn1 : momY μ l (n + 1) =
        xS μ l * kS l ^ (-(n : ℤ)) * mMom μ l (n + 1) := by
      simpa using momY_eq_mMom (μ := μ) h hl hlm (n + 1) (by omega)
    have hmnp : momY μ l (n - 1) =
        xS μ l * kS l ^ (1 - (((n - 1 : ℕ) : ℤ))) * mMom μ l (n - 1) := by
      rw [momY_eq_mMom (μ := μ) h hl hlm (n - 1) (by omega)]
    rw [hmn, hmn1, hmnp]
    have hpow1 : kS l ^ (n - 1) * kS l ^ (1 - (((n - 1 : ℕ) : ℤ))) = kS l := by
      rw [← zpow_natCast (kS l) (n - 1), ← zpow_add₀ hk.ne']
      have he : (((n - 1 : ℕ) : ℤ)) + (1 - (((n - 1 : ℕ) : ℤ))) = 1 := by ring
      rw [he, zpow_one]
    have hpow2 : kS l ^ (n - 1) * kS l ^ (1 - (n : ℤ)) = 1 := by
      rw [← zpow_natCast (kS l) (n - 1), ← zpow_add₀ hk.ne']
      have he : (((n - 1 : ℕ) : ℤ)) + (1 - (n : ℤ)) = 0 := by omega
      rw [he, zpow_zero]
    have hpow3 : kS l ^ (n - 1) * kS l ^ (-(n : ℤ)) = (kS l)⁻¹ := by
      rw [← zpow_natCast (kS l) (n - 1), ← zpow_add₀ hk.ne']
      have he : (((n - 1 : ℕ) : ℤ)) + (-(n : ℤ)) = -1 := by omega
      rw [he, zpow_neg_one]
    have hkl : l * (kS l)⁻¹ = kS l := by
      have hksq := kS_sq hl
      field_simp [hk.ne']
      nlinarith
    simp only [Nat.add_sub_cancel, if_neg hn1, zero_add]
    symm
    calc
      _ = xS μ l * ((kS l ^ (n - 1) * kS l ^ (1 - (((n - 1 : ℕ) : ℤ))) *
            mMom μ l (n - 1)) -
          (1 + l) * (kS l ^ (n - 1) * kS l ^ (1 - (n : ℤ))) * mMom μ l n +
          l * (kS l ^ (n - 1) * kS l ^ (-(n : ℤ))) * mMom μ l (n + 1)) := by ring
      _ = xS μ l * (kS l * mMom μ l (n - 1) - (1 + l) * mMom μ l n +
          l * (kS l)⁻¹ * mMom μ l (n + 1)) := by rw [hpow1, hpow2, hpow3]; ring
      _ = _ := by rw [hkl]; ring

private lemma Ccoef_nonneg_f7 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ Ccoef μ l n := by
  rw [Ccoef_eq μ h hl hlm hn]
  apply mul_nonneg (pow_nonneg (kS_pos hl).le _)
  apply integral_nonneg_of_ae
  filter_upwards [ae_escape_pos h (by linarith) hlm] with T hT
  obtain ⟨hy0, hy1⟩ := Yt_mem hl hT
  have hl0 : 0 < l := by linarith
  have hy1' : Yt l T ≤ 1 := by
    exact (hy1.trans ((div_lt_one hl0).2 hl)).le
  have hly : l * Yt l T ≤ 1 := by
    calc
      l * Yt l T ≤ l * (1 / l) := mul_le_mul_of_nonneg_left hy1.le hl0.le
      _ = 1 := by field_simp
  exact mul_nonneg (mul_nonneg (pow_nonneg hy0.le _) (by linarith)) (by linarith)

private lemma xS_mul_Vsc_f7 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) :
    xS μ l * Vsc μ l = rr μ l := by
  unfold xS Vsc rr
  field_simp [(pBr_pos h).ne', (show l - 1 ≠ 0 by linarith)]

private lemma xS_mul_Dcoef_f7 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (hn : 1 ≤ n) :
    xS μ l * Dcoef μ l n = ∫ T, (kS l * Yt l T) ^ (n - 1) *
      fθ l (rr μ l) 0 (Yt l T) ∂GW μ := by
  have hk : 0 < kS l := kS_pos hl
  have hm : momY μ l n = xS μ l * kS l ^ (1 - (n : ℤ)) * mMom μ l n :=
    momY_eq_mMom (μ := μ) h hl hlm n hn
  have hpow : kS l ^ (1 - (n : ℤ)) * kS l ^ (n - 1) = 1 := by
    rw [← zpow_natCast (kS l) (n - 1), ← zpow_add₀ hk.ne']
    convert zpow_zero (kS l) using 2
    omega
  have hxm : xS μ l * mMom μ l n = kS l ^ (n - 1) * momY μ l n := by
    calc
      _ = (kS l ^ (1 - (n : ℤ)) * kS l ^ (n - 1)) * (xS μ l * mMom μ l n) := by
        rw [hpow, one_mul]
      _ = kS l ^ (n - 1) * (xS μ l * kS l ^ (1 - (n : ℤ)) * mMom μ l n) := by ring
      _ = _ := by rw [← hm]
  have hxv : xS μ l * (Vsc μ l * (kS l ^ (n - 1) *
      ∫ T, Yt l T ^ (n - 1) * (1 - Yt l T) * (1 - l * Yt l T) ∂GW μ)) =
      rr μ l * (kS l ^ (n - 1) *
        ∫ T, Yt l T ^ (n - 1) * (1 - Yt l T) * (1 - l * Yt l T) ∂GW μ) := by
    calc
      _ = (xS μ l * Vsc μ l) * (kS l ^ (n - 1) *
          ∫ T, Yt l T ^ (n - 1) * (1 - Yt l T) * (1 - l * Yt l T) ∂GW μ) := by ring
      _ = _ := by rw [xS_mul_Vsc_f7 μ h hl]
  rw [Dcoef, Ccoef_eq μ h hl hlm hn, mul_sub, hxm, hxv]
  have hI : Integrable (fun T => Yt l T ^ (n - 1) * (1 - Yt l T) *
      (1 - l * Yt l T)) (GW μ) := by
    have h0 := integrable_Yt_pow_f7 μ h hl hlm (n - 1)
    have h1 := integrable_Yt_pow_f7 μ h hl hlm n
    have h2 := integrable_Yt_pow_f7 μ h hl hlm (n + 1)
    have heq : (fun T => Yt l T ^ (n - 1) * (1 - Yt l T) * (1 - l * Yt l T)) =
        fun T => (Yt l T ^ (n - 1) - (1 + l) * Yt l T ^ n) + l * Yt l T ^ (n + 1) := by
      funext T
      have hn1 : Yt l T ^ n = Yt l T ^ (n - 1) * Yt l T := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      have hn2 : Yt l T ^ (n + 1) = Yt l T ^ (n - 1) * Yt l T ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      rw [hn1, hn2]
      ring
    rw [heq]
    exact (h0.sub (h1.const_mul (1 + l))).add (h2.const_mul l)
  unfold momY fθ
  have hlin : (∫ T, Yt l T ^ n ∂GW μ) - rr μ l *
      (∫ T, Yt l T ^ (n - 1) * (1 - Yt l T) * (1 - l * Yt l T) ∂GW μ) =
      ∫ T, Yt l T ^ n - rr μ l *
        (Yt l T ^ (n - 1) * (1 - Yt l T) * (1 - l * Yt l T)) ∂GW μ := by
    rw [integral_sub (integrable_Yt_pow_f7 μ h hl hlm n) (hI.const_mul (rr μ l)),
      integral_const_mul]
  calc
    _ = kS l ^ (n - 1) * ((∫ T, Yt l T ^ n ∂GW μ) - rr μ l *
        (∫ T, Yt l T ^ (n - 1) * (1 - Yt l T) * (1 - l * Yt l T) ∂GW μ)) := by ring
    _ = kS l ^ (n - 1) * ∫ T, (Yt l T ^ n - rr μ l *
        (Yt l T ^ (n - 1) * (1 - Yt l T) * (1 - l * Yt l T))) ∂GW μ := by rw [hlin]
    _ = ∫ T, kS l ^ (n - 1) * (Yt l T ^ n - rr μ l *
        (Yt l T ^ (n - 1) * (1 - Yt l T) * (1 - l * Yt l T))) ∂GW μ := by
      rw [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with T
      simp only [zero_mul, sub_zero, mul_pow]
      have hY : Yt l T ^ n = Yt l T ^ (n - 1) * Yt l T := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      rw [hY]
      ring

/-- The coefficient `Dₙ` lies between zero and `mₙ`. -/
theorem Dcoef_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ Dcoef μ l n ∧ Dcoef μ l n ≤ mMom μ l n := by
  have hx := xS_pos (μ := μ) h hl
  have hDpos : 0 < xS μ l * Dcoef μ l n := by
    rw [xS_mul_Dcoef_f7 μ h hl hlm hn]
    exact f0_rank_pos μ h hl hlm (n - 1)
  have hD0 : 0 ≤ Dcoef μ l n := by
    by_contra hn0
    have := mul_nonpos_of_nonneg_of_nonpos hx.le (lt_of_not_ge hn0).le
    linarith
  have hC := Ccoef_nonneg_f7 μ h hl hlm hn
  have hV := (Vsc_pos_f7 μ h hl hlm).le
  exact ⟨hD0, by unfold Dcoef; nlinarith [mul_nonneg hV hC]⟩

private lemma Ssc_pos_f7 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : 0 < Ssc μ l := by
  unfold Ssc
  exact (summable_Ssc (μ := μ) h hl hlm).tsum_pos (fun n => sq_nonneg _) 0
    (by simpa using pow_pos (mMom_one_pos_f7 μ h hl hlm) 2)

private lemma Tsc_le_f7 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : Tsc μ l ≤ Ssc μ l / kS l := by
  have hk := kS_pos hl
  have hterm : ∀ n : ℕ, mMom μ l (n + 1) * mMom μ l (n + 2) ≤
      mMom μ l (n + 1) ^ 2 / kS l := by
    intro n
    have hs := mMom_succ_le (μ := μ) h hl hlm (n := n + 1) (by omega)
    have hm := (mMom_mem (μ := μ) h hl hlm (n + 1)).1
    calc
      _ ≤ mMom μ l (n + 1) * (mMom μ l (n + 1) / kS l) :=
        mul_le_mul_of_nonneg_left hs hm
      _ = _ := by ring
  unfold Tsc Ssc
  rw [← tsum_div_const]
  exact (summable_Tsc (μ := μ) h hl hlm).tsum_le_tsum hterm
    ((summable_Ssc (μ := μ) h hl hlm).div_const (kS l))

/-- The positive deficit `S - γT`. -/
theorem S_sub_gamT (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    (l - 1) * Ssc μ l / (2 * l) ≤ Ssc μ l - gamS l * Tsc μ l ∧ 0 < Ssc μ l := by
  have hk := kS_pos hl
  have hS := Ssc_pos_f7 μ h hl hlm
  have hT := Tsc_le_f7 μ h hl hlm
  have hg : 0 ≤ gamS l := by unfold gamS; positivity
  have hγT : gamS l * Tsc μ l ≤ gamS l * (Ssc μ l / kS l) :=
    mul_le_mul_of_nonneg_left hT hg
  have hid : Ssc μ l - gamS l * (Ssc μ l / kS l) =
      (l - 1) * Ssc μ l / (2 * l) := by
    unfold gamS
    have hksq := kS_sq hl
    field_simp [hk.ne', (show l ≠ 0 by linarith)]
    nlinarith
  refine ⟨?_, hS⟩
  rw [← hid]
  linarith

/-! ### Summability of the three moment-derivative products -/

private lemma summable_mMom_dx_shift_f7 (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) {i j : ℕ} (hi : i ≤ 2) (hj : j ≤ 2) :
    Summable (fun n : ℕ => mMom μ l (n + i) *
      dx μ (fun y => mMom μ y (n + j)) l) := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, hB⟩ := mMom'_summable_bound (μ := μ) h
    (a := (1 + l) / 2) (b := (l + mean μ) / 2) (by linarith) (by linarith) (by linarith)
  have hBl := hB l ⟨by linarith, by linarith⟩
  let A : ℝ := -((l - 1) ^ 2 / pBr μ)
  let K : ℝ := 9 * |A| * C ^ 2
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => K * (((n : ℝ) + 1) ^ 2 * (ρ ^ 2) ^ n))
    ((summable_sq_mul_geom (sq_nonneg ρ) (by nlinarith)).mul_left K)
  intro n
  have hBi := hBl (n + i)
  have hBj := hBl (n + j)
  have hρi : ρ ^ (n + i) ≤ ρ ^ n := by
    rw [pow_add]
    have hp : ρ ^ i ≤ 1 := pow_le_one₀ hρ0 hρ1.le
    nlinarith [pow_nonneg hρ0 n]
  have hρj : ρ ^ (n + j) ≤ ρ ^ n := by
    rw [pow_add]
    have hp : ρ ^ j ≤ 1 := pow_le_one₀ hρ0 hρ1.le
    nlinarith [pow_nonneg hρ0 n]
  have hρn : 0 ≤ ρ ^ n := pow_nonneg hρ0 n
  have hCi : |mMom μ l (n + i)| ≤ C * (3 * ((n : ℝ) + 1)) * ρ ^ n := by
    have hnn : ((n + i : ℕ) : ℝ) + 1 ≤ 3 * ((n : ℝ) + 1) := by
      push_cast
      have hiR : (i : ℝ) ≤ 2 := by exact_mod_cast hi
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [hn0, hiR]
    have hnon : 0 ≤ C * (3 * ((n : ℝ) + 1)) * ρ ^ n := by positivity
    calc
      |mMom μ l (n + i)| ≤ C * (((n + i : ℕ) : ℝ) + 1) * ρ ^ (n + i) := by
        linarith [abs_nonneg (mMom' μ l (n + i))]
      _ ≤ C * (3 * ((n : ℝ) + 1)) * ρ ^ n := by
        have hh := mul_le_mul hnn hρi (pow_nonneg hρ0 _) (by positivity)
        calc
          C * (((n + i : ℕ) : ℝ) + 1) * ρ ^ (n + i) =
              C * ((((n + i : ℕ) : ℝ) + 1) * ρ ^ (n + i)) := by ring
          _ ≤ C * ((3 * ((n : ℝ) + 1)) * ρ ^ n) := mul_le_mul_of_nonneg_left hh hC
          _ = _ := by ring
  have hCj : |mMom' μ l (n + j)| ≤ C * (3 * ((n : ℝ) + 1)) * ρ ^ n := by
    have hnn : ((n + j : ℕ) : ℝ) + 1 ≤ 3 * ((n : ℝ) + 1) := by
      push_cast
      have hjR : (j : ℝ) ≤ 2 := by exact_mod_cast hj
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [hn0, hjR]
    calc
      |mMom' μ l (n + j)| ≤ C * (((n + j : ℕ) : ℝ) + 1) * ρ ^ (n + j) := by
        linarith [abs_nonneg (mMom μ l (n + j))]
      _ ≤ C * (3 * ((n : ℝ) + 1)) * ρ ^ n := by
        have hh := mul_le_mul hnn hρj (pow_nonneg hρ0 _) (by positivity)
        calc
          C * (((n + j : ℕ) : ℝ) + 1) * ρ ^ (n + j) =
              C * ((((n + j : ℕ) : ℝ) + 1) * ρ ^ (n + j)) := by ring
          _ ≤ C * ((3 * ((n : ℝ) + 1)) * ρ ^ n) := mul_le_mul_of_nonneg_left hh hC
          _ = _ := by ring
  have hprod : |mMom μ l (n + i)| * |mMom' μ l (n + j)| ≤
      (C * (3 * ((n : ℝ) + 1)) * ρ ^ n) ^ 2 :=
    by simpa only [pow_two] using mul_le_mul hCi hCj (abs_nonneg _) (by positivity)
  rw [Real.norm_eq_abs, abs_mul, dx, show deriv (fun y => mMom μ y (n + j)) l =
    mMom' μ l (n + j) by rfl]
  change |mMom μ l (n + i)| * |A * mMom' μ l (n + j)| ≤ _
  rw [abs_mul]
  calc
    _ = |A| * (|mMom μ l (n + i)| * |mMom' μ l (n + j)|) := by ring
    _ ≤ |A| * (C * (3 * ((n : ℝ) + 1)) * ρ ^ n) ^ 2 :=
      mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    _ = _ := by dsimp [K]; rw [mul_pow]; ring

private lemma summable_mMom_zero_dx_f7 (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    Summable (fun n : ℕ => mMom μ l n * dx μ (fun y => mMom μ y (n + 1)) l) := by
  have hE := summable_mMom_dx_shift_f7 μ h hl hlm (i := 1) (j := 2) (by omega) (by omega)
  apply (summable_nat_add_iff 1).mp
  apply hE.congr
  intro n
  have hidx : n + 1 + 1 = n + 2 := by omega
  rw [hidx]

private lemma tsum_mMom_zero_dx_f7 (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    (∑' n : ℕ, mMom μ l n * dx μ (fun y => mMom μ y (n + 1)) l) =
      ∑' n : ℕ, mMom μ l (n + 1) * dx μ (fun y => mMom μ y (n + 2)) l := by
  have hF := summable_mMom_zero_dx_f7 μ h hl hlm
  rw [hF.tsum_eq_zero_add]
  have hm0 : mMom μ l 0 = 0 := by simp [mMom]
  rw [hm0, zero_mul, zero_add]

private lemma summable_Ccoef_dx_f7 (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    Summable (fun n : ℕ => Ccoef μ l (n + 1) *
      dx μ (fun y => mMom μ y (n + 1)) l) := by
  have hA := summable_mMom_dx_shift_f7 μ h hl hlm (i := 1) (j := 1) (by omega) (by omega)
  have hB := summable_mMom_dx_shift_f7 μ h hl hlm (i := 2) (j := 1) (by omega) (by omega)
  have hF := summable_mMom_zero_dx_f7 μ h hl hlm
  let d : ℕ → ℝ := fun n => if n = 0 then dx μ (fun y => mMom μ y 1) l else 0
  have hd : Summable d := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [d, hn]
  apply (hd.add (((hF.add hB).mul_left (xS μ l * kS l)).sub
    (hA.mul_left (xS μ l * (1 + l))))).congr
  intro n
  by_cases hn : n = 0
  · subst n
    have hm0 : mMom μ l 0 = 0 := by simp [mMom]
    simp [d, Ccoef, hm0]
    ring
  · have hn1 : n + 1 ≠ 1 := by omega
    simp [d, Ccoef, hn, hn1]
    ring

private lemma summable_Dcoef_dx_f7 (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    Summable (fun n : ℕ => Dcoef μ l (n + 1) *
      dx μ (fun y => mMom μ y (n + 1)) l) := by
  have hA := summable_mMom_dx_shift_f7 μ h hl hlm (i := 1) (j := 1) (by omega) (by omega)
  have hC := summable_Ccoef_dx_f7 μ h hl hlm
  apply (hA.sub (hC.mul_left (Vsc μ l))).congr
  intro n
  simp only [Dcoef]
  ring

private lemma dx_Ssc_f7 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : dx μ (Ssc μ) l =
      2 * ∑' n : ℕ, mMom μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l := by
  rw [dx, (hasDerivAt_Ssc (μ := μ) h hl hlm).deriv, SscDeriv, ← tsum_mul_left]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [dx, mMom']
  ring

private lemma dx_Tsc_f7 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : dx μ (Tsc μ) l =
      (∑' n : ℕ, mMom μ l (n + 2) * dx μ (fun y => mMom μ y (n + 1)) l) +
      ∑' n : ℕ, mMom μ l (n + 1) * dx μ (fun y => mMom μ y (n + 2)) l := by
  have hB := summable_mMom_dx_shift_f7 μ h hl hlm (i := 2) (j := 1) (by omega) (by omega)
  have hE := summable_mMom_dx_shift_f7 μ h hl hlm (i := 1) (j := 2) (by omega) (by omega)
  calc
    dx μ (Tsc μ) l = ∑' n : ℕ,
        (mMom μ l (n + 2) * dx μ (fun y => mMom μ y (n + 1)) l +
         mMom μ l (n + 1) * dx μ (fun y => mMom μ y (n + 2)) l) := by
      rw [dx, (hasDerivAt_Tsc (μ := μ) h hl hlm).deriv, TscDeriv, ← tsum_mul_left]
      apply tsum_congr
      intro n
      simp only [dx, mMom']
      ring
    _ = _ := hB.tsum_add hE

private lemma tsum_Ccoef_dx_f7 (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    (∑' n : ℕ, Ccoef μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l) =
      dx μ (fun y => mMom μ y 1) l +
      xS μ l * kS l * ((∑' n : ℕ,
        mMom μ l (n + 1) * dx μ (fun y => mMom μ y (n + 2)) l) +
       ∑' n : ℕ, mMom μ l (n + 2) * dx μ (fun y => mMom μ y (n + 1)) l) -
      xS μ l * (1 + l) * ∑' n : ℕ,
        mMom μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l := by
  have hA := summable_mMom_dx_shift_f7 μ h hl hlm (i := 1) (j := 1) (by omega) (by omega)
  have hB := summable_mMom_dx_shift_f7 μ h hl hlm (i := 2) (j := 1) (by omega) (by omega)
  have hF := summable_mMom_zero_dx_f7 μ h hl hlm
  let d : ℕ → ℝ := fun n => if n = 0 then dx μ (fun y => mMom μ y 1) l else 0
  have hd : Summable d := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [d, hn]
  calc
    _ = ∑' n : ℕ, (d n + xS μ l * kS l *
        (mMom μ l n * dx μ (fun y => mMom μ y (n + 1)) l +
         mMom μ l (n + 2) * dx μ (fun y => mMom μ y (n + 1)) l) -
        xS μ l * (1 + l) * (mMom μ l (n + 1) *
          dx μ (fun y => mMom μ y (n + 1)) l)) := by
      apply tsum_congr
      intro n
      by_cases hn : n = 0
      · subst n
        have hm0 : mMom μ l 0 = 0 := by simp [mMom]
        simp [d, Ccoef, hm0]
        ring
      · have hn1 : n + 1 ≠ 1 := by omega
        simp [d, Ccoef, hn, hn1]
        ring
    _ = _ := by
      rw [(hd.add ((hF.add hB).mul_left (xS μ l * kS l))).tsum_sub
        (hA.mul_left (xS μ l * (1 + l))),
        hd.tsum_add ((hF.add hB).mul_left (xS μ l * kS l)),
        tsum_mul_left, tsum_mul_left, hF.tsum_add hB,
        tsum_mMom_zero_dx_f7 μ h hl hlm]
      have hdt : (∑' n, d n) = dx μ (fun y => mMom μ y 1) l := by
        rw [tsum_eq_single 0]
        simp [d]
        intro n hn
        simp [d, hn]
      rw [hdt]

private lemma dx_hsc_sub_tsum_Ccoef_f7 (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    dx μ (hsc μ) l -
      (∑' n : ℕ, Ccoef μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l) =
      -(Ssc μ l - gamS l * Tsc μ l) := by
  have hxder := (hasDerivAt_xS (μ := μ) hl).deriv
  have hkder := (hasDerivAt_kS (show 0 < l by linarith)).deriv
  have hhder := (hasDerivAt_hsc (μ := μ) h hl hlm).deriv
  have hS := dx_Ssc_f7 μ h hl hlm
  have hT := dx_Tsc_f7 μ h hl hlm
  have hC := tsum_Ccoef_dx_f7 μ h hl hlm
  have hk := kS_pos hl
  have hxa : xS μ l * ((l - 1) ^ 2 / pBr μ) = l - 1 := by
    unfold xS
    field_simp [(pBr_pos h).ne', (show l - 1 ≠ 0 by linarith)]
    <;> ring
  have hkx : kS l - (l - 1) / (2 * kS l) = gamS l := by
    unfold gamS
    have hksq := kS_sq hl
    field_simp [hk.ne']
    nlinarith
  have hSder := (hasDerivAt_Ssc (μ := μ) h hl hlm).deriv
  have hTder := (hasDerivAt_Tsc (μ := μ) h hl hlm).deriv
  have hid : deriv (fun y : ℝ => y) l = 1 := by simpa using congrFun deriv_id'' l
  have hksq := kS_sq hl
  have hdxh : dx μ (hsc μ) l = dx μ (fun y => mMom μ y 1) l -
      (dx μ (fun y => xS μ y) l * ((1 + l) * Ssc μ l / 2 - kS l * Tsc μ l) +
      xS μ l * ((dx μ (fun y : ℝ => y) l * Ssc μ l + (1 + l) * dx μ (Ssc μ) l) / 2 -
        (dx μ (kS) l * Tsc μ l + kS l * dx μ (Tsc μ) l))) := by
    simp only [dx, hhder, hscDeriv, hSder, hTder, mMom', hxder, hkder, hid]
    ring
  have hdxx : dx μ (fun y => xS μ y) l = 1 := by
    rw [dx, hxder]
    field_simp [(pBr_pos h).ne', (show l - 1 ≠ 0 by linarith)]
    <;> ring
  have hdxl : dx μ (fun y : ℝ => y) l = -((l - 1) ^ 2 / pBr μ) := by
    rw [dx, hid]
    ring
  have hdxk : dx μ (kS) l = -(((l - 1) ^ 2 / pBr μ) / (2 * kS l)) := by
    rw [dx, hkder]
    ring
  have hscalar : -((1 + l) * Ssc μ l / 2 - kS l * Tsc μ l) +
      xS μ l * ((l - 1) ^ 2 / pBr μ) * Ssc μ l / 2 +
      -(xS μ l * ((l - 1) ^ 2 / pBr μ) * Tsc μ l / (2 * kS l)) =
      -(Ssc μ l - gamS l * Tsc μ l) := by
    simp only [hxa]
    rw [← hkx]
    field_simp [hk.ne']
    nlinarith [hksq]
  rw [hdxh, hC, hS, hT, hdxx, hdxl, hdxk]
  linear_combination hscalar

private lemma hasDerivAt_Vsc_f7 (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    HasDerivAt (Vsc μ)
      ((SscDeriv μ l * (2 * hsc μ l) - Ssc μ l * (2 * hscDeriv μ l)) /
        (2 * hsc μ l) ^ 2) l := by
  have hS := hasDerivAt_Ssc (μ := μ) h hl hlm
  have hH := hasDerivAt_hsc (μ := μ) h hl hlm
  have hm1 := mMom_one_pos_f7 μ h hl hlm
  have hHb := (hsc_bounds (μ := μ) h hl hlm).1
  have hHpos : 0 < hsc μ l := by linarith
  have hq := hS.div (hH.const_mul 2) (by positivity : 2 * hsc μ l ≠ 0)
  apply hq.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hl, eventually_lt_nhds hlm] with y hy hym
  exact Vsc_eq (μ := μ) h hy hym

private lemma hsc_mul_dx_Vsc_f7 (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    hsc μ l * dx μ (Vsc μ) l =
      (∑' n : ℕ, mMom μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l) -
      Vsc μ l * dx μ (hsc μ) l := by
  have hm1 := mMom_one_pos_f7 μ h hl hlm
  have hHb := (hsc_bounds (μ := μ) h hl hlm).1
  have hHpos : 0 < hsc μ l := by linarith
  have hVder := (hasDerivAt_Vsc_f7 μ h hl hlm).deriv
  have hSder := (hasDerivAt_Ssc (μ := μ) h hl hlm).deriv
  have hHder := (hasDerivAt_hsc (μ := μ) h hl hlm).deriv
  have hS := dx_Ssc_f7 μ h hl hlm
  have hV := Vsc_eq (μ := μ) h hl hlm
  rw [dx, hVder]
  rw [dx] at hS ⊢
  rw [hSder] at hS
  rw [hHder, hV]
  field_simp [hHpos.ne']
  ring_nf at hS ⊢
  nlinarith

/-- **Equation (4.2)** (`eq:scaled-mark`). Differentiation of `V = S/(2h)` in the
scaled variable, with all moment coordinates displayed. -/
theorem scaled_mark (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    Summable (fun n : ℕ => Dcoef μ l (n + 1) *
      dx μ (fun l => mMom μ l (n + 1)) l) ∧
    hsc μ l * dx μ (Vsc μ) l = Vsc μ l * (Ssc μ l - gamS l * Tsc μ l) +
      ∑' n : ℕ, Dcoef μ l (n + 1) * dx μ (fun l => mMom μ l (n + 1)) l := by
  have hsum := summable_Dcoef_dx_f7 μ h hl hlm
  refine ⟨hsum, ?_⟩
  have hA := summable_mMom_dx_shift_f7 μ h hl hlm (i := 1) (j := 1) (by omega) (by omega)
  have hC := summable_Ccoef_dx_f7 μ h hl hlm
  have hDsum : (∑' n : ℕ, Dcoef μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l) =
      (∑' n : ℕ, mMom μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l) -
      Vsc μ l * ∑' n : ℕ, Ccoef μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l := by
    calc
      _ = ∑' n : ℕ, (mMom μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l -
          Vsc μ l * (Ccoef μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l)) := by
        apply tsum_congr
        intro n
        simp only [Dcoef]
        ring
      _ = _ := by rw [hA.tsum_sub (hC.mul_left (Vsc μ l)), tsum_mul_left]
  have hquot := hsc_mul_dx_Vsc_f7 μ h hl hlm
  have hcoord := dx_hsc_sub_tsum_Ccoef_f7 μ h hl hlm
  rw [hDsum]
  have hcoord' : dx μ (hsc μ) l = -(Ssc μ l - gamS l * Tsc μ l) +
      ∑' n : ℕ, Ccoef μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l := by
    linarith
  rw [hcoord'] at hquot
  linarith

end LPPMonotonicityProof.Analytic
