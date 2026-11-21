module

public import LPPMonotonicityProof.Analytic.Defs
public import LPPMonotonicityProof.Speed.Signed.TwoCopyBounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Kernel bounds and positivity of the speed

This module proves the pointwise bounds (2.2) (`eq:kernel-bounds`) on the two-copy
denominator `D`, and restates the consequences `0 < N < Z < ∞` and the integrability
of both kernels, which are proved in `LPPMonotonicityProof.Speed.Signed.TwoCopyBounds`.
It deduces that the speed `speedValueProv` (the copy of `Speed.speedValue`) satisfies
`0 < v(λ)` on `[0, m)`, the positivity clause of
`speed_monotone_of_interval_certificates`, and `v(λ) < 1` for `0 < λ < m`.
-/

@[expose] public section

namespace LPPMonotonicityProof.Analytic

open MeasureTheory Filter Topology
open LPPMonotonicityProof.Speed

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

/-- The speed `speedValueProv` is `N / Z` at nonzero bias and `1` at zero bias, as
`Speed.speedValue`, of which it is a copy. -/
theorem speedValueProv_eq (l : ℝ) :
    speedValueProv μ l = if l = 0 then 1 else Speed.Nval μ l / Speed.Zval μ l := rfl

private lemma Dfun_ge_left_of_mem_Ioc {l b b' : ℝ} (_hl : 0 < l)
    (hb : b ∈ Set.Ioc 0 1) (hb' : b' ∈ Set.Ioc 0 1)
    (hlow : l < 1 → 1 - l ≤ b ∧ 1 - l ≤ b') :
    min 1 l * b ≤ Speed.Dfun l b b' := by
  by_cases hl1 : l < 1
  · rw [min_eq_right hl1.le]
    have hfactor : (1 - b) * (1 - b') ≤ (1 - b) * l :=
      mul_le_mul_of_nonneg_left (by linarith [(hlow hl1).2]) (sub_nonneg.mpr hb.2)
    unfold Speed.Dfun
    nlinarith
  · have hl1' : 1 ≤ l := le_of_not_gt hl1
    rw [min_eq_left hl1']
    have hnonneg : 0 ≤ b' * (1 - b) := mul_nonneg hb'.1.le (sub_nonneg.mpr hb.2)
    unfold Speed.Dfun
    nlinarith

private lemma Dfun_ge_right_of_mem_Ioc {l b b' : ℝ} (hl : 0 < l)
    (hb : b ∈ Set.Ioc 0 1) (hb' : b' ∈ Set.Ioc 0 1)
    (hlow : l < 1 → 1 - l ≤ b ∧ 1 - l ≤ b') :
    min 1 l * b' ≤ Speed.Dfun l b b' := by
  rw [Speed.Dfun, show l - 1 + b + b' - b * b' = l - 1 + b' + b - b' * b by ring]
  exact Dfun_ge_left_of_mem_Ioc hl hb' hb fun h => ⟨(hlow h).2, (hlow h).1⟩

private lemma Dfun_lower_of_mem_Ioc {l b b' : ℝ} (hl : 0 < l)
    (hb : b ∈ Set.Ioc 0 1) (hb' : b' ∈ Set.Ioc 0 1)
    (hlow : l < 1 → 1 - l ≤ b ∧ 1 - l ≤ b') :
    min 1 l * max b b' ≤ Speed.Dfun l b b' := by
  rcases le_total b b' with h | h
  · rw [max_eq_right h]
    exact Dfun_ge_right_of_mem_Ioc hl hb hb' hlow
  · rw [max_eq_left h]
    exact Dfun_ge_left_of_mem_Ioc hl hb hb' hlow

private lemma Dfun_pos_of_mem_Ioc {l b b' : ℝ} (hl : 0 < l)
    (hb : b ∈ Set.Ioc 0 1) (hb' : b' ∈ Set.Ioc 0 1)
    (hlow : l < 1 → 1 - l ≤ b ∧ 1 - l ≤ b') : 0 < Speed.Dfun l b b' := by
  have hmin : 0 < min 1 l := lt_min zero_lt_one hl
  have hmax : 0 < max b b' := lt_max_of_lt_left hb.1
  exact (mul_pos hmin hmax).trans_le (Dfun_lower_of_mem_Ioc hl hb hb' hlow)

private lemma Dfun_le_of_mem_Ioc {l b b' : ℝ} (hb : b ∈ Set.Ioc 0 1)
    (hb' : b' ∈ Set.Ioc 0 1) : Speed.Dfun l b b' ≤ l := by
  have hnonneg : 0 ≤ (1 - b) * (1 - b') :=
    mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr hb'.2)
  unfold Speed.Dfun
  nlinarith

private lemma tau_le_two_max_of_mem_Ioc {b b' : ℝ} (hb : b ∈ Set.Ioc 0 1)
    (hb' : b' ∈ Set.Ioc 0 1) : tau b b' ≤ 2 * max b b' := by
  have hb0 := hb.1.le
  have hb1 := hb.2
  have hb'0 := hb'.1.le
  have hb'1 := hb'.2
  rcases le_total b b' with h | h
  · rw [max_eq_right h]
    unfold tau
    nlinarith
  · rw [max_eq_left h]
    unfold tau
    nlinarith

/-- All three denominator bounds of equation (2.2) (`eq:kernel-bounds`). -/
theorem Dfun_bounds {l b b' : ℝ} (hl : 0 < l) (hb : b ∈ Set.Ioc 0 1)
    (hb' : b' ∈ Set.Ioc 0 1)
    (hlow : l < 1 → 1 - l ≤ b ∧ 1 - l ≤ b') :
    min 1 l * max b b' ≤ Speed.Dfun l b b' ∧ Speed.Dfun l b b' ≤ l ∧
      (1 ≤ l → tau b b' ≤ Speed.Dfun l b b') := by
  refine ⟨Dfun_lower_of_mem_Ioc hl hb hb' hlow, Dfun_le_of_mem_Ioc hb hb', ?_⟩
  intro hl1
  unfold tau Speed.Dfun
  linarith

/-- The stronger lower bound below bias one in (2.2), in the form `D ≥ λ(1 - λ)`.  The
hypothesis `hb1 : b ≤ 1` is necessary: arbitrarily large `b, b'` otherwise make `Dfun`
negative. -/
theorem Dfun_ge_of_lt_one {l b b' : ℝ} (hl : 0 < l) (_hl1 : l < 1)
    (hb : 1 - l ≤ b) (hb' : 1 - l ≤ b') (hb1 : b ≤ 1) :
    l * (1 - l) ≤ Speed.Dfun l b b' := by
  have hfactor : (1 - b) * (1 - b') ≤ (1 - b) * l :=
    mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hb1)
  have hmul : l * (1 - l) ≤ l * b := mul_le_mul_of_nonneg_left hb hl.le
  unfold Speed.Dfun
  nlinarith

private lemma prod_le_max_of_mem_Ioc {b b' : ℝ} (hb : b ∈ Set.Ioc 0 1)
    (hb' : b' ∈ Set.Ioc 0 1) : b * b' ≤ max b b' := by
  calc
    b * b' ≤ max b b' * b' := mul_le_mul_of_nonneg_right (le_max_left _ _) hb'.1.le
    _ ≤ max b b' * 1 :=
      mul_le_mul_of_nonneg_left hb'.2 (hb.1.trans_le (le_max_left _ _)).le
    _ = max b b' := mul_one _

/-- The pointwise numerator-kernel bound. -/
theorem kernel_N_le {l b b' : ℝ} (hl : 0 < l) (hb : b ∈ Set.Ioc 0 1)
    (hb' : b' ∈ Set.Ioc 0 1)
    (hlow : l < 1 → 1 - l ≤ b ∧ 1 - l ≤ b') :
    b * b' / Speed.Dfun l b b' ≤ (min 1 l)⁻¹ := by
  have hmin : 0 < min 1 l := lt_min zero_lt_one hl
  have hD : 0 < Speed.Dfun l b b' := Dfun_pos_of_mem_Ioc hl hb hb' hlow
  apply (div_le_iff₀ hD).2
  calc
    b * b' ≤ max b b' := prod_le_max_of_mem_Ioc hb hb'
    _ = (min 1 l)⁻¹ * (min 1 l * max b b') := by
      rw [← mul_assoc, inv_mul_cancel₀ hmin.ne', one_mul]
    _ ≤ (min 1 l)⁻¹ * Speed.Dfun l b b' :=
      mul_le_mul_of_nonneg_left (Dfun_lower_of_mem_Ioc hl hb hb' hlow) (inv_nonneg.mpr hmin.le)

/-- The pointwise denominator-kernel bound. -/
theorem kernel_Z_le {l b b' : ℝ} (hl : 0 < l) (hb : b ∈ Set.Ioc 0 1)
    (hb' : b' ∈ Set.Ioc 0 1)
    (hlow : l < 1 → 1 - l ≤ b ∧ 1 - l ≤ b') :
    tau b b' / Speed.Dfun l b b' ≤ 2 * (min 1 l)⁻¹ := by
  have hmin : 0 < min 1 l := lt_min zero_lt_one hl
  have hD : 0 < Speed.Dfun l b b' := Dfun_pos_of_mem_Ioc hl hb hb' hlow
  apply (div_le_iff₀ hD).2
  calc
    tau b b' ≤ 2 * max b b' := tau_le_two_max_of_mem_Ioc hb hb'
    _ = (2 * (min 1 l)⁻¹) * (min 1 l * max b b') := by
      field_simp
    _ ≤ (2 * (min 1 l)⁻¹) * Speed.Dfun l b b' :=
      mul_le_mul_of_nonneg_left (Dfun_lower_of_mem_Ioc hl hb hb' hlow) (by positivity)

/-- Strict positivity of the two-copy numerator. -/
theorem Nval_pos (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ) :
    0 < Speed.Nval μ l :=
  Speed.Nval_pos μ hl h hlm

/-- The two-copy denominator is finite and strictly larger than the numerator. -/
theorem Nval_lt_Zval (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ) :
    Speed.Nval μ l < Speed.Zval μ l :=
  Speed.Nval_lt_Zval μ hl h hlm

/-- Integrability of the numerator kernel. -/
theorem integrable_kernel_N (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) :
    Integrable (fun p : ℝ × ℝ => p.1 * p.2 / Speed.Dfun l p.1 p.2)
      ((Speed.escLaw μ l).prod (Speed.escLaw μ l)) :=
  Speed.integrable_N_kernel μ hl h hlm

/-- Integrability of the denominator kernel. -/
theorem integrable_kernel_Z (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) :
    Integrable (fun p : ℝ × ℝ => tau p.1 p.2 / Speed.Dfun l p.1 p.2)
      ((Speed.escLaw μ l).prod (Speed.escLaw μ l)) :=
  Speed.integrable_Z_kernel μ hl h hlm

/-- The speed is strictly positive on the closed-left transient interval. -/
theorem speedValue_pos (h : OffspringHyp μ) :
    ∀ l ∈ Set.Ico 0 (mean μ), 0 < speedValueProv μ l := by
  intro l hl
  rcases hl.1.eq_or_lt with rfl | hl0
  · simp [speedValueProv]
  · rw [speedValueProv_eq, ite_eq_right hl0.ne']
    exact div_pos (Speed.Nval_pos μ hl0 h hl.2) (Speed.Zval_pos μ hl0 h hl.2)

/-- At positive bias the speed is strictly below one. -/
theorem speedValue_lt_one (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) : speedValueProv μ l < 1 := by
  rw [speedValueProv_eq, ite_eq_right hl.ne']
  exact (div_lt_one (Speed.Zval_pos μ hl h hlm)).2 (Speed.Nval_lt_Zval μ hl h hlm)

/-- Away from zero the speed `speedValueProv` is literally `N / Z`. -/
theorem speedValue_eventuallyEq {l : ℝ} (hl : 0 < l) :
    speedValueProv μ =ᶠ[𝓝 l] fun l' => Speed.Nval μ l' / Speed.Zval μ l' := by
  filter_upwards [eventually_ne_nhds hl.ne'] with l' hl'
  rw [speedValueProv_eq, ite_eq_right hl']

end LPPMonotonicityProof.Analytic
