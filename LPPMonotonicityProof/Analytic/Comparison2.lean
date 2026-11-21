module

public import LPPMonotonicityProof.Analytic.Comparison
public import LPPMonotonicityProof.Analytic.Tools
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Fixed-mean comparison of the transformed speed kernel

This module proves equation (3.2) (`eq:kernel-shape`) and the admissibility of the
coefficients of its moment series, from the proof of Lemma 3.3 (`lem:speed-ceiling`).
It also computes the moments of the comparison geometric law of Lemma 3.2
(`lem:convex-order`) and the exact geometric reset quotient `v_*` from the proof of
Lemma 3.3.  The series is kept in a
product-measure form so that changing the moments in either copy requires no
additional interchange argument.
-/

@[expose] public section

namespace LPPMonotonicityProof.Analytic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

variable {l : ℝ}

private lemma integrable_bounded_of_ae {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] {f : Ω → ℝ}
    (hf : AEMeasurable f ρ) {C : ℝ} (hC : ∀ᵐ x ∂ρ, ‖f x‖ ≤ C) : Integrable f ρ :=
  (integrable_const C).mono' hf.aestronglyMeasurable hC

private lemma inv_l_mem_of_mem_Icc {y : ℝ} (hl : 1 < l) (hy : y ∈ Set.Icc 0 (1 / l)) :
    0 ≤ y ∧ y ≤ 1 ∧ l * y ≤ 1 := by
  have hl0 : 0 < l := by linarith
  refine ⟨hy.1, hy.2.trans ?_, ?_⟩
  · exact (div_le_one hl0).2 (by linarith)
  · calc
      l * y ≤ l * (1 / l) := mul_le_mul_of_nonneg_left hy.2 hl0.le
      _ = 1 := by field_simp

private lemma one_sub_prod_mem {y t : ℝ} (hl : 1 < l)
    (hy : y ∈ Set.Icc 0 (1 / l)) (ht : t ∈ Set.Icc 0 (1 / l)) :
    0 < 1 - l * y * t ∧ (l - 1) / l ≤ 1 - l * y * t := by
  obtain ⟨hy0, hy1, hly⟩ := inv_l_mem_of_mem_Icc hl hy
  obtain ⟨ht0, ht1, hlt⟩ := inv_l_mem_of_mem_Icc hl ht
  have hprod : l * y * t ≤ 1 / l := by
    calc
      l * y * t ≤ 1 * t := mul_le_mul_of_nonneg_right hly ht0
      _ = t := one_mul _
      _ ≤ 1 / l := ht.2
  constructor
  · have hlt : l * y * t < 1 := hprod.trans_lt ((div_lt_one (by linarith : 0 < l)).2 hl)
    linarith
  · have heq : (l - 1) / l = 1 - 1 / l := by field_simp
    rw [heq]
    linarith

private lemma Bw_norm_le {w t : ℝ} (hl : 1 < l) (ht : t ∈ Set.Icc 0 (1 / l)) :
    ‖Bw l w t‖ ≤ (l - 1) / l + |w| := by
  obtain ⟨ht0, ht1, hlt⟩ := inv_l_mem_of_mem_Icc hl ht
  have ha : 0 < l - 1 := by linarith
  have hfac0 : 0 ≤ 1 - t := by linarith
  have hfac1 : 0 ≤ 1 - l * t := by linarith
  have hprod : (1 - t) * (1 - l * t) ≤ 1 := by nlinarith
  have h₁ : |(l - 1) * t| ≤ (l - 1) / l := by
    rw [abs_of_nonneg (mul_nonneg ha.le ht0)]
    exact (le_div_iff₀ (by linarith : 0 < l)).2 (by nlinarith)
  have h₂ : |w * (1 - t) * (1 - l * t)| ≤ |w| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hfac0, abs_of_nonneg hfac1]
    calc
      |w| * (1 - t) * (1 - l * t) ≤ |w| * 1 * 1 := by gcongr <;> nlinarith
      _ = |w| := by ring
  rw [Bw, Real.norm_eq_abs]
  exact (abs_sub _ _).trans (add_le_add h₁ h₂)

private lemma integrable_Bw_pow {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {w : ℝ}
    (hl : 1 < l) (hρ : ∀ᵐ t ∂ρ, t ∈ Set.Icc 0 (1 / l)) (n : ℕ) :
    Integrable (fun t => t ^ n * Bw l w t) ρ := by
  apply integrable_bounded_of_ae (by unfold Bw; fun_prop)
  filter_upwards [hρ] with t ht
  obtain ⟨ht0, ht1, _⟩ := inv_l_mem_of_mem_Icc hl ht
  calc
    ‖t ^ n * Bw l w t‖ = |t| ^ n * ‖Bw l w t‖ := by simp [norm_mul, norm_pow]
    _ ≤ 1 * ((l - 1) / l + |w|) := by
      gcongr
      · exact pow_le_one₀ (abs_nonneg t) (by rw [abs_of_nonneg ht0]; exact ht1)
      · exact Bw_norm_le hl ht
    _ = (l - 1) / l + |w| := one_mul _

private lemma integrable_Hw {ρ ξ : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ξ] (hl : 1 < l)
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc 0 (1 / l))
    (hξ : ∀ᵐ t ∂ξ, t ∈ Set.Icc 0 (1 / l)) (w : ℝ) :
    Integrable (fun p => Hw l w p.1 p.2) (ρ.prod ξ) := by
  have hy := (Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := ξ)).ae hρ
  have ht := (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := ξ)).ae hξ
  apply integrable_bounded_of_ae (by unfold Hw; fun_prop)
  let C := ((l - 1) / l ^ 2 + |w| * (2 / l + (1 + l) / l ^ 2)) * (l / (l - 1))
  filter_upwards [hy, ht] with p hpY hpT
  obtain ⟨hy0, hy1, _⟩ := inv_l_mem_of_mem_Icc hl hpY
  obtain ⟨ht0, ht1, _⟩ := inv_l_mem_of_mem_Icc hl hpT
  obtain ⟨hden, hdenlo⟩ := one_sub_prod_mem hl hpY hpT
  rw [Hw, Real.norm_eq_abs, abs_div, abs_of_pos hden]
  have hnum : |(l - 1) * p.1 * p.2 - w * (p.1 + p.2 - (1 + l) * p.1 * p.2)| ≤
      (l - 1) / l ^ 2 + |w| * (2 / l + (1 + l) / l ^ 2) := by
    have hpprod : p.1 * p.2 ≤ (1 / l) * (1 / l) :=
      mul_le_mul hpY.2 hpT.2 hpT.1 (by positivity)
    have hA : |(l - 1) * p.1 * p.2| ≤ (l - 1) / l ^ 2 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (l - 1) * p.1 * p.2)]
      apply (le_div_iff₀ (by positivity : 0 < l ^ 2)).2
      calc
        (l - 1) * p.1 * p.2 * l ^ 2 ≤ (l - 1) * ((1 / l) * (1 / l)) * l ^ 2 := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpprod (by positivity : 0 ≤ l - 1))
            (pow_nonneg (by linarith : 0 ≤ l) 2)
        _ = l - 1 := by field_simp
    have hB : |w * (p.1 + p.2 - (1 + l) * p.1 * p.2)| ≤
        |w| * (2 / l + (1 + l) / l ^ 2) := by
      rw [abs_mul]
      gcongr
      calc
        |p.1 + p.2 - (1 + l) * p.1 * p.2| ≤ |p.1| + |p.2| + |(1 + l) * p.1 * p.2| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
        _ ≤ 1 / l + 1 / l + (1 + l) / l ^ 2 := by
          rw [abs_of_nonneg hy0, abs_of_nonneg ht0,
            abs_of_nonneg (by positivity : 0 ≤ (1 + l) * p.1 * p.2)]
          have hp : (1 + l) * p.1 * p.2 ≤ (1 + l) / l ^ 2 := by
            apply (le_div_iff₀ (by positivity : 0 < l ^ 2)).2
            calc
              (1 + l) * p.1 * p.2 * l ^ 2 ≤ (1 + l) * ((1 / l) * (1 / l)) * l ^ 2 := by
                simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hpprod (by positivity : 0 ≤ 1 + l))
                  (pow_nonneg (by linarith : 0 ≤ l) 2)
              _ = 1 + l := by field_simp
          exact add_le_add (add_le_add hpY.2 hpT.2) hp
        _ = 2 / l + (1 + l) / l ^ 2 := by ring
    exact (abs_sub _ _).trans (add_le_add hA hB)
  apply (div_le_iff₀ hden).2
  calc
    |(l - 1) * p.1 * p.2 - w * (p.1 + p.2 - (1 + l) * p.1 * p.2)| ≤
        (l - 1) / l ^ 2 + |w| * (2 / l + (1 + l) / l ^ 2) := hnum
    _ ≤ C * (1 - l * p.1 * p.2) := by
      dsimp [C]
      have hC0 : 0 ≤ (l - 1) / l ^ 2 + |w| * (2 / l + (1 + l) / l ^ 2) := by positivity
      calc
        _ ≤ ((l - 1) / l ^ 2 + |w| * (2 / l + (1 + l) / l ^ 2)) *
            ((l / (l - 1)) * (1 - l * p.1 * p.2)) := by
          apply le_mul_of_one_le_right hC0
          have hlri : 1 ≤ (l / (l - 1)) * (1 - l * p.1 * p.2) := by
            calc
              (1 : ℝ) = (l / (l - 1)) * ((l - 1) / l) := by field_simp
              _ ≤ (l / (l - 1)) * (1 - l * p.1 * p.2) := by
                exact mul_le_mul_of_nonneg_left hdenlo (by positivity)
          exact hlri
        _ = C * (1 - l * p.1 * p.2) := by ring

private lemma Hw_decomp (l w y t : ℝ) (h : 1 - l * y * t ≠ 0) :
    Hw l w y t = -w * t + y * Bw l w t / (1 - l * y * t) := by
  unfold Hw Bw
  field_simp [h]
  ring

private lemma Hw_pair_series {ρ ξ : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ξ] (hl : 1 < l)
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc 0 (1 / l))
    (hξ : ∀ᵐ t ∂ξ, t ∈ Set.Icc 0 (1 / l)) (w : ℝ) :
    ∫ p, Hw l w p.1 p.2 ∂ρ.prod ξ = -w * ∫ t, t ∂ξ +
      ∑' n : ℕ, l ^ n * (∫ y, y ^ (n + 1) ∂ρ) * ∫ t, t ^ n * Bw l w t ∂ξ := by
  have hInt := integrable_Hw hl hρ hξ w
  have hlin : Integrable (fun p : ℝ × ℝ => -w * p.2) (ρ.prod ξ) := by
    apply integrable_bounded_of_ae (by fun_prop)
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := ξ)).ae hξ] with p hp
    obtain ⟨ht0, ht1, _⟩ := inv_l_mem_of_mem_Icc hl hp
    simp only [norm_mul, norm_neg, Real.norm_eq_abs]
    calc
      |w| * |p.2| ≤ |w| * 1 := by gcongr; rw [abs_of_nonneg ht0]; exact ht1
      _ = |w| := mul_one _
  have hdecomp : ∀ᵐ p ∂ρ.prod ξ, Hw l w p.1 p.2 =
      -w * p.2 + p.1 * Bw l w p.2 / (1 - l * p.1 * p.2) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := ξ)).ae hρ,
      (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := ξ)).ae hξ] with p hpY hpT
    exact Hw_decomp _ _ _ _ (one_sub_prod_mem hl hpY hpT).1.ne'
  have htail : Integrable
      (fun p : ℝ × ℝ => p.1 * Bw l w p.2 / (1 - l * p.1 * p.2)) (ρ.prod ξ) := by
    apply (hInt.sub hlin).congr
    filter_upwards [hdecomp] with p hp
    change Hw l w p.1 p.2 - (-w * p.2) = _
    rw [hp]
    ring
  rw [integral_congr_ae hdecomp, integral_add hlin htail]
  have hseries := integral_kernel_series (e := 1) hl hρ hξ
    (f := fun y => y) (g := Bw l w) (by fun_prop) (by unfold Bw; fun_prop)
    ⟨1 / l, fun y hy => by rw [abs_of_nonneg hy.1]; exact hy.2⟩
    (by
      obtain ⟨t, ht⟩ := hξ.exists
      exact ⟨(l - 1) / l + |w|, fun t ht => Bw_norm_le hl ht⟩)
    (Or.inl rfl)
  simp only [if_true, one_mul, pow_one] at hseries
  have hmean : ∫ p : ℝ × ℝ, -w * p.2 ∂ρ.prod ξ = -w * ∫ t, t ∂ξ := by
    rw [integral_const_mul, integral_fun_snd (μ := ρ) (ν := ξ) (f := fun t : ℝ => t)]
    simp [Measure.real]
  rw [hmean, hseries]
  congr 1

/-- Equation (3.2) (`eq:kernel-shape`) in the fixed second law. -/
theorem kernel_shape (hl : 1 < l) {ξ : Measure ℝ} [IsProbabilityMeasure ξ]
    (hξ : ∀ᵐ t ∂ξ, t ∈ Set.Icc 0 (1 / l)) {y : ℝ}
    (hy : y ∈ Set.Icc 0 (1 / l)) (w : ℝ) :
    ∫ t, Hw l w y t ∂ξ = -w * ∫ t, t ∂ξ +
      ∑' n : ℕ, l ^ n * (∫ t, t ^ n * Bw l w t ∂ξ) * y ^ (n + 1) := by
  have hpair := Hw_pair_series (ρ := Measure.dirac y) hl (by rw [ae_dirac_eq]; exact hy) hξ w
  rw [Measure.dirac_prod, integral_map_of_stronglyMeasurable (by fun_prop)
    (by unfold Hw; fun_prop)] at hpair
  simpa [mul_comm, mul_left_comm, mul_assoc] using hpair

private lemma integrable_pow_on {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hl : 1 < l) (hρ : ∀ᵐ t ∂ρ, t ∈ Set.Icc 0 (1 / l)) (n : ℕ) :
    Integrable (fun t => t ^ n) ρ := by
  apply integrable_bounded_of_ae (by fun_prop)
  filter_upwards [hρ] with t ht
  obtain ⟨ht0, ht1, _⟩ := inv_l_mem_of_mem_Icc hl ht
  rw [norm_pow, Real.norm_of_nonneg ht0]
  exact pow_le_one₀ ht0 ht1

private lemma integrable_escape_poly_on {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hl : 1 < l) (hρ : ∀ᵐ t ∂ρ, t ∈ Set.Icc 0 (1 / l)) :
    Integrable (fun t => (1 - t) * (1 - l * t)) ρ := by
  apply integrable_bounded_of_ae (by fun_prop)
  filter_upwards [hρ] with t ht
  obtain ⟨ht0, ht1, hlt⟩ := inv_l_mem_of_mem_Icc hl ht
  have h1 : 0 ≤ 1 - t := by linarith
  have h2 : 0 ≤ 1 - l * t := by linarith
  rw [Real.norm_of_nonneg (mul_nonneg h1 h2)]
  nlinarith

/-- Admissibility of every coefficient of the kernel expansion. -/
theorem kernel_coeff_nonneg (hl : 1 < l) {ξ : Measure ℝ} [IsProbabilityMeasure ξ]
    (hξ : ∀ᵐ t ∂ξ, t ∈ Set.Icc 0 (1 / l)) (w : ℝ)
    (hm : 0 < ∫ t, t ∂ξ)
    (hw : 0 ≤ w ∧ w ≤ (l - 1) * (∫ t, t ∂ξ) / (1 - ∫ t, t ∂ξ)) (n : ℕ) :
    0 ≤ ∫ t, t ^ n * Bw l w t ∂ξ := by
  let m : ℝ := ∫ t, t ∂ξ
  let m₂ : ℝ := ∫ t, t ^ 2 ∂ξ
  let q : ℝ := ∫ t, (1 - t) * (1 - l * t) ∂ξ
  have hm₁ : Integrable (fun t : ℝ => t) ξ := by
    simpa using integrable_pow_on (l := l) hl hξ 1
  have hm₂ : Integrable (fun t : ℝ => t ^ 2) ξ := integrable_pow_on hl hξ 2
  have hq : Integrable (fun t : ℝ => (1 - t) * (1 - l * t)) ξ :=
    integrable_escape_poly_on hl hξ
  have hm_le : m ≤ 1 / l := by
    dsimp [m]
    calc
      ∫ t, t ∂ξ ≤ ∫ _t, 1 / l ∂ξ := by
        apply integral_mono_ae hm₁ (integrable_const _)
        filter_upwards [hξ] with t ht
        exact ht.2
      _ = 1 / l := by simp [Measure.real]
  have hm_lt_one : m < 1 := hm_le.trans_lt ((div_lt_one (by linarith : 0 < l)).2 hl)
  have hm₂_le : m₂ ≤ m := by
    dsimp [m, m₂]
    apply integral_mono_ae hm₂ hm₁
    filter_upwards [hξ] with t ht
    obtain ⟨ht0, ht1, _⟩ := inv_l_mem_of_mem_Icc hl ht
    nlinarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    apply integral_nonneg_of_ae
    filter_upwards [hξ] with t ht
    obtain ⟨ht0, ht1, hlt⟩ := inv_l_mem_of_mem_Icc hl ht
    exact mul_nonneg (by linarith) (by linarith)
  have hq_eval : q = 1 - (1 + l) * m + l * m₂ := by
    have hdecomp : (fun t : ℝ => (1 - t) * (1 - l * t)) =
        (fun t => 1 - (1 + l) * t + l * t ^ 2) := by
      funext t; ring
    rw [show q = ∫ t, (1 - t) * (1 - l * t) ∂ξ from rfl, hdecomp]
    rw [integral_add (f := fun t : ℝ => 1 - (1 + l) * t) (g := fun t => l * t ^ 2)
      ((integrable_const 1).sub (hm₁.const_mul (1 + l))) (hm₂.const_mul l)]
    rw [integral_sub (f := fun _t : ℝ => (1 : ℝ)) (g := fun t => (1 + l) * t)
      (integrable_const 1) (hm₁.const_mul (1 + l)),
      integral_const, integral_const_mul, integral_const_mul]
    simp [m, m₂, Measure.real]
  have hm₂_eval : 0 ≤ m - m₂ := sub_nonneg.mpr hm₂_le
  have hq_le : q ≤ 1 - m := by
    rw [hq_eval]
    nlinarith
  have hwq : w * q ≤ (l - 1) * m := by
    have hden : 0 < 1 - m := sub_pos.mpr hm_lt_one
    have hw' : w * (1 - m) ≤ (l - 1) * m := by
      apply (le_div_iff₀ hden).1
      exact hw.2
    calc
      w * q ≤ w * (1 - m) := mul_le_mul_of_nonneg_left hq_le hw.1
      _ ≤ (l - 1) * m := hw'
  have hmean0 : 0 ≤ ∫ t, Bw l w t ∂ξ := by
    have heval : ∫ t, Bw l w t ∂ξ = (l - 1) * m - w * q := by
      have hdecomp : (fun t : ℝ => Bw l w t) =
          (fun t => (l - 1) * t - w * ((1 - t) * (1 - l * t))) := by
        funext t
        unfold Bw
        ring
      rw [hdecomp, integral_sub (hm₁.const_mul (l - 1)) (hq.const_mul w),
        integral_const_mul, integral_const_mul]
    rw [heval]
    linarith
  have hBw_mono : MonotoneOn (Bw l w) (Set.Icc 0 (1 / l)) := by
    intro x hx y hy hxy
    obtain ⟨hx0, hx1, hxl⟩ := inv_l_mem_of_mem_Icc hl hx
    obtain ⟨hy0, hy1, hyl⟩ := inv_l_mem_of_mem_Icc hl hy
    have hK : 0 ≤ (l - 1) + w * (1 + l) - w * l * (x + y) := by
      have hsum : x + y ≤ 2 / l := by
        have h := add_le_add hx.2 hy.2
        convert h using 1 <;> ring
      have hwx : w * l * (x + y) ≤ w * l * (2 / l) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hw.1 (by linarith))
      have hid : w * l * (2 / l) = 2 * w := by field_simp
      rw [hid] at hwx
      nlinarith
    have hid : Bw l w y - Bw l w x =
        (y - x) * ((l - 1) + w * (1 + l) - w * l * (x + y)) := by
      unfold Bw
      ring
    have hprod : 0 ≤ Bw l w y - Bw l w x := by
      rw [hid]
      exact mul_nonneg (sub_nonneg.mpr hxy) hK
    linarith
  have hp_mono : MonotoneOn (fun t : ℝ => t ^ n) (Set.Icc 0 (1 / l)) := by
    intro x hx y hy hxy
    exact pow_le_pow_left₀ hx.1 hxy n
  have hpow : Integrable (fun t : ℝ => t ^ n) ξ := integrable_pow_on hl hξ n
  have hBw : Integrable (Bw l w) ξ := by
    simpa using integrable_Bw_pow (l := l) (w := w) hl hξ 0
  have hcov := integral_mul_ge_of_monotone (P := ξ) (Z := fun t : ℝ => t)
    (Set.Icc 0 (1 / l)) hξ hp_mono hBw_mono hpow hBw (integrable_Bw_pow hl hξ n)
  have hpow0 : 0 ≤ ∫ t, t ^ n ∂ξ := by
    apply integral_nonneg_of_ae
    filter_upwards [hξ] with t ht
    exact pow_nonneg ht.1 n
  have hprod0 : 0 ≤ (∫ t, t ^ n ∂ξ) * ∫ t, Bw l w t ∂ξ :=
    mul_nonneg hpow0 hmean0
  exact hprod0.trans hcov

private lemma Hw_terms_summable {ρ ξ : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ξ] (hl : 1 < l)
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc 0 (1 / l))
    (hξ : ∀ᵐ t ∂ξ, t ∈ Set.Icc 0 (1 / l)) (w : ℝ) :
    Summable (fun n : ℕ => (l ^ n * ∫ y, y ^ (n + 1) ∂ρ) * ∫ t, t ^ n * Bw l w t ∂ξ) := by
  let r : ℝ := 1 / l
  let C : ℝ := (l - 1) / l + |w|
  have hl0 : 0 < l := by linarith
  have hr0 : 0 ≤ r := by positivity
  have hr1 : ‖r‖ < 1 := by
    dsimp [r]
    rw [abs_of_nonneg hr0]
    exact (div_lt_one hl0).2 hl
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (n : ℕ) :
      ‖(l ^ n * ∫ y, y ^ (n + 1) ∂ρ) * ∫ t, t ^ n * Bw l w t ∂ξ‖ ≤ C * r * r ^ n := by
    have hM : ‖∫ y, y ^ (n + 1) ∂ρ‖ ≤ r ^ (n + 1) := by
      have h := norm_integral_le_of_norm_le_const (μ := ρ)
        (C := r ^ (n + 1)) (f := fun y => y ^ (n + 1)) (by
          filter_upwards [hρ] with y hy
          obtain ⟨hy0, hy1, _⟩ := inv_l_mem_of_mem_Icc hl hy
          rw [norm_pow, Real.norm_of_nonneg hy0]
          exact pow_le_pow_left₀ hy0 hy.2 (n + 1))
      simpa [Measure.real] using h
    have hI : ‖∫ t, t ^ n * Bw l w t ∂ξ‖ ≤ C / l ^ n := by
      have h := norm_integral_le_of_norm_le_const (μ := ξ)
        (C := C / l ^ n) (f := fun t => t ^ n * Bw l w t) (by
          filter_upwards [hξ] with t ht
          obtain ⟨ht0, ht1, _⟩ := inv_l_mem_of_mem_Icc hl ht
          calc
            ‖t ^ n * Bw l w t‖ = |t| ^ n * ‖Bw l w t‖ := by simp [norm_mul, norm_pow]
            _ ≤ (1 / l) ^ n * C := by
              apply mul_le_mul
              · exact pow_le_pow_left₀ (abs_nonneg t) (by rw [abs_of_nonneg ht0]; exact ht.2) n
              · exact Bw_norm_le hl ht
              · positivity
              · positivity
            _ = C / l ^ n := by
              simp only [one_mul, div_eq_mul_inv, ← inv_pow]
              ring)
      simpa [Measure.real] using h
    rw [norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg hl0.le]
    calc
      l ^ n * ‖∫ y, y ^ (n + 1) ∂ρ‖ * ‖∫ t, t ^ n * Bw l w t ∂ξ‖ ≤
          l ^ n * r ^ (n + 1) * (C / l ^ n) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul hM hI (norm_nonneg _) (by positivity)) (pow_nonneg hl0.le n)
      _ = C * r * r ^ n := by
        have hn : l ^ n ≠ 0 := pow_ne_zero _ hl0.ne'
        dsimp [r]
        field_simp [hl0.ne', hn]
        calc
          l * (1 / l) ^ (n + 1) * C = (l * (1 / l)) * C * (1 / l) ^ n := by
            rw [pow_succ]
            ring
          _ = C * (1 / l) ^ n := by
            rw [show l * (1 / l) = 1 by field_simp]
            ring
  exact ((summable_geometric_of_norm_lt_one hr1).mul_left (C * r)).of_norm_bounded hbound

/-- The expanded kernel compares two first-coordinate laws at fixed mean. -/
theorem kernel_compare (hl : 1 < l) {ρ₁ ρ₂ ξ : Measure ℝ}
    [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂] [IsProbabilityMeasure ξ]
    (hρ₁ : ∀ᵐ y ∂ρ₁, y ∈ Set.Icc 0 (1 / l))
    (hρ₂ : ∀ᵐ y ∂ρ₂, y ∈ Set.Icc 0 (1 / l))
    (hξ : ∀ᵐ t ∂ξ, t ∈ Set.Icc 0 (1 / l))
    (hmom : ∀ n ≥ 1, ∫ y, y ^ n ∂ρ₁ ≤ ∫ y, y ^ n ∂ρ₂)
    (w : ℝ) (hcoeff : ∀ n : ℕ, 0 ≤ ∫ t, t ^ n * Bw l w t ∂ξ) :
    ∫ p, Hw l w p.1 p.2 ∂ρ₁.prod ξ ≤ ∫ p, Hw l w p.1 p.2 ∂ρ₂.prod ξ := by
  rw [Hw_pair_series hl hρ₁ hξ, Hw_pair_series hl hρ₂ hξ]
  apply add_le_add_right
  apply Summable.tsum_le_tsum
  · intro n
    have hl0 : 0 ≤ l ^ n := pow_nonneg (by linarith) n
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hmom (n + 1) (Nat.succ_pos n)) (hcoeff n)) hl0
  · exact Hw_terms_summable hl hρ₁ hξ w
  · exact Hw_terms_summable hl hρ₂ hξ w

/-- The transformed numerator minus a multiple of the denominator. -/
theorem NY_sub_ZY (l w : ℝ) {ρ ρ' : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ρ'] (hl : 1 < l)
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc 0 (1 / l))
    (hρ' : ∀ᵐ t ∂ρ', t ∈ Set.Icc 0 (1 / l)) :
    NY l ρ ρ' - w * ZY l ρ ρ' = ∫ p, Hw l w p.1 p.2 ∂ρ.prod ρ' := by
  have hN : Integrable
      (fun p : ℝ × ℝ => (l - 1) * p.1 * p.2 / (1 - l * p.1 * p.2)) (ρ.prod ρ') := by
    simpa [Hw] using integrable_Hw hl hρ hρ' 0
  have hZ : Integrable
      (fun p : ℝ × ℝ => (p.1 * (1 - p.2) + p.2 * (1 - l * p.1)) /
        (1 - l * p.1 * p.2)) (ρ.prod ρ') := by
    apply (hN.sub (integrable_Hw hl hρ hρ' 1)).congr
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := ρ')).ae hρ,
      (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := ρ')).ae hρ'] with p hpY hpT
    have hden := (one_sub_prod_mem hl hpY hpT).1.ne'
    change (l - 1) * p.1 * p.2 / (1 - l * p.1 * p.2) - Hw l 1 p.1 p.2 = _
    unfold Hw
    field_simp [hden]
    ring
  unfold NY ZY
  rw [← integral_const_mul, ← integral_sub hN (hZ.const_mul w)]
  apply integral_congr_ae
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := ρ')).ae hρ,
    (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := ρ')).ae hρ'] with p hpY hpT
  have hden := (one_sub_prod_mem hl hpY hpT).1.ne'
  unfold Hw
  field_simp [hden]
  ring

/-! ## Geometric laws -/

private lemma geomY_probability {b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1) :
    IsProbabilityMeasure (geomY l b) := by
  have hr0 : 0 ≤ 1 - b := by linarith [hb.2]
  have hr1 : 1 - b < 1 := by linarith [hb.1]
  have hsum : Summable (fun g : ℕ => b * (1 - b) ^ g) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine ⟨?_⟩
  rw [geomY, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun g => mul_nonneg hb.1.le (pow_nonneg hr0 _)) hsum]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rw [sub_sub_cancel, mul_inv_cancel₀ hb.1.ne', ENNReal.ofReal_one]

private lemma ae_geomY_mem {b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1) :
    ∀ᵐ y ∂geomY l b, y ∈ Set.Icc 0 (1 / l) := by
  rw [geomY, Measure.ae_sum_iff]
  intro g
  apply Filter.Eventually.filter_mono (Measure.ae_smul_measure_le _)
  refine (mem_ae_dirac_iff (s := Set.Icc (0 : ℝ) (1 / l)) measurableSet_Icc).2 ⟨?_, ?_⟩
  · exact (zpow_pos (show 0 < l by linarith) (-((g : ℤ) + 1))).le
  · calc
      l ^ (-((g : ℤ) + 1)) ≤ l ^ (-1 : ℤ) := by
        apply zpow_le_zpow_right₀ hl.le
        omega
      _ = 1 / l := by simp

/-- Lemma 3.2 (`lem:convex-order`): moments of the comparison geometric law. -/
theorem geom_moment {b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1) (n : ℕ) :
    ∫ y, y ^ n ∂geomY l b = b / (l ^ n - 1 + b) := by
  have hn : 0 < l ^ n := pow_pos (by linarith) _
  have hr0 : 0 ≤ 1 - b := by linarith [hb.2]
  have hr1 : 1 - b < 1 := by linarith [hb.1]
  unfold geomY
  rw [integral_sum_dirac (by intro g; simp)]
  simp only [ENNReal.toReal_ofReal (mul_nonneg hb.1.le (pow_nonneg hr0 _)), smul_eq_mul]
  have hterm (g : ℕ) :
      b * (1 - b) ^ g * (l ^ (-((g : ℤ) + 1))) ^ n =
        b * (l ^ n)⁻¹ * ((1 - b) * (l ^ n)⁻¹) ^ g := by
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
  have hr'0 : 0 ≤ (1 - b) * (l ^ n)⁻¹ := mul_nonneg hr0 (inv_nonneg.mpr hn.le)
  have hr'1 : (1 - b) * (l ^ n)⁻¹ < 1 := by
    have hi : (l ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hl.le)
    calc
      (1 - b) * (l ^ n)⁻¹ ≤ (1 - b) * 1 := mul_le_mul_of_nonneg_left hi hr0
      _ < 1 := by simpa using hr1
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr'0 hr'1]
  field_simp [hb.1.ne', hn.ne']
  ring

/-- Lemma 3.2 (`lem:convex-order`): the geometric law with parameter `p_eff` has the
actual transformed mean. -/
theorem mean_geomY_peff (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    ∫ y, y ∂geomY l (peff μ l) = muY μ l := by
  have hb := peff_mem μ h hl hlm
  have hm := muY_mem μ h hl hlm
  rw [show (∫ y, y ∂geomY l (peff μ l)) = ∫ y, y ^ 1 ∂geomY l (peff μ l) by simp,
    geom_moment hl hb 1]
  have hm1 : muY μ l < 1 := hm.2.trans ((div_lt_one (by linarith : 0 < l)).2 (by linarith))
  have hden : 0 < 1 - muY μ l := sub_pos.mpr hm1
  have ha : 0 < l - 1 := by linarith
  unfold peff
  field_simp [ha.ne', hden.ne', hm.1.ne']
  ring

private lemma inverse_pow_eq_zpow (g : ℕ) :
    l ^ (-((g : ℤ) + 1)) = (l⁻¹) ^ (g + 1) := by
  have hg : -((g : ℤ) + 1) = -(((g + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [hg, zpow_neg, zpow_natCast, inv_pow]

private lemma geomY_prod_atoms {b : ℝ} (hb : b ∈ Set.Ioo 0 1) :
    (geomY l b).prod (geomY l b) = Measure.sum fun p : ℕ × ℕ =>
      ENNReal.ofReal ((b * (1 - b) ^ p.1) * (b * (1 - b) ^ p.2)) •
        Measure.dirac ((l⁻¹) ^ (p.1 + 1), (l⁻¹) ^ (p.2 + 1)) := by
  unfold geomY
  simp_rw [inverse_pow_eq_zpow (l := l)]
  rw [Measure.prod_sum]
  apply congrArg Measure.sum
  funext p
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.dirac_prod_dirac,
    smul_smul, ← ENNReal.ofReal_mul (mul_nonneg hb.1.le (pow_nonneg (by linarith [hb.2]) _))]

private lemma integral_geom_pair (hl : 1 < l) {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (F : ℝ × ℝ → ℝ) :
    ∫ p, F p ∂(geomY l b).prod (geomY l b) =
      ∑' p : ℕ × ℕ, ((b * (1 - b) ^ p.1) * (b * (1 - b) ^ p.2)) *
        F ((l⁻¹) ^ (p.1 + 1), (l⁻¹) ^ (p.2 + 1)) := by
  rw [geomY_prod_atoms hb, integral_sum_dirac (by intro p; simp)]
  apply tsum_congr
  intro p
  rw [ENNReal.toReal_ofReal (mul_nonneg
    (mul_nonneg hb.1.le (pow_nonneg (by linarith [hb.2]) _))
    (mul_nonneg hb.1.le (pow_nonneg (by linarith [hb.2]) _)))]
  rfl

private lemma summable_geometric_atom_weights {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun p : ℕ × ℕ => q ^ p.1 * q ^ p.2) := by
  have hq : Summable (fun g : ℕ => q ^ g) := summable_geometric_of_lt_one hq0 hq1
  apply (summable_prod_of_nonneg (fun p : ℕ × ℕ => by positivity)).2
  constructor
  · intro g
    exact hq.mul_left (q ^ g)
  · have heq : (fun g : ℕ => ∑' h : ℕ, q ^ g * q ^ h) =
        (fun g => q ^ g * (1 - q)⁻¹) := by
      funext g
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    rw [heq]
    exact hq.mul_right _

private lemma tsum_eq_sum_antidiagonal {F : ℕ × ℕ → ℝ} (hF : Summable F) :
    (∑' p : ℕ × ℕ, F p) = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, F kl := by
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq F]
  have hs : Summable (fun x : Σ n : ℕ, Finset.antidiagonal n => F x.2) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hF
  conv_rhs => congr; ext n; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  exact hs.tsum_sigma' (fun n => (hasSum_fintype _).summable)

private lemma geom_pair_eq_antidiagonal {b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1)
    (F : ℕ × ℕ → ℝ) (hF : Summable F) :
    ∑' p : ℕ × ℕ, F p = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, F kl :=
  tsum_eq_sum_antidiagonal hF

private lemma reset_den_identity (hl : 1 < l) (g h : ℕ) :
    1 - l * (l⁻¹) ^ (g + 1) * (l⁻¹) ^ (h + 1) =
      1 - (l⁻¹) ^ (g + h + 1) := by
  have hlr : l * l⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  congr 1
  calc
    l * (l⁻¹) ^ (g + 1) * (l⁻¹) ^ (h + 1) =
        (l * l⁻¹) * (l⁻¹) ^ (g + h + 1) := by
      rw [mul_assoc, ← pow_add, show g + 1 + (h + 1) = (g + h + 1) + 1 by omega, pow_succ]
      ring
    _ = (l⁻¹) ^ (g + h + 1) := by rw [hlr, one_mul]

private lemma reset_ratio_bound_one (hl : 1 < l) (g h : ℕ) :
    ‖(l⁻¹) ^ (g + 1) / (1 - l * (l⁻¹) ^ (g + 1) * (l⁻¹) ^ (h + 1))‖ ≤
      (l - 1)⁻¹ := by
  have hr0 : 0 ≤ (l⁻¹ : ℝ) := by positivity
  have hr1 : (l⁻¹ : ℝ) < 1 := (inv_lt_one₀ (by linarith)).2 hl
  rw [reset_den_identity hl]
  have hden : 0 < 1 - (l⁻¹) ^ (g + h + 1) := by
    have := pow_lt_one₀ hr0 hr1 (show g + h + 1 ≠ 0 by omega)
    linarith
  have hpow_le : (l⁻¹) ^ (g + h + 1) ≤ l⁻¹ :=
    pow_le_of_le_one hr0 hr1.le (by omega)
  have hnum_le : (l⁻¹) ^ (g + 1) ≤ l⁻¹ :=
    pow_le_of_le_one hr0 hr1.le (by omega)
  rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg hr0 _) hden.le)]
  apply (div_le_iff₀ hden).2
  have hlow : l⁻¹ ≤ ((l - 1)⁻¹) * (1 - (l⁻¹) ^ (g + h + 1)) := by
    calc
      l⁻¹ = ((l - 1)⁻¹) * (1 - l⁻¹) := by field_simp
      _ ≤ ((l - 1)⁻¹) * (1 - (l⁻¹) ^ (g + h + 1)) := by
        gcongr
  exact hnum_le.trans hlow

private lemma reset_ratio_bound_two (hl : 1 < l) (g h : ℕ) :
    ‖((l⁻¹) ^ (g + 1) * (l⁻¹) ^ (h + 1)) /
      (1 - l * (l⁻¹) ^ (g + 1) * (l⁻¹) ^ (h + 1))‖ ≤ (l - 1)⁻¹ := by
  have hr0 : 0 ≤ (l⁻¹ : ℝ) := by positivity
  have hr1 : (l⁻¹ : ℝ) < 1 := (inv_lt_one₀ (by linarith)).2 hl
  rw [reset_den_identity hl]
  have hden : 0 < 1 - (l⁻¹) ^ (g + h + 1) := by
    have := pow_lt_one₀ hr0 hr1 (show g + h + 1 ≠ 0 by omega)
    linarith
  have hnum : (l⁻¹) ^ (g + 1) * (l⁻¹) ^ (h + 1) ≤ l⁻¹ := by
    rw [← pow_add]
    exact pow_le_of_le_one hr0 hr1.le (by omega)
  have hpow_le : (l⁻¹) ^ (g + h + 1) ≤ l⁻¹ :=
    pow_le_of_le_one hr0 hr1.le (by omega)
  rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg (pow_nonneg hr0 _) (pow_nonneg hr0 _)) hden.le)]
  apply (div_le_iff₀ hden).2
  calc
    (l⁻¹) ^ (g + 1) * (l⁻¹) ^ (h + 1) ≤ l⁻¹ := hnum
    _ = ((l - 1)⁻¹) * (1 - l⁻¹) := by field_simp
    _ ≤ ((l - 1)⁻¹) * (1 - (l⁻¹) ^ (g + h + 1)) := by gcongr

private lemma inverse_geom_sum (hl : 1 < l) (n : ℕ) :
    ∑ g ∈ Finset.range (n + 1), (l⁻¹) ^ (g + 1) =
      (1 - (l⁻¹) ^ (n + 1)) / (l - 1) := by
  have ha : 0 < l - 1 := by linarith
  have hgeom := geom_sum_mul_neg (l⁻¹ : ℝ) (n + 1)
  have hshift : (∑ g ∈ Finset.range (n + 1), (l⁻¹) ^ (g + 1)) =
      l⁻¹ * ∑ g ∈ Finset.range (n + 1), (l⁻¹) ^ g := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [pow_succ]
    ring
  rw [hshift]
  apply (eq_div_iff ha.ne').2
  have har : 1 - (l⁻¹ : ℝ) = (l - 1) * l⁻¹ := by field_simp
  calc
    (l⁻¹ * ∑ g ∈ Finset.range (n + 1), (l⁻¹) ^ g) * (l - 1) =
        (∑ g ∈ Finset.range (n + 1), (l⁻¹) ^ g) * (1 - l⁻¹) := by rw [har]; ring
    _ = 1 - (l⁻¹) ^ (n + 1) := hgeom

/-- The first geometric reset kernel. -/
theorem geom_kernel_one {b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1) :
    ∫ p, p.1 / (1 - l * p.1 * p.2) ∂(geomY l b).prod (geomY l b) = b / (l - 1) := by
  let F : ℕ × ℕ → ℝ := fun p =>
    ((b * (1 - b) ^ p.1) * (b * (1 - b) ^ p.2)) *
      ((l⁻¹) ^ (p.1 + 1) / (1 - l * (l⁻¹) ^ (p.1 + 1) * (l⁻¹) ^ (p.2 + 1)))
  have hq0 : 0 ≤ 1 - b := by linarith [hb.2]
  have hq1 : 1 - b < 1 := by linarith [hb.1]
  have hweights := summable_geometric_atom_weights hq0 hq1
  have hF : Summable F := by
    apply ((hweights.mul_left (b ^ 2 / (l - 1)))).of_norm_bounded
    intro p
    dsimp [F]
    have hw0 : 0 ≤ (b * (1 - b) ^ p.1) * (b * (1 - b) ^ p.2) :=
      mul_nonneg (mul_nonneg hb.1.le (pow_nonneg hq0 _))
        (mul_nonneg hb.1.le (pow_nonneg hq0 _))
    rw [abs_mul, abs_of_nonneg hw0]
    calc
      (b * (1 - b) ^ p.1 * (b * (1 - b) ^ p.2)) *
          ‖(l⁻¹) ^ (p.1 + 1) / (1 - l * (l⁻¹) ^ (p.1 + 1) * (l⁻¹) ^ (p.2 + 1))‖ ≤
          (b * (1 - b) ^ p.1 * (b * (1 - b) ^ p.2)) * (l - 1)⁻¹ :=
        mul_le_mul_of_nonneg_left (reset_ratio_bound_one hl p.1 p.2) hw0
      _ = b ^ 2 / (l - 1) * ((1 - b) ^ p.1 * (1 - b) ^ p.2) := by ring
  rw [integral_geom_pair hl hb]
  change (∑' p, F p) = _
  rw [tsum_eq_sum_antidiagonal hF]
  have hinner (n : ℕ) : ∑ kl ∈ Finset.antidiagonal n, F kl =
      b ^ 2 * (1 - b) ^ n / (l - 1) := by
    have ha : 0 < l - 1 := by linarith
    have hden : 1 - (l⁻¹) ^ (n + 1) ≠ 0 := by
      have := pow_lt_one₀ (show 0 ≤ (l⁻¹ : ℝ) by positivity)
        ((inv_lt_one₀ (by linarith)).2 hl) (show n + 1 ≠ 0 by omega)
      linarith
    calc
      ∑ kl ∈ Finset.antidiagonal n, F kl =
          ∑ kl ∈ Finset.antidiagonal n, (b ^ 2 * (1 - b) ^ n) *
            ((l⁻¹) ^ (kl.1 + 1) / (1 - (l⁻¹) ^ (n + 1))) := by
        apply Finset.sum_congr rfl
        intro kl hkl
        have hsum := Finset.mem_antidiagonal.mp hkl
        dsimp [F]
        rw [← hsum, reset_den_identity hl]
        rw [hsum]
        rw [show b * (1 - b) ^ kl.1 * (b * (1 - b) ^ kl.2) =
          b ^ 2 * ((1 - b) ^ kl.1 * (1 - b) ^ kl.2) by ring, ← pow_add, hsum]
      _ = (b ^ 2 * (1 - b) ^ n / (1 - (l⁻¹) ^ (n + 1))) *
          ∑ kl ∈ Finset.antidiagonal n, (l⁻¹) ^ (kl.1 + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro kl _
        ring
      _ = (b ^ 2 * (1 - b) ^ n / (1 - (l⁻¹) ^ (n + 1))) *
          ∑ g ∈ Finset.range (n + 1), (l⁻¹) ^ (g + 1) := by
        congr 1
        exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun g _h => (l⁻¹) ^ (g + 1)) n
      _ = b ^ 2 * (1 - b) ^ n / (l - 1) := by
        rw [inverse_geom_sum hl]
        have hden' : 1 - (1 / l) ^ (n + 1) ≠ 0 := by simpa only [one_div] using hden
        field_simp [ha.ne', hden']
  simp_rw [hinner]
  have ha : 0 < l - 1 := by linarith
  rw [show (fun n : ℕ => b ^ 2 * (1 - b) ^ n / (l - 1)) =
      (fun n => b ^ 2 / (l - 1) * (1 - b) ^ n) by funext n; ring]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  field_simp [hb.1.ne', ha.ne']
  ring

private lemma reset_second_ratio (hl : 1 < l) (n : ℕ) :
    (l⁻¹) ^ (n + 2) / (1 - (l⁻¹) ^ (n + 1)) =
      (1 / Qgeo l (n + 1)) / ((l - 1) * l) := by
  have hl0 : 0 < l := by linarith
  have ha : 0 < l - 1 := by linarith
  have hlpow : 1 < l ^ (n + 1) := one_lt_pow₀ hl (by omega)
  have hQ : Qgeo l (n + 1) * (l - 1) = l ^ (n + 1) - 1 :=
    geom_sum_mul_of_one_le hl.le (n + 1)
  have hQpos : 0 < Qgeo l (n + 1) := by
    have hp : 0 < Qgeo l (n + 1) * (l - 1) := by rw [hQ]; linarith
    exact pos_of_mul_pos_left hp ha.le
  have hden : 1 - (l⁻¹) ^ (n + 1) ≠ 0 := by
    have := pow_lt_one₀ (show 0 ≤ (l⁻¹ : ℝ) by positivity)
      ((inv_lt_one₀ hl0).2 hl) (show n + 1 ≠ 0 by omega)
    linarith
  simp only [inv_pow]
  rw [pow_succ]
  field_simp [hl0.ne', ha.ne', hden, hQpos.ne', pow_ne_zero _ hl0.ne']
  rw [hQ]

/-- The second geometric reset kernel. -/
theorem geom_kernel_two {b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1) :
    ∫ p, p.1 * p.2 / (1 - l * p.1 * p.2) ∂(geomY l b).prod (geomY l b) =
      b ^ 2 * Sgeo l (1 - b) / ((l - 1) * l) := by
  let F : ℕ × ℕ → ℝ := fun p =>
    ((b * (1 - b) ^ p.1) * (b * (1 - b) ^ p.2)) *
      (((l⁻¹) ^ (p.1 + 1) * (l⁻¹) ^ (p.2 + 1)) /
        (1 - l * (l⁻¹) ^ (p.1 + 1) * (l⁻¹) ^ (p.2 + 1)))
  have hq0 : 0 ≤ 1 - b := by linarith [hb.2]
  have hq1 : 1 - b < 1 := by linarith [hb.1]
  have hweights := summable_geometric_atom_weights hq0 hq1
  have hF : Summable F := by
    apply ((hweights.mul_left (b ^ 2 / (l - 1)))).of_norm_bounded
    intro p
    dsimp [F]
    have hw0 : 0 ≤ (b * (1 - b) ^ p.1) * (b * (1 - b) ^ p.2) :=
      mul_nonneg (mul_nonneg hb.1.le (pow_nonneg hq0 _))
        (mul_nonneg hb.1.le (pow_nonneg hq0 _))
    rw [abs_mul, abs_of_nonneg hw0]
    calc
      (b * (1 - b) ^ p.1 * (b * (1 - b) ^ p.2)) *
          ‖((l⁻¹) ^ (p.1 + 1) * (l⁻¹) ^ (p.2 + 1)) /
            (1 - l * (l⁻¹) ^ (p.1 + 1) * (l⁻¹) ^ (p.2 + 1))‖ ≤
          (b * (1 - b) ^ p.1 * (b * (1 - b) ^ p.2)) * (l - 1)⁻¹ :=
        mul_le_mul_of_nonneg_left (reset_ratio_bound_two hl p.1 p.2) hw0
      _ = b ^ 2 / (l - 1) * ((1 - b) ^ p.1 * (1 - b) ^ p.2) := by ring
  rw [integral_geom_pair hl hb]
  change (∑' p, F p) = _
  rw [tsum_eq_sum_antidiagonal hF]
  have hinner (n : ℕ) : ∑ kl ∈ Finset.antidiagonal n, F kl =
      (b ^ 2 / ((l - 1) * l)) * ((n : ℝ) + 1) * (1 - b) ^ n / Qgeo l (n + 1) := by
    calc
      ∑ kl ∈ Finset.antidiagonal n, F kl = ∑ _kl ∈ Finset.antidiagonal n,
          (b ^ 2 * (1 - b) ^ n) * ((l⁻¹) ^ (n + 2) / (1 - (l⁻¹) ^ (n + 1))) := by
        apply Finset.sum_congr rfl
        intro kl hkl
        have hsum := Finset.mem_antidiagonal.mp hkl
        dsimp [F]
        rw [← hsum, reset_den_identity hl]
        rw [hsum]
        rw [show b * (1 - b) ^ kl.1 * (b * (1 - b) ^ kl.2) =
          b ^ 2 * ((1 - b) ^ kl.1 * (1 - b) ^ kl.2) by ring, ← pow_add, hsum]
        congr 1
        rw [← pow_add, show kl.1 + 1 + (kl.2 + 1) = n + 2 by omega]
      _ = (n + 1 : ℕ) • ((b ^ 2 * (1 - b) ^ n) *
          ((l⁻¹) ^ (n + 2) / (1 - (l⁻¹) ^ (n + 1)))) := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal]
      _ = (b ^ 2 * (1 - b) ^ n) * (((n : ℝ) + 1) / Qgeo l (n + 1)) /
          ((l - 1) * l) := by
        rw [reset_second_ratio hl]
        simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring
      _ = (b ^ 2 / ((l - 1) * l)) * ((n : ℝ) + 1) * (1 - b) ^ n /
          Qgeo l (n + 1) := by ring
  simp_rw [hinner]
  unfold Sgeo
  calc
    _ = ∑' n : ℕ, (b ^ 2 / ((l - 1) * l)) *
        (((n : ℝ) + 1) * (1 - b) ^ n / Qgeo l (n + 1)) := by
      apply tsum_congr
      intro n
      ring
    _ = (b ^ 2 / ((l - 1) * l)) *
        ∑' n : ℕ, ((n : ℝ) + 1) * (1 - b) ^ n / Qgeo l (n + 1) :=
      tsum_mul_left
    _ = _ := by ring

private lemma integrable_reset_one {b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1) :
    Integrable (fun p : ℝ × ℝ => p.1 / (1 - l * p.1 * p.2)) ((geomY l b).prod (geomY l b)) := by
  letI := geomY_probability hl hb
  have hmem := ae_geomY_mem hl hb
  apply integrable_bounded_of_ae (by fun_prop)
  have hfst := (Measure.quasiMeasurePreserving_fst
    (μ := geomY l b) (ν := geomY l b)).ae hmem
  have hsnd := (Measure.quasiMeasurePreserving_snd
    (μ := geomY l b) (ν := geomY l b)).ae hmem
  filter_upwards [hfst, hsnd] with p hpY hpT
  obtain ⟨hden, hdenlo⟩ := one_sub_prod_mem hl hpY hpT
  rw [Real.norm_of_nonneg (div_nonneg hpY.1 hden.le)]
  apply (div_le_iff₀ hden).2
  calc
    p.1 ≤ 1 / l := hpY.2
    _ ≤ (l - 1)⁻¹ * (1 - l * p.1 * p.2) := by
      calc
        1 / l = (l - 1)⁻¹ * ((l - 1) / l) := by field_simp
        _ ≤ (l - 1)⁻¹ * (1 - l * p.1 * p.2) := by gcongr

private lemma integrable_reset_two {b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1) :
    Integrable (fun p : ℝ × ℝ => p.1 * p.2 / (1 - l * p.1 * p.2))
      ((geomY l b).prod (geomY l b)) := by
  letI := geomY_probability hl hb
  have hmem := ae_geomY_mem hl hb
  have h := integrable_Hw (ρ := geomY l b) (ξ := geomY l b) hl hmem hmem 0
  have hscale := h.const_mul ((l - 1)⁻¹)
  apply hscale.congr
  apply Filter.Eventually.of_forall
  intro p
  simp only [Hw, zero_mul, sub_zero, zero_add]
  calc
    _ = ((l - 1)⁻¹ * (l - 1)) * (p.1 * p.2 / (1 - l * p.1 * p.2)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (by linarith : l - 1 ≠ 0), one_mul]

/-- The geometric speed is the explicit reset quotient. -/
theorem geom_speed {b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1)
    (hden : 0 < 2 * l - (1 + l) * b * Sgeo l (1 - b)) :
    NY l (geomY l b) (geomY l b) / ZY l (geomY l b) (geomY l b) =
      (l - 1) * b * Sgeo l (1 - b) / (2 * l - (1 + l) * b * Sgeo l (1 - b)) := by
  letI := geomY_probability hl hb
  have hmem := ae_geomY_mem hl hb
  have h₁ := geom_kernel_one hl hb
  have h₂ := geom_kernel_two hl hb
  have hi₁ := integrable_reset_one hl hb
  have hi₂ := integrable_reset_two hl hb
  have hNY : NY l (geomY l b) (geomY l b) =
      (l - 1) * ∫ p, p.1 * p.2 / (1 - l * p.1 * p.2) ∂(geomY l b).prod (geomY l b) := by
    unfold NY
    calc
      _ = ∫ p : ℝ × ℝ, (l - 1) * (p.1 * p.2 / (1 - l * p.1 * p.2))
          ∂(geomY l b).prod (geomY l b) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by ring
      _ = _ := integral_const_mul (r := l - 1)
        (f := fun p : ℝ × ℝ => p.1 * p.2 / (1 - l * p.1 * p.2))
  have hZ : ZY l (geomY l b) (geomY l b) =
      2 * (∫ p, p.1 / (1 - l * p.1 * p.2) ∂(geomY l b).prod (geomY l b)) -
        (1 + l) * ∫ p, p.1 * p.2 / (1 - l * p.1 * p.2) ∂(geomY l b).prod (geomY l b) := by
    have hi₁' : Integrable (fun p : ℝ × ℝ => p.1 / (1 - l * p.1 * p.2))
        ((geomY l b).prod (geomY l b)) := hi₁
    have hi₁'' : Integrable (fun p : ℝ × ℝ => p.2 / (1 - l * p.1 * p.2))
        ((geomY l b).prod (geomY l b)) := by
      simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hi₁.swap
    unfold ZY
    rw [show (fun p : ℝ × ℝ => (p.1 * (1 - p.2) + p.2 * (1 - l * p.1)) /
        (1 - l * p.1 * p.2)) = (fun p =>
        (p.1 / (1 - l * p.1 * p.2) + p.2 / (1 - l * p.1 * p.2)) -
          (1 + l) * (p.1 * p.2 / (1 - l * p.1 * p.2))) by
      funext p
      ring]
    rw [integral_sub
      (f := fun p : ℝ × ℝ => p.1 / (1 - l * p.1 * p.2) + p.2 / (1 - l * p.1 * p.2))
      (g := fun p : ℝ × ℝ => (1 + l) * (p.1 * p.2 / (1 - l * p.1 * p.2)))
      (hi₁'.add hi₁'') (hi₂.const_mul (1 + l)),
      integral_add hi₁' hi₁'', integral_const_mul]
    have hs : (∫ p : ℝ × ℝ, p.2 / (1 - l * p.1 * p.2) ∂(geomY l b).prod (geomY l b)) =
        ∫ p : ℝ × ℝ, p.1 / (1 - l * p.1 * p.2) ∂(geomY l b).prod (geomY l b) := by
      simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
        (integral_prod_swap (μ := geomY l b) (ν := geomY l b)
          (fun p : ℝ × ℝ => p.1 / (1 - l * p.1 * p.2)))
    rw [hs]
    ring
  rw [hZ, h₁, h₂, hNY, h₂]
  have ha : 0 < l - 1 := by linarith
  have hb0 : b ≠ 0 := hb.1.ne'
  have hZne : 2 * (b / (l - 1)) -
      (1 + l) * (b ^ 2 * Sgeo l (1 - b) / ((l - 1) * l)) ≠ 0 := by
    have hl0 : 0 < l := by linarith
    have heq : 2 * (b / (l - 1)) -
        (1 + l) * (b ^ 2 * Sgeo l (1 - b) / ((l - 1) * l)) =
        b * (2 * l - (1 + l) * b * Sgeo l (1 - b)) / ((l - 1) * l) := by
      field_simp [ha.ne', hl0.ne']
    rw [heq]
    exact div_ne_zero (mul_ne_zero hb0 hden.ne') (mul_ne_zero ha.ne' hl0.ne')
  field_simp [ha.ne', hZne, hden.ne']

end LPPMonotonicityProof.Analytic
