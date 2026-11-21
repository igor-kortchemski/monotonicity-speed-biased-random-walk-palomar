module

public import LPPMonotonicityProof.Analytic.Ceiling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Averaged speed gradient

This module proves the averaged-gradient part of Lemma 3.3 (`lem:speed-ceiling`):
`Γ(0) = E f₀(Y)`, `0 < Γ(t) ≤ E Y` for `t ∈ [0, 1]`, and `E[(√λ Y)^j f₀(Y)] > 0` for
every `j ≥ 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

private lemma integrable_bounded_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → ℝ} (hf : AEMeasurable f P) {C : ℝ}
    (hC : ∀ᵐ x ∂P, ‖f x‖ ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C hC

private lemma y_factor_bounds {l y : ℝ} (hl : 1 < l)
    (hy : y ∈ Set.Icc 0 (1 / l)) :
    0 ≤ y ∧ y ≤ 1 ∧ 0 ≤ (1 - y) * (1 - l * y) ∧
      (1 - y) * (1 - l * y) ≤ 1 := by
  have hl0 : 0 < l := by linarith
  have h1l : 1 / l ≤ 1 := by
    apply (div_le_iff₀ hl0).2
    nlinarith
  have hy1 : y ≤ 1 := hy.2.trans h1l
  have hly : l * y ≤ 1 := by
    calc
      l * y ≤ l * (1 / l) := mul_le_mul_of_nonneg_left hy.2 hl0.le
      _ = 1 := by field_simp
  have hA : 0 ≤ 1 - y := by linarith
  have hB : 0 ≤ 1 - l * y := by linarith
  have hA1 : 1 - y ≤ 1 := by linarith [hy.1]
  have hly0 : 0 ≤ l * y := mul_nonneg hl0.le hy.1
  have hB1 : 1 - l * y ≤ 1 := by linarith
  have hp : 0 ≤ (1 - y) * (1 - l * y) := mul_nonneg hA hB
  have hp1 : (1 - y) * (1 - l * y) ≤ 1 := by
    calc
      (1 - y) * (1 - l * y) ≤ (1 - y) * 1 :=
        mul_le_mul_of_nonneg_left hB1 hA
      _ ≤ 1 := by nlinarith
  exact ⟨hy.1, hy1, hp, hp1⟩

private lemma integrable_Ylaw_comp (l : ℝ) (F : ℝ → ℝ)
    (hF : AEStronglyMeasurable F (Ylaw μ l)) :
    ∫ y, F y ∂Ylaw μ l = ∫ T, F (Yt l T) ∂GW μ := by
  unfold Ylaw
  exact integral_map (measurable_Yt l).aemeasurable hF

private noncomputable def gammaWeight (l t y : ℝ) : ℝ :=
  ((l - 1) / ((l - 1) + t * (1 - l * y))) ^ 2

private lemma measurable_f0 (l r : ℝ) : Measurable (fun y : ℝ => fθ l r 0 y) := by
  unfold fθ
  fun_prop

private lemma measurable_gammaWeight (l t : ℝ) : Measurable (gammaWeight l t) := by
  unfold gammaWeight
  fun_prop

private lemma measurable_Bw (l w : ℝ) : Measurable (Bw l w) := by
  unfold Bw
  fun_prop

private lemma f0_shape (l r y : ℝ) :
    fθ l r 0 y = y - r * ((1 - y) * (1 - l * y)) := by
  simp [fθ]
  ring

private lemma Bw_shape (l w y : ℝ) :
    Bw l w y = (l - 1) * y - w * ((1 - y) * (1 - l * y)) := by
  unfold Bw
  ring

private lemma yLaw_probability (l : ℝ) : IsProbabilityMeasure (Ylaw μ l) := by
  unfold Ylaw
  infer_instance

private lemma yLaw_Ioo (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Ioo 0 (1 / l) :=
  ae_Ylaw_mem μ h hl hlm

private lemma yLaw_Icc (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l) := by
  filter_upwards [yLaw_Ioo μ h hl hlm] with y hy
  exact ⟨hy.1.le, hy.2.le⟩

private lemma yLaw_mean (l : ℝ) : ∫ y, y ∂Ylaw μ l = muY μ l := by
  unfold Ylaw muY
  exact integral_map (measurable_Yt l).aemeasurable measurable_id.aestronglyMeasurable

private lemma integrable_escape_factor {l : ℝ} [IsProbabilityMeasure (Ylaw μ l)] (hl : 1 < l)
    (hY : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l)) :
    Integrable (fun y => (1 - y) * (1 - l * y)) (Ylaw μ l) := by
  apply integrable_bounded_ae (by fun_prop) (C := 1)
  filter_upwards [hY] with y hy
  obtain ⟨_, _, hp, hp1⟩ := y_factor_bounds hl hy
  rw [Real.norm_of_nonneg hp]
  exact hp1

private lemma integral_escape_factor_pos (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    0 < ∫ y, (1 - y) * (1 - l * y) ∂Ylaw μ l := by
  letI : IsProbabilityMeasure (Ylaw μ l) := yLaw_probability μ l
  have hY := yLaw_Icc μ h hl hlm
  have hYo := yLaw_Ioo μ h hl hlm
  have hi := integrable_escape_factor μ hl hY
  apply integral_pos_of_ae_pos hi
  filter_upwards [hYo] with y hy
  have h1 : 0 < 1 - y := by
    have hl0 : 0 < l := by linarith
    have h1l : 1 / l < 1 := by
      apply (div_lt_iff₀ hl0).2
      nlinarith
    exact sub_pos.mpr (hy.2.trans h1l)
  have h2 : 0 < 1 - l * y := by
    have hl0 : 0 < l := by linarith
    have h := mul_lt_mul_of_pos_left hy.2 hl0
    have hly : l * y < 1 := by
      calc
        l * y < l * (1 / l) := h
        _ = 1 := by field_simp
    linarith
  exact mul_pos h1 h2

private lemma integrable_Bw {l : ℝ} [IsProbabilityMeasure (Ylaw μ l)] (hl : 1 < l)
    (hY : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l)) (w : ℝ) :
    Integrable (fun y => Bw l w y) (Ylaw μ l) := by
  apply integrable_bounded_ae (measurable_Bw l w).aemeasurable (C := |l - 1| + |w|)
  filter_upwards [hY] with y hy
  obtain ⟨hy0, hy1, hg0, hg1⟩ := y_factor_bounds hl hy
  rw [Real.norm_eq_abs, Bw_shape]
  calc
    |(l - 1) * y - w * ((1 - y) * (1 - l * y))| ≤
        |(l - 1) * y| + |w * ((1 - y) * (1 - l * y))| := abs_sub _ _
    _ = |l - 1| * |y| + |w| * |(1 - y) * (1 - l * y)| := by
      rw [abs_mul, abs_mul]
    _ ≤ |l - 1| + |w| := by
      have hyabs : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
      have hgabs : |(1 - y) * (1 - l * y)| ≤ 1 := by
        rw [abs_of_nonneg hg0]
        exact hg1
      nlinarith [abs_nonneg (l - 1), abs_nonneg w]

private lemma f0_integrable {l r : ℝ} [IsProbabilityMeasure (Ylaw μ l)] (hl : 1 < l)
    (hY : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l)) :
    Integrable (fun y => fθ l r 0 y) (Ylaw μ l) := by
  apply integrable_bounded_ae (measurable_f0 l r).aemeasurable (C := 1 + |r|)
  filter_upwards [hY] with y hy
  obtain ⟨hy0, hy1, hg0, hg1⟩ := y_factor_bounds hl hy
  rw [Real.norm_eq_abs, f0_shape]
  calc
    |y - r * ((1 - y) * (1 - l * y))| ≤
        |y| + |r * ((1 - y) * (1 - l * y))| := abs_sub _ _
    _ = |y| + |r| * |(1 - y) * (1 - l * y)| := by rw [abs_mul]
    _ ≤ 1 + |r| := by
      have hyabs : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
      have hgabs : |(1 - y) * (1 - l * y)| ≤ 1 := by
        rw [abs_of_nonneg hg0]
        exact hg1
      nlinarith [abs_nonneg r]

private lemma f0_le_id {l r y : ℝ} (hl : 1 < l)
    (hy : y ∈ Set.Icc 0 (1 / l)) (hr : 0 ≤ r) :
    fθ l r 0 y ≤ y := by
  obtain ⟨_, _, hg, _⟩ := y_factor_bounds hl hy
  rw [f0_shape]
  exact sub_le_self _ (mul_nonneg hr hg)

private lemma f0_monoOn {l r : ℝ} (hl : 1 < l) (hr : 0 ≤ r) :
    MonotoneOn (fun y => fθ l r 0 y) (Set.Icc 0 (1 / l)) := by
  intro x hx y hy hxy
  have hl0 : 0 < l := by linarith
  have hsum : x + y ≤ 2 / l := by
    calc
      x + y ≤ 1 / l + 1 / l := add_le_add hx.2 hy.2
      _ = 2 / l := by ring
  have hlsum : l * (x + y) ≤ 2 := by
    calc
      l * (x + y) ≤ l * (2 / l) := mul_le_mul_of_nonneg_left hsum hl0.le
      _ = 2 := by field_simp
  have hdiff : fθ l r 0 y - fθ l r 0 x =
      (y - x) * (1 + r * (1 + l - l * (x + y))) := by
    rw [f0_shape, f0_shape]
    ring
  have hfactor : 0 ≤ 1 + r * (1 + l - l * (x + y)) := by
    have hbase : 0 ≤ 1 + l - l * (x + y) := by linarith
    positivity
  rw [← sub_nonneg]
  rw [hdiff]
  exact mul_nonneg (sub_nonneg.mpr hxy) hfactor

private lemma gammaWeight_bounds {l t y : ℝ} (hl : 1 < l)
    (ht : t ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 (1 / l)) :
    0 ≤ gammaWeight l t y ∧ gammaWeight l t y ≤ 1 := by
  have ha : 0 < l - 1 := by linarith
  have hly : l * y ≤ 1 := by
    calc
      l * y ≤ l * (1 / l) := mul_le_mul_of_nonneg_left hy.2 (by linarith)
      _ = 1 := by field_simp
  let d := (l - 1) + t * (1 - l * y)
  have hd : 0 < d := by
    dsimp [d]
    have ht0 : 0 ≤ t := ht.1
    positivity
  have hratio0 : 0 ≤ (l - 1) / d := div_nonneg ha.le hd.le
  have hratio1 : (l - 1) / d ≤ 1 := by
    apply (div_le_iff₀ hd).2
    dsimp [d]
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hly)]
  have hsq : ((l - 1) / d) ^ 2 ≤ 1 := by
    have hsum : 0 ≤ 1 + (l - 1) / d := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio1) hsum]
  constructor
  · unfold gammaWeight
    exact sq_nonneg _
  · unfold gammaWeight
    simpa [d] using hsq

private lemma gammaWeight_pos {l t y : ℝ} (hl : 1 < l)
    (ht : t ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 (1 / l)) :
    0 < gammaWeight l t y := by
  have ha : 0 < l - 1 := by linarith
  have hly : l * y ≤ 1 := by
    calc
      l * y ≤ l * (1 / l) := mul_le_mul_of_nonneg_left hy.2 (by linarith)
      _ = 1 := by field_simp
  have hd : 0 < (l - 1) + t * (1 - l * y) := by
    have ht0 : 0 ≤ t := ht.1
    positivity
  unfold gammaWeight
  exact sq_pos_of_pos (div_pos ha hd)

private lemma gammaWeight_monoOn {l t : ℝ} (hl : 1 < l)
    (ht : t ∈ Set.Icc 0 1) :
    MonotoneOn (gammaWeight l t) (Set.Icc 0 (1 / l)) := by
  intro x hx y hy hxy
  have ha : 0 < l - 1 := by linarith
  have hl0 : 0 < l := by linarith
  let dx := (l - 1) + t * (1 - l * x)
  let dy := (l - 1) + t * (1 - l * y)
  have hxy' : 1 - l * y ≤ 1 - l * x := by
    have hmul := mul_le_mul_of_nonneg_left hxy hl0.le
    linarith
  have hden : dy ≤ dx := by
    dsimp [dx, dy]
    exact add_le_add (le_refl (l - 1)) (mul_le_mul_of_nonneg_left hxy' ht.1)
  have hdx : 0 < dx := by
    dsimp [dx]
    have hly : l * x ≤ 1 := by
      calc
        l * x ≤ l * (1 / l) := mul_le_mul_of_nonneg_left hx.2 hl0.le
        _ = 1 := by field_simp
    have ht0 : 0 ≤ t := ht.1
    positivity
  have hdy : 0 < dy := by
    dsimp [dy]
    have hly : l * y ≤ 1 := by
      calc
        l * y ≤ l * (1 / l) := mul_le_mul_of_nonneg_left hy.2 hl0.le
        _ = 1 := by field_simp
    have ht0 : 0 ≤ t := ht.1
    positivity
  have hratio : (l - 1) / dx ≤ (l - 1) / dy := by
    apply (div_le_div_iff₀ hdx hdy).2
    exact mul_le_mul_of_nonneg_left hden ha.le
  have hx0 : 0 ≤ (l - 1) / dx := div_nonneg ha.le hdx.le
  have hy0 : 0 ≤ (l - 1) / dy := div_nonneg ha.le hdy.le
  have hsq : ((l - 1) / dx) ^ 2 ≤ ((l - 1) / dy) ^ 2 := by
    have hsum : 0 ≤ (l - 1) / dy + (l - 1) / dx := add_nonneg hy0 hx0
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio) hsum]
  unfold gammaWeight
  dsimp [dx, dy] at hratio hx0 hy0
  simpa [dx, dy] using hsq

private lemma integrable_gammaWeight {l t : ℝ} [IsProbabilityMeasure (Ylaw μ l)] (hl : 1 < l)
    (ht : t ∈ Set.Icc 0 1) (hY : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l)) :
    Integrable (gammaWeight l t) (Ylaw μ l) := by
  apply integrable_bounded_ae (measurable_gammaWeight l t).aemeasurable (C := 1)
  filter_upwards [hY] with y hy
  obtain ⟨hw0, hw1⟩ := gammaWeight_bounds hl ht hy
  rw [Real.norm_of_nonneg hw0]
  exact hw1

private lemma integrable_f0_mul_weight {l r t : ℝ} [IsProbabilityMeasure (Ylaw μ l)] (hl : 1 < l)
    (ht : t ∈ Set.Icc 0 1) (hY : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l)) :
    Integrable (fun y => fθ l r 0 y * gammaWeight l t y) (Ylaw μ l) := by
  apply integrable_bounded_ae
    ((measurable_f0 l r).mul (measurable_gammaWeight l t)).aemeasurable
    (C := 1 + |r|)
  filter_upwards [hY] with y hy
  have ⟨hw0, hw1⟩ := gammaWeight_bounds hl ht hy
  have hFbound : ‖fθ l r 0 y‖ ≤ 1 + |r| := by
    have ⟨hy0, hy1, hg0, hg1⟩ := y_factor_bounds hl hy
    rw [Real.norm_eq_abs, f0_shape]
    calc
      |y - r * ((1 - y) * (1 - l * y))| ≤
          |y| + |r * ((1 - y) * (1 - l * y))| := abs_sub _ _
      _ = |y| + |r| * |(1 - y) * (1 - l * y)| := by rw [abs_mul]
      _ ≤ 1 + |r| := by
        have hyabs : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
        have hgabs : |(1 - y) * (1 - l * y)| ≤ 1 := by
          rw [abs_of_nonneg hg0]
          exact hg1
        nlinarith [abs_nonneg r]
  change ‖fθ l r 0 y * gammaWeight l t y‖ ≤ 1 + |r|
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
  calc
    ‖fθ l r 0 y‖ * gammaWeight l t y ≤ ‖fθ l r 0 y‖ * 1 :=
      mul_le_mul_of_nonneg_left hw1 (norm_nonneg _)
    _ ≤ 1 + |r| := by simpa using hFbound

private lemma pol_at_zero_eq_f0 {l v β : ℝ} (hl : 1 < l) (hβ : 0 ≤ β) :
    Pol l v β / (l - 1 + β) ^ 2 = fθ l (v / (l - 1)) 0 (β / (l - 1 + β)) := by
  have ha : l - 1 + β ≠ 0 := by linarith
  simp only [Pol, fθ, zero_mul, sub_zero]
  field_simp [ha]
  ring

private lemma gammaWeight_factor {l t β : ℝ} (hl : 1 < l)
    (ht : t ∈ Set.Icc 0 1) (hβ : β ∈ Set.Icc 0 1) :
    gammaWeight l t (β / (l - 1 + β)) =
      ((l - 1 + β) / DfunProv l t β) ^ 2 := by
  have ha : 0 < l - 1 := by linarith
  have haβpos : 0 < l - 1 + β := by linarith [ha, hβ.1]
  have haβ : l - 1 + β ≠ 0 := haβpos.ne'
  have hden : 0 < DfunProv l t β := by
    unfold DfunProv
    have h := mul_nonneg hβ.1 (sub_nonneg.mpr ht.2)
    nlinarith [ha, ht.1, hβ.1, h]
  have htransform :
      1 - l * (β / (l - 1 + β)) = (l - 1) * (1 - β) / (l - 1 + β) := by
    field_simp [haβ]
    ring
  have hden2 : 0 < (l - 1) + t * (1 - l * (β / (l - 1 + β))) := by
    rw [htransform]
    have hβ' : 0 ≤ 1 - β := by linarith [hβ.2]
    have hfrac : 0 ≤ (l - 1) * (1 - β) / (l - 1 + β) :=
      div_nonneg (mul_nonneg ha.le hβ') haβpos.le
    have htfrac : 0 ≤ t * ((l - 1) * (1 - β) / (l - 1 + β)) :=
      mul_nonneg ht.1 hfrac
    linarith
  have hprod :
      (l - 1 + β) * ((l - 1) + t * (1 - l * (β / (l - 1 + β)))) =
        (l - 1) * DfunProv l t β := by
    rw [htransform]
    unfold DfunProv
    field_simp [haβ]
    ring
  have hratio :
      (l - 1) / ((l - 1) + t * (1 - l * (β / (l - 1 + β)))) =
        (l - 1 + β) / DfunProv l t β := by
    apply (div_eq_div_iff hden2.ne' hden.ne').2
    nlinarith [hprod]
  unfold gammaWeight
  rw [hratio]

private lemma gamma_integrand_eq {l t : ℝ} (hl : 1 < l)
    (ht : t ∈ Set.Icc 0 1) (T : Tree) :
    Pol l (speedValueProv μ l) (escape l T) /
        DfunProv l t (escape l T) ^ 2 =
      fθ l (rr μ l) 0 (Yt l T) * gammaWeight l t (Yt l T) := by
  let β := escape l T
  have hl0 : 0 < l := by linarith
  have hβ : β ∈ Set.Icc 0 1 := escape_mem_Icc hl0 T
  have ha : l - 1 + β ≠ 0 := by linarith [hβ.1]
  have hdenpos : 0 < DfunProv l t β := by
    unfold DfunProv
    have h := mul_nonneg hβ.1 (sub_nonneg.mpr ht.2)
    nlinarith [hl, ht.1, hβ.1, h]
  have hden : DfunProv l t β ≠ 0 := hdenpos.ne'
  have hpol := pol_at_zero_eq_f0 (l := l) (v := speedValueProv μ l) (β := β) hl hβ.1
  have hw := gammaWeight_factor hl ht hβ
  have hY : Yt l T = β / (l - 1 + β) := by
    simp [Yt, β]
  have hfactor :
      Pol l (speedValueProv μ l) β / DfunProv l t β ^ 2 =
        (Pol l (speedValueProv μ l) β / (l - 1 + β) ^ 2) *
          ((l - 1 + β) / DfunProv l t β) ^ 2 := by
    field_simp [ha, hden]
  change Pol l (speedValueProv μ l) β / DfunProv l t β ^ 2 = _
  calc
    _ = (Pol l (speedValueProv μ l) β / (l - 1 + β) ^ 2) *
          ((l - 1 + β) / DfunProv l t β) ^ 2 := hfactor
    _ = fθ l (rr μ l) 0 (β / (l - 1 + β)) *
          gammaWeight l t (β / (l - 1 + β)) := by
      rw [hpol, hw]
      congr 1
    _ = _ := by rw [hY]

private lemma Gam_eq_Ylaw {l t : ℝ} (hl : 1 < l)
    (ht : t ∈ Set.Icc 0 1) :
    Gam μ l t = ∫ y, fθ l (rr μ l) 0 y * gammaWeight l t y ∂Ylaw μ l := by
  unfold Gam
  calc
    _ = ∫ T, fθ l (rr μ l) 0 (Yt l T) * gammaWeight l t (Yt l T) ∂GW μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun T => by
        have h := gamma_integrand_eq (μ := μ) hl ht T
        simpa using h
    _ = _ := (integrable_Ylaw_comp μ l _
      ((measurable_f0 l (rr μ l)).mul (measurable_gammaWeight l t)).aestronglyMeasurable).symm

private lemma f0_integral_pos (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    0 < ∫ y, fθ l (rr μ l) 0 y ∂Ylaw μ l := by
  letI : IsProbabilityMeasure (Ylaw μ l) := yLaw_probability μ l
  let b : ℝ := peff μ l
  have hY := yLaw_Icc μ h hl hlm
  have hmeanY := yLaw_mean μ l
  have hm : 0 < ∫ y, y ∂Ylaw μ l := by
    rw [hmeanY]
    exact (muY_mem μ h hl hlm).1
  have hb : 0 < b := by
    dsimp [b]
    exact (peff_mem μ h hl hlm).1
  have hwb : 0 ≤ b ∧
      b ≤ (l - 1) * (∫ y, y ∂Ylaw μ l) / (1 - ∫ y, y ∂Ylaw μ l) := by
    refine ⟨hb.le, ?_⟩
    rw [hmeanY]
    dsimp [b, peff]
    rfl
  have hcoeff : 0 ≤ ∫ y, Bw l b y ∂Ylaw μ l := by
    have hc := kernel_coeff_nonneg (l := l) hl hY b hm hwb 0
    simpa using hc
  obtain ⟨_, hv, hv2, hvb⟩ := speed_le_ceiling μ h hl hlm
  have hspeed : Speed.speedValue μ l < b := by
    dsimp [b]
    exact hv.trans_lt (hv2.trans_lt hvb)
  have hspeed' : speedValueProv μ l < b := by
    rw [← speedValue_eq_speedValueProv μ l]
    exact hspeed
  have hfactorpos := integral_escape_factor_pos μ h hl hlm
  have hfactorint := integrable_escape_factor μ hl hY
  have hbb := integrable_Bw (μ := μ) (l := l) hl hY b
  have hdecomp : (fun y => Bw l (speedValueProv μ l) y) =
      fun y => Bw l b y + (b - speedValueProv μ l) * ((1 - y) * (1 - l * y)) := by
    funext y
    unfold Bw
    ring
  have hBv : 0 < ∫ y, Bw l (speedValueProv μ l) y ∂Ylaw μ l := by
    rw [hdecomp, integral_add hbb (hfactorint.const_mul (b - speedValueProv μ l)),
      integral_const_mul]
    have hp : 0 < (b - speedValueProv μ l) *
        ∫ y, (1 - y) * (1 - l * y) ∂Ylaw μ l :=
      mul_pos (sub_pos.mpr hspeed') hfactorpos
    linarith [hcoeff]
  have hscale : (fun y => fθ l (rr μ l) 0 y) =
      fun y => (l - 1)⁻¹ * Bw l (speedValueProv μ l) y := by
    funext y
    simp only [fθ, Bw, rr, zero_mul, sub_zero]
    field_simp [ne_of_gt (show l - 1 > 0 by linarith)]
    <;> ring
  rw [hscale, integral_const_mul]
  exact mul_pos (inv_pos.mpr (by linarith)) hBv

private lemma integrable_f0_mul_rank {l r : ℝ} [IsProbabilityMeasure (Ylaw μ l)] (hl : 1 < l) (j : ℕ)
    (hY : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l)) :
    Integrable (fun y => (kS l * y) ^ j * fθ l r 0 y) (Ylaw μ l) := by
  apply integrable_bounded_ae
    (((measurable_const.mul measurable_id).pow_const j).mul (measurable_f0 l r)).aemeasurable
    (C := (kS l) ^ j * (1 + |r|))
  filter_upwards [hY] with y hy
  obtain ⟨hy0, hy1, hg0, hg1⟩ := y_factor_bounds hl hy
  have hk : 0 ≤ kS l := by
    dsimp [kS]
    positivity
  have hpow : 0 ≤ (kS l * y) ^ j := pow_nonneg (mul_nonneg hk hy0) j
  have hpow_le : (kS l * y) ^ j ≤ (kS l) ^ j := by
    apply pow_le_pow_left₀ (mul_nonneg hk hy0)
    simpa using mul_le_mul_of_nonneg_left hy1 hk
  have hf : ‖fθ l r 0 y‖ ≤ 1 + |r| := by
    rw [Real.norm_eq_abs, f0_shape]
    calc
      |y - r * ((1 - y) * (1 - l * y))| ≤
          |y| + |r * ((1 - y) * (1 - l * y))| := abs_sub _ _
      _ = |y| + |r| * |(1 - y) * (1 - l * y)| := by rw [abs_mul]
      _ ≤ 1 + |r| := by
        have hyabs : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
        have hgabs : |(1 - y) * (1 - l * y)| ≤ 1 := by
          rw [abs_of_nonneg hg0]
          exact hg1
        nlinarith [abs_nonneg r]
  change ‖(kS l * y) ^ j * fθ l r 0 y‖ ≤ (kS l) ^ j * (1 + |r|)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow]
  have hfabs : |fθ l r 0 y| ≤ 1 + |r| := by
    simpa [Real.norm_eq_abs] using hf
  exact mul_le_mul hpow_le hfabs (abs_nonneg _) (by positivity : 0 ≤ (kS l) ^ j)

private lemma integrable_rankPower {l : ℝ} [IsProbabilityMeasure (Ylaw μ l)]
    (hl : 1 < l) (hY : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l)) (j : ℕ) :
    Integrable (fun y => (kS l * y) ^ j) (Ylaw μ l) := by
  apply integrable_bounded_ae
    (((measurable_const.mul measurable_id).pow_const j).aemeasurable) (C := (kS l) ^ j)
  filter_upwards [hY] with y hy
  obtain ⟨hy0, hy1, _, _⟩ := y_factor_bounds hl hy
  have hk : 0 ≤ kS l := by
    dsimp [kS]
    positivity
  have hpow : 0 ≤ (kS l * y) ^ j := pow_nonneg (mul_nonneg hk hy0) j
  have hky : kS l * y ≤ kS l := by
    calc
      kS l * y ≤ kS l * 1 := mul_le_mul_of_nonneg_left hy1 hk
      _ = kS l := by ring
  have hle : (kS l * y) ^ j ≤ (kS l) ^ j :=
    pow_le_pow_left₀ (mul_nonneg hk hy0) hky j
  change ‖(kS l * y) ^ j‖ ≤ (kS l) ^ j
  rw [Real.norm_of_nonneg hpow]
  exact hle

private lemma rankPower_monoOn {l : ℝ} (hl : 1 < l) (j : ℕ) :
    MonotoneOn (fun y => (kS l * y) ^ j) (Set.Icc 0 (1 / l)) := by
  intro x hx y hy hxy
  have hk : 0 ≤ kS l := by
    dsimp [kS]
    positivity
  have hmul : kS l * x ≤ kS l * y := mul_le_mul_of_nonneg_left hxy hk
  exact pow_le_pow_left₀ (mul_nonneg hk hx.1) hmul j

private lemma rankPower_integral_pos {h : OffspringHyp μ} {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (j : ℕ) :
    0 < ∫ y, (kS l * y) ^ j ∂Ylaw μ l := by
  letI : IsProbabilityMeasure (Ylaw μ l) := yLaw_probability μ l
  have hYo := yLaw_Ioo μ h hl hlm
  have hi := integrable_rankPower μ hl (yLaw_Icc μ h hl hlm) j
  apply integral_pos_of_ae_pos hi
  filter_upwards [hYo] with y hy
  have hk : 0 < kS l := by
    dsimp [kS]
    exact Real.sqrt_pos.2 (by linarith)
  exact pow_pos (mul_pos hk hy.1) j

/-- At zero the averaged gradient is the mean of `f₀(Y)`. The hypotheses
`OffspringHyp μ` and `l < mean μ` are not used; the identity follows
algebraically for every `l > 1`. -/
theorem Gam_zero_eq (_h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (_hlm : l < mean μ) :
    Gam μ l 0 = ∫ T, fθ l (rr μ l) 0 (Yt l T) ∂GW μ := by
  letI : IsProbabilityMeasure (Ylaw μ l) := yLaw_probability μ l
  have h0 : (0 : ℝ) ∈ Set.Icc 0 1 := by simp
  calc
    Gam μ l 0 = ∫ y, fθ l (rr μ l) 0 y * gammaWeight l 0 y ∂Ylaw μ l :=
      Gam_eq_Ylaw μ hl h0
    _ = ∫ y, fθ l (rr μ l) 0 y ∂Ylaw μ l := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        have ha : l - 1 ≠ 0 := ne_of_gt (by linarith)
        simp [gammaWeight, ha]
    _ = ∫ T, fθ l (rr μ l) 0 (Yt l T) ∂GW μ :=
      integrable_Ylaw_comp μ l _ (measurable_f0 l (rr μ l)).aestronglyMeasurable

/-- The averaged gradient is positive and bounded above by the transformed mean. -/
theorem Gam_pos_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    0 < Gam μ l t ∧ Gam μ l t ≤ muY μ l := by
  letI : IsProbabilityMeasure (Ylaw μ l) := yLaw_probability μ l
  have hY := yLaw_Icc μ h hl hlm
  have hr : 0 < rr μ l := by
    exact rr_pos μ h hl hlm
  have hfmean := f0_integral_pos μ h hl hlm
  have hfint := f0_integrable (μ := μ) (l := l) (r := rr μ l) hl hY
  have hwint := integrable_gammaWeight (μ := μ) hl ht hY
  have hprodint := integrable_f0_mul_weight (μ := μ) (l := l) (r := rr μ l) hl ht hY
  have hWpos : 0 < ∫ y, gammaWeight l t y ∂Ylaw μ l := by
    apply integral_pos_of_ae_pos hwint
    filter_upwards [hY] with y hy
    exact gammaWeight_pos hl ht hy
  have hfmono := f0_monoOn (l := l) (r := rr μ l) hl hr.le
  have hwmono := gammaWeight_monoOn (l := l) hl ht
  have hcov := integral_mul_ge_of_monotone (P := Ylaw μ l) (Z := fun y : ℝ => y)
    (Set.Icc 0 (1 / l)) hY hfmono hwmono hfint hwint hprodint
  have hGpos : 0 < ∫ y, fθ l (rr μ l) 0 y * gammaWeight l t y ∂Ylaw μ l := by
    have hmul : 0 < (∫ y, fθ l (rr μ l) 0 y ∂Ylaw μ l) *
        ∫ y, gammaWeight l t y ∂Ylaw μ l := mul_pos hfmean hWpos
    exact hmul.trans_le (by simpa using hcov)
  have hYint : Integrable (fun y : ℝ => y) (Ylaw μ l) :=
    integrable_bounded_ae measurable_id.aemeasurable (C := 1) (by
      filter_upwards [hY] with y hy
      obtain ⟨hy0, hy1, _, _⟩ := y_factor_bounds hl hy
      rw [Real.norm_eq_abs, abs_of_nonneg hy0]
      exact hy1)
  have hupper : ∫ y, fθ l (rr μ l) 0 y * gammaWeight l t y ∂Ylaw μ l ≤
      ∫ y, y ∂Ylaw μ l := by
    apply integral_mono_ae hprodint hYint
    filter_upwards [hY] with y hy
    obtain ⟨hw0, hw1⟩ := gammaWeight_bounds hl ht hy
    have hfy := f0_le_id hl hy hr.le
    have hdiff : y - fθ l (rr μ l) 0 y * gammaWeight l t y =
        (1 - gammaWeight l t y) * y +
          gammaWeight l t y * (y - fθ l (rr μ l) 0 y) := by ring
    rw [← sub_nonneg]
    rw [hdiff]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hw1) hy.1)
      (mul_nonneg hw0 (sub_nonneg.mpr hfy))
  constructor
  · rw [Gam_eq_Ylaw μ hl ht]
    exact hGpos
  · rw [Gam_eq_Ylaw μ hl ht, ← yLaw_mean μ l]
    exact hupper

/-- Every transformed rank moment of `f₀` is strictly positive. -/
theorem f0_rank_pos (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (j : ℕ) :
    0 < ∫ T, (kS l * Yt l T) ^ j * fθ l (rr μ l) 0 (Yt l T) ∂GW μ := by
  letI : IsProbabilityMeasure (Ylaw μ l) := yLaw_probability μ l
  have hY := yLaw_Icc μ h hl hlm
  have hfmean := f0_integral_pos μ h hl hlm
  have hfint := f0_integrable (μ := μ) (l := l) (r := rr μ l) hl hY
  have hrankint := integrable_rankPower μ hl hY j
  have hprodint := integrable_f0_mul_rank (μ := μ) (l := l) (r := rr μ l) hl j hY
  have hrankpos := rankPower_integral_pos (μ := μ) (h := h) hl hlm j
  have hmono := f0_monoOn (l := l) (r := rr μ l) hl (rr_pos μ h hl hlm).le
  have hpowmono := rankPower_monoOn (l := l) hl j
  have hcov := integral_mul_ge_of_monotone (P := Ylaw μ l) (Z := fun y : ℝ => y)
    (Set.Icc 0 (1 / l)) hY hpowmono hmono hrankint hfint hprodint
  have hpos : 0 < ∫ y, (kS l * y) ^ j * fθ l (rr μ l) 0 y ∂Ylaw μ l := by
    have hp : 0 < (∫ y, (kS l * y) ^ j ∂Ylaw μ l) *
        ∫ y, fθ l (rr μ l) 0 y ∂Ylaw μ l := mul_pos hrankpos hfmean
    exact hp.trans_le (by simpa using hcov)
  have hmap := integrable_Ylaw_comp μ l
    (fun y => (kS l * y) ^ j * fθ l (rr μ l) 0 y)
    ((((measurable_const.mul measurable_id).pow_const j).mul
      (measurable_f0 l (rr μ l))).aestronglyMeasurable)
  rw [← hmap]
  exact hpos

end LPPMonotonicityProof.Analytic
