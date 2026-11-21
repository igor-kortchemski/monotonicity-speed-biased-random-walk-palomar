module

public import LPPMonotonicityProof.Analytic.Ceiling2
public import LPPMonotonicityProof.Analytic.Tools
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The single-crossing lemma

This module proves the second part of Lemma 3.4 (`lem:single-crossing`): the quadratic
crossing of `f_θ`, the transformed `Gam - θ Gam2` identity, and its sign for
admissible `θ`. The generic first part is `single_crossing` in `Analytic/Tools.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

private lemma fθ_eq_quadratic (l r θ y : ℝ) :
    fθ l r θ y = -(θ + r * l) * y ^ 2 + (1 + r * (1 + l)) * y - r := by
  unfold fθ
  ring

/-- **Lemma 3.4, quadratic part.**  The residual has a crossing on `[0, 1/l]`.
In the convex case it is strictly increasing there; in the concave case the
secant identities rule out any further change of sign. -/
theorem fθ_single_crossing {l r θ : ℝ} (hl : 1 < l) (hr : 0 < r) (hθ : θ ≤ 1) :
    ∃ c ∈ Set.Ioo 0 (1 / l),
      (∀ y ∈ Set.Icc 0 (1 / l), y < c → fθ l r θ y ≤ 0) ∧
      (∀ y ∈ Set.Icc 0 (1 / l), c < y → 0 ≤ fθ l r θ y) := by
  have hl0 : 0 < l := by linarith
  have hu : 0 < 1 / l := one_div_pos.mpr hl0
  let A : ℝ := θ + r * l
  let B : ℝ := 1 + r * (1 + l)
  have hB : 0 < B := by dsimp [B]; positivity
  have hf (y : ℝ) : fθ l r θ y = -A * y ^ 2 + B * y - r := by
    simpa [A, B] using fθ_eq_quadratic l r θ y
  have hf0 : fθ l r θ 0 = -r := by simp [fθ]
  have hfu : fθ l r θ (1 / l) = (l - θ) / l ^ 2 := by
    rw [hf]
    field_simp
    ring
  have hfu_pos : 0 < fθ l r θ (1 / l) := by
    rw [hfu]
    exact div_pos (by linarith) (sq_pos_of_pos hl0)
  have hcont : Continuous (fun y => fθ l r θ y) := by
    unfold fθ
    fun_prop
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hu.le hcont.continuousOn
    (show 0 ∈ Set.Icc (fθ l r θ 0) (fθ l r θ (1 / l)) by
      rw [hf0]
      exact ⟨by linarith, hfu_pos.le⟩)
  change fθ l r θ c = 0 at hfc
  have hc0 : 0 < c := by
    rcases hc.1.eq_or_lt with heq | hlt
    · exfalso
      rw [← heq, hf0] at hfc
      linarith
    · exact hlt
  have hcu : c < 1 / l := by
    rcases hc.2.eq_or_lt with heq | hlt
    · exfalso
      rw [heq] at hfc
      linarith
    · exact hlt
  refine ⟨c, ⟨hc0, hcu⟩, ?_, ?_⟩
  · intro y hy hyc
    have hy0 : 0 ≤ y := hy.1
    by_cases hA : 0 < A
    · by_contra hnonpos
      have hfy : 0 < fθ l r θ y := lt_of_not_ge hnonpos
      have hid : (1 / l - y) * fθ l r θ c =
          (1 / l - c) * fθ l r θ y + (c - y) * fθ l r θ (1 / l) +
            A * (c - y) * (1 / l - c) * (1 / l - y) := by
        rw [hf, hf, hf]
        ring
      rw [hfc] at hid
      have hp1 : 0 < (1 / l - c) * fθ l r θ y := mul_pos (by linarith) hfy
      have hp2 : 0 < (c - y) * fθ l r θ (1 / l) := mul_pos (by linarith) hfu_pos
      have hp3 : 0 ≤ A * (c - y) * (1 / l - c) * (1 / l - y) :=
        mul_nonneg (mul_nonneg (mul_nonneg hA.le (by linarith)) (by linarith)) (by linarith)
      nlinarith
    · have hA0 : A ≤ 0 := le_of_not_gt hA
      have hfac : 0 < B - A * (c + y) := by
        have : 0 ≤ -A * (c + y) :=
          mul_nonneg (neg_nonneg.mpr hA0) (by linarith)
        dsimp [B] at hB ⊢
        nlinarith
      have hid : fθ l r θ c - fθ l r θ y =
          (c - y) * (B - A * (c + y)) := by
        rw [hf, hf]
        ring
      rw [hfc] at hid
      have := mul_pos (sub_pos.mpr hyc) hfac
      nlinarith
  · intro y hy hcy
    have hy0 : 0 ≤ y := hy.1
    by_cases hA : 0 < A
    · have hid : (1 / l - c) * fθ l r θ y =
          (1 / l - y) * fθ l r θ c + (y - c) * fθ l r θ (1 / l) +
            A * (y - c) * (1 / l - y) * (1 / l - c) := by
        rw [hf, hf, hf]
        ring
      rw [hfc] at hid
      have hp1 : 0 ≤ (y - c) * fθ l r θ (1 / l) :=
        mul_nonneg (by linarith) hfu_pos.le
      have hp2 : 0 ≤ A * (y - c) * (1 / l - y) * (1 / l - c) :=
        mul_nonneg (mul_nonneg (mul_nonneg hA.le (by linarith)) (by linarith [hy.2])) (by linarith)
      have hleft : 0 ≤ (1 / l - c) * fθ l r θ y := by nlinarith
      exact nonneg_of_mul_nonneg_right hleft (by linarith)
    · have hA0 : A ≤ 0 := le_of_not_gt hA
      have hfac : 0 < B - A * (y + c) := by
        have : 0 ≤ -A * (y + c) :=
          mul_nonneg (neg_nonneg.mpr hA0) (by linarith)
        dsimp [B] at hB ⊢
        nlinarith
      have hid : fθ l r θ y - fθ l r θ c =
          (y - c) * (B - A * (y + c)) := by
        rw [hf, hf]
        ring
      rw [hfc] at hid
      have := mul_pos (sub_pos.mpr hcy) hfac
      nlinarith


private lemma DfunProv_lower_sc {l b β : ℝ} (_hl : 1 < l)
    (hb : 0 ≤ b) (hβ : β ∈ Set.Icc 0 1) :
    l - 1 ≤ DfunProv l b β := by
  have hrest : 0 ≤ b * (1 - β) + β :=
    add_nonneg (mul_nonneg hb (sub_nonneg.mpr hβ.2)) hβ.1
  unfold DfunProv
  nlinarith

private lemma transformed_kernel_identity_sc {l b β v θ : ℝ} (hl : 1 < l)
    (hb : b ∈ Set.Icc 0 1) (hβ : β ∈ Set.Ioo 0 1) :
    (Pol l v β - θ * β ^ 2) / DfunProv l b β ^ 2 =
      (1 - b / (l - 1 + b)) ^ 2 *
        (fθ l (v / (l - 1)) θ (β / (l - 1 + β)) /
          (1 - l * (b / (l - 1 + b)) * (β / (l - 1 + β))) ^ 2) := by
  have ha : 0 < l - 1 := by linarith
  have hdenb : 0 < l - 1 + b := by linarith [hb.1]
  have hdenβ : 0 < l - 1 + β := by linarith [hβ.1]
  have hD : 0 < DfunProv l b β :=
    lt_of_lt_of_le ha (DfunProv_lower_sc hl hb.1 ⟨hβ.1.le, hβ.2.le⟩)
  have hq : b / (l - 1 + b) ≤ 1 / l := by
    rw [div_le_div_iff₀ hdenb (by linarith : 0 < l)]
    nlinarith [hb.2]
  have hy : β / (l - 1 + β) < 1 / l := by
    rw [div_lt_div_iff₀ hdenβ (by linarith : 0 < l)]
    nlinarith [hβ.2]
  have hq0 : 0 ≤ b / (l - 1 + b) := div_nonneg hb.1 hdenb.le
  have hy0 : 0 ≤ β / (l - 1 + β) := div_nonneg hβ.1.le hdenβ.le
  have hprod : l * (b / (l - 1 + b)) * (β / (l - 1 + β)) < 1 := by
    have hmul : (b / (l - 1 + b)) * (β / (l - 1 + β)) < (1 / l) * (1 / l) :=
      mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hq hy hy0 (by positivity)
    calc
      l * (b / (l - 1 + b)) * (β / (l - 1 + β)) =
          l * ((b / (l - 1 + b)) * (β / (l - 1 + β))) := by ring
      _ < l * ((1 / l) * (1 / l)) := mul_lt_mul_of_pos_left hmul (by linarith)
      _ = 1 / l := by field_simp
      _ < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hH : 0 < 1 - l * (b / (l - 1 + b)) * (β / (l - 1 + β)) := by
    linarith
  have hHid : 1 - l * (b / (l - 1 + b)) * (β / (l - 1 + β)) =
      (l - 1) * DfunProv l b β / ((l - 1 + b) * (l - 1 + β)) := by
    unfold DfunProv
    field_simp [ha.ne', hdenb.ne', hdenβ.ne']
    ring
  have hfid : fθ l (v / (l - 1)) θ (β / (l - 1 + β)) =
      (Pol l v β - θ * β ^ 2) / (l - 1 + β) ^ 2 := by
    unfold Pol fθ
    field_simp [ha.ne', hdenβ.ne']
    ring
  have h1q : (1 - b / (l - 1 + b)) ^ 2 = (l - 1) ^ 2 / (l - 1 + b) ^ 2 := by
    field_simp [ha.ne', hdenb.ne']
    ring
  rw [hfid, h1q, hHid]
  field_simp [ha.ne', hdenb.ne', hdenβ.ne', hD.ne']

private lemma norm_Pol_le_sc {l v β : ℝ} (hl : 1 < l) (hβ : β ∈ Set.Icc 0 1) :
    ‖Pol l v β‖ ≤ 1 + (l - 1) * (1 + |v|) + (l - 1) * |v| := by
  have ha : 0 ≤ l - 1 := by linarith
  have hβabs : |β| ≤ 1 := by simpa [abs_of_nonneg hβ.1] using hβ.2
  have hv : |1 + v| ≤ 1 + |v| := by simpa using abs_add_le (1 : ℝ) v
  rw [Real.norm_eq_abs]
  calc
    |Pol l v β| = |β ^ 2 + (l - 1) * (1 + v) * β - (l - 1) * v| := by
      rw [show Pol l v β = β ^ 2 + (l - 1) * (1 + v) * β - (l - 1) * v by
        unfold Pol
        ring]
    _ ≤ |β ^ 2| + |(l - 1) * (1 + v) * β| + |(l - 1) * v| := by
      exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ 1 + (l - 1) * (1 + |v|) + (l - 1) * |v| := by
      simp only [abs_mul, abs_pow, abs_of_nonneg ha]
      have hβsq : |β| ^ 2 ≤ 1 := by nlinarith [abs_nonneg β]
      have hmid : (l - 1) * |1 + v| * |β| ≤ (l - 1) * (1 + |v|) := by
        calc
          (l - 1) * |1 + v| * |β| ≤ (l - 1) * (1 + |v|) * |β| := by gcongr
          _ ≤ (l - 1) * (1 + |v|) * 1 := by gcongr
          _ = (l - 1) * (1 + |v|) := by ring
      nlinarith

private lemma integrable_gam_sc (h : OffspringHyp μ) {l b v : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (hb : b ∈ Set.Icc 0 1) :
    Integrable (fun T => Pol l v (escape l T) / DfunProv l b (escape l T) ^ 2) (GW μ) := by
  have ha : 0 < l - 1 := by linarith
  let K : ℝ := 1 + (l - 1) * (1 + |v|) + (l - 1) * |v|
  apply Integrable.of_bound (((by fun_prop : Measurable (fun x : ℝ =>
    (x ^ 2 + (l - 1) * (1 + v) * x - (l - 1) * v) /
      (l - 1 + b + x - b * x) ^ 2)).comp (measurable_escape l)).aestronglyMeasurable)
    (K / (l - 1) ^ 2)
  filter_upwards [ae_escape_mem_Ioo h (by linarith) hlm] with T hT
  have hβ : escape l T ∈ Set.Icc 0 1 := ⟨hT.1.le, hT.2.le⟩
  have hD : 0 < DfunProv l b (escape l T) :=
    lt_of_lt_of_le ha (DfunProv_lower_sc hl hb.1 hβ)
  have hDs : (l - 1) ^ 2 ≤ DfunProv l b (escape l T) ^ 2 :=
    (sq_le_sq₀ ha.le hD.le).2 (DfunProv_lower_sc hl hb.1 hβ)
  have hK : ‖Pol l v (escape l T)‖ ≤ K := norm_Pol_le_sc hl hβ
  change ‖Pol l v (escape l T) / DfunProv l b (escape l T) ^ 2‖ ≤ K / (l - 1) ^ 2
  simp only [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hD]
  rw [div_le_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos ha)]
  exact mul_le_mul hK hDs (sq_nonneg _) (by positivity)

private lemma integrable_gam2_sc (h : OffspringHyp μ) {l b : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (hb : b ∈ Set.Icc 0 1) :
    Integrable (fun T => escape l T ^ 2 / DfunProv l b (escape l T) ^ 2) (GW μ) := by
  have ha : 0 < l - 1 := by linarith
  apply Integrable.of_bound (((by fun_prop : Measurable (fun x : ℝ =>
    x ^ 2 / (l - 1 + b + x - b * x) ^ 2)).comp
      (measurable_escape l)).aestronglyMeasurable) (1 / (l - 1) ^ 2)
  filter_upwards [ae_escape_mem_Ioo h (by linarith) hlm] with T hT
  have hβ : escape l T ∈ Set.Icc 0 1 := ⟨hT.1.le, hT.2.le⟩
  have hD : 0 < DfunProv l b (escape l T) :=
    lt_of_lt_of_le ha (DfunProv_lower_sc hl hb.1 hβ)
  have hDs : (l - 1) ^ 2 ≤ DfunProv l b (escape l T) ^ 2 :=
    (sq_le_sq₀ ha.le hD.le).2 (DfunProv_lower_sc hl hb.1 hβ)
  have hnum : ‖escape l T ^ 2‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_nonneg hβ.1 (sub_nonneg.mpr hβ.2)]
  change ‖escape l T ^ 2 / DfunProv l b (escape l T) ^ 2‖ ≤ 1 / (l - 1) ^ 2
  simp only [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hD]
  rw [div_le_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos ha)]
  simpa using mul_le_mul hnum hDs (sq_nonneg _) (by positivity)

/-- **Lemma 3.4, identity.** `Γ(t) - θΓ₂(t) = (1-y_t)² E[f_θ(Y)/(1-λy_tY)²]`. -/
theorem Gam_sub_Gam2 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {b : ℝ} (hb : b ∈ Set.Icc 0 1) (θ : ℝ) :
    Gam μ l b - θ * Gam2 μ l b = (1 - b / (l - 1 + b)) ^ 2 *
      ∫ T, fθ l (rr μ l) θ (Yt l T) /
        (1 - l * (b / (l - 1 + b)) * Yt l T) ^ 2 ∂GW μ := by
  have hgi := integrable_gam_sc μ h hl hlm hb (v := speedValueProv μ l)
  have hg2i := integrable_gam2_sc μ h hl hlm hb
  rw [Gam, Gam2, ← integral_const_mul, ← integral_sub hgi (hg2i.const_mul θ),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_escape_mem_Ioo h (by linarith) hlm] with T hT
  have hid := transformed_kernel_identity_sc (v := speedValueProv μ l)
    (θ := θ) hl hb hT
  rw [show Pol l (speedValueProv μ l) (escape l T) / DfunProv l b (escape l T) ^ 2 -
      θ * (escape l T ^ 2 / DfunProv l b (escape l T) ^ 2) =
      (Pol l (speedValueProv μ l) (escape l T) - θ * escape l T ^ 2) /
        DfunProv l b (escape l T) ^ 2 by ring]
  rw [hid]
  simp only [rr, Yt]


private lemma yb_mem_sc {l b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Icc 0 1) :
    b / (l - 1 + b) ∈ Set.Icc 0 (1 / l) := by
  have ha : 0 < l - 1 := by linarith
  have hden : 0 < l - 1 + b := by linarith [hb.1]
  constructor
  · exact div_nonneg hb.1 hden.le
  · rw [div_le_div_iff₀ hden (by linarith : 0 < l)]
    nlinarith [hb.2]

private lemma weight_denom_pos_sc {l b y : ℝ} (hl : 1 < l)
    (hb : b ∈ Set.Icc 0 1) (hy : y ∈ Set.Ioo 0 (1 / l)) :
    0 < 1 - l * (b / (l - 1 + b)) * y := by
  have hl0 : 0 < l := by linarith
  have hq := yb_mem_sc hl hb
  have hmul : (b / (l - 1 + b)) * y < (1 / l) * (1 / l) :=
    mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hq.2 hy.2 hy.1.le (one_div_pos.mpr hl0)
  have hprod : l * (b / (l - 1 + b)) * y < 1 := by
    calc
      l * (b / (l - 1 + b)) * y = l * ((b / (l - 1 + b)) * y) := by ring
      _ < l * ((1 / l) * (1 / l)) := mul_lt_mul_of_pos_left hmul hl0
      _ = 1 / l := by field_simp
      _ < 1 := (div_lt_one hl0).2 hl
  linarith

private lemma weight_mono_sc {l b c : ℝ} (hl : 1 < l)
    (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Ioo 0 (1 / l)) :
    MonotoneOn (fun y => 1 / (1 - l * (b / (l - 1 + b)) * y) ^ 2)
      (Set.Ioo 0 (1 / l) ∪ {c}) := by
  have hs : Set.Ioo 0 (1 / l) ∪ {c} ⊆ Set.Ioo 0 (1 / l) :=
    Set.union_subset (fun _ hy => hy) (Set.singleton_subset_iff.mpr hc)
  intro x hx y hy hxy
  have hx' := hs hx
  have hy' := hs hy
  have hq0 := (yb_mem_sc hl hb).1
  have hHx := weight_denom_pos_sc hl hb hx'
  have hHy := weight_denom_pos_sc hl hb hy'
  have hden : 1 - l * (b / (l - 1 + b)) * y ≤
      1 - l * (b / (l - 1 + b)) * x := by
    have hmul := mul_le_mul_of_nonneg_left hxy
      (mul_nonneg (by linarith : 0 ≤ l) hq0)
    nlinarith
  exact one_div_le_one_div_of_le (sq_pos_of_pos hHy)
    (pow_le_pow_left₀ hHy.le hden 2)

private lemma integrable_weighted_sc (h : OffspringHyp μ) {l b : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (hb : b ∈ Set.Icc 0 1) (θ : ℝ) :
    Integrable (fun T => fθ l (rr μ l) θ (Yt l T) /
      (1 - l * (b / (l - 1 + b)) * Yt l T) ^ 2) (GW μ) := by
  have hgi := integrable_gam_sc μ h hl hlm hb (v := speedValueProv μ l)
  have hg2i := integrable_gam2_sc μ h hl hlm hb
  have hbase : Integrable (fun T =>
      (Pol l (speedValueProv μ l) (escape l T) - θ * escape l T ^ 2) /
        DfunProv l b (escape l T) ^ 2) (GW μ) := by
    have heq : (fun T =>
        (Pol l (speedValueProv μ l) (escape l T) - θ * escape l T ^ 2) /
          DfunProv l b (escape l T) ^ 2) = (fun T =>
        Pol l (speedValueProv μ l) (escape l T) / DfunProv l b (escape l T) ^ 2 -
          θ * (escape l T ^ 2 / DfunProv l b (escape l T) ^ 2)) := by
      funext T
      ring
    rw [heq]
    exact hgi.sub (hg2i.const_mul θ)
  have ha : 0 < l - 1 := by linarith
  have hden : 0 < l - 1 + b := by linarith [hb.1]
  have hK : 0 < 1 - b / (l - 1 + b) := by
    rw [sub_pos, div_lt_one hden]
    linarith
  have hscaled := hbase.const_mul ((1 - b / (l - 1 + b)) ^ 2)⁻¹
  apply hscaled.congr
  filter_upwards [ae_escape_mem_Ioo h (by linarith) hlm] with T hT
  have hid := transformed_kernel_identity_sc (v := speedValueProv μ l)
    (θ := θ) hl hb hT
  let K : ℝ := (1 - b / (l - 1 + b)) ^ 2
  have hK0 : K ≠ 0 := pow_ne_zero _ hK.ne'
  symm
  change fθ l (speedValueProv μ l / (l - 1)) θ
      (escape l T / (l - 1 + escape l T)) /
      (1 - l * (b / (l - 1 + b)) * (escape l T / (l - 1 + escape l T))) ^ 2 =
    K⁻¹ * ((Pol l (speedValueProv μ l) (escape l T) - θ * escape l T ^ 2) /
      DfunProv l b (escape l T) ^ 2)
  calc
    _ = K⁻¹ * (K * (fθ l (speedValueProv μ l / (l - 1)) θ
        (escape l T / (l - 1 + escape l T)) /
        (1 - l * (b / (l - 1 + b)) *
          (escape l T / (l - 1 + escape l T))) ^ 2)) := by field_simp
    _ = _ := by
      dsimp [K]
      rw [← hid]


/-- **Lemma 3.4, sign for every admissible parameter.** -/
theorem Gam_sub_Gam2_nonneg (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {θ : ℝ} (hθ : Admissible μ l θ) {b : ℝ}
    (hb : b ∈ Set.Icc 0 1) : 0 ≤ Gam μ l b - θ * Gam2 μ l b := by
  letI : IsProbabilityMeasure (Ylaw μ l) := by
    unfold Ylaw
    infer_instance
  obtain ⟨c, hc, hneg, hpos⟩ :=
    fθ_single_crossing hl (rr_pos μ h hl hlm) hθ.1
  let g : ℝ → ℝ := fun y => fθ l (rr μ l) θ y
  let w : ℝ → ℝ := fun y => 1 / (1 - l * (b / (l - 1 + b)) * y) ^ 2
  have hY : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Ioo 0 (1 / l) := ae_Ylaw_mem μ h hl hlm
  have hgGW : Integrable (fun T => fθ l (rr μ l) θ (Yt l T)) (GW μ) := by
    simpa using integrable_weighted_sc μ h hl hlm (Set.left_mem_Icc.mpr zero_le_one) θ
  have hwgGW : Integrable (fun T => fθ l (rr μ l) θ (Yt l T) /
      (1 - l * (b / (l - 1 + b)) * Yt l T) ^ 2) (GW μ) :=
    integrable_weighted_sc μ h hl hlm hb θ
  have hgmeas : Measurable g := by
    dsimp [g]
    unfold fθ
    fun_prop
  have hwgmeas : Measurable (g * w) := by
    dsimp [g, w]
    unfold fθ
    fun_prop
  have hg : Integrable g (Ylaw μ l) := by
    unfold Ylaw
    apply (integrable_map_measure hgmeas.aestronglyMeasurable
      (measurable_Yt l).aemeasurable).2
    simpa only [Function.comp_def, g] using hgGW
  have hwg : Integrable (g * w) (Ylaw μ l) := by
    unfold Ylaw
    apply (integrable_map_measure hwgmeas.aestronglyMeasurable
      (measurable_Yt l).aemeasurable).2
    simpa only [Function.comp_def, Pi.mul_apply, g, w, div_eq_mul_inv, one_mul] using hwgGW
  have hcross : w c * ∫ y, g y ∂Ylaw μ l ≤ ∫ y, g y * w y ∂Ylaw μ l :=
    single_crossing hY
      (fun y hy hyc => hneg y ⟨hy.1.le, hy.2.le⟩ hyc)
      (fun y hy hcy => hpos y ⟨hy.1.le, hy.2.le⟩ hcy)
      (by simpa only [w] using weight_mono_sc hl hb hc) (Set.mem_union_right _ (Set.mem_singleton c))
      hg hwg
  have hwc : 0 < w c := by
    dsimp [w]
    exact one_div_pos.mpr (sq_pos_of_pos (weight_denom_pos_sc hl hb hc))
  have hmean : 0 ≤ ∫ y, g y ∂Ylaw μ l := by
    unfold Ylaw
    rw [integral_map (measurable_Yt l).aemeasurable hgmeas.aestronglyMeasurable]
    exact hθ.2
  have hInt : 0 ≤ ∫ y, g y * w y ∂Ylaw μ l :=
    (mul_nonneg hwc.le hmean).trans hcross
  have hmap : (∫ y, g y * w y ∂Ylaw μ l) =
      ∫ T, fθ l (rr μ l) θ (Yt l T) /
        (1 - l * (b / (l - 1 + b)) * Yt l T) ^ 2 ∂GW μ := by
    unfold Ylaw
    change (∫ y, (g * w) y ∂(GW μ).map (Yt l)) = _
    rw [integral_map (measurable_Yt l).aemeasurable hwgmeas.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with T
    simp only [Pi.mul_apply, g, w]
    ring
  rw [hmap] at hInt
  rw [Gam_sub_Gam2 μ h hl hlm hb θ]
  exact mul_nonneg (sq_nonneg _) hInt

end LPPMonotonicityProof.Analytic
