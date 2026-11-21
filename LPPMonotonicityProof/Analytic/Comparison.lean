module

public import LPPMonotonicityProof.Analytic.Defs
public import LPPMonotonicityProof.Speed.Signed.TwoCopyBounds
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Transformed escapes above bias one

This module proves the transformed-escape identities of Proposition 3.1
(`prop:collapse`), including the additive odds (3.1) (`eq:additive-odds`), and
their basic integral consequences: `0 < Y < 1/λ` almost surely, `E Y ≤ Z ≤ 2 E Y`,
`0 < p_eff < 1`, `R₀ = E Y - λ E Y² > 0` and `r = v/a > 0`.  It uses the analytic
interface definitions and the signed two-copy definitions; the `rr` statement uses
`speedValueProv` of `LPPMonotonicityProof.Analytic.Defs`, which is definitionally
`Speed.speedValue` (`speedValue_eq_speedValueProv` in
`LPPMonotonicityProof.Analytic.Critical`).
-/

@[expose] public section

namespace LPPMonotonicityProof.Analytic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

private theorem Yt_nonneg {l : ℝ} (hl : 1 < l) (T : Tree) : 0 ≤ Yt l T := by
  have hl0 : 0 < l := by linarith
  exact div_nonneg (escape_mem_Icc hl0 T).1
    (add_nonneg (by linarith) (escape_mem_Icc hl0 T).1)

private theorem Yt_lt_inv {l : ℝ} (hl : 1 < l) (T : Tree) : Yt l T < 1 / l := by
  have hl0 : 0 < l := by linarith
  have hden : 0 < l - 1 + escape l T := by
    have := (escape_mem_Icc hl0 T).1
    positivity
  rw [Yt, div_lt_div_iff₀ hden hl0]
  have hβ := escape_lt_one hl0 T
  nlinarith

/-- Equation (3.1) (`eq:additive-odds`): additive odds in the transformed escape
variable. -/
theorem additive_odds {l : ℝ} (hl : 1 < l) (T : Tree) :
    l * Yt l T / (1 - l * Yt l T) =
      ∑ i : Fin (degree T), Yt l (child T (i + 1)) / (1 - Yt l (child T (i + 1))) := by
  have hl0 : 0 < l := by linarith
  have ha : 0 < l - 1 := by linarith
  have hS : 0 ≤ childSum l T := by
    exact Finset.sum_nonneg fun i _ => (escape_mem_Icc hl0 _).1
  have hroot : l * Yt l T / (1 - l * Yt l T) = childSum l T / (l - 1) := by
    have h₁ : l + childSum l T ≠ 0 := by positivity
    have h₂ : l - 1 + childSum l T / (l + childSum l T) ≠ 0 := by positivity
    have h₃ : l - 1 + childSum l T ≠ 0 := by positivity
    have hla : l * (l - 1) ≠ 0 := mul_ne_zero hl0.ne' ha.ne'
    have hll : l < l ^ 2 := by nlinarith [mul_lt_mul_of_pos_left hl hl0]
    have hla' : -l + l ^ 2 ≠ 0 := by
      intro hz
      exact (ne_of_lt hll) (by linarith)
    rw [Yt, escape_eq hl0]
    field_simp [h₁, h₂, h₃, hla]
    have hfinal : (l + childSum l T) * (l - 1) + childSum l T - l * childSum l T ≠ 0 := by
      convert hla using 1; ring
    apply (div_eq_iff hfinal).2
    ring
  rw [hroot]
  unfold childSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hβ : 0 ≤ escape l (child T (i + 1)) := (escape_mem_Icc hl0 _).1
  have hden : 0 < l - 1 + escape l (child T (i + 1)) := by positivity
  rw [Yt]
  field_simp [ha.ne', hden.ne']
  ring

/-- The almost-sure transformed-escape range. -/
theorem Yt_mem {l : ℝ} (hl : 1 < l) {T : Tree} (hβ : 0 < escape l T) :
    0 < Yt l T ∧ Yt l T < 1 / l := by
  exact ⟨div_pos hβ (by have := (escape_mem_Icc (by linarith : 0 < l) T).1; positivity),
    Yt_lt_inv hl T⟩

private lemma y_mem_of_escape {l b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1) :
    b / (l - 1 + b) ∈ Set.Ioo 0 (1 / l) := by
  have hden : 0 < l - 1 + b := by linarith [hb.1]
  constructor
  · exact div_pos hb.1 hden
  · rw [div_lt_div_iff₀ hden (by linarith : 0 < l)]
    nlinarith [hb.2]

/-- Proposition 3.1 (`prop:collapse`), pointwise: the four collapsed kernel identities
and the two mean bounds. -/
theorem collapse_identities {l : ℝ} (hl : 1 < l) {b b' : ℝ}
    (hb : b ∈ Set.Ioo 0 1) (hb' : b' ∈ Set.Ioo 0 1) :
    let y := b / (l - 1 + b)
    let y' := b' / (l - 1 + b')
    1 - l * y * y' = (l - 1) * Dfun l b b' / ((l - 1 + b) * (l - 1 + b')) ∧
    b * b' / Dfun l b b' = (l - 1) * y * y' / (1 - l * y * y') ∧
    tau b b' / Dfun l b b' =
      (y * (1 - y') + y' * (1 - l * y)) / (1 - l * y * y') ∧
    tau b b' / Dfun l b b' = 1 - (1 - y) * (1 - y') / (1 - l * y * y') ∧
    max y y' ≤ tau b b' / Dfun l b b' ∧ tau b b' / Dfun l b b' ≤ y + y' := by
  dsimp only
  let y := b / (l - 1 + b)
  let y' := b' / (l - 1 + b')
  have hy := y_mem_of_escape hl hb
  have hy' := y_mem_of_escape hl hb'
  have hy1 : y < 1 := hy.2.trans ((div_lt_one (by linarith : 0 < l)).2 (by linarith))
  have hy'1 : y' < 1 := hy'.2.trans ((div_lt_one (by linarith : 0 < l)).2 (by linarith))
  have ha : 0 < l - 1 := by linarith
  have hden : 0 < l - 1 + b := by linarith [hb.1]
  have hden' : 0 < l - 1 + b' := by linarith [hb'.1]
  have hD : 0 < Dfun l b b' := by
    unfold Dfun
    nlinarith [mul_pos hb.1 hb'.1, mul_nonneg hb.1.le (sub_nonneg.mpr hb'.2.le),
      mul_nonneg hb'.1.le (sub_nonneg.mpr hb.2.le)]
  have hly : l * y < 1 := by
    have h := mul_lt_mul_of_pos_left hy.2 (by linarith : 0 < l)
    rwa [mul_one_div, div_self (by linarith : l ≠ 0)] at h
  have hly' : l * y' < 1 := by
    have h := mul_lt_mul_of_pos_left hy'.2 (by linarith : 0 < l)
    rwa [mul_one_div, div_self (by linarith : l ≠ 0)] at h
  have hq : 0 < 1 - l * y * y' := by
    have hll : l * y * y' < 1 * y' := mul_lt_mul_of_pos_right hly hy'.1
    linarith
  have hqalt : 1 - y * y' * l ≠ 0 := by nlinarith [hq]
  have hDraw : l - 1 + b + b' - b * b' ≠ 0 := by simpa [Dfun] using hD.ne'
  have hqraw : 1 - l * (b / (l - 1 + b)) * (b' / (l - 1 + b')) ≠ 0 := by
    simpa only [y, y'] using hq.ne'
  have hid₁ : 1 - l * y * y' =
      (l - 1) * Dfun l b b' / ((l - 1 + b) * (l - 1 + b')) := by
    dsimp [y, y']
    unfold Dfun
    field_simp [ha.ne', hden.ne', hden'.ne', hDraw]
    ring
  have hid₂ : b * b' / Dfun l b b' = (l - 1) * y * y' / (1 - l * y * y') := by
    apply (eq_div_iff hq.ne').2
    rw [hid₁]
    dsimp [y, y']
    field_simp [ha.ne', hden.ne', hden'.ne', hDraw]
  have hid₃ : tau b b' / Dfun l b b' =
      (y * (1 - y') + y' * (1 - l * y)) / (1 - l * y * y') := by
    apply (eq_div_iff hq.ne').2
    rw [hid₁]
    dsimp [y, y']
    unfold tau
    field_simp [ha.ne', hden.ne', hden'.ne', hDraw]
    ring
  have hid₄ : tau b b' / Dfun l b b' =
      1 - (1 - y) * (1 - y') / (1 - l * y * y') := by
    rw [hid₃, sub_div' hq.ne']
    ring
  refine ⟨hid₁, hid₂, hid₃, hid₄, ?_, ?_⟩
  · apply max_le
    · rw [hid₃]
      have heq : (y * (1 - y') + y' * (1 - l * y)) / (1 - l * y * y') - y =
          y' * ((1 - y) * (1 - l * y) / (1 - l * y * y')) := by
        rw [div_sub' hq.ne', ← mul_div_assoc]
        ring
      have hnonneg : 0 ≤ y' * ((1 - y) * (1 - l * y) / (1 - l * y * y')) :=
        mul_nonneg hy'.1.le (div_nonneg
          (mul_nonneg (sub_nonneg.mpr hy1.le) (sub_nonneg.mpr hly.le)) hq.le)
      linarith
    · rw [show tau b b' / Dfun l b b' =
          (y' * (1 - y) + y * (1 - l * y')) / (1 - l * y * y') by
            rw [hid₃]; congr 1; ring]
      have heq : (y' * (1 - y) + y * (1 - l * y')) / (1 - l * y * y') - y' =
          y * ((1 - y') * (1 - l * y') / (1 - l * y * y')) := by
        rw [div_sub' hq.ne', ← mul_div_assoc]
        ring
      have hnonneg : 0 ≤ y * ((1 - y') * (1 - l * y') / (1 - l * y * y')) :=
        mul_nonneg hy.1.le (div_nonneg
          (mul_nonneg (sub_nonneg.mpr hy'1.le) (sub_nonneg.mpr hly'.le)) hq.le)
      linarith
  · have hA0 : 0 ≤ (1 - y) * (1 - l * y) / (1 - l * y * y') :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hy1.le) (sub_nonneg.mpr hly.le)) hq.le
    have hA1 : (1 - y) * (1 - l * y) / (1 - l * y * y') ≤ 1 := by
      rw [div_le_one hq]
      have hc : 0 < 1 + l - l * y - l * y' := by nlinarith
      have hprod : 0 ≤ y * (1 + l - l * y - l * y') := mul_nonneg hy.1.le hc.le
      nlinarith
    rw [hid₃]
    have heq : (y * (1 - y') + y' * (1 - l * y)) / (1 - l * y * y') =
        y + y' * ((1 - y) * (1 - l * y) / (1 - l * y * y')) := by
      have hd : (y * (1 - y') + y' * (1 - l * y)) / (1 - l * y * y') - y =
          y' * ((1 - y) * (1 - l * y) / (1 - l * y * y')) := by
        rw [div_sub' hq.ne', ← mul_div_assoc]
        ring
      linarith
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hA1 hy'.1.le]

private lemma ae_pair_escape_mem (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    ∀ᵐ p : Tree × Tree ∂(GW μ).prod (GW μ),
      escape l p.1 ∈ Set.Ioo 0 1 ∧ escape l p.2 ∈ Set.Ioo 0 1 := by
  have hmem := ae_escape_mem_Ioo h (by linarith) hlm
  filter_upwards [(measurePreserving_fst (μ := GW μ) (ν := GW μ)).quasiMeasurePreserving.ae hmem,
    (measurePreserving_snd (μ := GW μ) (ν := GW μ)).quasiMeasurePreserving.ae hmem] with p hp hp'
  exact ⟨hp, hp'⟩

private lemma Nval_eq_pair (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) :
    Nval μ l = ∫ p, escape l p.1 * escape l p.2 / Dfun l (escape l p.1) (escape l p.2)
      ∂(GW μ).prod (GW μ) := by
  unfold Nval escLaw
  rw [Measure.map_prod_map _ _ (measurable_escape l) (measurable_escape l)]
  exact integral_map_of_stronglyMeasurable
    ((measurable_escape l).prodMap (measurable_escape l))
    (((measurable_fst.mul measurable_snd).div (measurable_Dfun l)).stronglyMeasurable)

private lemma Zval_eq_pair (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) :
    Zval μ l = ∫ p, tau (escape l p.1) (escape l p.2) / Dfun l (escape l p.1) (escape l p.2)
      ∂(GW μ).prod (GW μ) := by
  unfold Zval escLaw tau
  rw [Measure.map_prod_map _ _ (measurable_escape l) (measurable_escape l)]
  exact integral_map_of_stronglyMeasurable
    ((measurable_escape l).prodMap (measurable_escape l))
    ((((measurable_fst.add measurable_snd).sub (measurable_fst.mul measurable_snd)).div
      (measurable_Dfun l)).stronglyMeasurable)

/-- Numerator in the transformed law. -/
theorem Nval_eq_NY (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    Nval μ l = NY l (Ylaw μ l) (Ylaw μ l) := by
  rw [Nval_eq_pair]
  unfold NY Ylaw
  rw [Measure.map_prod_map _ _ (measurable_Yt l) (measurable_Yt l)]
  symm
  calc
    _ = ∫ p, (l - 1) * Yt l p.1 * Yt l p.2 / (1 - l * Yt l p.1 * Yt l p.2)
        ∂(GW μ).prod (GW μ) :=
      integral_map_of_stronglyMeasurable
        ((measurable_Yt l).prodMap (measurable_Yt l))
        (by fun_prop)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_pair_escape_mem μ h hl hlm] with p hp
      exact (collapse_identities hl hp.1 hp.2).2.1.symm

/-- Denominator in the transformed law. -/
theorem Zval_eq_ZY (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    Zval μ l = ZY l (Ylaw μ l) (Ylaw μ l) := by
  rw [Zval_eq_pair]
  unfold ZY Ylaw
  rw [Measure.map_prod_map _ _ (measurable_Yt l) (measurable_Yt l)]
  symm
  calc
    _ = ∫ p, (Yt l p.1 * (1 - Yt l p.2) + Yt l p.2 * (1 - l * Yt l p.1)) /
        (1 - l * Yt l p.1 * Yt l p.2) ∂(GW μ).prod (GW μ) :=
      integral_map_of_stronglyMeasurable
        ((measurable_Yt l).prodMap (measurable_Yt l))
        (by fun_prop)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_pair_escape_mem μ h hl hlm] with p hp
      exact (collapse_identities hl hp.1 hp.2).2.2.1.symm

private lemma integrable_Yt (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    Integrable (Yt l) (GW μ) := by
  apply (integrable_const (1 / l)).mono' (measurable_Yt l).aestronglyMeasurable
  filter_upwards [ae_escape_pos h (by linarith) hlm] with T hT
  rw [Real.norm_eq_abs, abs_of_nonneg (Yt_nonneg hl T)]
  exact (Yt_lt_inv hl T).le

/-- The transformed denominator is pinched between one and two means. -/
theorem muY_le_Zval_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    muY μ l ≤ Zval μ l ∧ Zval μ l ≤ 2 * muY μ l := by
  have hY := integrable_Yt μ h hl hlm
  have hZmap := integrable_Z_kernel μ (by linarith : 0 < l) h hlm
  unfold escLaw at hZmap
  rw [Measure.map_prod_map _ _ (measurable_escape l) (measurable_escape l)] at hZmap
  have hZ : Integrable
      (fun p : Tree × Tree => tau (escape l p.1) (escape l p.2) /
        Dfun l (escape l p.1) (escape l p.2)) ((GW μ).prod (GW μ)) := by
    apply (integrable_map_measure
      ((((measurable_fst.add measurable_snd).sub (measurable_fst.mul measurable_snd)).div
        (measurable_Dfun l)).aestronglyMeasurable)
      ((measurable_escape l).prodMap (measurable_escape l)).aemeasurable).mp
    exact hZmap
  have hYfst : Integrable (fun p : Tree × Tree => Yt l p.1) ((GW μ).prod (GW μ)) :=
    hY.comp_fst (GW μ)
  have hYsum : Integrable (fun p : Tree × Tree => Yt l p.1 + Yt l p.2) ((GW μ).prod (GW μ)) :=
    hYfst.add (hY.comp_snd (GW μ))
  rw [Zval_eq_pair]
  have hfst : ∫ p, Yt l p.1 ∂(GW μ).prod (GW μ) = muY μ l := by
    rw [integral_fun_fst]
    simp [muY, Measure.real]
  have hsum : ∫ p, (Yt l p.1 + Yt l p.2) ∂(GW μ).prod (GW μ) = 2 * muY μ l := by
    rw [integral_add hYfst (hY.comp_snd (GW μ)), integral_fun_fst, integral_fun_snd]
    simp [muY, Measure.real]
    ring
  constructor
  · calc
      muY μ l = ∫ p, Yt l p.1 ∂(GW μ).prod (GW μ) := hfst.symm
      _ ≤ _ := by
        apply integral_mono_ae hYfst hZ
        filter_upwards [ae_pair_escape_mem μ h hl hlm] with p hp
        exact (le_max_left _ _).trans (collapse_identities hl hp.1 hp.2).2.2.2.2.1
  · calc
      _ ≤ ∫ p, (Yt l p.1 + Yt l p.2) ∂(GW μ).prod (GW μ) := by
        apply integral_mono_ae hZ hYsum
        filter_upwards [ae_pair_escape_mem μ h hl hlm] with p hp
        exact (collapse_identities hl hp.1 hp.2).2.2.2.2.2
      _ = 2 * muY μ l := hsum

/-- The transformed law is supported on `(0, 1/l)`. -/
theorem ae_Ylaw_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Ioo 0 (1 / l) := by
  unfold Ylaw
  change ∀ᵐ y ∂(GW μ).map (Yt l), 0 < y ∧ y < 1 / l
  rw [ae_map_iff (measurable_Yt l).aemeasurable measurableSet_Ioo]
  filter_upwards [ae_escape_pos h (by linarith) hlm] with T hT
  exact Yt_mem hl hT

/-- Strict bounds for the transformed mean. -/
theorem muY_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    0 < muY μ l ∧ muY μ l < 1 / l := by
  have hY := integrable_Yt μ h hl hlm
  have hae : ∀ᵐ T ∂GW μ, 0 < Yt l T ∧ Yt l T < 1 / l := by
    filter_upwards [ae_escape_pos h (by linarith) hlm] with T hT
    exact Yt_mem hl hT
  constructor
  · unfold muY
    exact integral_pos_of_ae_pos hY (hae.mono fun _ hT => hT.1)
  · have hpos : 0 < ∫ T, (1 / l - Yt l T) ∂GW μ := by
      apply integral_pos_of_ae_pos ((integrable_const (1 / l)).sub hY)
      filter_upwards [hae] with T hT
      exact sub_pos.mpr hT.2
    rw [integral_sub (integrable_const _) hY, integral_const] at hpos
    simp [Measure.real] at hpos
    simpa only [muY, one_div] using hpos

/-- The effective geometric parameter lies in `(0,1)`. -/
theorem peff_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    0 < peff μ l ∧ peff μ l < 1 := by
  obtain ⟨hm0, hml⟩ := muY_mem μ h hl hlm
  have hm1 : muY μ l < 1 := hml.trans ((div_lt_one (by linarith : 0 < l)).2 (by linarith))
  have hden : 0 < 1 - muY μ l := sub_pos.mpr hm1
  unfold peff
  constructor
  · exact div_pos (mul_pos (by linarith) hm0) hden
  · rw [div_lt_one hden]
    have hnum : (l - 1) * muY μ l < 1 - muY μ l := by
      have := mul_lt_mul_of_pos_left hml (by linarith : 0 < l)
      rw [mul_one_div, div_self (by linarith : l ≠ 0)] at this
      nlinarith
    exact hnum

private lemma integrable_Yt_sq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : Integrable (fun T => Yt l T ^ 2) (GW μ) := by
  apply (integrable_const (1 : ℝ)).mono' ((measurable_Yt l).pow_const 2).aestronglyMeasurable
  filter_upwards [ae_escape_pos h (by linarith) hlm] with T hT
  have hy := Yt_mem hl hT
  have hy1 : Yt l T < 1 := hy.2.trans ((div_lt_one (by linarith : 0 < l)).2 (by linarith))
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy.1.le _)]
  nlinarith [mul_pos hy.1 (sub_pos.mpr hy1)]

/-- Positivity of the second-order residual `R₀`. -/
theorem R0_pos (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    l * momY μ l 2 < muY μ l := by
  have hY := integrable_Yt μ h hl hlm
  have hY2 : Integrable (fun T => l * Yt l T ^ 2) (GW μ) :=
    (integrable_Yt_sq μ h hl hlm).const_mul l
  have hpos : 0 < ∫ T, (Yt l T - l * Yt l T ^ 2) ∂GW μ := by
    apply integral_pos_of_ae_pos (hY.sub hY2)
    filter_upwards [ae_escape_pos h (by linarith) hlm] with T hT
    have hy := Yt_mem hl hT
    have hly : l * Yt l T < 1 := by
      have := mul_lt_mul_of_pos_left hy.2 (by linarith : 0 < l)
      rwa [mul_one_div, div_self (by linarith : l ≠ 0)] at this
    change 0 < Yt l T - l * Yt l T ^ 2
    nlinarith [mul_pos hy.1 (sub_pos.mpr hly)]
  rw [integral_sub hY hY2, integral_const_mul] at hpos
  exact sub_pos.mp hpos

private lemma NvalProv_eq (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) :
    NvalProv μ l = Nval μ l := by
  rfl

private lemma ZvalProv_eq (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) :
    ZvalProv μ l = Zval μ l := by
  rfl

/-- Positivity of the speed ratio at fixed offspring law. -/
theorem rr_pos (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    0 < rr μ l := by
  unfold rr speedValueProv
  rw [if_neg (by linarith : l ≠ 0), NvalProv_eq, ZvalProv_eq]
  exact div_pos
    (div_pos (Nval_pos μ (by linarith) h hlm) (Zval_pos μ (by linarith) h hlm))
    (by linarith)

end LPPMonotonicityProof.Analytic
