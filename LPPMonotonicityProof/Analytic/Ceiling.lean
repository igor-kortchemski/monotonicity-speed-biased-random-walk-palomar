module

public import LPPMonotonicityProof.Analytic.Comparison3
public import LPPMonotonicityProof.Analytic.GeomSum
public import LPPMonotonicityProof.Analytic.Critical
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Speed ceiling (Lemma 3.3, `lem:speed-ceiling`)

This module proves the speed bound of Lemma 3.3,
`v ≤ abS(1-b) / [2λ - (1+λ)bS(1-b)] < b`, with the intermediate bound from
equation (3.3) (`eq:geometric-sum`).  The averaged-gradient part of the lemma is in
`LPPMonotonicityProof.Analytic.Ceiling2`.

The two escape copies are compared successively with the matching geometric
law.  Products are commuted with `integral_prod_swap`, not with a dependent
family construction.
-/

@[expose] public section

namespace LPPMonotonicityProof.Analytic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

private lemma geomY_probability_own {l b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1) :
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

private lemma ae_geomY_mem_own {l b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1) :
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

private lemma Ylaw_mom (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) (n : ℕ) :
    ∫ y, y ^ n ∂Ylaw μ l = momY μ l n := by
  unfold Ylaw momY
  exact integral_map (measurable_Yt l).aemeasurable
    (measurable_id.pow_const n).aestronglyMeasurable

private lemma Sgeo_nonneg_own {l q : ℝ} (hl : 1 < l) (hq : 0 ≤ q) : 0 ≤ Sgeo l q := by
  apply tsum_nonneg
  intro j
  have hQ : 0 < Qgeo l (j + 1) := by
    have hpow := pow_le_Qgeo_div hl.le (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
    have hpos : 0 < ((1 + l) / 2) ^ j := pow_pos (by linarith) _
    have hdiv : 0 < Qgeo l (j + 1) / (j + 1) := by
      apply lt_of_lt_of_le hpos
      convert hpow using 1 <;> simp
    exact (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < j + 1)).mp hdiv
  exact div_nonneg (mul_nonneg (by positivity) (pow_nonneg hq _)) hQ.le

private lemma inv_l_mem_own {l y : ℝ} (hl : 1 < l) (hy : y ∈ Set.Icc 0 (1 / l)) :
    0 ≤ y ∧ y ≤ 1 ∧ l * y ≤ 1 := by
  have hl0 : 0 < l := by linarith
  refine ⟨hy.1, hy.2.trans ?_, ?_⟩
  · exact (div_le_one hl0).2 (by linarith)
  · calc
      l * y ≤ l * (1 / l) := mul_le_mul_of_nonneg_left hy.2 hl0.le
      _ = 1 := by field_simp

private lemma one_sub_prod_own {l y t : ℝ} (hl : 1 < l)
    (hy : y ∈ Set.Icc 0 (1 / l)) (ht : t ∈ Set.Icc 0 (1 / l)) :
    0 < 1 - l * y * t ∧ (l - 1) / l ≤ 1 - l * y * t := by
  obtain ⟨hy0, hy1, hly⟩ := inv_l_mem_own hl hy
  obtain ⟨ht0, ht1, hlt⟩ := inv_l_mem_own hl ht
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

private lemma integrable_bounded_own {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] {f : Ω → ℝ}
    (hf : AEMeasurable f ρ) {C : ℝ} (hC : ∀ᵐ x ∂ρ, ‖f x‖ ≤ C) : Integrable f ρ :=
  Integrable.of_bound hf.aestronglyMeasurable C hC

private lemma Bw_norm_own {l w t : ℝ} (hl : 1 < l) (ht : t ∈ Set.Icc 0 (1 / l)) :
    ‖Bw l w t‖ ≤ (l - 1) / l + |w| := by
  obtain ⟨ht0, ht1, hlt⟩ := inv_l_mem_own hl ht
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

private lemma integrable_Hw_own {l : ℝ} {ρ ξ : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ξ] (hl : 1 < l)
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc 0 (1 / l))
    (hξ : ∀ᵐ t ∂ξ, t ∈ Set.Icc 0 (1 / l)) (w : ℝ) :
    Integrable (fun p => Hw l w p.1 p.2) (ρ.prod ξ) := by
  have hy := (Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := ξ)).ae hρ
  have ht := (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := ξ)).ae hξ
  apply integrable_bounded_own (by unfold Hw; fun_prop)
  let C := ((l - 1) / l ^ 2 + |w| * (2 / l + (1 + l) / l ^ 2)) * (l / (l - 1))
  filter_upwards [hy, ht] with p hpY hpT
  obtain ⟨hy0, hy1, _⟩ := inv_l_mem_own hl hpY
  obtain ⟨ht0, ht1, _⟩ := inv_l_mem_own hl hpT
  obtain ⟨hden, hdenlo⟩ := one_sub_prod_own hl hpY hpT
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

private lemma Hw_integral_swap {l : ℝ} {ρ ξ : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ξ] (w : ℝ) :
    ∫ p, Hw l w p.1 p.2 ∂ρ.prod ξ = ∫ p, Hw l w p.1 p.2 ∂ξ.prod ρ := by
  calc
    _ = ∫ p, Hw l w p.2 p.1 ∂ρ.prod ξ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro p
      unfold Hw
      ring
    _ = _ := integral_prod_swap (μ := ξ) (ν := ρ) (fun p => Hw l w p.1 p.2)

private lemma geom_ZY_pos {l b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1)
    (hm : 0 < ∫ y, y ∂geomY l b) : 0 < ZY l (geomY l b) (geomY l b) := by
  letI := geomY_probability_own hl hb
  have hmem := ae_geomY_mem_own hl hb
  have hN : Integrable (fun p : ℝ × ℝ => (l - 1) * p.1 * p.2 / (1 - l * p.1 * p.2))
      ((geomY l b).prod (geomY l b)) := by
    simpa [Hw] using integrable_Hw_own hl hmem hmem 0
  have hZ : Integrable (fun p : ℝ × ℝ =>
      (p.1 * (1 - p.2) + p.2 * (1 - l * p.1)) / (1 - l * p.1 * p.2))
      ((geomY l b).prod (geomY l b)) := by
    apply (hN.sub (integrable_Hw_own hl hmem hmem 1)).congr
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := geomY l b)
      (ν := geomY l b)).ae hmem, (Measure.quasiMeasurePreserving_snd (μ := geomY l b)
      (ν := geomY l b)).ae hmem] with p hpY hpT
    have hd := (one_sub_prod_own hl hpY hpT).1.ne'
    change (l - 1) * p.1 * p.2 / (1 - l * p.1 * p.2) - Hw l 1 p.1 p.2 = _
    unfold Hw
    field_simp [hd]
    ring
  have hfst : Integrable (fun p : ℝ × ℝ => p.1) ((geomY l b).prod (geomY l b)) := by
    apply integrable_bounded_own (by fun_prop)
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := geomY l b)
      (ν := geomY l b)).ae hmem] with p hp
    rw [Real.norm_of_nonneg hp.1]
    exact hp.2
  calc
    0 < ∫ p : ℝ × ℝ, p.1 ∂(geomY l b).prod (geomY l b) := by
      rw [integral_fun_fst (μ := geomY l b) (ν := geomY l b) (f := fun y : ℝ => y)]
      simpa [Measure.real] using hm
    _ ≤ ZY l (geomY l b) (geomY l b) := by
      unfold ZY
      apply integral_mono_ae hfst hZ
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := geomY l b)
        (ν := geomY l b)).ae hmem, (Measure.quasiMeasurePreserving_snd (μ := geomY l b)
        (ν := geomY l b)).ae hmem] with p hpY hpT
      have hd := (one_sub_prod_own hl hpY hpT).1
      have hnon : 0 ≤ 1 - p.2 := by linarith [(inv_l_mem_own hl hpT).2.1]
      have hly : 0 ≤ 1 - l * p.1 := by linarith [(inv_l_mem_own hl hpY).2.2]
      have hnum : p.1 * (1 - l * p.1 * p.2) ≤ p.1 * (1 - p.2) + p.2 * (1 - l * p.1) := by
        have hp : 0 ≤ p.2 * (1 - p.1) := mul_nonneg hpT.1 (by linarith [(inv_l_mem_own hl hpY).2.1])
        nlinarith
      exact (le_div_iff₀ hd).2 (by nlinarith)

private lemma reset_quotient_mono {l X Y : ℝ} (hl : 1 < l) (hX : 0 ≤ X) (hXY : X ≤ Y)
    (hden : 0 < 2 * l - (1 + l) * Y) :
    (l - 1) * X / (2 * l - (1 + l) * X) ≤
      (l - 1) * Y / (2 * l - (1 + l) * Y) := by
  have hdenX : 0 < 2 * l - (1 + l) * X := by nlinarith
  apply (div_le_div_iff₀ hdenX hden).2
  have hmul : 0 ≤ (l - 1) * (2 * l) * (Y - X) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sub_nonneg.mpr hXY)
  nlinarith

/-- **Lemma 3.3** (`lem:speed-ceiling`), speed bound, including both explicit rational
ceilings. -/
theorem speed_le_ceiling (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    let b := peff μ l
    let S := Sgeo l (1 - b)
    0 < 2 * l - (1 + l) * b * S ∧
      Speed.speedValue μ l ≤ (l - 1) * b * S / (2 * l - (1 + l) * b * S) ∧
      (l - 1) * b * S / (2 * l - (1 + l) * b * S) ≤ b * (1 + l) / (2 * l - (l - 1) * b) ∧
      b * (1 + l) / (2 * l - (l - 1) * b) < b := by
  dsimp only
  let b := peff μ l
  let S := Sgeo l (1 - b)
  let Y : ℝ := b * (1 + l) / ((l - 1) + 2 * b)
  have hb : b ∈ Set.Ioo 0 1 := peff_mem μ h hl hlm
  have hb0 : 0 < b := hb.1
  have ha : 0 < l - 1 := by linarith
  have hq : 0 ≤ 1 - b ∧ 1 - b < 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
  have hSp : 0 ≤ S := Sgeo_nonneg_own hl hq.1
  have hSle : S ≤ (1 + l) / (1 + l - 2 * (1 - b)) := Sgeo_le hl hq
  have hSle' : S ≤ (1 + l) / ((l - 1) + 2 * b) := by convert hSle using 1 <;> ring
  have hXY : b * S ≤ Y := by
    dsimp [Y]
    calc
      b * S ≤ b * ((1 + l) / ((l - 1) + 2 * b)) :=
        mul_le_mul_of_nonneg_left hSle' hb0.le
      _ = _ := by ring
  have hdenY : 0 < 2 * l - (1 + l) * Y := by
    have hden : 0 < (l - 1) + 2 * b := by positivity
    have heq : (2 * l - (1 + l) * Y) * ((l - 1) + 2 * b) =
        (l - 1) * (2 * l - (l - 1) * b) := by
      dsimp [Y]
      field_simp [hden.ne', ha.ne']
      ring
    have hp : 0 < (l - 1) * (2 * l - (l - 1) * b) := by
      exact mul_pos ha (by nlinarith [mul_lt_mul_of_pos_left hb.2 ha])
    nlinarith [heq]
  have hden : 0 < 2 * l - (1 + l) * b * S := by nlinarith [hXY, hSp, hb0.le]
  let v : ℝ := (l - 1) * b * S / (2 * l - (1 + l) * b * S)
  let vY : ℝ := (l - 1) * Y / (2 * l - (1 + l) * Y)
  have hvvY : v ≤ vY := by
    simpa only [v, vY, mul_assoc] using
      reset_quotient_mono hl (mul_nonneg hb0.le hSp) hXY hdenY
  have hvYeq : vY = b * (1 + l) / (2 * l - (l - 1) * b) := by
    have hd : (l - 1) + 2 * b ≠ 0 := by positivity
    have hd1 : 2 * l - (l - 1) * b ≠ 0 := by nlinarith [mul_lt_mul_of_pos_left hb.2 ha]
    dsimp [vY]
    rw [div_eq_div_iff hdenY.ne' hd1]
    dsimp [Y]
    field_simp [hd]
    ring
  have hvYb : vY < b := by
    rw [hvYeq]
    apply (div_lt_iff₀ (by nlinarith [mul_lt_mul_of_pos_left hb.2 ha] :
      0 < 2 * l - (l - 1) * b)).2
    nlinarith [mul_lt_mul_of_pos_left hb.2 ha]
  have hvb : v < b := lt_of_le_of_lt hvvY hvYb
  have hv0 : 0 ≤ v := by
    dsimp [v]
    exact div_nonneg (mul_nonneg (mul_nonneg ha.le hb0.le) hSp) hden.le
  letI : IsProbabilityMeasure (Ylaw μ l) := by
    unfold Ylaw
    infer_instance
  letI : IsProbabilityMeasure (geomY l b) := geomY_probability_own hl hb
  have hYmem : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l) :=
    (ae_Ylaw_mem μ h hl hlm).mono fun y hy => ⟨hy.1.le, hy.2.le⟩
  have hGmem := ae_geomY_mem_own hl hb
  have hGmean : ∫ y, y ∂geomY l b = muY μ l := mean_geomY_peff μ h hl hlm
  have hmom : ∀ n ≥ 1, ∫ y, y ^ n ∂Ylaw μ l ≤ ∫ y, y ^ n ∂geomY l b := by
    intro n hn
    rw [Ylaw_mom, geom_moment hl hb]
    exact momY_le_geom μ h hl hlm n hn
  have hYmean : ∫ y, y ∂Ylaw μ l = muY μ l := by
    rw [show (∫ y, y ∂Ylaw μ l) = ∫ y, y ^ 1 ∂Ylaw μ l by simp, Ylaw_mom]
    simp only [momY, muY, pow_one]
  have hmean : 0 < ∫ y, y ∂Ylaw μ l := hYmean ▸ (muY_mem μ h hl hlm).1
  have hcoeffY : ∀ n : ℕ, 0 ≤ ∫ t, t ^ n * Bw l v t ∂Ylaw μ l := by
    intro n
    apply kernel_coeff_nonneg hl hYmem v hmean
    refine ⟨hv0, ?_⟩
    rw [hYmean]
    simpa only [b, peff] using hvb.le
  have hcoeffG : ∀ n : ℕ, 0 ≤ ∫ t, t ^ n * Bw l v t ∂geomY l b := by
    apply kernel_coeff_nonneg hl hGmem v (hGmean ▸ (muY_mem μ h hl hlm).1)
    refine ⟨hv0, ?_⟩
    rw [hGmean]
    simpa only [b, peff] using hvb.le
  have h₁ : ∫ p, Hw l v p.1 p.2 ∂(Ylaw μ l).prod (Ylaw μ l) ≤
      ∫ p, Hw l v p.1 p.2 ∂(geomY l b).prod (Ylaw μ l) :=
    kernel_compare hl hYmem hGmem hYmem hmom v hcoeffY
  have h₂ : ∫ p, Hw l v p.1 p.2 ∂(Ylaw μ l).prod (geomY l b) ≤
      ∫ p, Hw l v p.1 p.2 ∂(geomY l b).prod (geomY l b) :=
    kernel_compare hl hYmem hGmem hGmem hmom v hcoeffG
  have hcomp : ∫ p, Hw l v p.1 p.2 ∂(Ylaw μ l).prod (Ylaw μ l) ≤
      ∫ p, Hw l v p.1 p.2 ∂(geomY l b).prod (geomY l b) :=
    h₁.trans ((Hw_integral_swap (ρ := geomY l b) (ξ := Ylaw μ l) v).trans_le h₂)
  rw [← NY_sub_ZY l v hl hYmem hYmem, ← NY_sub_ZY l v hl hGmem hGmem] at hcomp
  have hZg : 0 < ZY l (geomY l b) (geomY l b) := geom_ZY_pos hl hb (hGmean ▸ (muY_mem μ h hl hlm).1)
  have hgs := geom_speed hl hb hden
  have hzero : NY l (geomY l b) (geomY l b) - v * ZY l (geomY l b) (geomY l b) = 0 := by
    apply sub_eq_zero.mpr
    exact (div_eq_iff hZg.ne').mp (by simpa [v, S] using hgs)
  rw [hzero] at hcomp
  have hvN : Speed.Nval μ l ≤ v * Speed.Zval μ l := by
    rw [Nval_eq_NY μ h hl hlm, Zval_eq_ZY μ h hl hlm]
    exact sub_nonpos.mp hcomp
  have hZ : 0 < Speed.Zval μ l := Zval_pos μ (by linarith) h hlm
  have hv : Speed.speedValue μ l ≤ v := by
    rw [speedValue_eq_speedValueProv, speedValueProv_eq, ite_eq_right (by linarith : l ≠ 0)]
    apply (div_le_iff₀ hZ).2
    exact hvN
  refine ⟨hden, hv, ?_, ?_⟩
  · exact hvvY.trans_eq hvYeq
  · rw [← hvYeq]
    exact hvYb

/-- The speed bound of Lemma 3.3 in the simpler mean-parameter form `v ≤ b`. -/
theorem speed_le_peff_ratio (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : Speed.speedValue μ l ≤ (l - 1) * muY μ l / (1 - muY μ l) := by
  obtain ⟨_, hv, hv2, hvb⟩ := speed_le_ceiling μ h hl hlm
  exact hv.trans (hv2.trans hvb.le)

end LPPMonotonicityProof.Analytic
