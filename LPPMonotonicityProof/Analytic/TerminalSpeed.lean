module

public import LPPMonotonicityProof.Analytic.Joint
public import LPPMonotonicityProof.Analytic.Comparison2
public import LPPMonotonicityProof.Analytic.Comparison3
public import LPPMonotonicityProof.Analytic.Ceiling
public import LPPMonotonicityProof.Analytic.FirstSplit3
public import LPPMonotonicityProof.Analytic.Kernel2
public import LPPMonotonicityProof.Analytic.Critical
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Terminal speed comparison

This module proves Lemma 5.4 (`lem:terminal-speed`): replacing the first-split law by
its extremal two-point law `W₊` bounds the speed ratio `r = v/a`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private lemma eta_geom_sum (η : ℝ) (j : ℕ) :
    η * (∑ i ∈ Finset.range j, (1 - η) ^ i) = 1 - (1 - η) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ]
      rw [pow_succ]
      nlinarith [ih]

/-- The `W₊` law from `lem:terminal-speed`, including its zero-over-zero
convention through Lean's real division. -/
theorem wPlus_moment {d₀ η₀ : ℝ} (hd : 0 ≤ d₀) (hdη : d₀ ≤ η₀)
    (_hη : η₀ ≤ 1) (j : ℕ) :
    ∫ w, w ^ j ∂wPlus d₀ η₀ =
      1 - d₀ * (∑ i ∈ Finset.range j, (1 - η₀) ^ i) := by
  have hη0 : 0 ≤ η₀ := hd.trans hdη
  have hp : 0 ≤ d₀ / η₀ := div_nonneg hd hη0
  have hp1 : d₀ / η₀ ≤ 1 := by
    by_cases hzero : η₀ = 0
    · have hd0 : d₀ = 0 := le_antisymm (by simpa [hzero] using hdη) hd
      simp [hzero, hd0]
    · exact (div_le_one (lt_of_le_of_ne hη0 (Ne.symm hzero))).2 hdη
  have hq : 0 ≤ 1 - d₀ / η₀ := by linarith
  have hI₁ : Integrable (fun w : ℝ => w ^ j)
      (ENNReal.ofReal (d₀ / η₀) • Measure.dirac (1 - η₀)) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  have hI₂ : Integrable (fun w : ℝ => w ^ j)
      (ENNReal.ofReal (1 - d₀ / η₀) • Measure.dirac 1) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  rw [wPlus, integral_add_measure hI₁ hI₂,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq, smul_eq_mul]
  by_cases hzero : η₀ = 0
  · have hd0 : d₀ = 0 := by linarith
    simp [hzero, hd0]
  · have hηpos : 0 < η₀ := lt_of_le_of_ne hη0 (Ne.symm hzero)
    have hpη : d₀ / η₀ * η₀ = d₀ := div_mul_cancel₀ _ hzero
    calc
      (d₀ / η₀) * (1 - η₀) ^ j + (1 - d₀ / η₀) * 1 ^ j =
          1 - (d₀ / η₀) * (1 - (1 - η₀) ^ j) := by ring
      _ = 1 - (d₀ / η₀) * (η₀ * ∑ i ∈ Finset.range j, (1 - η₀) ^ i) := by
        rw [eta_geom_sum]
      _ = 1 - d₀ * ∑ i ∈ Finset.range j, (1 - η₀) ^ i := by
        rw [← mul_assoc, hpη]

private lemma wPlus_probability {d₀ η₀ : ℝ} (hd : 0 ≤ d₀) (hdη : d₀ ≤ η₀)
    (_hη : η₀ ≤ 1) : IsProbabilityMeasure (wPlus d₀ η₀) := by
  have hη0 : 0 ≤ η₀ := hd.trans hdη
  have hp : 0 ≤ d₀ / η₀ := div_nonneg hd hη0
  have hp1 : d₀ / η₀ ≤ 1 := by
    by_cases hzero : η₀ = 0
    · have hd0 : d₀ = 0 := le_antisymm (by simpa [hzero] using hdη) hd
      simp [hzero, hd0]
    · exact (div_le_one (lt_of_le_of_ne hη0 (Ne.symm hzero))).2 hdη
  have hq : 0 ≤ 1 - d₀ / η₀ := by linarith
  refine ⟨?_⟩
  rw [wPlus, Measure.add_apply]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply,
    mul_one]
  rw [← ENNReal.ofReal_add hp hq]
  rw [show d₀ / η₀ + (1 - d₀ / η₀) = 1 by ring, ENNReal.ofReal_one]

private lemma geomY_probability_closed {l b : ℝ} (_hl : 1 < l)
    (hb : 0 < b) (hb1 : b ≤ 1) : IsProbabilityMeasure (geomY l b) := by
  have hq0 : 0 ≤ 1 - b := by linarith
  have hq1 : 1 - b < 1 := by linarith
  have hsum : Summable (fun g : ℕ => b * (1 - b) ^ g) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  refine ⟨?_⟩
  rw [geomY, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply,
    mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun g => mul_nonneg hb.le (pow_nonneg hq0 _)) hsum]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  rw [sub_sub_cancel, mul_inv_cancel₀ hb.ne', ENNReal.ofReal_one]

private lemma geomY_ae_Icc {l b : ℝ} (hl : 1 < l) (_hb : 0 < b) :
    ∀ᵐ y ∂geomY l b, y ∈ Set.Icc (0 : ℝ) (1 / l) := by
  rw [geomY, Measure.ae_sum_iff]
  intro g
  apply Filter.Eventually.filter_mono (Measure.ae_smul_measure_le _)
  refine (mem_ae_dirac_iff (s := Set.Icc (0 : ℝ) (1 / l)) measurableSet_Icc).2
    ⟨?_, ?_⟩
  · exact (zpow_pos (show 0 < l by linarith) (-((g : ℤ) + 1))).le
  · calc
      l ^ (-((g : ℤ) + 1)) ≤ l ^ (-1 : ℤ) := by
        apply zpow_le_zpow_right₀ (by linarith : 1 ≤ l)
        omega
      _ = 1 / l := by simp

private lemma geomY_moment_closed {l b : ℝ} (hl : 1 < l)
    (hb : 0 < b) (hb1 : b ≤ 1) (n : ℕ) :
    ∫ y, y ^ n ∂geomY l b = b / (l ^ n - 1 + b) := by
  have hn : 0 < l ^ n := pow_pos (by linarith) _
  have hq0 : 0 ≤ 1 - b := by linarith
  have hq1 : 1 - b < 1 := by linarith
  unfold geomY
  rw [integral_sum_dirac (by intro g; simp)]
  simp only [ENNReal.toReal_ofReal (mul_nonneg hb.le (pow_nonneg hq0 _)), smul_eq_mul]
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
  have hr'0 : 0 ≤ (1 - b) * (l ^ n)⁻¹ := mul_nonneg hq0 (inv_nonneg.mpr hn.le)
  have hr'1 : (1 - b) * (l ^ n)⁻¹ < 1 := by
    have hi : (l ^ n)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith : 1 ≤ l))
    calc
      (1 - b) * (l ^ n)⁻¹ ≤ (1 - b) * 1 := mul_le_mul_of_nonneg_left hi hq0
      _ < 1 := by simpa using hq1
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr'0 hr'1]
  field_simp [hb.ne', hn.ne']
  ring

private lemma wPlus_ae_Icc {d₀ η₀ : ℝ} (hd : 0 ≤ d₀) (hdη : d₀ ≤ η₀)
    (hη : η₀ ≤ 1) : ∀ᵐ w ∂wPlus d₀ η₀, w ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  have hset : MeasurableSet {w : ℝ | w ∉ Set.Icc (0 : ℝ) 1} :=
    measurableSet_Icc.compl
  rw [wPlus, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  have hη0 : 0 ≤ η₀ := hd.trans hdη
  have hlow : 0 ≤ 1 - η₀ := by linarith
  simp [Measure.dirac_apply' _ hset, Set.indicator_apply, hlow, hη, hη0]

private lemma integrable_bounded_ae_terminal {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] {f : Ω → ℝ}
    (hf : AEMeasurable f ρ) {C : ℝ} (hC : ∀ᵐ x ∂ρ, ‖f x‖ ≤ C) : Integrable f ρ :=
  (integrable_const C).mono' hf.aestronglyMeasurable hC

private lemma integrable_Wt_pow_terminal (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : Integrable (fun T => Wt l T ^ n) (splitLaw μ) := by
  letI := splitLaw_prob h
  apply (integrable_const (1 : ℝ)).mono' ((measurable_Wt l).pow_const n).aestronglyMeasurable
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hT.1.le _)]
  exact pow_le_one₀ hT.1.le hT.2.le

private lemma integrable_one_sub_Wt_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    Integrable (fun T => 1 - Wt l T) (splitLaw μ) := by
  letI := splitLaw_prob h
  exact (integrable_const (1 : ℝ)).sub
    (by simpa only [pow_one] using integrable_Wt_pow_terminal h hl hlm 1)

private lemma integrable_Wt_deficit_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    Integrable (fun T => Wt l T * (1 - Wt l T)) (splitLaw μ) := by
  have h₁ := integrable_Wt_pow_terminal h hl hlm 1
  have h₂ := integrable_Wt_pow_terminal h hl hlm 2
  apply (h₁.sub h₂).congr
  filter_upwards with T
  change Wt l T ^ 1 - Wt l T ^ 2 = Wt l T * (1 - Wt l T)
  rw [pow_one]
  ring

private lemma integral_one_sub_Wt_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    (∫ T, 1 - Wt l T ∂splitLaw μ) = dW μ l := by
  letI := splitLaw_prob h
  have hW : Integrable (Wt l) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow_terminal h hl hlm 1
  rw [integral_sub (integrable_const (1 : ℝ)) hW]
  simp [dW, wbar, etaW]

private lemma integral_deficit_sq_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    (∫ T, (1 - Wt l T) ^ 2 ∂splitLaw μ) =
      1 - 2 * wbar μ l + etaW μ l 2 := by
  letI := splitLaw_prob h
  have hW : Integrable (Wt l) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow_terminal h hl hlm 1
  have hW2 := integrable_Wt_pow_terminal h hl hlm 2
  calc
    (∫ T, (1 - Wt l T) ^ 2 ∂splitLaw μ) =
        ∫ T, (1 - 2 * Wt l T) + Wt l T ^ 2 ∂splitLaw μ := by
      apply integral_congr_ae
      filter_upwards with T
      ring
    _ = (∫ T, 1 - 2 * Wt l T ∂splitLaw μ) +
        ∫ T, Wt l T ^ 2 ∂splitLaw μ := by
      rw [integral_add (f := fun T => 1 - 2 * Wt l T)
        (g := fun T => Wt l T ^ 2)
        ((integrable_const (1 : ℝ)).sub (hW.const_mul 2)) hW2]
    _ = 1 - 2 * wbar μ l + etaW μ l 2 := by
      rw [integral_sub (f := fun _ : Tree => (1 : ℝ))
        (g := fun T => 2 * Wt l T)
        (integrable_const (1 : ℝ)) (hW.const_mul 2), integral_const_mul]
      simp [wbar, etaW, Measure.real]

private lemma integral_Wt_deficit_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    (∫ T, Wt l T * (1 - Wt l T) ∂splitLaw μ) =
      wbar μ l - etaW μ l 2 := by
  letI := splitLaw_prob h
  have hW : Integrable (Wt l) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow_terminal h hl hlm 1
  have hW2 := integrable_Wt_pow_terminal h hl hlm 2
  calc
    _ = ∫ T, Wt l T - Wt l T ^ 2 ∂splitLaw μ := by
      apply integral_congr_ae
      filter_upwards with T
      change Wt l T * (1 - Wt l T) = Wt l T - Wt l T ^ 2
      ring
    _ = _ := by
      rw [integral_sub hW hW2]
      simp [wbar, etaW]

private lemma integral_Wt_deficit_eq_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    (∫ T, Wt l T * (1 - Wt l T) ∂splitLaw μ) =
      dW μ l * (1 - etaD μ l) := by
  have hdpos := dW_pos h hl hlm
  have hsq := integral_deficit_sq_terminal h hl hlm
  have hwd := integral_Wt_deficit_terminal h hl hlm
  unfold etaD
  rw [hwd, hsq]
  unfold dW
  field_simp [show 1 - wbar μ l ≠ 0 by simpa [dW] using hdpos.ne']
  ring

private lemma convex_tangent_pow_terminal (k : ℕ) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y ^ k + (k : ℝ) * y ^ (k - 1) * (x - y) ≤ x ^ k := by
  cases k with
  | zero => simp
  | succ k =>
      by_cases hxy : x = y
      · subst x
        simp
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · have hs := (convexOn_pow (𝕜 := ℝ) (k + 1)).slope_le_of_hasDerivAt
          (show x ∈ Set.Ici (0 : ℝ) from hx) (show y ∈ Set.Ici (0 : ℝ) from hy) hlt
          (hasDerivAt_pow (k + 1) y)
        rw [slope_def_field] at hs
        have hm := (div_le_iff₀ (sub_pos.mpr hlt)).mp hs
        simp only [Nat.add_sub_cancel, pow_succ] at hm ⊢
        push_cast at hm ⊢
        nlinarith [hm]
      · have hs := (convexOn_pow (𝕜 := ℝ) (k + 1)).le_slope_of_hasDerivAt
          (show y ∈ Set.Ici (0 : ℝ) from hy) (show x ∈ Set.Ici (0 : ℝ) from hx) hgt
          (hasDerivAt_pow (k + 1) y)
        rw [slope_def_field] at hs
        have hm := (le_div_iff₀ (sub_pos.mpr hgt)).mp hs
        simp only [Nat.add_sub_cancel, pow_succ] at hm ⊢
        push_cast at hm ⊢
        nlinarith [hm]

/-- Jensen's inequality under the law tilted by the deficit `1 - W`. -/
private theorem deficit_tilt_moment_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (j : ℕ) :
    dW μ l * (1 - etaD μ l) ^ j ≤
      ∫ T, Wt l T ^ j * (1 - Wt l T) ∂splitLaw μ := by
  letI := splitLaw_prob h
  have hdpos := dW_pos h hl hlm
  have heta := dW_le_etaD h hl hlm
  have hdef := integrable_one_sub_Wt_terminal h hl hlm
  have hzero :
      (∫ T, (1 - Wt l T) * (Wt l T - (1 - etaD μ l)) ∂splitLaw μ) = 0 := by
    have hprod : Integrable
        (fun T => (1 - Wt l T) * (Wt l T - (1 - etaD μ l))) (splitLaw μ) := by
      apply ((integrable_Wt_deficit_terminal h hl hlm).sub
        (hdef.const_mul (1 - etaD μ l))).congr
      filter_upwards with T
      change (Wt l T * (1 - Wt l T)) -
          (1 - etaD μ l) * (1 - Wt l T) =
        (1 - Wt l T) * (Wt l T - (1 - etaD μ l))
      ring
    calc
      _ = (∫ T, Wt l T * (1 - Wt l T) ∂splitLaw μ) -
          (1 - etaD μ l) * ∫ T, (1 - Wt l T) ∂splitLaw μ := by
        rw [show (fun T => (1 - Wt l T) * (Wt l T - (1 - etaD μ l))) =
          fun T => Wt l T * (1 - Wt l T) - (1 - etaD μ l) * (1 - Wt l T) by
            funext T; ring]
        rw [integral_sub (integrable_Wt_deficit_terminal h hl hlm)
          (hdef.const_mul (1 - etaD μ l)), integral_const_mul]
      _ = 0 := by rw [integral_Wt_deficit_eq_terminal h hl hlm,
        integral_one_sub_Wt_terminal h hl hlm]; ring
  have hwt_int (k : ℕ) : Integrable (fun T => Wt l T ^ k * (1 - Wt l T))
      (splitLaw μ) := by
    have hk := integrable_Wt_pow_terminal h hl hlm k
    have hk1 := integrable_Wt_pow_terminal h hl hlm (k + 1)
    apply (hk.sub hk1).congr
    filter_upwards with T
    change Wt l T ^ k - Wt l T ^ (k + 1) =
      Wt l T ^ k * (1 - Wt l T)
    ring
  cases j with
  | zero =>
      simpa only [pow_zero, one_mul] using
        (le_of_eq (by
          rw [integral_one_sub_Wt_terminal h hl hlm]
          simp))
  | succ k =>
      let y : ℝ := 1 - etaD μ l
      have hy : 0 ≤ y := by dsimp [y]; linarith [heta.1, heta.2, hdpos]
      have hleft : Integrable
          (fun T => y ^ (k + 1) * (1 - Wt l T) +
            ((k + 1 : ℕ) : ℝ) * y ^ k * ((1 - Wt l T) * (Wt l T - y)))
          (splitLaw μ) := by
        have hprod : Integrable (fun T => (1 - Wt l T) * (Wt l T - y)) (splitLaw μ) := by
          apply ((integrable_Wt_deficit_terminal h hl hlm).sub (hdef.const_mul y)).congr
          filter_upwards with T
          dsimp [y]
          ring
        exact (hdef.const_mul _).add (hprod.const_mul _)
      have hright : Integrable (fun T => Wt l T ^ (k + 1) * (1 - Wt l T))
          (splitLaw μ) := hwt_int (k + 1)
      have hpoint : ∀ᵐ T ∂splitLaw μ,
          y ^ (k + 1) * (1 - Wt l T) +
              ((k + 1 : ℕ) : ℝ) * y ^ k * ((1 - Wt l T) * (Wt l T - y)) ≤
            Wt l T ^ (k + 1) * (1 - Wt l T) := by
        filter_upwards [ae_Wt_mem h hl hlm] with T hT
        have htan := convex_tangent_pow_terminal (k + 1) hT.1.le hy
        have hmul := mul_le_mul_of_nonneg_right htan (sub_nonneg.mpr hT.2.le)
        convert hmul using 1 <;> dsimp [y] <;> ring
      have hmono := integral_mono_ae hleft hright hpoint
      have hfactor :
          (∫ T, y ^ (k + 1) * (1 - Wt l T) +
            ((k + 1 : ℕ) : ℝ) * y ^ k * ((1 - Wt l T) * (Wt l T - y))
              ∂splitLaw μ) = dW μ l * y ^ (k + 1) := by
        have hprod : Integrable
            (fun T => ((k + 1 : ℕ) : ℝ) * y ^ k *
              ((1 - Wt l T) * (Wt l T - y))) (splitLaw μ) := by
          have hi := integrable_Wt_deficit_terminal h hl hlm
          have hj := hdef.const_mul y
          apply ((hi.sub hj).const_mul (((k + 1 : ℕ) : ℝ) * y ^ k)).congr
          filter_upwards with T
          change ((k + 1 : ℕ) : ℝ) * y ^ k *
              ((Wt l T * (1 - Wt l T)) - y * (1 - Wt l T)) =
            ((k + 1 : ℕ) : ℝ) * y ^ k *
              ((1 - Wt l T) * (Wt l T - y))
          ring
        rw [integral_add (hdef.const_mul _) hprod,
          integral_const_mul, integral_const_mul, hzero,
          integral_one_sub_Wt_terminal h hl hlm]
        ring
      rw [hfactor] at hmono
      simpa [y] using hmono

private theorem Wt_moment_le_wPlus_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) {d₀ η₀ : ℝ}
    (hd₀ : 0 ≤ d₀) (hd₀d : d₀ ≤ dW μ l)
    (hηη₀ : etaD μ l ≤ η₀) (hη₀ : η₀ ≤ 1) (n : ℕ) :
    ∫ T, Wt l T ^ n ∂splitLaw μ ≤ ∫ w, w ^ n ∂wPlus d₀ η₀ := by
  letI := splitLaw_prob h
  have heta := dW_le_etaD h hl hlm
  have hd₀η₀ : d₀ ≤ η₀ := hd₀d.trans (heta.1.trans hηη₀)
  letI := wPlus_probability hd₀ hd₀η₀ hη₀
  have hdpos := dW_pos h hl hlm
  have hΔ (j : ℕ) :
      d₀ * (1 - η₀) ^ j ≤ ∫ T, Wt l T ^ j * (1 - Wt l T) ∂splitLaw μ := by
    have hy0 : 0 ≤ 1 - η₀ := by linarith
    have hy1 : 1 - η₀ ≤ 1 - etaD μ l := by linarith
    have hpow : (1 - η₀) ^ j ≤ (1 - etaD μ l) ^ j := by gcongr
    calc
      d₀ * (1 - η₀) ^ j ≤ dW μ l * (1 - η₀) ^ j :=
        mul_le_mul_of_nonneg_right hd₀d (pow_nonneg hy0 _)
      _ ≤ dW μ l * (1 - etaD μ l) ^ j :=
        mul_le_mul_of_nonneg_left hpow hdpos.le
      _ ≤ ∫ T, Wt l T ^ j * (1 - Wt l T) ∂splitLaw μ :=
        deficit_tilt_moment_terminal h hl hlm j
  induction n with
  | zero => simp
  | succ n ih =>
      have hWn := integrable_Wt_pow_terminal h hl hlm n
      have hWn1 := integrable_Wt_pow_terminal h hl hlm (n + 1)
      have hdrop : Integrable (fun T => Wt l T ^ n * (1 - Wt l T)) (splitLaw μ) := by
        have h₁ := integrable_Wt_pow_terminal h hl hlm n
        have h₂ := integrable_Wt_pow_terminal h hl hlm (n + 1)
        apply (h₁.sub h₂).congr
        filter_upwards with T
        change Wt l T ^ n - Wt l T ^ (n + 1) = _
        ring
      have hrec :
          (∫ T, Wt l T ^ (n + 1) ∂splitLaw μ) =
            (∫ T, Wt l T ^ n ∂splitLaw μ) -
              ∫ T, Wt l T ^ n * (1 - Wt l T) ∂splitLaw μ := by
        calc
          _ = ∫ T, Wt l T ^ n - Wt l T ^ n * (1 - Wt l T) ∂splitLaw μ := by
            apply integral_congr_ae
            filter_upwards with T
            rw [pow_succ]
            ring
          _ = _ := by rw [integral_sub hWn hdrop]
      have hplusrec :
          (∫ w, w ^ (n + 1) ∂wPlus d₀ η₀) =
            (∫ w, w ^ n ∂wPlus d₀ η₀) - d₀ * (1 - η₀) ^ n := by
        rw [wPlus_moment hd₀ hd₀η₀ hη₀ (n + 1),
          wPlus_moment hd₀ hd₀η₀ hη₀ n,
          Finset.sum_range_succ]
        ring
      rw [hrec, hplusrec]
      linarith [ih, hΔ n]

private lemma lawL_eq_geomY (x a : ℝ) : lawL x a = geomY (1 + a) (a * x) := by
  unfold lawL geomY
  apply congrArg Measure.sum
  funext g
  have hg : -((g : ℤ) + 1) = -(((g + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [hg, zpow_neg, zpow_natCast]

private lemma integrable_pow_Icc01_terminal {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    Integrable (fun y : ℝ => y ^ n) ρ := by
  apply integrable_bounded_ae_terminal (measurable_id.pow_const n).aemeasurable
  filter_upwards [hρ] with y hy
  change ‖y ^ n‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy.1 _)]
  exact pow_le_one₀ hy.1 hy.2

private theorem integral_mul_pow_map_prod_terminal {ρ σ : Measure ℝ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc (0 : ℝ) 1)
    (hσ : ∀ᵐ y ∂σ, y ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    ∫ z, z ^ n ∂((ρ.prod σ).map fun p : ℝ × ℝ => p.1 * p.2) =
      (∫ y, y ^ n ∂ρ) * (∫ y, y ^ n ∂σ) := by
  calc
    _ = ∫ p : ℝ × ℝ, (p.1 * p.2) ^ n ∂ρ.prod σ :=
      integral_map (measurable_fst.mul measurable_snd).aemeasurable
        (measurable_id.pow_const n).aestronglyMeasurable
    _ = ∫ p : ℝ × ℝ, p.1 ^ n * p.2 ^ n ∂ρ.prod σ := by
      apply integral_congr_ae
      filter_upwards with p
      rw [mul_pow]
    _ = _ := integral_prod_mul (fun y : ℝ => y ^ n) (fun y : ℝ => y ^ n)

private lemma geomY_moment_measure_terminal {l b : ℝ} (hl : 1 < l)
    (hb : 0 < b) (hb1 : b ≤ 1) (n : ℕ) :
    ∫ y, y ^ n ∂geomY l b = b / (l ^ n - 1 + b) :=
  geomY_moment_closed hl hb hb1 n

private lemma ae_mul_map_Icc_terminal {ρ σ : Measure ℝ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] {l : ℝ} (hl : 1 < l)
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc (0 : ℝ) (1 / l))
    (hσ : ∀ᵐ y ∂σ, y ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂((ρ.prod σ).map fun p : ℝ × ℝ => p.1 * p.2),
      z ∈ Set.Icc (0 : ℝ) (1 / l) := by
  apply (ae_map_iff (measurable_fst.mul measurable_snd).aemeasurable
    measurableSet_Icc).2
  filter_upwards [
    (Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := σ)).ae hρ,
    (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := σ)).ae hσ] with p hp hq
  constructor
  · exact mul_nonneg hp.1 hq.1
  · calc
      p.1 * p.2 ≤ (1 / l) * p.2 := mul_le_mul_of_nonneg_right hp.2 hq.1
      _ ≤ (1 / l) * 1 := mul_le_mul_of_nonneg_left hq.2 (by positivity)
      _ = 1 / l := by ring

private lemma pBr_le_one_terminal (h : OffspringHyp μ) : pBr μ ≤ 1 := by
  have hp1 : 0 ≤ p1 μ := measureReal_nonneg
  linarith [p1_add_pBr h]

private lemma lawL_xS_eq_geomY_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) : lawL (xS μ l) (l - 1) = geomY l (pBr μ) := by
  rw [lawL_eq_geomY]
  have ha : 0 < l - 1 := by linarith
  have hpx : (l - 1) * xS μ l = pBr μ := by
    rw [xS]
    field_simp [ha.ne']
  rw [show 1 + (l - 1) = l by ring, hpx]

private lemma integral_Wlaw_moment_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    ∫ w, w ^ n ∂(splitLaw μ).map (Wt l) = etaW μ l n := by
  calc
    _ = ∫ T, (Wt l T) ^ n ∂splitLaw μ :=
      integral_map (measurable_Wt l).aemeasurable
        (measurable_id.pow_const n).aestronglyMeasurable
    _ = _ := by rfl

private lemma Ylaw_moment_split_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    ∫ y, y ^ n ∂Ylaw μ l =
      (pBr μ / (l ^ n - 1 + pBr μ)) * etaW μ l n := by
  letI : IsProbabilityMeasure (splitLaw μ) := splitLaw_prob h
  have hp := pBr_pos h
  have hp1 := pBr_le_one_terminal h
  letI : IsProbabilityMeasure (geomY l (pBr μ)) :=
    geomY_probability_closed hl hp hp1
  letI : IsProbabilityMeasure ((splitLaw μ).map (Wt l)) := by infer_instance
  have hGmem : ∀ᵐ y ∂geomY l (pBr μ), y ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [geomY_ae_Icc hl hp] with y hy
    exact ⟨hy.1, hy.2.trans ((div_le_one (by linarith : 0 < l)).2 (by linarith))⟩
  have hWmem : ∀ᵐ y ∂(splitLaw μ).map (Wt l), y ∈ Set.Icc (0 : ℝ) 1 := by
    apply (ae_map_iff (measurable_Wt l).aemeasurable measurableSet_Icc).2
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    exact ⟨hT.1.le, hT.2.le⟩
  rw [Ylaw_eq_prod h hl hlm]
  rw [integral_mul_pow_map_prod_terminal hGmem hWmem n,
    geomY_moment_closed hl hp hp1 n,
    integral_Wlaw_moment_terminal h hl hlm n]

private lemma yPlus_moment_split_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) {d₀ η₀ : ℝ} (hd₀ : 0 ≤ d₀) (hd₀η₀ : d₀ ≤ η₀)
    (hη₀ : η₀ ≤ 1)
    (n : ℕ) :
    ∫ y, y ^ n ∂yPlus (xS μ l) (l - 1) d₀ η₀ =
      (pBr μ / (l ^ n - 1 + pBr μ)) *
        (1 - d₀ * ∑ i ∈ Finset.range n, (1 - η₀) ^ i) := by
  letI : IsProbabilityMeasure (geomY l (pBr μ)) :=
    geomY_probability_closed hl (pBr_pos h) (pBr_le_one_terminal h)
  letI : IsProbabilityMeasure (wPlus d₀ η₀) :=
    wPlus_probability hd₀ hd₀η₀ hη₀
  have hlaw := lawL_xS_eq_geomY_terminal h hl
  letI : IsProbabilityMeasure (lawL (xS μ l) (l - 1)) := by
    rw [hlaw]
    infer_instance
  have hLmem : ∀ᵐ y ∂lawL (xS μ l) (l - 1), y ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hlaw]
    filter_upwards [geomY_ae_Icc hl (pBr_pos h)] with y hy
    exact ⟨hy.1, hy.2.trans ((div_le_one (by linarith : 0 < l)).2 (by linarith))⟩
  have hWmem := wPlus_ae_Icc hd₀ hd₀η₀ hη₀
  have hmom := integral_mul_pow_map_prod_terminal hLmem hWmem n
  rw [yPlus, hmom, hlaw, geomY_moment_closed hl (pBr_pos h)
    (pBr_le_one_terminal h) n, wPlus_moment hd₀ hd₀η₀ hη₀ n]

private theorem Ylaw_moment_le_yPlus_terminal (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) {d₀ η₀ : ℝ}
    (hd₀ : 0 ≤ d₀) (hd₀d : d₀ ≤ dW μ l)
    (hηη₀ : etaD μ l ≤ η₀) (hη₀ : η₀ ≤ 1) (n : ℕ) :
    ∫ y, y ^ n ∂Ylaw μ l ≤
      ∫ y, y ^ n ∂yPlus (xS μ l) (l - 1) d₀ η₀ := by
  rw [Ylaw_moment_split_terminal h hl hlm n,
    yPlus_moment_split_terminal h hl hd₀
      (hd₀d.trans ((dW_le_etaD h hl hlm).1.trans hηη₀)) hη₀ n]
  have hp := pBr_pos h
  have hden : 0 < l ^ n - 1 + pBr μ := by
    have hpw : 1 ≤ l ^ n := one_le_pow₀ (by linarith : 1 ≤ l)
    linarith
  have hfactor : 0 ≤ pBr μ / (l ^ n - 1 + pBr μ) := div_nonneg hp.le hden.le
  have hmoment : etaW μ l n ≤
      1 - d₀ * ∑ i ∈ Finset.range n, (1 - η₀) ^ i := by
    change (∫ T, Wt l T ^ n ∂splitLaw μ) ≤ _
    rw [← wPlus_moment hd₀
      (hd₀d.trans ((dW_le_etaD h hl hlm).1.trans hηη₀)) hη₀ n]
    exact Wt_moment_le_wPlus_terminal h hl hlm hd₀ hd₀d hηη₀ hη₀ n
  exact mul_le_mul_of_nonneg_left hmoment hfactor

private lemma ZY_pos_of_mean_terminal {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {l : ℝ} (hl : 1 < l)
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc (0 : ℝ) (1 / l))
    (hm : 0 < ∫ y, y ∂ρ) : 0 < ZY l ρ ρ := by
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := ρ)).ae hρ
  have hsnd := (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := ρ)).ae hρ
  have hZint : Integrable
      (fun p : ℝ × ℝ =>
        (p.1 * (1 - p.2) + p.2 * (1 - l * p.1)) / (1 - l * p.1 * p.2))
      (ρ.prod ρ) := by
    apply integrable_bounded_ae_terminal (by fun_prop)
    let C : ℝ := 2 * l / (l - 1)
    filter_upwards [hfst, hsnd] with p hp hq
    have hl0 : 0 < l := by linarith
    have hy0 := hp.1
    have hy1 := hp.2
    have ht0 := hq.1
    have ht1 := hq.2
    have hly : l * p.1 ≤ 1 := by
      calc
        l * p.1 ≤ l * (1 / l) := mul_le_mul_of_nonneg_left hy1 (by linarith)
        _ = 1 := by field_simp
    have hprod : l * p.1 * p.2 ≤ 1 / l := by
      calc
        l * p.1 * p.2 ≤ 1 * p.2 := mul_le_mul_of_nonneg_right hly ht0
        _ = p.2 := by ring
        _ ≤ 1 / l := ht1
    have hdenpos : 0 < 1 - l * p.1 * p.2 := by
      have hlt : 1 / l < 1 := (div_lt_one hl0).2 hl
      linarith
    have hdenlo : (l - 1) / l ≤ 1 - l * p.1 * p.2 := by
      have heq : (l - 1) / l = 1 - 1 / l := by field_simp
      rw [heq]
      linarith
    have hdenle : 1 - l * p.1 * p.2 ≤ 1 := by
      have hnonneg : 0 ≤ l * p.1 * p.2 :=
        mul_nonneg (mul_nonneg (by linarith) hp.1) hq.1
      linarith
    have hnum0 : 0 ≤ p.1 * (1 - p.2) + p.2 * (1 - l * p.1) := by
      have h1 : 0 ≤ 1 - p.2 := by
        have hp2 : p.2 ≤ 1 := ht1.trans ((div_le_one hl0).2 (by linarith))
        linarith
      have h2 : 0 ≤ 1 - l * p.1 := by linarith
      exact add_nonneg (mul_nonneg hy0 h1) (mul_nonneg ht0 h2)
    have hnumle : p.1 * (1 - p.2) + p.2 * (1 - l * p.1) ≤ 2 := by
      have hp2 : p.2 ≤ 1 := ht1.trans ((div_le_one hl0).2 (by linarith))
      have h1 : p.1 * (1 - p.2) ≤ 1 := by nlinarith [hy1, hp2]
      have h2 : p.2 * (1 - l * p.1) ≤ 1 := by nlinarith [ht1, hly]
      linarith
    change ‖(p.1 * (1 - p.2) + p.2 * (1 - l * p.1)) /
      (1 - l * p.1 * p.2)‖ ≤ C
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hnum0, abs_of_pos hdenpos]
    apply (div_le_iff₀ hdenpos).2
    calc
      p.1 * (1 - p.2) + p.2 * (1 - l * p.1) ≤ 2 := hnumle
      _ = C * ((l - 1) / l) := by dsimp [C]; field_simp
      _ ≤ C * (1 - l * p.1 * p.2) :=
        mul_le_mul_of_nonneg_left hdenlo (by dsimp [C]; positivity)
  have hlin : Integrable (fun p : ℝ × ℝ => (1 - 1 / l) * p.1) (ρ.prod ρ) := by
    apply integrable_bounded_ae_terminal (by fun_prop)
    filter_upwards [hfst] with p hp
    have hcoef : 0 ≤ 1 - 1 / l := by
      have hl0 : 0 < l := by linarith
      have hlt : 1 / l < 1 := (div_lt_one hl0).2 hl
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoef,
      abs_of_nonneg hp.1]
    calc
      (1 - 1 / l) * p.1 ≤ (1 - 1 / l) * (1 / l) :=
        mul_le_mul_of_nonneg_left hp.2 hcoef
      _ ≤ 1 := by
        have hratio : 0 ≤ 1 / l := by positivity
        have hratio1 : 1 / l ≤ 1 := (div_le_one (by linarith : 0 < l)).2 (by linarith)
        have hcoef1 : 1 - 1 / l ≤ 1 := by linarith
        calc
          (1 - 1 / l) * (1 / l) ≤ 1 * (1 / l) :=
            mul_le_mul_of_nonneg_right hcoef1 hratio
          _ ≤ 1 := by simpa using hratio1
  have hpoint : ∀ᵐ p ∂ρ.prod ρ,
      (1 - 1 / l) * p.1 ≤
        (p.1 * (1 - p.2) + p.2 * (1 - l * p.1)) / (1 - l * p.1 * p.2) := by
    filter_upwards [hfst, hsnd] with p hp hq
    have hl0 : 0 < l := by linarith
    have hly : l * p.1 ≤ 1 := by
      calc
        l * p.1 ≤ l * (1 / l) := mul_le_mul_of_nonneg_left hp.2 (by linarith)
        _ = 1 := by field_simp
    have hdenpos : 0 < 1 - l * p.1 * p.2 := by
      have hprod : l * p.1 * p.2 ≤ 1 / l := by
        calc
          l * p.1 * p.2 ≤ 1 * p.2 := mul_le_mul_of_nonneg_right hly hq.1
          _ = p.2 := by ring
          _ ≤ 1 / l := hq.2
      have hlt : 1 / l < 1 := (div_lt_one hl0).2 hl
      linarith
    have hnum0 : 0 ≤ p.1 * (1 - p.2) + p.2 * (1 - l * p.1) := by
      have hp2 : p.2 ≤ 1 := hq.2.trans ((div_le_one hl0).2 (by linarith))
      exact add_nonneg (mul_nonneg hp.1 (by linarith))
        (mul_nonneg hq.1 (by linarith))
    have hnumlo : (1 - 1 / l) * p.1 ≤
        p.1 * (1 - p.2) + p.2 * (1 - l * p.1) := by
      have hp2 : p.2 ≤ 1 / l := hq.2
      have hleft : (1 - 1 / l) * p.1 ≤ p.1 * (1 - p.2) := by nlinarith [hp.1]
      have hright : 0 ≤ p.2 * (1 - l * p.1) := by
        exact mul_nonneg hq.1 (by linarith)
      linarith
    have hdenle : 1 - l * p.1 * p.2 ≤ 1 := by
      have hnonneg : 0 ≤ l * p.1 * p.2 :=
        mul_nonneg (mul_nonneg (by linarith) hp.1) hq.1
      linarith
    calc
      (1 - 1 / l) * p.1 ≤ p.1 * (1 - p.2) + p.2 * (1 - l * p.1) := hnumlo
      _ ≤ _ := (le_div_iff₀ hdenpos).2 (by
        calc
          (p.1 * (1 - p.2) + p.2 * (1 - l * p.1)) *
              (1 - l * p.1 * p.2) ≤
            (p.1 * (1 - p.2) + p.2 * (1 - l * p.1)) * 1 :=
            mul_le_mul_of_nonneg_left hdenle hnum0
          _ = p.1 * (1 - p.2) + p.2 * (1 - l * p.1) := by ring)
  have hmeanInt : Integrable (fun y : ℝ => y) ρ := by
    apply integrable_bounded_ae_terminal measurable_id.aemeasurable
    filter_upwards [hρ] with y hy
    change ‖y‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg hy.1]
    exact hy.2.trans ((div_le_one (by linarith : 0 < l)).2 (by linarith))
  have hprodFirst :
      (∫ p : ℝ × ℝ, p.1 ∂ρ.prod ρ) = ∫ y, y ∂ρ := by
    simpa using (integral_fun_fst (μ := ρ) (ν := ρ) (fun y : ℝ => y))
  have hcoefpos : 0 < 1 - 1 / l := by
    have hl0 : 0 < l := by linarith
    have hlt : 1 / l < 1 := (div_lt_one hl0).2 hl
    linarith
  have hpos : 0 < (1 - 1 / l) * ∫ y, y ∂ρ := mul_pos hcoefpos hm
  have hZle := integral_mono_ae hlin hZint hpoint
  unfold ZY
  calc
    0 < (1 - 1 / l) * ∫ y, y ∂ρ := hpos
    _ = ∫ p : ℝ × ℝ, (1 - 1 / l) * p.1 ∂ρ.prod ρ := by
      rw [integral_const_mul, hprodFirst]
    _ ≤ ∫ p : ℝ × ℝ,
        (p.1 * (1 - p.2) + p.2 * (1 - l * p.1)) /
          (1 - l * p.1 * p.2) ∂ρ.prod ρ := hZle

private lemma Hw_integral_swap_terminal {l w : ℝ} {ρ ξ : Measure ℝ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ξ] :
    ∫ p, Hw l w p.1 p.2 ∂ρ.prod ξ = ∫ p, Hw l w p.1 p.2 ∂ξ.prod ρ := by
  calc
    _ = ∫ p, Hw l w p.2 p.1 ∂ρ.prod ξ := by
      apply integral_congr_ae
      filter_upwards with p
      unfold Hw
      ring
    _ = _ := integral_prod_swap (μ := ξ) (ν := ρ)
      (fun p => Hw l w p.1 p.2)

private lemma rTwoPoint_eq_NY_ZY_terminal (x l d₀ η₀ : ℝ) :
    rTwoPoint x (l - 1) d₀ η₀ =
      NY l (yPlus x (l - 1) d₀ η₀) (yPlus x (l - 1) d₀ η₀) /
        ((l - 1) * ZY l (yPlus x (l - 1) d₀ η₀)
          (yPlus x (l - 1) d₀ η₀)) := by
  unfold rTwoPoint kernelN kernelZ NY ZY
  simp only [show 1 + (l - 1) = l by ring]

/-- Lemma 5.4 (`lem:terminal-speed`): replacing the first-split law by its two-point
majorant bounds the actual speed ratio. -/
theorem rr_le_twoPoint (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {d₀ η₀ : ℝ}
    (hd : 0 ≤ d₀ ∧ d₀ ≤ dW μ l)
    (hη : etaD μ l ≤ η₀ ∧ η₀ ≤ 1) :
    rr μ l ≤ rTwoPoint (xS μ l) (l - 1) d₀ η₀ := by
  let ρ := yPlus (xS μ l) (l - 1) d₀ η₀
  let v : ℝ := Speed.speedValue μ l
  have hGeom := lawL_xS_eq_geomY_terminal h hl
  letI : IsProbabilityMeasure (geomY l (pBr μ)) :=
    geomY_probability_closed hl (pBr_pos h) (pBr_le_one_terminal h)
  have hLawProb : IsProbabilityMeasure (lawL (xS μ l) (l - 1)) := by
    rw [hGeom]
    infer_instance
  letI : IsProbabilityMeasure (lawL (xS μ l) (l - 1)) := hLawProb
  have hWplusProb : IsProbabilityMeasure (wPlus d₀ η₀) :=
    wPlus_probability hd.1 (hd.2.trans ((dW_le_etaD h hl hlm).1.trans hη.1)) hη.2
  letI : IsProbabilityMeasure (wPlus d₀ η₀) := hWplusProb
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ, yPlus]
    infer_instance
  letI : IsProbabilityMeasure (Ylaw μ l) := by
    unfold Ylaw
    infer_instance

  have hYmem : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc (0 : ℝ) (1 / l) :=
    (ae_Ylaw_mem μ h hl hlm).mono fun y hy => ⟨hy.1.le, hy.2.le⟩
  have hLmem : ∀ᵐ y ∂lawL (xS μ l) (l - 1),
      y ∈ Set.Icc (0 : ℝ) (1 / l) := by
    rw [hGeom]
    filter_upwards [geomY_ae_Icc hl (pBr_pos h)] with y hy
    exact ⟨hy.1, hy.2⟩
  have hWmem := wPlus_ae_Icc hd.1
    (hd.2.trans ((dW_le_etaD h hl hlm).1.trans hη.1)) hη.2
  have hρmem : ∀ᵐ y ∂ρ, y ∈ Set.Icc (0 : ℝ) (1 / l) := by
    dsimp [ρ, yPlus]
    exact ae_mul_map_Icc_terminal hl hLmem hWmem

  have hmeanY : ∫ y, y ∂Ylaw μ l = muY μ l := by
    calc
      ∫ y, y ∂Ylaw μ l = ∫ T, Yt l T ∂GW μ := by
        unfold Ylaw
        exact integral_map (measurable_Yt l).aemeasurable
          measurable_id.aestronglyMeasurable
      _ = muY μ l := by rfl
  have hmoment := Ylaw_moment_le_yPlus_terminal h hl hlm hd.1 hd.2 hη.1 hη.2 1
  have hmeanCmp : ∫ y, y ∂Ylaw μ l ≤ ∫ y, y ∂ρ := by
    simpa only [pow_one, ρ] using hmoment
  have hmeanYpos : 0 < ∫ y, y ∂Ylaw μ l := by
    rw [hmeanY]
    exact (muY_mem μ h hl hlm).1
  have hmeanρpos : 0 < ∫ y, y ∂ρ := hmeanYpos.trans_le hmeanCmp
  have hmeanρInt : Integrable (fun y : ℝ => y) ρ := by
    apply integrable_bounded_ae_terminal measurable_id.aemeasurable
    filter_upwards [hρmem] with y hy
    change ‖y‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg hy.1]
    exact hy.2.trans ((div_le_one (by linarith : 0 < l)).2 (by linarith))
  have hmeanρle : ∫ y, y ∂ρ ≤ 1 / l := by
    calc
      ∫ y, y ∂ρ ≤ ∫ _y : ℝ, 1 / l ∂ρ := by
        apply integral_mono_ae hmeanρInt (integrable_const _)
        filter_upwards [hρmem] with y hy
        exact hy.2
      _ = 1 / l := by simp [Measure.real]
  have hmeanρlt : ∫ y, y ∂ρ < 1 := by
    exact hmeanρle.trans_lt ((div_lt_one (by linarith : 0 < l)).2 hl)
  have hmeanYlt : muY μ l < 1 := by
    exact (muY_mem μ h hl hlm).2.trans
      ((div_lt_one (by linarith : 0 < l)).2 hl)
  have hratioMono :
      (l - 1) * muY μ l / (1 - muY μ l) ≤
        (l - 1) * (∫ y, y ∂ρ) / (1 - ∫ y, y ∂ρ) := by
    have hdenY : 0 < 1 - muY μ l := sub_pos.mpr hmeanYlt
    have hdenρ : 0 < 1 - ∫ y, y ∂ρ := sub_pos.mpr hmeanρlt
    have hdiv : muY μ l / (1 - muY μ l) ≤
        (∫ y, y ∂ρ) / (1 - ∫ y, y ∂ρ) := by
      rw [div_le_div_iff₀ hdenY hdenρ]
      have hmuCmp : muY μ l ≤ ∫ y, y ∂ρ := by
        rw [← hmeanY]
        exact hmeanCmp
      nlinarith [hmuCmp]
    calc
      (l - 1) * muY μ l / (1 - muY μ l) =
          (l - 1) * (muY μ l / (1 - muY μ l)) := by rw [mul_div_assoc]
      _ ≤ (l - 1) * ((∫ y, y ∂ρ) / (1 - ∫ y, y ∂ρ)) :=
        mul_le_mul_of_nonneg_left hdiv (by linarith)
      _ = (l - 1) * (∫ y, y ∂ρ) / (1 - ∫ y, y ∂ρ) := by
        rw [mul_div_assoc]

  have hvpos : 0 < v := by
    dsimp [v]
    rw [Speed.speedValue_of_pos μ (by linarith : 0 < l)]
    exact div_pos (Nval_pos μ h (by linarith) hlm)
      (Speed.Zval_pos μ (by linarith) h hlm)
  have hvCeiling : v ≤ (l - 1) * muY μ l / (1 - muY μ l) := by
    dsimp [v]
    exact speed_le_peff_ratio μ h hl hlm
  have hvρ : v ≤ (l - 1) * (∫ y, y ∂ρ) / (1 - ∫ y, y ∂ρ) :=
    hvCeiling.trans hratioMono

  have hmom : ∀ n ≥ 1, ∫ y, y ^ n ∂Ylaw μ l ≤ ∫ y, y ^ n ∂ρ := by
    intro n hn
    exact Ylaw_moment_le_yPlus_terminal h hl hlm hd.1 hd.2 hη.1 hη.2 n
  have hcoeffY : ∀ n : ℕ, 0 ≤ ∫ t, t ^ n * Bw l v t ∂Ylaw μ l := by
    intro n
    apply kernel_coeff_nonneg hl hYmem v hmeanYpos
    exact ⟨hvpos.le, by rw [hmeanY]; exact hvCeiling⟩
  have hcoeffρ : ∀ n : ℕ, 0 ≤ ∫ t, t ^ n * Bw l v t ∂ρ := by
    intro n
    apply kernel_coeff_nonneg hl hρmem v hmeanρpos
    exact ⟨hvpos.le, hvρ⟩

  have h₁ :
      ∫ p, Hw l v p.1 p.2 ∂(Ylaw μ l).prod (Ylaw μ l) ≤
        ∫ p, Hw l v p.1 p.2 ∂ρ.prod (Ylaw μ l) :=
    kernel_compare hl hYmem hρmem hYmem hmom v hcoeffY
  have h₂ :
      ∫ p, Hw l v p.1 p.2 ∂(Ylaw μ l).prod ρ ≤
        ∫ p, Hw l v p.1 p.2 ∂ρ.prod ρ :=
    kernel_compare hl hYmem hρmem hρmem hmom v hcoeffρ
  have hcomp :
      ∫ p, Hw l v p.1 p.2 ∂(Ylaw μ l).prod (Ylaw μ l) ≤
        ∫ p, Hw l v p.1 p.2 ∂ρ.prod ρ :=
    h₁.trans ((Hw_integral_swap_terminal (l := l) (w := v)
      (ρ := ρ) (ξ := Ylaw μ l)).trans_le h₂)
  have hzero :
      NY l (Ylaw μ l) (Ylaw μ l) - v * ZY l (Ylaw μ l) (Ylaw μ l) = 0 := by
    rw [← Nval_eq_NY μ h hl hlm, ← Zval_eq_ZY μ h hl hlm]
    dsimp [v]
    rw [Speed.speedValue_of_pos μ (by linarith : 0 < l)]
    have hZpos := Speed.Zval_pos μ (by linarith : 0 < l) h hlm
    field_simp [hZpos.ne'] <;> ring
  have hcompNY : 0 ≤ NY l ρ ρ - v * ZY l ρ ρ := by
    rw [← NY_sub_ZY l v hl hYmem hYmem,
      ← NY_sub_ZY l v hl hρmem hρmem] at hcomp
    rw [hzero] at hcomp
    exact hcomp
  have hZρpos : 0 < ZY l ρ ρ := ZY_pos_of_mean_terminal hl hρmem hmeanρpos
  have hvle : v ≤ NY l ρ ρ / ZY l ρ ρ := by
    apply (le_div_iff₀ hZρpos).2
    exact sub_nonneg.mp hcompNY
  have ha : 0 < l - 1 := by linarith
  have hrr : rr μ l = v / (l - 1) := by
    unfold rr
    rw [← speedValue_eq_speedValueProv μ l]
  calc
    rr μ l = v / (l - 1) := hrr
    _ ≤ (NY l ρ ρ / ZY l ρ ρ) / (l - 1) :=
      div_le_div_of_nonneg_right hvle ha.le
    _ = NY l ρ ρ / ((l - 1) * ZY l ρ ρ) := by
      rw [div_div]
      congr 1
      ring
    _ = rTwoPoint (xS μ l) (l - 1) d₀ η₀ := by
      symm
      simpa [ρ] using rTwoPoint_eq_NY_ZY_terminal
        (xS μ l) l d₀ η₀

end LPPMonotonicityProof.Analytic
