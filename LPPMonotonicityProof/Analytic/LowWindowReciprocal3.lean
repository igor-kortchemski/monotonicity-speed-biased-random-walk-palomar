module

public import LPPMonotonicityProof.Analytic.LowWindowReciprocal2
import all LPPMonotonicityProof.Analytic.LowWindowReciprocal2
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Reciprocal-escape estimates near bias one

This module proves the last two reciprocal-escape estimates of the proof of
Theorem 4.3 (`thm:low-window`), the lower bound on `Δ` and the bound
`2 E[p/τ] - p ≤ d`, and collects the five estimates in `lowWindow_reciprocal`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ] {l : ℝ}

lemma lowWindow_reciprocal_scalar {s t : ℝ} (hs₀ : 0 ≤ s) (hs : s ≤ 1 / 8)
    (hst : s ≤ t) (ht : t ≤ 1 / 3) :
    4 * (1 - s) * t ^ 2 ≥ s ^ 2 * (1 + 2 * t) := by
  have hts : 0 ≤ t + s := by linarith
  have hsq : s ^ 2 ≤ t ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hst) hts]
  calc
    s ^ 2 * (1 + 2 * t) ≤ s ^ 2 * (4 * (1 - s)) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    _ ≤ 4 * (1 - s) * t ^ 2 := by
      rw [mul_comm (s ^ 2)]
      exact mul_le_mul_of_nonneg_left hsq (by linarith)

/-- Jensen for the two independent split responses at fixed prefix lengths.
The coefficients are the two fixed powers of the bias. -/
lemma lowWindow_conditional_abs {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {W : Ω → ℝ}
    (hW : Integrable W ν) (a b : ℝ) :
    |(a - b) * ∫ z, W z ∂ν| ≤
      ∫ z, |a * W z.1 - b * W z.2| ∂ν.prod ν := by
  have h₁ := (hW.comp_fst ν).const_mul a
  have h₂ := (hW.comp_snd ν).const_mul b
  have he : (∫ z, a * W z.1 - b * W z.2 ∂ν.prod ν) =
      (a - b) * ∫ z, W z ∂ν := by
    rw [integral_sub h₁ h₂]
    rw [integral_const_mul, integral_const_mul]
    have hf := integral_prod_mul (μ := ν) (ν := ν) W (fun _ => (1 : ℝ))
    have hg := integral_prod_mul (μ := ν) (ν := ν) (fun _ => (1 : ℝ)) W
    simp only [mul_one, one_mul, integral_const, probReal_univ, smul_eq_mul] at hf hg
    rw [hf, hg]
    ring
  rw [← he]
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (μ := ν.prod ν) (f := fun z => a * W z.1 - b * W z.2))

/-! ### The geometric prefix and reciprocal escape -/

private noncomputable def prefixParam (h : OffspringHyp μ) : unitInterval :=
  ⟨pBr μ, (pBr_pos h).le, by
    have hq : 0 ≤ p1 μ := ENNReal.toReal_nonneg
    linarith [p1_add_pBr h]⟩

private lemma prefixParam_ne_zero (h : OffspringHyp μ) : prefixParam h ≠ 0 := by
  intro he
  have hp := congrArg Subtype.val he
  exact (pBr_pos h).ne' hp

private lemma prefix_product_law (h : OffspringHyp μ) :
    MeasurePreserving (fun T => (prefixLen T, splitTree T)) (GW μ)
      ((geometricMeasure (prefixParam h)).prod (splitLaw μ)) := by
  have hm := measurable_prefixLen.prodMk measurable_splitTree
  refine ⟨hm, ?_⟩
  let := splitLaw_prob h
  ext B hB
  let F : ℕ → Tree → ℝ≥0∞ := fun n T => B.indicator (fun _ => 1) (n - 1, T)
  have hf : Measurable (Function.uncurry F) :=
    (measurable_const.indicator hB).comp
      ((measurable_fst.sub_const 1).prodMk measurable_snd)
  have hleft := lintegral_firstSplit h hf
  change (∫⁻ T, B.indicator (fun _ => 1) (Gt T - 1, splitTree T) ∂GW μ) = _ at hleft
  simp only [Gt, Nat.add_sub_cancel] at hleft
  rw [Measure.map_apply hm hB, ← lintegral_indicator_one (hm hB)]
  change (∫⁻ T, B.indicator (fun _ => 1) (prefixLen T, splitTree T) ∂GW μ) = _
  rw [hleft, ← lintegral_indicator_one hB]
  change _ = ∫⁻ z, B.indicator (fun _ => (1 : ℝ≥0∞)) z
      ∂(geometricMeasure (prefixParam h)).prod (splitLaw μ)
  rw [lintegral_prod _ (measurable_const.indicator hB).aemeasurable,
    geometricMeasure_eq (prefixParam_ne_zero h), lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [lintegral_smul_measure, lintegral_dirac]
  have hq : 1 - (prefixParam h : ℝ) = p1 μ := by
    change 1 - pBr μ = p1 μ
    linarith [p1_add_pBr h]
  simp only [F, Nat.add_sub_cancel, hq, smul_eq_mul]
  rfl

private lemma ae_RR_prefix (h : OffspringHyp μ) (hl : 1 < l) (hlm : l < mean μ) :
    ∀ᵐ T ∂GW μ, RR μ l T + xS μ l =
      l ^ (prefixLen T + 1) * (xS μ l / Wt l (splitTree T)) := by
  filter_upwards [ae_escape_pos h (by linarith : 0 < l) hlm, ae_split_degree h] with T hT hd
  have hy := Yt_eq_prefix hl T hd
  have hl0 : l ≠ 0 := by linarith
  have hl1 : l - 1 ≠ 0 := by linarith
  have hs : 0 < l - 1 + escape l T := by linarith
  have hY : Yt l T ≠ 0 := div_ne_zero hT.ne' hs.ne'
  have hW : Wt l (splitTree T) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hy
    exact hY hy
  have he : RR μ l T + xS μ l = xS μ l / Yt l T := by
    unfold RR xS Yt
    field_simp [hl1, hT.ne', hs.ne']
  rw [he, hy]
  simp only [Gt, zpow_neg, zpow_natCast]
  field_simp [hW, hl0]

private lemma ae_RR_ge_prefix (h : OffspringHyp μ) (hl : 1 < l) (hlm : l < mean μ) :
    ∀ᵐ T ∂GW μ, pBr μ * ((prefixLen T : ℝ) + 1) ≤ RR μ l T := by
  have hl0 : 0 < l := by linarith
  have hl1 : 0 < l - 1 := by linarith
  have hx : 0 < xS μ l := div_pos (pBr_pos h) hl1
  let := splitLaw_prob h
  have hm := (prefix_product_law h).quasiMeasurePreserving.ae
    ((measurePreserving_snd (μ := geometricMeasure (prefixParam h))
      (ν := splitLaw μ)).quasiMeasurePreserving.ae (ae_Wt_mem h hl hlm))
  filter_upwards [ae_RR_prefix h hl hlm, hm] with T he hw
  change Wt l (splitTree T) ∈ Set.Ioo 0 1 at hw
  have hratio : xS μ l ≤ xS μ l / Wt l (splitTree T) :=
    (le_div_iff₀ hw.1).2 (by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hw.2.le)])
  have hpow := one_add_mul_sub_le_pow (a := l) (by linarith) (prefixLen T + 1)
  have heq : xS μ l * (l - 1) = pBr μ := by
    unfold xS
    field_simp
  have h₁ := mul_le_mul_of_nonneg_right hpow hx.le
  have h₂ := mul_le_mul_of_nonneg_left hratio (pow_nonneg hl0.le (prefixLen T + 1))
  rw [← he] at h₂
  push_cast at h₁
  calc
    pBr μ * ((prefixLen T : ℝ) + 1) =
        (1 + ((prefixLen T : ℝ) + 1) * (l - 1)) * xS μ l - xS μ l := by
      rw [← heq]
      ring
    _ ≤ RR μ l T := by linarith

/-! ### Cauchy–Schwarz for the two-copy dispersion -/

private lemma lowWindow_cauchy (h : OffspringHyp μ) (hl : 1 < l) (hlm : l < mean μ)
    (hs : sS μ l ≤ 1 / 8) :
    let M := ∫ T, RR μ l T ∂GW μ
    let Δ := (1 / 2) * ∫ z, DD μ l z ∂(GW μ).prod (GW μ)
    (∫ z, |RR μ l z.1 - RR μ l z.2| ∂(GW μ).prod (GW μ)) ^ 2 ≤ 4 * M * Δ := by
  intro M Δ
  let ν := (GW μ).prod (GW μ)
  let U : Tree × Tree → ℝ := fun z => RR μ l z.1 + RR μ l z.2
  let V := DD μ l
  let f : Tree × Tree → ℝ := fun z => √(U z)
  let g : Tree × Tree → ℝ := fun z => √(V z)
  have hr := integrable_RR h hl hlm hs
  have hiU : Integrable U ν := (hr.comp_fst _).add (hr.comp_snd _)
  have hiV : Integrable V ν := integrable_DD h hl hlm hs
  have hmeasU : Measurable U :=
    ((measurable_RR μ l).comp measurable_fst).add ((measurable_RR μ l).comp measurable_snd)
  have hmeasV : Measurable V := measurable_DD μ l
  have hsqU : (fun z => f z ^ 2) =ᵐ[ν] U := by
    filter_upwards [ae_RR_pos_prod h hl hlm] with z hz
    exact Real.sq_sqrt (add_nonneg hz.1.le hz.2.le)
  have hsqV : (fun z => g z ^ 2) =ᵐ[ν] V := by
    filter_upwards [ae_RR_pos_prod h hl hlm] with z hz
    exact Real.sq_sqrt (DD_nonneg hz.1.le hz.2.le)
  have hf := (memLp_two_iff_integrable_sq hmeasU.sqrt.aestronglyMeasurable).2
    (hiU.congr hsqU.symm)
  have hg := (memLp_two_iff_integrable_sq hmeasV.sqrt.aestronglyMeasurable).2
    (hiV.congr hsqV.symm)
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ν) (f := f) (g := g)
    (p := 2) (q := 2) (by norm_num [Real.holderConjugate_iff])
    (ae_of_all _ fun z => Real.sqrt_nonneg _) (ae_of_all _ fun z => Real.sqrt_nonneg _)
    (by simpa using hf) (by simpa using hg)
  have he : (fun z => f z * g z) =ᵐ[ν] fun z => |RR μ l z.1 - RR μ l z.2| := by
    filter_upwards [ae_RR_pos_prod h hl hlm] with z hz
    change √(RR μ l z.1 + RR μ l z.2) * √(DD μ l z) = _
    rw [← Real.sqrt_mul (add_nonneg hz.1.le hz.2.le)]
    unfold DD
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (add_pos hz.1 hz.2).ne',
      Real.sqrt_sq_eq_abs]
  rw [integral_congr_ae he] at hc
  simp only [Real.rpow_two] at hc
  rw [integral_congr_ae hsqU, integral_congr_ae hsqV, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow] at hc
  have hnon : 0 ≤ ∫ z, |RR μ l z.1 - RR μ l z.2| ∂ν :=
    integral_nonneg fun _ => abs_nonneg _
  have hU : 0 ≤ ∫ z, U z ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_RR_pos_prod h hl hlm] with z hz
    exact add_nonneg hz.1.le hz.2.le
  have hV : 0 ≤ ∫ z, V z ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_RR_pos_prod h hl hlm] with z hz
    exact DD_nonneg hz.1.le hz.2.le
  have hcs := pow_le_pow_left₀ hnon hc 2
  rw [mul_pow, Real.sq_sqrt hU, Real.sq_sqrt hV] at hcs
  have hIU : (∫ z, U z ∂ν) = 2 * M := by
    dsimp only [U, ν, M]
    rw [integral_add (hr.comp_fst _) (hr.comp_snd _),
      integral_RR_fst h hl hlm hs, integral_RR_snd h hl hlm hs]
    ring
  rw [hIU] at hcs
  calc
    _ ≤ _ := hcs
    _ = 4 * M * Δ := by dsimp only [V, Δ, ν]; ring

private lemma lowWindow_delta_scalar {s q M A Δ L : ℝ}
    (hs : 0 ≤ s) (hs₁ : s ≤ 1 / 8) (hq : 0 ≤ q) (hM : 0 < M)
    (hA : 3 / 8 ≤ A) (hMA : M ≤ 1 / A)
    (hL : 2 * q * (1 + s * M) / (2 - s) ≤ L) (hcs : L ^ 2 ≤ 4 * M * Δ) :
    q ^ 2 * A * (1 + s / A) ^ 2 / (2 - s) ^ 2 ≤ Δ := by
  have ha : 0 < A := by linarith
  have hd : 0 < 2 - s := by linarith
  have hsA : s / A ≤ 1 / 3 := (div_le_iff₀ ha).2 (by linarith)
  have hsm : s * M ≤ s / A := by
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hMA hs
  have hAM : 0 ≤ 1 - A * M :=
    sub_nonneg.mpr (by simpa [one_div, mul_comm] using (le_div_iff₀ ha).1 hMA)
  have hprod : 0 ≤ 1 - (s * M) * (s / A) := by
    have ht := div_nonneg hs ha.le
    have hh := mul_le_mul hsm hsA ht ht
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hsA)]
  have hmono : M * (A * (1 + s / A) ^ 2) ≤ (1 + s * M) ^ 2 := by
    have he : (1 + s * M) ^ 2 - M * (A * (1 + s / A) ^ 2) =
        (1 - A * M) * (1 - (s * M) * (s / A)) := by
      field_simp
      ring
    linarith [mul_nonneg hAM hprod]
  have hL₀ : 0 ≤ 2 * q * (1 + s * M) / (2 - s) := by positivity
  have hsq := (pow_le_pow_left₀ hL₀ hL 2).trans hcs
  rw [div_pow] at hsq
  have hh := (div_le_iff₀ (sq_pos_of_pos hd)).1 hsq
  have hh' := mul_le_mul_of_nonneg_left hmono (sq_nonneg q)
  apply (div_le_iff₀ (sq_pos_of_pos hd)).2
  apply (le_of_mul_le_mul_left ?_ hM)
  nlinarith only [hh, hh']


/-! ### The reciprocal sum of two geometric prefixes -/

private lemma geometric_prod_integral {a : unitInterval} (ha : a ≠ 0)
    (f : ℕ × ℕ → ℝ) :
    ∫ z, f z ∂(geometricMeasure a).prod (geometricMeasure a) =
      ∑' z : ℕ × ℕ, ((1 - (a : ℝ)) ^ z.1 * a) * ((1 - (a : ℝ)) ^ z.2 * a) * f z := by
  let w : ℕ → ℝ := fun n => (1 - (a : ℝ)) ^ n * a
  have hw (n : ℕ) : 0 ≤ w n := geometricMeasure_nonneg a n
  have hμ : (geometricMeasure a).prod (geometricMeasure a) =
      Measure.sum fun z : ℕ × ℕ => ENNReal.ofReal (w z.1 * w z.2) • Measure.dirac z := by
    rw [geometricMeasure_eq ha, Measure.prod_sum]
    congr 1
    funext z
    rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.dirac_prod_dirac,
      smul_smul, ← ENNReal.ofReal_mul (hw _)]
  rw [hμ, integral_sum_dirac (by intro z; simp)]
  apply tsum_congr
  intro z
  rw [ENNReal.toReal_ofReal (mul_nonneg (hw _) (hw _)), smul_eq_mul]

private lemma geometric_succ_sum_inv {a : unitInterval} (ha : a ≠ 0) :
    (∫ z : ℕ × ℕ, 1 / ((z.1 : ℝ) + z.2 + 1) ∂
      (geometricMeasure a).prod (geometricMeasure a)) = (a : ℝ) := by
  let p : ℝ := a
  let q : ℝ := 1 - p
  have hp : 0 < p := lt_of_le_of_ne a.2.1 (by
    intro hz
    exact ha (Subtype.ext hz.symm))
  have hq : 0 ≤ q := sub_nonneg.mpr a.2.2
  have hq1 : q < 1 := by dsimp [q]; linarith
  let f : ℕ × ℕ → ℝ := fun z => (p ^ 2 * q ^ (z.1 + z.2)) / ((z.1 : ℝ) + z.2 + 1)
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun z => by dsimp [f]; positivity)
      (f := fun z : ℕ × ℕ => (q ^ z.1 * p) * (q ^ z.2 * p))
    · intro z
      have hone : (1 : ℝ) ≤ (z.1 : ℝ) + z.2 + 1 := by linarith [Nat.cast_nonneg (α := ℝ) z.1, Nat.cast_nonneg (α := ℝ) z.2]
      have hnon : 0 ≤ p ^ 2 * q ^ (z.1 + z.2) := by positivity
      calc
        f z ≤ p ^ 2 * q ^ (z.1 + z.2) :=
          div_le_self hnon hone
        _ = (q ^ z.1 * p) * (q ^ z.2 * p) := by rw [pow_add]; ring
    · have hw := (summable_geometric_of_lt_one hq hq1).mul_right p
      exact hw.mul_of_nonneg hw (fun n => mul_nonneg (pow_nonneg hq n) hp.le)
        (fun n => mul_nonneg (pow_nonneg hq n) hp.le)
  rw [geometric_prod_integral ha]
  calc
    _ = ∑' z, f z := by
      apply tsum_congr
      intro z
      dsimp only [f, p, q]
      rw [pow_add]
      ring
    _ = ∑' n : ℕ, ∑ z ∈ Finset.antidiagonal n, f z := by
      let e : (Σ n : ℕ, Finset.antidiagonal n) ≃ ℕ × ℕ :=
        Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
      rw [← e.tsum_eq f]
      change (∑' z, (f ∘ e) z) = _
      rw [(e.summable_iff.2 hf).tsum_sigma' (fun n => (hasSum_fintype _).summable)]
      apply tsum_congr
      intro n
      rw [tsum_fintype]
      change (∑ z : ↥(Finset.antidiagonal n), f z.val) = _
      exact Finset.sum_coe_sort (Finset.antidiagonal n) f
    _ = ∑' n : ℕ, p ^ 2 * q ^ n := by
      apply tsum_congr
      intro n
      have he (z : ℕ × ℕ) (hz : z ∈ Finset.antidiagonal n) :
          f z = (p ^ 2 * q ^ n) / ((n : ℝ) + 1) := by
        have hzn := Finset.mem_antidiagonal.mp hz
        have hcast : (z.1 : ℝ) + z.2 = n := by exact_mod_cast hzn
        dsimp only [f]
        rw [hzn, hcast]
      rw [Finset.sum_congr rfl he, Finset.sum_const, Finset.Nat.card_antidiagonal,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      field_simp
    _ = (a : ℝ) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1]
      change p ^ 2 * (1 - q)⁻¹ = p
      have he : 1 - q = p := by dsimp [q]; ring
      rw [he]
      field_simp

private lemma lowWindow_inverse_sum_bound (h : OffspringHyp μ) (hl : 1 < l)
    (hlm : l < mean μ) :
    (∫ z, pBr μ / (RR μ l z.1 + RR μ l z.2 - pBr μ) ∂(GW μ).prod (GW μ)) ≤ pBr μ := by
  let ν := (GW μ).prod (GW μ)
  let p := pBr μ
  let F : Tree × Tree → ℝ := fun z => p / (RR μ l z.1 + RR μ l z.2 - p)
  let H : ℕ × ℕ → ℝ := fun z => 1 / ((z.1 : ℝ) + z.2 + 1)
  let g : Tree × Tree → ℕ × ℕ := fun z => (prefixLen z.1, prefixLen z.2)
  have hg₁ : MeasurePreserving prefixLen (GW μ) (geometricMeasure (prefixParam h)) := by
    let := splitLaw_prob h
    exact (measurePreserving_fst (μ := geometricMeasure (prefixParam h))
      (ν := splitLaw μ)).comp (prefix_product_law h)
  have hg : MeasurePreserving g ν ((geometricMeasure (prefixParam h)).prod
      (geometricMeasure (prefixParam h))) := hg₁.prod hg₁
  have hH : Measurable H := measurable_of_countable _
  have hH₁ (z : ℕ × ℕ) : H z ≤ 1 := by
    have he : (1 : ℝ) ≤ (z.1 : ℝ) + z.2 + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) z.1, Nat.cast_nonneg (α := ℝ) z.2]
    exact div_le_self (by norm_num) he
  have hf₀ : Measurable F := measurable_const.div
    ((((measurable_RR μ l).comp measurable_fst).add
      ((measurable_RR μ l).comp measurable_snd)).sub_const _)
  have hf : ∀ᵐ z ∂ν, 0 ≤ F z ∧ F z ≤ H (g z) := by
    have hfst := (measurePreserving_fst (μ := GW μ) (ν := GW μ)).quasiMeasurePreserving.ae
      (ae_RR_ge_prefix h hl hlm)
    have hsnd := (measurePreserving_snd (μ := GW μ) (ν := GW μ)).quasiMeasurePreserving.ae
      (ae_RR_ge_prefix h hl hlm)
    filter_upwards [hfst, hsnd] with z hz₁ hz₂
    have hp : 0 < p := pBr_pos h
    have hden : p * ((prefixLen z.1 : ℝ) + prefixLen z.2 + 1) ≤
        RR μ l z.1 + RR μ l z.2 - p := by linarith
    have hpos : 0 < p * ((prefixLen z.1 : ℝ) + prefixLen z.2 + 1) := by positivity
    refine ⟨div_nonneg hp.le (hpos.le.trans hden), ?_⟩
    calc
      F z ≤ p / (p * ((prefixLen z.1 : ℝ) + prefixLen z.2 + 1)) :=
        div_le_div_of_nonneg_left hp.le hpos hden
      _ = H (g z) := by dsimp only [H, g]; field_simp
  have hiF : Integrable F ν := by
    apply (integrable_const (1 : ℝ)).mono' hf₀.aestronglyMeasurable
    filter_upwards [hf] with z hz
    rw [Real.norm_of_nonneg hz.1]
    exact hz.2.trans (hH₁ _)
  have hiH : Integrable (fun z => H (g z)) ν := by
    apply (integrable_const (1 : ℝ)).mono' (hH.comp hg.measurable).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_of_nonneg (by dsimp [H]; positivity)]
      exact hH₁ _
  change (∫ z, F z ∂ν) ≤ p
  calc
    _ ≤ ∫ z, H (g z) ∂ν := integral_mono_ae hiF hiH (hf.mono fun _ hz => hz.2)
    _ = p := by
      rw [← integral_map hg.measurable.aemeasurable hH.aestronglyMeasurable, hg.map_eq]
      exact geometric_succ_sum_inv (prefixParam_ne_zero h)


/-! ### The geometric minimum and conditional Jensen -/

private lemma geometric_tail {a : unitInterval} (ha : a ≠ 0) (n : ℕ) :
    geometricMeasure a (Set.Ici n) = ENNReal.ofReal (1 - (a : ℝ)) ^ n := by
  classical
  let w : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal ((1 - (a : ℝ)) ^ k * a)
  let q : ℝ≥0∞ := ENNReal.ofReal (1 - (a : ℝ))
  have hw (k : ℕ) : w (n + k) = q ^ n * w k := by
    have hq : 0 ≤ 1 - (a : ℝ) := sub_nonneg.mpr a.2.2
    dsimp only [w, q]
    rw [pow_add, mul_assoc, ENNReal.ofReal_mul (pow_nonneg hq _), ENNReal.ofReal_pow hq]
  have hsum : ∑' k, w k = 1 := by
    have h := measure_univ (μ := geometricMeasure a)
    rw [geometricMeasure_eq ha, Measure.sum_apply _ MeasurableSet.univ] at h
    simpa [w, Measure.smul_apply] using h
  let e : ℕ ≃ Set.Ici n :=
    ⟨fun k => ⟨n + k, by simp⟩, fun k => k - n, by intro k; simp,
      fun k => Subtype.ext (Nat.add_sub_of_le k.2)⟩
  calc
    geometricMeasure a (Set.Ici n) =
        ∑' k : Set.Ici n, w k := by
      rw [← (geometricMeasure a).tsum_indicator_apply_singleton _ measurableSet_Ici,
        tsum_subtype]
      simp only [geometricMeasure_singleton ha, w]
    _ = ∑' k : ℕ, w (n + k) := (e.tsum_eq fun k : Set.Ici n => w k).symm
    _ = q ^ n := by simp only [hw, ENNReal.tsum_mul_left, hsum, mul_one]

private lemma geometric_min_law {a b : unitInterval} (ha : a ≠ 0) (hb : b ≠ 0)
    (hbq : 1 - (b : ℝ) = (1 - (a : ℝ)) ^ 2) :
    MeasurePreserving (fun z : ℕ × ℕ => min z.1 z.2)
      ((geometricMeasure a).prod (geometricMeasure a)) (geometricMeasure b) := by
  let f : ℕ × ℕ → ℕ := fun z => min z.1 z.2
  have hf : Measurable f := measurable_of_countable _
  refine ⟨hf, Measure.ext_of_singleton fun n => ?_⟩
  have ht (k : ℕ) : ((geometricMeasure a).prod (geometricMeasure a)).map f (Set.Ici k) =
      geometricMeasure b (Set.Ici k) := by
    have he : f ⁻¹' Set.Ici k = Set.Ici k ×ˢ Set.Ici k := by
      ext z
      change k ≤ min z.1 z.2 ↔ k ≤ z.1 ∧ k ≤ z.2
      exact le_min_iff
    rw [Measure.map_apply hf measurableSet_Ici, he, Measure.prod_prod,
      geometric_tail ha, geometric_tail hb, hbq,
      ENNReal.ofReal_pow (sub_nonneg.mpr a.2.2), ← pow_mul, mul_comm 2, pow_mul, pow_two]
  have he : Set.Ici n \ Set.Ici (n + 1) = ({n} : Set ℕ) := by
    ext k
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff]
    omega
  change ((geometricMeasure a).prod (geometricMeasure a)).map f {n} =
    geometricMeasure b {n}
  rw [← he, measure_sdiff, measure_sdiff, ht n, ht (n + 1)]
  all_goals first | exact measure_ne_top _ _ | exact measurableSet_Ici.nullMeasurableSet |
    exact Set.Ici_subset_Ici.mpr (Nat.le_succ _)

private lemma geometric_power {a : unitInterval} (ha : a ≠ 0) (hl : 0 < l)
    (hq : l * (1 - (a : ℝ)) < 1) :
    Integrable (fun n : ℕ => l ^ (n + 1)) (geometricMeasure a) ∧
      (∫ n : ℕ, l ^ (n + 1) ∂geometricMeasure a) =
        (l * (a : ℝ)) / (1 - l * (1 - (a : ℝ))) := by
  have hq0 : 0 ≤ l * (1 - (a : ℝ)) := mul_nonneg hl.le (sub_nonneg.mpr a.2.2)
  have he (n : ℕ) : ((1 - (a : ℝ)) ^ n * a) * l ^ (n + 1) =
      (l * (a : ℝ)) * (l * (1 - (a : ℝ))) ^ n := by
    rw [mul_pow, pow_succ]
    ring
  constructor
  · apply (integrable_geometricMeasure_iff ha).2
    simp only [Real.norm_of_nonneg (pow_nonneg hl.le _), he]
    exact (summable_geometric_of_lt_one hq0 hq).mul_left _
  · rw [integral_geometricMeasure ha]
    simp only [smul_eq_mul, he, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq, div_eq_mul_inv]

private lemma geometric_abs_power {a : unitInterval} (ha : a ≠ 0)
    (hl : 1 < l) (hq : l * (1 - (a : ℝ)) < 1) :
    (∫ z : ℕ × ℕ, |l ^ (z.1 + 1) - l ^ (z.2 + 1)| ∂
      (geometricMeasure a).prod (geometricMeasure a)) =
      2 * ((l * (a : ℝ)) / (1 - l * (1 - (a : ℝ))) -
        (l * (1 - (1 - (a : ℝ)) ^ 2)) / (1 - l * (1 - (a : ℝ)) ^ 2)) := by
  let q : ℝ := 1 - (a : ℝ)
  have hl₀ : 0 < l := by linarith
  have hq₀ : 0 ≤ q := sub_nonneg.mpr a.2.2
  have ha₀ : 0 < (a : ℝ) := lt_of_le_of_ne a.2.1
    (fun he => ha (Subtype.ext he.symm))
  have hq₁ : q < 1 := by dsimp [q]; linarith
  have hq2 : q ^ 2 ≤ q := by nlinarith [mul_nonneg hq₀ (sub_nonneg.mpr hq₁.le)]
  let b : unitInterval := ⟨1 - q ^ 2, by linarith, by nlinarith⟩
  have hbl : 1 - (b : ℝ) = q ^ 2 := by change 1 - (1 - q ^ 2) = _; ring
  have hb : b ≠ 0 := by
    intro he
    have hb0 := congrArg Subtype.val he
    change 1 - q ^ 2 = 0 at hb0
    linarith
  have hbq : l * (1 - (b : ℝ)) < 1 := by
    rw [hbl]
    exact (mul_le_mul_of_nonneg_left hq2 hl₀.le).trans_lt hq
  let ν := geometricMeasure a
  let f : ℕ → ℝ := fun n => l ^ (n + 1)
  have hf := geometric_power ha hl₀ hq
  have hbpow := geometric_power hb hl₀ hbq
  have hm := geometric_min_law ha hb hbl
  have hi₁ : Integrable (fun z : ℕ × ℕ => f z.1) (ν.prod ν) := hf.1.comp_fst ν
  have hi₂ : Integrable (fun z : ℕ × ℕ => f z.2) (ν.prod ν) := hf.1.comp_snd ν
  have him : Integrable (fun z : ℕ × ℕ => f (min z.1 z.2)) (ν.prod ν) :=
    hm.integrable_comp_of_integrable hbpow.1
  have hF : Measurable f := measurable_of_countable _
  have h₁ : (∫ z : ℕ × ℕ, f z.1 ∂ν.prod ν) = ∫ n, f n ∂ν := by
    rw [← integral_map (measurable_fst.aemeasurable) hF.aestronglyMeasurable,
      measurePreserving_fst.map_eq]
  have h₂ : (∫ z : ℕ × ℕ, f z.2 ∂ν.prod ν) = ∫ n, f n ∂ν := by
    rw [← integral_map (measurable_snd.aemeasurable) hF.aestronglyMeasurable,
      measurePreserving_snd.map_eq]
  have hmin : (∫ z : ℕ × ℕ, f (min z.1 z.2) ∂ν.prod ν) = ∫ n, f n ∂geometricMeasure b := by
    rw [← integral_map hm.measurable.aemeasurable hF.aestronglyMeasurable, hm.map_eq]
  have he (z : ℕ × ℕ) : |f z.1 - f z.2| = f z.1 + f z.2 - 2 * f (min z.1 z.2) := by
    rcases le_total z.1 z.2 with hz | hz
    · have hh : f z.1 ≤ f z.2 := pow_le_pow_right₀ hl.le (by omega)
      rw [min_eq_left hz, abs_of_nonpos (sub_nonpos.mpr hh)]
      ring
    · have hh : f z.2 ≤ f z.1 := pow_le_pow_right₀ hl.le (by omega)
      rw [min_eq_right hz, abs_of_nonneg (sub_nonneg.mpr hh)]
      ring
  change (∫ z : ℕ × ℕ, |f z.1 - f z.2| ∂ν.prod ν) = _
  simp_rw [he]
  rw [integral_sub (f := fun z : ℕ × ℕ => f z.1 + f z.2) (hi₁.add hi₂)
    (him.const_mul 2), integral_add hi₁ hi₂,
    integral_const_mul, h₁, h₂, hmin, hf.2, hbpow.2, hbl]
  change _ = 2 * (_ - l * (1 - q ^ 2) / _)
  dsimp only [b]
  ring


private lemma measurePreserving_pair_reorder {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (ν : Measure X) (ξ : Measure Y)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    MeasurePreserving (fun z : (X × Y) × (X × Y) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      ((ν.prod ξ).prod (ν.prod ξ)) ((ν.prod ν).prod (ξ.prod ξ)) := by
  have h₁ := measurePreserving_prodAssoc ν ξ (ν.prod ξ)
  have h₂ := (MeasurePreserving.id ν).prod
    ((measurePreserving_prodAssoc ξ ν ξ).symm)
  have h₃ := (MeasurePreserving.id ν).prod
    ((Measure.measurePreserving_swap (μ := ξ) (ν := ν)).prod (MeasurePreserving.id ξ))
  have h₄ := (MeasurePreserving.id ν).prod (measurePreserving_prodAssoc ν ξ ξ)
  have h₅ := (measurePreserving_prodAssoc ν ν (ξ.prod ξ)).symm
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

private lemma lowWindow_prefix_scalar {p q s l M C : ℝ} (hp : 0 < p) (hq : 0 ≤ q)
    (hpq : q + p = 1) (hs₀ : 0 < s) (hs : s ≤ 1 / 8)
    (hl : l = 1 + p * s) (hM : 0 ≤ M)
    (hlq : l * q < 1) (hlq₂ : l * q ^ 2 < 1)
    (hC : C * (l * p / (1 - l * q)) = M + 1 / s) :
    2 * q * (1 + s * M) / (2 - s) ≤
      C * (2 * (l * p / (1 - l * q) - l * (1 - q ^ 2) / (1 - l * q ^ 2))) := by
  have hq₁ : q ≤ 1 := by linarith
  have hD : 1 - l * q ^ 2 = p * (1 + q - s * q ^ 2) := by
    rw [hl, ← show 1 - q = p by linarith]
    ring
  have hD₀ : 0 < 1 + q - s * q ^ 2 := by
    by_contra! ht
    have hh := mul_nonpos_of_nonneg_of_nonpos hp.le ht
    linarith
  have hD₁ : 1 + q - s * q ^ 2 ≤ 2 - s := by
    have hh : 1 - q - s + s * q ^ 2 = (1 - q) * (1 - s * (1 + q)) := by ring
    have hs' : s * (1 + q) ≤ (1 / 8 : ℝ) * 2 :=
      mul_le_mul hs (by linarith) (by linarith) (by norm_num)
    have hsn : 0 ≤ 1 - s * (1 + q) := by linarith
    linarith [mul_nonneg (sub_nonneg.mpr hq₁) hsn]
  have hd : 0 < 1 - l * q := by linarith
  have hd₂ : 0 < 1 - l * q ^ 2 := by linarith
  have he : l * p / (1 - l * q) - l * (1 - q ^ 2) / (1 - l * q ^ 2) =
      (l * p / (1 - l * q)) * ((l - 1) * q / (1 - l * q ^ 2)) := by
    field_simp [hd.ne', hd₂.ne']
    rw [← show 1 - q = p by linarith]
    ring
  rw [he, show C * (2 * (l * p / (1 - l * q) *
      ((l - 1) * q / (1 - l * q ^ 2)))) =
      2 * (C * (l * p / (1 - l * q))) * ((l - 1) * q / (1 - l * q ^ 2)) by ring, hC]
  rw [hD, show l - 1 = p * s by linarith]
  calc
    _ ≤ 2 * q * (1 + s * M) / (1 + q - s * q ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hD₀ hD₁
    _ = _ := by field_simp; ring

private lemma lowWindow_abs_lower (h : OffspringHyp μ) (hl : 1 < l) (hlm : l < mean μ)
    (hs : sS μ l ≤ 1 / 8) :
    let M := ∫ T, RR μ l T ∂GW μ
    2 * p1 μ * (1 + sS μ l * M) / (2 - sS μ l) ≤
      ∫ z, |RR μ l z.1 - RR μ l z.2| ∂(GW μ).prod (GW μ) := by
  intro M
  let p := pBr μ
  let q := p1 μ
  let s := sS μ l
  let a := prefixParam h
  let ν := geometricMeasure a
  let ξ := splitLaw μ
  let : IsProbabilityMeasure ξ := splitLaw_prob h
  let P : ℕ → ℝ := fun n => l ^ (n + 1)
  let W : Tree → ℝ := fun T => xS μ l / Wt l T
  let C := ∫ T, W T ∂ξ
  let F : ℕ × Tree → ℝ := fun z => P z.1 * W z.2
  have hp : 0 < p := pBr_pos h
  have hq : 0 ≤ q := ENNReal.toReal_nonneg
  have hpq : q + p = 1 := p1_add_pBr h
  have ha : 1 - (a : ℝ) = q := by change 1 - p = q; linarith
  have hl₀ : 0 < l := by linarith
  have hs₀ : 0 < s := div_pos (by linarith) hp
  have hlps : l = 1 + p * s := by
    change l = 1 + p * ((l - 1) / p)
    field_simp
    ring
  have hq₁ : q ≤ 1 := by linarith
  have hlq : l * q < 1 := by
    have hh : 0 ≤ s * q := mul_nonneg hs₀.le hq
    have hu : s * q ≤ 1 / 8 := (mul_le_mul_of_nonneg_left hq₁ hs₀.le).trans (by simpa using hs)
    have he : 1 - l * q = p * (1 - s * q) := by rw [hlps]; nlinarith
    linarith [mul_pos hp (show 0 < 1 - s * q by linarith)]
  have hlq₂ : l * q ^ 2 < 1 :=
    (mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hq (sub_nonneg.mpr hq₁)]) hl₀.le).trans_lt hlq
  have hPm : Measurable P := measurable_of_countable _
  have hWm : Measurable W := measurable_const.div (measurable_Wt l)
  have hFm : Measurable F := (hPm.comp measurable_fst).mul (hWm.comp measurable_snd)
  have hmp := prefix_product_law h
  have hr := integrable_RR h hl hlm hs
  have hF : Integrable F (ν.prod ξ) := by
    apply (hmp.integrable_comp hFm.aestronglyMeasurable).1
    exact (hr.add (integrable_const _)).congr (ae_RR_prefix h hl hlm)
  have hW₀ : 0 ≤ᵐ[ξ] W := by
    filter_upwards [ae_Wt_mem h hl hlm] with T hw
    exact div_nonneg (div_nonneg hp.le (by linarith)) hw.1.le
  have hW : Integrable W ξ := by
    have hi : Integrable (fun z : ℕ × Tree => W z.2) (ν.prod ξ) := by
      apply hF.mono' (hWm.comp measurable_snd).aestronglyMeasurable
      have hn := (measurePreserving_snd (μ := ν) (ν := ξ)).quasiMeasurePreserving.ae hW₀
      filter_upwards [hn] with z hz
      change ‖W z.2‖ ≤ F z
      rw [Real.norm_of_nonneg hz]
      have hP : 1 ≤ P z.1 := one_le_pow₀ hl.le
      exact le_mul_of_one_le_left hz hP
    exact ((measurePreserving_snd (μ := ν) (ν := ξ)).integrable_comp hWm.aestronglyMeasurable).1 hi
  have hC₀ : 0 ≤ C := integral_nonneg_of_ae hW₀
  have hpow := geometric_power (a := a) (prefixParam_ne_zero h) hl₀ (by rw [ha]; exact hlq)
  have hC : C * (l * p / (1 - l * q)) = M + 1 / s := by
    have hx : xS μ l = 1 / s := by
      change p / (l - 1) = 1 / ((l - 1) / p)
      field_simp
    calc
      _ = ∫ z, F z ∂ν.prod ξ := by
        change _ = ∫ z, P z.1 * W z.2 ∂ν.prod ξ
        rw [integral_prod_mul, hpow.2, ha]
        exact mul_comm _ _
      _ = ∫ T, F (prefixLen T, splitTree T) ∂GW μ := by
        rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hFm.aestronglyMeasurable]
      _ = ∫ T, RR μ l T + xS μ l ∂GW μ :=
        integral_congr_ae ((ae_RR_prefix h hl hlm).mono fun _ hz => hz.symm)
      _ = _ := by rw [integral_add hr (integrable_const _), integral_const, probReal_univ, one_smul, hx]
  let J : (ℕ × ℕ) × (Tree × Tree) → ℝ := fun z =>
    |P z.1.1 * W z.2.1 - P z.1.2 * W z.2.2|
  let K : ℕ × ℕ → ℝ := fun z => C * |P z.1 - P z.2|
  have hJm : Measurable J := continuous_abs.measurable.comp
    (((hPm.comp (measurable_fst.comp measurable_fst)).mul
      (hWm.comp (measurable_fst.comp measurable_snd))).sub
      ((hPm.comp (measurable_snd.comp measurable_fst)).mul
        (hWm.comp (measurable_snd.comp measurable_snd))))
  have hpair := (measurePreserving_pair_reorder ν ξ).comp (hmp.prod hmp)
  have hJE : (fun z : Tree × Tree => J
      ((prefixLen z.1, prefixLen z.2), (splitTree z.1, splitTree z.2))) =ᵐ[(GW μ).prod (GW μ)]
      (fun z => |RR μ l z.1 - RR μ l z.2|) := by
    have h₁ := (measurePreserving_fst (μ := GW μ) (ν := GW μ)).quasiMeasurePreserving.ae
      (ae_RR_prefix h hl hlm)
    have h₂ := (measurePreserving_snd (μ := GW μ) (ν := GW μ)).quasiMeasurePreserving.ae
      (ae_RR_prefix h hl hlm)
    filter_upwards [h₁, h₂] with z hz₁ hz₂
    change _ + _ = P _ * W _ at hz₁ hz₂
    dsimp only [J]
    rw [← hz₁, ← hz₂]
    ring_nf
  have hJ : Integrable J ((ν.prod ν).prod (ξ.prod ξ)) := by
    apply (hpair.integrable_comp hJm.aestronglyMeasurable).1
    exact ((hr.comp_fst (GW μ)).sub (hr.comp_snd (GW μ))).abs.congr hJE.symm
  have hK : Integrable K (ν.prod ν) :=
    (((hpow.1.comp_fst ν).sub (hpow.1.comp_snd ν)).abs).const_mul C
  have hle : ∀ z : ℕ × ℕ, K z ≤ ∫ w, J (z, w) ∂ξ.prod ξ := by
    intro z
    have hh := lowWindow_conditional_abs hW (P z.1) (P z.2)
    rwa [abs_mul, abs_of_nonneg hC₀, mul_comm] at hh
  have hgeom := geometric_abs_power (a := a) (prefixParam_ne_zero h) hl (by rw [ha]; exact hlq)
  rw [ha] at hgeom
  calc
    _ ≤ C * (2 * (l * p / (1 - l * q) - l * (1 - q ^ 2) / (1 - l * q ^ 2))) :=
      lowWindow_prefix_scalar hp hq hpq hs₀ hs hlps
        (integral_nonneg_of_ae ((ae_RR_pos h hl hlm).mono fun _ hz => hz.le)) hlq hlq₂ hC
    _ = ∫ z, K z ∂ν.prod ν := by
      change _ = ∫ z, C * |l ^ (z.1 + 1) - l ^ (z.2 + 1)| ∂ν.prod ν
      rw [integral_const_mul, hgeom]
      rfl
    _ ≤ ∫ z, ∫ w, J (z, w) ∂ξ.prod ξ ∂ν.prod ν :=
      integral_mono hK hJ.integral_prod_left hle
    _ = ∫ z, J z ∂(ν.prod ν).prod (ξ.prod ξ) := (integral_prod J hJ).symm
    _ = _ := by
      rw [← hpair.map_eq, integral_map hpair.measurable.aemeasurable hJm.aestronglyMeasurable]
      exact integral_congr_ae hJE

/-- **Lower bound on `Δ`.** The geometric prefix gives a lower bound on
the two-copy dispersion of reciprocal escape. -/
theorem lowWindow_reciprocal_delta_lower (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    let p := pBr μ
    let q := p1 μ
    let e := eJ μ
    let s := sS μ l
    let A := 1 - e - s * (q + p * e)
    let M := ∫ T, p / escape l T ∂GW μ
    let Δ := (1 / 2) * ∫ x, (p / escape l x.1 - p / escape l x.2) ^ 2 /
      (p / escape l x.1 + p / escape l x.2) ∂(GW μ).prod (GW μ)
    q ^ 2 * A * (1 + s / A) ^ 2 / (2 - s) ^ 2 ≤ Δ := by
  intro p q e s A M Δ
  have hpos : 0 < M := by
    have hr := integrable_RR h hl hlm hs
    have hp := pBr_pos h
    have hle : p ≤ M := by
      change p ≤ ∫ T, RR μ l T ∂GW μ
      have hae : ∀ᵐ T ∂GW μ, p ≤ RR μ l T := by
        filter_upwards [ae_escape_pos h (by linarith : 0 < l) hlm] with T hT
        exact RR_lower h hl T hT
      simpa only [integral_const, probReal_univ, one_smul] using
        integral_mono_ae (integrable_const p) hr hae
    exact hp.trans_le hle
  exact lowWindow_delta_scalar (div_nonneg (by linarith) (pBr_pos h).le) hs
    ENNReal.toReal_nonneg hpos (lowWindow_reciprocal_A_lower h hl hlm hs)
    (lowWindow_reciprocal_M_le' h hl hlm hs) (lowWindow_abs_lower h hl hlm hs)
    (lowWindow_cauchy h hl hlm hs)


/-! ### The two-copy inverse kernel -/

private lemma lowWindow_pair_pointwise {p b c : ℝ} (hp : 0 < p)
    (hb : b ∈ Set.Ioc 0 1) (hc : c ∈ Set.Ioc 0 1) :
    let x := p / b
    let y := p / c
    4 * (p / tau b c) ≤ x + y + p + p * (p / (x + y - p)) - (x - y) ^ 2 / (x + y) := by
  intro x y
  have hpx : p ≤ x := (le_div_iff₀ hb.1).2 (by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hb.2)])
  have hpy : p ≤ y := (le_div_iff₀ hc.1).2 (by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hc.2)])
  have hden : 0 < x + y - p := by linarith
  have hτ : 0 < tau b c := by
    unfold tau
    nlinarith only [hb.1, mul_nonneg hc.1.le (sub_nonneg.mpr hb.2)]
  have hT : p / tau b c = x * y / (x + y - p) := by
    apply (div_eq_div_iff hτ.ne' hden.ne').2
    dsimp only [x, y, tau]
    field_simp [hb.1.ne', hc.1.ne']
    ring
  have hIdentity : 4 * (p / tau b c) =
      x + y + p + p * (p / (x + y - p)) - (x - y) ^ 2 / (x + y - p) := by
    rw [hT]
    field_simp
    ring
  rw [hIdentity]
  have hle := div_le_div_of_nonneg_left (sq_nonneg (x - y)) hden
    (show x + y - p ≤ x + y by linarith)
  linarith

private lemma lowWindow_pair_moment (h : OffspringHyp μ) (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    let p := pBr μ
    let q := p1 μ
    let M := ∫ T, RR μ l T ∂GW μ
    let Δ := (1 / 2) * ∫ z, DD μ l z ∂(GW μ).prod (GW μ)
    2 * pairE μ l (fun b c => p / tau b c) - p ≤ M - Δ - p * q / 2 := by
  intro p q M Δ
  let ν := (GW μ).prod (GW μ)
  let x : Tree × Tree → ℝ := fun z => RR μ l z.1
  let y : Tree × Tree → ℝ := fun z => RR μ l z.2
  let B : Tree × Tree → ℝ := fun z => p / (x z + y z - p)
  let T : Tree × Tree → ℝ := fun z => p / tau (escape l z.1) (escape l z.2)
  have hp : 0 < p := pBr_pos h
  have hpq := p1_add_pBr h
  have hl₀ : 0 < l := by linarith
  have he : ∀ᵐ z : Tree × Tree ∂ν,
      escape l z.1 ∈ Set.Ioc 0 1 ∧ escape l z.2 ∈ Set.Ioc 0 1 := by
    have hbase : ∀ᵐ t ∂GW μ, escape l t ∈ Set.Ioc 0 1 := by
      filter_upwards [ae_escape_pos h hl₀ hlm] with t ht
      exact ⟨ht, (escape_mem_Icc hl₀ t).2⟩
    exact ((measurePreserving_fst (μ := GW μ) (ν := GW μ)).quasiMeasurePreserving.ae hbase).and
      ((measurePreserving_snd (μ := GW μ) (ν := GW μ)).quasiMeasurePreserving.ae hbase)
  have em₁ : Measurable (fun z : Tree × Tree => escape l z.1) :=
    (measurable_escape l).comp measurable_fst
  have em₂ : Measurable (fun z : Tree × Tree => escape l z.2) :=
    (measurable_escape l).comp measurable_snd
  have hx : Integrable x ν := (integrable_RR h hl hlm hs).comp_fst _
  have hy : Integrable y ν := (integrable_RR h hl hlm hs).comp_snd _
  have hB : Integrable B ν := by
    have hm : Measurable B := measurable_const.div
      ((((measurable_RR μ l).comp measurable_fst).add
        ((measurable_RR μ l).comp measurable_snd)).sub_const _)
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [he] with z hz
    have h₁ : p ≤ x z := RR_lower h hl z.1 hz.1.1
    have h₂ : p ≤ y z := RR_lower h hl z.2 hz.2.1
    have hpos : 0 < x z + y z - p := by linarith
    change ‖p / (x z + y z - p)‖ ≤ 1
    rw [Real.norm_of_nonneg (div_nonneg hp.le hpos.le)]
    exact (div_le_one hpos).2 (by linarith)
  have hT : Integrable T ν := by
    have hm : Measurable T := measurable_const.div ((em₁.add em₂).sub (em₁.mul em₂))
    apply hx.mono' hm.aestronglyMeasurable
    filter_upwards [he] with z hz
    have hge : escape l z.1 ≤ tau (escape l z.1) (escape l z.2) := by
      unfold tau
      nlinarith [mul_nonneg hz.2.1.le (sub_nonneg.mpr hz.1.2)]
    have hτ := hz.1.1.trans_le hge
    change ‖p / tau (escape l z.1) (escape l z.2)‖ ≤ p / escape l z.1
    rw [Real.norm_of_nonneg (div_nonneg hp.le hτ.le)]
    exact div_le_div_of_nonneg_left hp.le hz.1.1 hge
  have hD := integrable_DD h hl hlm hs
  have hxy : Integrable (fun z => x z + y z) ν := hx.add hy
  have hU : Integrable (fun z => x z + y z + p) ν := hxy.add (integrable_const p)
  have hV : Integrable (fun z => x z + y z + p + p * B z) ν := hU.add (hB.const_mul p)
  have hineq : (∫ z, 4 * T z ∂ν) ≤
      ∫ z, x z + y z + p + p * B z - DD μ l z ∂ν := by
    apply integral_mono_ae (hT.const_mul _) (hV.sub hD)
    filter_upwards [he] with z hz
    exact lowWindow_pair_pointwise hp hz.1 hz.2
  rw [integral_const_mul, integral_sub hV hD, integral_add hU (hB.const_mul p),
    integral_add hxy (integrable_const p), integral_add hx hy, integral_const_mul,
    integral_const, probReal_univ, one_smul, integral_RR_fst h hl hlm hs,
    integral_RR_snd h hl hlm hs] at hineq
  have hB_le : (∫ z, B z ∂ν) ≤ p := lowWindow_inverse_sum_bound h hl hlm
  have hB_mul := mul_le_mul_of_nonneg_left hB_le hp.le
  change 4 * pairE μ l (fun b c => p / tau b c) ≤
    M + M + p + p * (∫ z, B z ∂ν) - ∫ z, DD μ l z ∂ν at hineq
  change q + p = 1 at hpq
  have heq : p * p - p = -(p * q) := by nlinarith
  dsimp only [Δ]
  linarith

private lemma lowWindow_pair_scalar {p q e l s A M Δ H : ℝ}
    (hp : 0 < p) (hq : 0 ≤ q) (hpq : q + p = 1)
    (hs₀ : 0 ≤ s) (hs : s ≤ 1 / 8) (hA : 3 / 8 ≤ A) (hA₁ : A ≤ 1)
    (hAe : A + l * e = 1 - s * q) (hAM : A * M ≤ 1 - l * e * Δ)
    (hΔ : q ^ 2 * A * (1 + s / A) ^ 2 / (2 - s) ^ 2 ≤ Δ)
    (hH : H ≤ M - Δ - p * q / 2) :
    H ≤ (1 - s * q ^ 2 / 2) / A - q * (1 + p) / 4 := by
  let t := s / A
  have ha : 0 < A := by linarith
  have hq₁ : q ≤ 1 := by linarith
  have ht₀ : s ≤ t := (le_div_iff₀ ha).2 (by nlinarith [mul_nonneg hs₀ (sub_nonneg.mpr hA₁)])
  have ht : t ≤ 1 / 3 := (div_le_iff₀ ha).2 (by linarith)
  have hts := lowWindow_reciprocal_scalar hs₀ hs ht₀ ht
  have hd : 0 < 2 - s := by linarith
  have hR : 1 / 4 + t / 2 ≤ (1 - s) * (1 + t) ^ 2 / (2 - s) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hd)).2
    linear_combination hts / 4
  have hΔ₀ : 0 ≤ Δ := (by positivity : 0 ≤ q ^ 2 * A * (1 + s / A) ^ 2 / (2 - s) ^ 2).trans hΔ
  have hcoeff : 1 - s ≤ A + l * e := by
    rw [hAe]
    nlinarith [mul_nonneg hs₀ (sub_nonneg.mpr hq₁)]
  have hdisp : q ^ 2 * (A / 4 + s / 2) ≤ (A + l * e) * Δ := by
    have htA : A * t = s := by dsimp only [t]; field_simp
    calc
      _ = (q ^ 2 * A) * (1 / 4 + t / 2) := by linear_combination -(q ^ 2 / 2) * htA
      _ ≤ (q ^ 2 * A) * ((1 - s) * (1 + t) ^ 2 / (2 - s) ^ 2) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
      _ = (1 - s) * (q ^ 2 * A * (1 + s / A) ^ 2 / (2 - s) ^ 2) := by
        dsimp only [t]; ring
      _ ≤ (1 - s) * Δ := mul_le_mul_of_nonneg_left hΔ (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hΔ₀
  have hH' := mul_le_mul_of_nonneg_left hH ha.le
  rw [le_sub_iff_add_le]
  apply (le_div_iff₀ ha).2
  have hqq : q ^ 2 + 2 * p * q = q * (1 + p) := by nlinarith
  nlinarith only [hH', hdisp, hAM, congrArg (fun z : ℝ => A * z / 4) hqq]

/-- **`2 E[p/τ] - p ≤ d`.** Bound the two-copy inverse kernel on the low window. -/
theorem lowWindow_reciprocal_pair_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    let p := pBr μ
    let q := p1 μ
    let e := eJ μ
    let s := sS μ l
    let A := 1 - e - s * (q + p * e)
    let M := ∫ T, p / escape l T ∂GW μ
    let Δ := (1 / 2) * ∫ x, (p / escape l x.1 - p / escape l x.2) ^ 2 /
      (p / escape l x.1 + p / escape l x.2) ∂(GW μ).prod (GW μ)
    2 * pairE μ l (fun b b' => p / tau b b') - p ≤
      (1 - s * q ^ 2 / 2) / A - q * (1 + p) / 4 := by
  intro p q e s A M Δ
  have hp : 0 < p := pBr_pos h
  have hq : 0 ≤ q := ENNReal.toReal_nonneg
  have hpq : q + p = 1 := p1_add_pBr h
  have he : 0 ≤ e := (eJ_mem h).1.le
  have hs₀ : 0 ≤ s := div_nonneg (by linarith) hp.le
  have hlps : l = 1 + p * s := by
    change l = 1 + p * ((l - 1) / p)
    field_simp
    ring
  have hA₁ : A ≤ 1 := by
    change 1 - e - s * (q + p * e) ≤ 1
    linarith [mul_nonneg hs₀ (add_nonneg hq (mul_nonneg hp.le he))]
  have hAe : A + l * e = 1 - s * q := by
    change 1 - e - s * (q + p * e) + l * e = 1 - s * q
    rw [hlps]
    ring
  exact lowWindow_pair_scalar (M := M) (Δ := Δ) hp hq hpq hs₀ hs
    (lowWindow_reciprocal_A_lower h hl hlm hs) hA₁ hAe
    (lowWindow_reciprocal_AM_le h hl hlm hs)
    (lowWindow_reciprocal_delta_lower h hl hlm hs) (lowWindow_pair_moment h hl hlm hs)

/-- The five reciprocal-escape estimates of the proof of Theorem 4.3 on the low window. -/
theorem lowWindow_reciprocal (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    let p := pBr μ
    let q := p1 μ
    let e := eJ μ
    let s := sS μ l
    let A := 1 - e - s * (q + p * e)
    let M := ∫ T, p / escape l T ∂GW μ
    let Δ := (1 / 2) * ∫ x, (p / escape l x.1 - p / escape l x.2) ^ 2 /
      (p / escape l x.1 + p / escape l x.2) ∂(GW μ).prod (GW μ)
    3 / 8 ≤ A ∧ M ≤ 1 / A ∧ A * M ≤ 1 - l * e * Δ ∧
      q ^ 2 * A * (1 + s / A) ^ 2 / (2 - s) ^ 2 ≤ Δ ∧
      2 * pairE μ l (fun b b' => p / tau b b') - p ≤
        (1 - s * q ^ 2 / 2) / A - q * (1 + p) / 4 :=
  ⟨lowWindow_reciprocal_A_lower h hl hlm hs, lowWindow_reciprocal_M_le' h hl hlm hs,
    lowWindow_reciprocal_AM_le h hl hlm hs, lowWindow_reciprocal_delta_lower h hl hlm hs,
    lowWindow_reciprocal_pair_le h hl hlm hs⟩

end LPPMonotonicityProof.Analytic
