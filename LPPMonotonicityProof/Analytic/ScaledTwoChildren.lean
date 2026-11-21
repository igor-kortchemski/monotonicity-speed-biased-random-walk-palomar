module

public import LPPMonotonicityProof.Analytic.ChildResponse
public import LPPMonotonicityProof.Analytic.ScaledPrefix2
public import LPPMonotonicityProof.Analytic.ScaledSeries

/-!
# Response at the first split

This module proves Lemma 4.5 (`lem:scaled-two-children`): the quantitative response
bounds and the nonnegativity criterion `M_* ≥ 1` for the scaled moments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem dx_mul (f g : ℝ → ℝ) (l : ℝ)
    (hf : DifferentiableAt ℝ f l) (hg : DifferentiableAt ℝ g l) :
    dx μ (fun y => f y * g y) l =
      dx μ f l * g l + f l * dx μ g l := by
  unfold dx
  change -((l - 1) ^ 2 / pBr μ) * deriv (f * g) l = _
  rw [deriv_mul hf hg]
  ring

private theorem dx_const_mul (c : ℝ) (f : ℝ → ℝ) (l : ℝ)
    (hf : DifferentiableAt ℝ f l) :
    dx μ (fun y => c * f y) l = c * dx μ f l := by
  unfold dx
  rw [deriv_const_mul _ hf]
  ring

private theorem dx_sub (f g : ℝ → ℝ) (l : ℝ)
    (hf : DifferentiableAt ℝ f l) (hg : DifferentiableAt ℝ g l) :
    dx μ (fun y => f y - g y) l = dx μ f l - dx μ g l := by
  unfold dx
  change -((l - 1) ^ 2 / pBr μ) * deriv (f - g) l = _
  rw [deriv_sub hf hg]
  ring

private theorem mMom_eq_mul {n : ℕ} (hn : 1 ≤ n) :
    (fun y => mMom μ y n) = fun y => Acoef μ y n * etaW μ y n := by
  funext y
  simp [mMom, Nat.ne_of_gt hn]

theorem wbar_pos_f10 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : 0 < wbar μ l := by
  letI := splitLaw_prob h
  have hi : Integrable (Wt l) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow' h hl hlm 1
  have hn : 0 ≤ᵐ[splitLaw μ] Wt l :=
    (ae_Wt_mem h hl hlm).mono fun _ hT => hT.1.le
  have hs : Function.support (Wt l) =ᵐ[splitLaw μ] Set.univ := by
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    simp [Function.support, hT.1.ne']
  simp only [wbar, etaW, pow_one]
  rw [integral_pos_iff_support_of_nonneg_ae hn hi, measure_congr hs]
  simp

theorem mMom_one_pos_f10 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : 0 < mMom μ l 1 := by
  have hA : 0 < Acoef μ l 1 := by
    rw [Acoef]
    have hi : 0 < iota μ l 1 := by
      unfold iota
      apply inv_pos.mpr
      exact add_pos_of_pos_of_nonneg (xS_pos (μ := μ) h hl)
        (Qgeo_nonneg (by linarith : 0 ≤ l) 1)
    simpa using mul_pos (pow_pos (kS_pos hl) 0) hi
  rw [show mMom μ l 1 = Acoef μ l 1 * wbar μ l by simp [mMom, wbar]]
  exact mul_pos hA (wbar_pos_f10 h hl hlm)

private theorem Bn_nonneg (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : 0 ≤ Bn μ l n := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_regTree_split h] with T hT
  exact mul_nonneg (pow_nonneg (Wt_mem_Icc' hl T).1 _)
    ((mul_nonneg (Wt_mem_Icc' hl T).1 (sub_nonneg.mpr (Wt_mem_Icc' hl T).2)).trans
      (Bresp_ge h hT hl hlm))

private theorem Bn_one_ge (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : wbar μ l * (1 - tW μ l) ≤ Bn μ l 1 := by
  letI := splitLaw_prob h
  have hw := wbar_pos_f10 h hl hlm
  have hWi : Integrable (Wt l) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow' h hl hlm 1
  have hW2i := integrable_Wt_pow' h hl hlm 2
  have hlow : (fun T => Wt l T * (1 - Wt l T)) = fun T => Wt l T - Wt l T ^ 2 := by
    funext T
    ring
  have hli : Integrable (fun T => Wt l T * (1 - Wt l T)) (splitLaw μ) := by
    rw [hlow]
    exact hWi.sub hW2i
  have hBi : Integrable (Bresp l) (splitLaw μ) := by
    change Integrable (fun T : Tree => -(l - 1) * deriv (fun l' => Wt l' T) l) (splitLaw μ)
    let a := (1 + l) / 2
    let b := (l + mean μ) / 2
    have ha : 1 < a := by dsimp [a]; linarith
    have hb : b < mean μ := by dsimp [b]; linarith
    have hx : l ∈ Set.Icc a b := ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
    have hdom := (integrable_deriv_bound (a := a) (b := b) h ha (hx.1.trans hx.2) hb 1).const_mul (l - 1)
    apply hdom.mono' ((aemeasurable_deriv_Wt h hl hlm).const_mul (-(l - 1))).aestronglyMeasurable
    filter_upwards [ae_regTree_split h, ae_norm_deriv_Wt_pow_le (a := a) (b := b) h ha (hx.1.trans hx.2) hb 1]
      with T hT hbound
    have hd := hbound l hx
    simp only [Nat.cast_one, Nat.sub_self, pow_zero, mul_one, one_mul] at hd
    rw [norm_mul, norm_neg, Real.norm_of_nonneg (by linarith : 0 ≤ l - 1)]
    simpa using mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ l - 1)
  have hBi' : Integrable (fun T => Wt l T ^ (1 - 1) * Bresp l T) (splitLaw μ) := by
    simpa using hBi
  have hint : (∫ T, Wt l T * (1 - Wt l T) ∂splitLaw μ) ≤ Bn μ l 1 := by
    unfold Bn
    apply integral_mono_ae hli hBi' 
    filter_upwards [ae_regTree_split h] with T hT
    simpa using Bresp_ge h hT hl hlm
  have heq : wbar μ l * (1 - tW μ l) = ∫ T, Wt l T * (1 - Wt l T) ∂splitLaw μ := by
    rw [hlow, integral_sub hWi hW2i]
    unfold tW
    field_simp [hw.ne']
    simp [wbar, etaW]
  rw [heq]
  exact hint

private theorem Bn_ge_Mtwo (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (hn : 1 ≤ n) :
    Mtwo μ l * xS μ l * Acoef μ l n ^ 2 * etaW μ l n ≤ Bn μ l n := by
  have hb := Bn_ge h hl hlm n hn
  have hM := Mtwo_le_Mstar h hl hlm
  have hx := (xS_pos (μ := μ) h hl).le
  have hA := Acoef_nonneg h hl n
  have heta := (etaW_mem h hl hlm n).1
  have hi : 0 ≤ iota μ l n := by
    unfold iota
    positivity [xS_pos (μ := μ) h hl, Qgeo_nonneg (by linarith : 0 ≤ l) n]
  have hBn := Bn_nonneg h hl hlm n
  have hdrop : 0 ≤ Mstar μ l * xS μ l * (iota μ l n * Bn μ l n) := by
    have hM0 : 0 ≤ Mstar μ l := (by
      have hMtwo0 : 0 ≤ Mtwo μ l := by
        unfold Mtwo
        positivity
      exact hMtwo0.trans hM)
    positivity
  have hbase : Mstar μ l * xS μ l * Acoef μ l n ^ 2 * etaW μ l n ≤ Bn μ l n := by
    nlinarith
  calc
    Mtwo μ l * xS μ l * Acoef μ l n ^ 2 * etaW μ l n ≤
        Mstar μ l * xS μ l * Acoef μ l n ^ 2 * etaW μ l n := by
      have hcoef : 0 ≤ xS μ l * Acoef μ l n ^ 2 * etaW μ l n := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hM hcoef]
    _ ≤ Bn μ l n := hbase

/-- Lemma 4.5 (`lem:scaled-two-children`): quantitative response of the first scaled
moment. -/
theorem dx_m1_ge (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    wbar μ l * Acoef μ l 1 * ((1 - tW μ l) / xS μ l - Acoef μ l 1) ≤
      dx μ (fun l => mMom μ l 1) l := by
  have hx := xS_pos (μ := μ) h hl
  have hA := Acoef_nonneg h hl 1
  have hw := (wbar_pos_f10 h hl hlm).le
  have hprod : dx μ (fun y => mMom μ y 1) l =
      dx μ (fun y => Acoef μ y 1) l * wbar μ l +
        Acoef μ l 1 * dx μ (fun y => etaW μ y 1) l := by
    rw [mMom_eq_mul (Nat.le_refl 1), dx_mul _ _ _
      (hasDerivAt_Acoef h hl 1).differentiableAt
      (hasDerivAt_etaW h hl hlm 1).differentiableAt]
    rfl
  have hAder := dx_Acoef_ge μ h hl (Nat.le_refl 1)
  have hcn : cn μ l 1 = 0 := by norm_num [cn]
  rw [hcn] at hAder
  have heta := x_dx_etaW h hl hlm 1 (Nat.le_refl 1)
  have hBn := Bn_one_ge h hl hlm
  rw [hprod]
  have hdxeta : dx μ (fun y => etaW μ y 1) l = Bn μ l 1 / xS μ l := by
    apply (eq_div_iff hx.ne').2
    simpa [mul_comm] using heta
  rw [hdxeta]
  have hmain : Acoef μ l 1 * (Bn μ l 1 / xS μ l) ≥
      Acoef μ l 1 * (wbar μ l * (1 - tW μ l) / xS μ l) := by
    apply mul_le_mul_of_nonneg_left _ hA
    exact div_le_div_of_nonneg_right hBn hx.le
  calc
    wbar μ l * Acoef μ l 1 * ((1 - tW μ l) / xS μ l - Acoef μ l 1) =
        Acoef μ l 1 ^ 2 * (0 - 1) * wbar μ l +
          Acoef μ l 1 * (wbar μ l * (1 - tW μ l) / xS μ l) := by ring
    _ ≤ dx μ (fun y => Acoef μ y 1) l * wbar μ l +
          Acoef μ l 1 * (Bn μ l 1 / xS μ l) :=
      add_le_add (mul_le_mul_of_nonneg_right hAder hw) hmain

/-- Lemma 4.5 (`lem:scaled-two-children`): quantitative response of the higher scaled
moments. -/
theorem dx_mn_ge (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (hn : 2 ≤ n) :
    mMom μ l n * Acoef μ l n * (cn μ l n - 1 + n * Acoef μ l n * Mtwo μ l) ≤
      dx μ (fun l => mMom μ l n) l := by
  have hx := xS_pos (μ := μ) h hl
  have hA := Acoef_nonneg h hl n
  have heta := (etaW_mem h hl hlm n).1
  have hprod : dx μ (fun y => mMom μ y n) l =
      dx μ (fun y => Acoef μ y n) l * etaW μ l n +
        Acoef μ l n * dx μ (fun y => etaW μ y n) l := by
    rw [mMom_eq_mul (by omega : 1 ≤ n), dx_mul _ _ _
      (hasDerivAt_Acoef h hl n).differentiableAt
      (hasDerivAt_etaW h hl hlm n).differentiableAt]
  rw [hprod, show mMom μ l n = Acoef μ l n * etaW μ l n by simp [mMom, Nat.ne_of_gt (by omega : 1 ≤ n)]]
  have hAder := dx_Acoef_ge μ h hl (by omega : 1 ≤ n)
  have hdxeta : dx μ (fun y => etaW μ y n) l = (n : ℝ) * Bn μ l n / xS μ l := by
    apply (eq_div_iff hx.ne').2
    simpa [mul_assoc, mul_comm] using x_dx_etaW h hl hlm n (by omega : 1 ≤ n)
  rw [hdxeta]
  have hBn := Bn_ge_Mtwo h hl hlm n (by omega : 1 ≤ n)
  have hresp : Acoef μ l n * ((n : ℝ) * Bn μ l n / xS μ l) ≥
      Acoef μ l n * ((n : ℝ) * (Mtwo μ l * xS μ l * Acoef μ l n ^ 2 * etaW μ l n) /
        xS μ l) := by
    apply mul_le_mul_of_nonneg_left _ hA
    apply div_le_div_of_nonneg_right _ hx.le
    exact mul_le_mul_of_nonneg_left hBn (Nat.cast_nonneg n)
  have hfirst : Acoef μ l n ^ 2 * (cn μ l n - 1) * etaW μ l n ≤
      dx μ (fun y => Acoef μ y n) l * etaW μ l n :=
    mul_le_mul_of_nonneg_right hAder heta
  field_simp [hx.ne'] at hresp ⊢
  nlinarith


private theorem dx_const (c : ℝ) (l : ℝ) : dx μ (fun _ => c) l = 0 := by
  simp [dx]

private theorem iota_pos_f10 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) :
    0 < iota μ l n := by
  unfold iota
  apply inv_pos.mpr
  exact add_pos_of_pos_of_nonneg (xS_pos (μ := μ) h hl)
    (Qgeo_nonneg (by linarith : 0 ≤ l) n)

private theorem xS_mul_iota_closed (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) :
    xS μ l * iota μ l n = pBr μ / (pBr μ + l ^ n - 1) := by
  have hp := pBr_pos h
  have ha : 0 < l - 1 := by linarith
  have hQ : Qgeo l n * (l - 1) = l ^ n - 1 := geom_sum_mul_of_one_le hl.le n
  have hden : xS μ l + Qgeo l n = (pBr μ + l ^ n - 1) / (l - 1) := by
    unfold xS
    field_simp [ha.ne']
    nlinarith
  have hbase : pBr μ + l ^ n - 1 ≠ 0 := by
    nlinarith [one_le_pow₀ hl.le (n := n), hp]
  rw [xS, iota, hden]
  field_simp [ha.ne', hp.ne', hbase]

private theorem hasDerivAt_xS_mul_iota (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) :
    HasDerivAt (fun y => xS μ y * iota μ y n)
      (-(pBr μ * (n : ℝ) * l ^ (n - 1)) / (pBr μ + l ^ n - 1) ^ 2) l := by
  have hD : 0 < pBr μ + l ^ n - 1 := by
    nlinarith [one_le_pow₀ hl.le (n := n), pBr_pos h]
  have hden := ((hasDerivAt_pow n l).const_add (pBr μ)).sub_const 1
  have hraw := (hasDerivAt_const l (pBr μ)).div hden hD.ne'
  have heq : (fun y => xS μ y * iota μ y n) =ᶠ[𝓝 l]
      (fun y => pBr μ / (pBr μ + y ^ n - 1)) := by
    filter_upwards [lt_mem_nhds hl] with y hy
    exact xS_mul_iota_closed h hy n
  apply (hraw.congr_deriv (by ring)).congr_of_eventuallyEq heq

private theorem dx_xS_mul_iota (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) :
    dx μ (fun y => xS μ y * iota μ y n) l = (n : ℝ) * Acoef μ l n ^ 2 := by
  have hD : pBr μ + l ^ n - 1 ≠ 0 := by
    nlinarith [one_le_pow₀ hl.le (n := n), pBr_pos h]
  have hp := (pBr_pos h).ne'
  rw [dx, (hasDerivAt_xS_mul_iota h hl n).deriv, Acoef_eq_closed hl n]
  have hpow := lpow_eq_kS hl (n - 1)
  rw [hpow]
  field_simp [hp, hD]

private theorem hasDerivAt_Ugeo_kS_f10 {l : ℝ} (hl : 1 < l) (n : ℕ) :
    HasDerivAt (fun y => Ugeo (kS y) n)
      (∑ j ∈ Finset.range n,
        (((2 * (j : ℤ) - n + 1 : ℤ) : ℝ) * kS l ^ (2 * (j : ℤ) - n)) *
          (1 / (2 * kS l))) l := by
  have hl0 : l ≠ 0 := by linarith
  have hk0 : kS l ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  unfold Ugeo
  apply HasDerivAt.fun_sum
  intro j hj
  have he : 2 * (j : ℤ) - n + 1 - 1 = 2 * (j : ℤ) - n := by ring
  convert (hasDerivAt_zpow (2 * (j : ℤ) - n + 1) (kS l) (Or.inl hk0)).comp l
    (Real.hasDerivAt_sqrt hl0) using 1
  · ext y
    rfl
  · simp only [kS, he]

private theorem Ugeo_pos_f10 {l : ℝ} (hl : 1 < l) {n : ℕ} (hn : 1 ≤ n) :
    0 < Ugeo (kS l) n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hU : (n : ℝ) ≤ Ugeo (kS l) n := by
    rw [Ugeo_eq_symSum]
    exact CertA.symSum_lower _ (Real.one_le_sqrt.2 (by linarith)) _
  exact hnR.trans_le hU

private theorem Ugeo_eq_inv_mul_geom_f10 {k : ℝ} (hk : 0 < k) {n : ℕ} (hn : 1 ≤ n) :
    Ugeo k n = (k ^ (n - 1))⁻¹ * Qgeo (k ^ 2) n := by
  rw [Ugeo, Qgeo, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← pow_mul]
  symm
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hk.ne']
  congr 1
  omega

private theorem Qgeo_kS_f10 {l : ℝ} (hl : 1 < l) (n : ℕ) :
    Qgeo (kS l ^ 2) n = Qgeo l n := by
  rw [kS_sq hl]

private theorem one_sub_xS_mul_iota (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) :
    1 - xS μ l * iota μ l n = Qgeo l n * iota μ l n := by
  have hsum : 0 < xS μ l + Qgeo l n :=
    add_pos_of_pos_of_nonneg (xS_pos (μ := μ) h hl)
      (Qgeo_nonneg (by linarith : 0 ≤ l) n)
  unfold iota
  field_simp [hsum.ne']
  ring

private theorem mMom_factorization (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    {n : ℕ} (hn : 1 ≤ n) :
    mMom μ l n = (Ugeo (kS l) n)⁻¹ *
      ((1 - xS μ l * iota μ l n) * etaW μ l n) := by
  have hk := kS_pos hl
  have hQ : 0 < Qgeo l n := by
    unfold Qgeo
    exact geom_sum_pos (by linarith) (by omega)
  have hsum : 0 < xS μ l + Qgeo l n :=
    add_pos_of_pos_of_nonneg (xS_pos (μ := μ) h hl) hQ.le
  rw [show mMom μ l n = Acoef μ l n * etaW μ l n by simp [mMom, Nat.ne_of_gt hn],
    Acoef, one_sub_xS_mul_iota h hl n,
    Ugeo_eq_inv_mul_geom_f10 hk hn, Qgeo_kS_f10 hl]
  unfold iota
  field_simp [hQ.ne', hsum.ne', hk.ne']

private theorem dx_response_factor_nonneg (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hM : 1 ≤ Mstar μ l) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ dx μ (fun y => (1 - xS μ y * iota μ y n) * etaW μ y n) l := by
  have hx := xS_pos (μ := μ) h hl
  have hR := hasDerivAt_xS_mul_iota h hl n
  have hetaD := hasDerivAt_etaW h hl hlm n
  have hdsub : dx μ (fun y => 1 - xS μ y * iota μ y n) l =
      -dx μ (fun y => xS μ y * iota μ y n) l := by
    rw [dx_sub _ _ _ (differentiableAt_const 1) hR.differentiableAt, dx_const]
    ring
  rw [dx_mul (fun y => 1 - xS μ y * iota μ y n) (fun y => etaW μ y n) l
      ((hasDerivAt_const l 1).sub hR).differentiableAt hetaD.differentiableAt,
    hdsub, dx_xS_mul_iota h hl n]
  have hdxeta : dx μ (fun y => etaW μ y n) l = (n : ℝ) * Bn μ l n / xS μ l := by
    apply (eq_div_iff hx.ne').2
    simpa [mul_comm] using x_dx_etaW h hl hlm n hn
  rw [hdxeta]
  have hb := Bn_ge h hl hlm n hn
  have hBn := Bn_nonneg h hl hlm n
  have hi := (iota_pos_f10 h hl n).le
  have hA := Acoef_nonneg h hl n
  have heta := (etaW_mem h hl hlm n).1
  have hE : 0 ≤ xS μ l * (iota μ l n * Bn μ l n + Acoef μ l n ^ 2 * etaW μ l n) := by
    positivity
  have hstrong : xS μ l * (iota μ l n * Bn μ l n + Acoef μ l n ^ 2 * etaW μ l n) ≤
      Bn μ l n := by
    calc
      _ ≤ Mstar μ l * xS μ l *
          (iota μ l n * Bn μ l n + Acoef μ l n ^ 2 * etaW μ l n) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hM) hE]
      _ ≤ Bn μ l n := hb
  have hcancel : xS μ l * Acoef μ l n ^ 2 * etaW μ l n ≤
      (1 - xS μ l * iota μ l n) * Bn μ l n := by
    nlinarith
  have hcoef : 0 ≤ (n : ℝ) / xS μ l := div_nonneg (Nat.cast_nonneg n) hx.le
  have hmul := mul_le_mul_of_nonneg_left hcancel hcoef
  have hid : (n : ℝ) / xS μ l * (xS μ l * Acoef μ l n ^ 2 * etaW μ l n) =
      (n : ℝ) * Acoef μ l n ^ 2 * etaW μ l n := by
    field_simp [hx.ne']
  rw [hid] at hmul
  have hid' : (n : ℝ) / xS μ l * ((1 - xS μ l * iota μ l n) * Bn μ l n) =
      (1 - xS μ l * iota μ l n) * ((n : ℝ) * Bn μ l n / xS μ l) := by ring
  rw [hid'] at hmul
  nlinarith

/-- Lemma 4.5 (`lem:scaled-two-children`): all scaled moments respond nonnegatively when
`Mstar ≥ 1`. -/
theorem dx_mn_nonneg (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hM : 1 ≤ Mstar μ l) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ dx μ (fun l => mMom μ l n) l := by
  have hUder := hasDerivAt_Ugeo_kS_f10 hl n
  have hU := Ugeo_pos_f10 hl hn
  have hR := hasDerivAt_xS_mul_iota h hl n
  have hetaD := hasDerivAt_etaW h hl hlm n
  have hfun : (fun y => mMom μ y n) =ᶠ[𝓝 l]
      (fun y => (Ugeo (kS y) n)⁻¹ * ((1 - xS μ y * iota μ y n) * etaW μ y n)) := by
    filter_upwards [lt_mem_nhds hl] with y hy
    exact mMom_factorization h hy hn
  have hrewrite : dx μ (fun y => mMom μ y n) l =
      dx μ (fun y => (Ugeo (kS y) n)⁻¹ *
        ((1 - xS μ y * iota μ y n) * etaW μ y n)) l := by
    unfold dx
    rw [hfun.deriv_eq]
  rw [hrewrite, dx_mul (fun y => (Ugeo (kS y) n)⁻¹)
    (fun y => (1 - xS μ y * iota μ y n) * etaW μ y n) l
    (hUder.inv hU.ne').differentiableAt
    (((hasDerivAt_const l 1).sub hR).fun_mul hetaD).differentiableAt]
  have hg : 0 ≤ (1 - xS μ l * iota μ l n) * etaW μ l n := by
    rw [one_sub_xS_mul_iota h hl n]
    exact mul_nonneg (mul_nonneg (Qgeo_nonneg (by linarith : 0 ≤ l) n)
      (iota_pos_f10 h hl n).le) (etaW_mem h hl hlm n).1
  exact add_nonneg
    (mul_nonneg (dx_inv_Ugeo_nonneg μ h hl hn) hg)
    (mul_nonneg (inv_pos.mpr hU).le (dx_response_factor_nonneg h hl hlm hM hn))

end LPPMonotonicityProof.Analytic
