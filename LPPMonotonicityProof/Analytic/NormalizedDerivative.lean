module

public import LPPMonotonicityProof.Analytic.ScaledMark
public import LPPMonotonicityProof.Analytic.ScaledTwoChildren
public import LPPMonotonicityProof.Analytic.Terminal
public import LPPMonotonicityProof.Analytic.Certificates
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The normalized derivative and its infinite tails

This module normalizes `scaled_mark` at the actual offspring law, as in the proof of
Lemma A.1 (`lem:large-finite`), proves the two tail bounds of that proof, and shows
that the normalized data of the actual law satisfy `ScaledDomain`, the hypothesis
of `CertACovers`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- The normalized terminal law. -/
noncomputable def en (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) (n : ℕ) : ℝ :=
  etaW μ l n / wbar μ l

/-- The normalized scaled moments. -/
noncomputable def un (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) (n : ℕ) : ℝ :=
  mMom μ l n / wbar μ l

/-- `R₁₆ = Σ_{n>16} uₙ²` at the actual law. -/
noncomputable def tailR (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) : ℝ :=
  ∑' n : ℕ, (mMom μ l (n + 17) / wbar μ l) ^ 2

/-- `T₁₆ = Σ_{n>16} (uₙ-uₙ₊₁)²` at the actual law. -/
noncomputable def tailT (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) : ℝ :=
  ∑' n : ℕ, ((mMom μ l (n + 17) - mMom μ l (n + 18)) / wbar μ l) ^ 2

private lemma certK_actual (l : ℝ) : certK (l - 1) = kS l := by
  unfold certK kS
  congr 1
  ring

private lemma certIota_actual (l : ℝ) (n : ℕ) :
    certIota (xS μ l) (l - 1) n = iota μ l n := by
  unfold certIota iota certQ Qgeo
  rw [show 1 + (l - 1) = l by ring]

private lemma prefixFactor_actual (l : ℝ) (n : ℕ) :
    prefixFactor (xS μ l) (l - 1) n = Acoef μ l n := by
  unfold prefixFactor Acoef
  rw [certK_actual, certIota_actual]

private lemma scaled_u_actual (l : ℝ) (n : ℕ) :
    ScaledLB.u (xS μ l) (l - 1) (en μ l) n = un μ l n := by
  by_cases hn : n = 0
  · subst n
    simp [ScaledLB.u, un, mMom]
  · simp [ScaledLB.u, un, en, hn, prefixFactor_actual, mMom, div_mul_eq_mul_div,
      mul_div_assoc]

private lemma scaled_gap_actual (l : ℝ) (n : ℕ) :
    ScaledLB.gap (xS μ l) (l - 1) (en μ l) n = un μ l n - un μ l (n + 1) := by
  simp [ScaledLB.gap, scaled_u_actual]

private lemma un_nonneg (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : 0 ≤ un μ l n := by
  exact div_nonneg (mMom_mem h hl hlm n).1 (wbar_pos_f10 h hl hlm).le

private lemma un_one_pos (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : 0 < un μ l 1 := by
  exact div_pos (mMom_one_pos_f10 h hl hlm) (wbar_pos_f10 h hl hlm)

private lemma un_succ_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (hn : 1 ≤ n) : un μ l (n + 1) ≤ un μ l n := by
  have hk : 1 ≤ kS l := (one_lt_kS hl).le
  have hm := mMom_succ_le h hl hlm hn
  have hm0 := (mMom_mem h hl hlm n).1
  have hw := wbar_pos_f10 h hl hlm
  apply (div_le_div_iff₀ hw hw).2
  calc
    mMom μ l (n + 1) * wbar μ l ≤ (mMom μ l n / kS l) * wbar μ l :=
      mul_le_mul_of_nonneg_right hm hw.le
    _ ≤ mMom μ l n * wbar μ l := by
      have hdiv : mMom μ l n / kS l ≤ mMom μ l n := by
        rw [div_le_iff₀ (kS_pos hl)]
        nlinarith
      exact mul_le_mul_of_nonneg_right hdiv hw.le
    _ = mMom μ l n * wbar μ l := rfl

private lemma en_succ_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    en μ l n ≤ en μ l m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      have hstep : en μ l (m + (j + 1)) ≤ en μ l (m + j) := by
        have hd := (normalized_moments h hl hlm).2.2.2.2.2.1 (m + j) (by omega)
        exact sub_nonneg.mp hd.1
      exact hstep.trans (ih (by omega))

private lemma Mtwo_normalized (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    Mtwo μ l = 2 * (1 - wbar μ l * (2 - tW μ l)) := by
  letI := splitLaw_prob h
  have hW : Integrable (Wt l) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow' h hl hlm 1
  have hW2 := integrable_Wt_pow' h hl hlm 2
  have hw := wbar_pos_f10 h hl hlm
  have heq : (fun T => (1 - Wt l T) ^ 2) =
      (fun T => 1 - 2 * Wt l T + Wt l T ^ 2) := by
    funext T
    ring
  have h1 : Integrable (fun _ : Tree => (1 : ℝ)) (splitLaw μ) := integrable_const 1
  unfold Mtwo
  rw [heq, integral_add (f := fun T => 1 - 2 * Wt l T) (g := fun T => Wt l T ^ 2)
      (h1.sub (hW.const_mul 2)) hW2,
    integral_sub (f := fun _ => (1 : ℝ)) (g := fun T => 2 * Wt l T)
      h1 (hW.const_mul 2), integral_const, integral_const_mul]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one]
  have hw' : (∫ T, Wt l T ∂splitLaw μ) ≠ 0 := by
    simpa only [wbar, etaW, pow_one] using hw.ne'
  unfold tW wbar etaW
  field_simp [hw'] <;> ring

private lemma curv_actual {l : ℝ} (hl : 1 < l) (n : ℕ) :
    ScaledLB.curv (xS μ l) (l - 1) n = cn μ l n := by
  have hl0 : 0 < l := by linarith
  have hr : l ^ (3 / 2 : ℝ) = l * kS l := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hl0,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    rfl
  unfold ScaledLB.curv cn
  rw [certK_actual, hr]
  ring

/-- The normalized coefficient lower bounds from Lemma 4.5 (`lem:scaled-two-children`). -/
private lemma ell_le_dx (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (hn : 1 ≤ n) :
    ScaledLB.ell (xS μ l) (l - 1) (tW μ l) (wbar μ l) (en μ l) n ≤
      dx μ (fun y => mMom μ y n) l / wbar μ l := by
  have hw := wbar_pos_f10 h hl hlm
  by_cases hn1 : n = 1
  · subst n
    have hd := dx_m1_ge h hl hlm
    rw [ScaledLB.ell, if_pos rfl, prefixFactor_actual]
    apply (le_div_iff₀ hw).2
    calc
      Acoef μ l 1 * ((1 - tW μ l) / xS μ l - Acoef μ l 1) * wbar μ l =
          wbar μ l * Acoef μ l 1 * ((1 - tW μ l) / xS μ l - Acoef μ l 1) := by ring
      _ ≤ _ := hd
  · have hn2 : 2 ≤ n := by omega
    have hd := dx_mn_ge h hl hlm hn2
    rw [ScaledLB.ell, if_neg hn1, scaled_u_actual, prefixFactor_actual, curv_actual hl]
    apply (le_div_iff₀ hw).2
    calc
      un μ l n * Acoef μ l n *
          (cn μ l n - 1 + 2 * (n : ℝ) * Acoef μ l n *
            (1 - wbar μ l * (2 - tW μ l))) * wbar μ l =
          mMom μ l n * Acoef μ l n * (cn μ l n - 1 + n * Acoef μ l n * Mtwo μ l) := by
            rw [Mtwo_normalized h hl hlm]
            unfold un
            field_simp [hw.ne'] <;> ring
      _ ≤ _ := hd

private lemma Acoef_sq_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (n : ℕ) (hn : 1 ≤ n) :
    Acoef μ l n ^ 2 ≤ iota μ l (n - 1) - iota μ l n := by
  simpa [Acoef, AcoefProv, iota, iotaProv, xS, xSProv, pBrProv, pBr, kS, kSProv,
    Qgeo, QgeoProv] using (Acoef_le μ hl hn (pBr_pos h)).2

private lemma tailR_bounds_aux (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : 0 ≤ tailR μ l ∧
    tailR μ l ≤ (en μ l 17) ^ 2 * iota μ l 16 := by
  change 0 ≤ (∑' n : ℕ, un μ l (n + 17) ^ 2) ∧
    (∑' n : ℕ, un μ l (n + 17) ^ 2) ≤ (en μ l 17) ^ 2 * iota μ l 16
  have he0 : 0 ≤ en μ l 17 := by
    exact div_nonneg (etaW_mem h hl hlm 17).1 (wbar_pos_f10 h hl hlm).le
  have hterm (n : ℕ) : un μ l (n + 17) ^ 2 ≤
      en μ l 17 ^ 2 * (iota μ l (n + 16) - iota μ l (n + 17)) := by
    have hA := Acoef_nonneg h hl (n + 17)
    have hAe : un μ l (n + 17) = Acoef μ l (n + 17) * en μ l (n + 17) := by
      rw [← scaled_u_actual (μ := μ) l (n + 17), ScaledLB.u]
      simp [prefixFactor_actual]
    have he : en μ l (n + 17) ≤ en μ l 17 := en_succ_le h hl hlm (by omega) (by omega)
    have he' : 0 ≤ en μ l (n + 17) := by
      exact div_nonneg (etaW_mem h hl hlm _).1 (wbar_pos_f10 h hl hlm).le
    have hAsq := Acoef_sq_le h hl (n + 17) (by omega)
    have hi : n + 17 - 1 = n + 16 := by omega
    rw [hi] at hAsq
    rw [hAe]
    have hs : (Acoef μ l (n + 17) * en μ l (n + 17)) ^ 2 ≤
        (iota μ l (n + 16) - iota μ l (n + 17)) * en μ l 17 ^ 2 := by
      have he_sq : en μ l (n + 17) ^ 2 ≤ en μ l 17 ^ 2 := by nlinarith
      calc
        _ = Acoef μ l (n + 17) ^ 2 * en μ l (n + 17) ^ 2 := by ring
        _ ≤ (iota μ l (n + 16) - iota μ l (n + 17)) * en μ l (n + 17) ^ 2 :=
          mul_le_mul_of_nonneg_right hAsq (sq_nonneg _)
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left he_sq
          have hi0 := (sq_nonneg (Acoef μ l (n + 17))).trans hAsq
          linarith
    nlinarith
  have hnonneg (n : ℕ) : 0 ≤ un μ l (n + 17) ^ 2 := sq_nonneg _
  have hfin (N : ℕ) : ∑ n ∈ Finset.range N, un μ l (n + 17) ^ 2 ≤
      en μ l 17 ^ 2 * iota μ l 16 := by
    calc
      _ ≤ ∑ n ∈ Finset.range N,
          en μ l 17 ^ 2 * (iota μ l (n + 16) - iota μ l (n + 17)) := by
        exact Finset.sum_le_sum fun n _ => hterm n
      _ = en μ l 17 ^ 2 * (iota μ l 16 - iota μ l (N + 16)) := by
        rw [← Finset.mul_sum]
        congr 1
        simpa [add_assoc] using
          (Finset.sum_range_sub' (fun n => iota μ l (n + 16)) N)
      _ ≤ _ := by
        have hi : 0 ≤ iota μ l (N + 16) := by
          unfold iota
          positivity [xS_pos (μ := μ) h hl, Qgeo_nonneg (by linarith : 0 ≤ l) (N + 16)]
        nlinarith [mul_nonneg (sq_nonneg (en μ l 17)) hi]
  constructor
  · exact tsum_nonneg hnonneg
  · exact Real.tsum_le_of_sum_range_le hnonneg hfin

/-- **Square tail.** The normalized square tail is nonnegative and telescopes against `ι₁₆`. -/
theorem tailR_bounds (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    0 ≤ tailR μ l ∧
      tailR μ l ≤ (etaW μ l 17 / wbar μ l) ^ 2 * iota μ l 16 := by
  exact tailR_bounds_aux h hl hlm

private lemma tailT_eq_un (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) :
    tailT μ l = ∑' n : ℕ, (un μ l (n + 17) - un μ l (n + 18)) ^ 2 := by
  unfold tailT
  apply tsum_congr
  intro n
  dsimp [un]
  ring

private lemma tailT_bounds_aux (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : 0 ≤ tailT μ l ∧ tailT μ l ≤ un μ l 17 ^ 2 := by
  rw [tailT_eq_un]
  have hterm (n : ℕ) : (un μ l (n + 17) - un μ l (n + 18)) ^ 2 ≤
      un μ l (n + 17) ^ 2 - un μ l (n + 18) ^ 2 := by
    have h0 := un_nonneg h hl hlm (n + 18)
    have hle := un_succ_le h hl hlm (n := n + 17) (by omega)
    have hn : un μ l (n + 18) = un μ l (n + 17 + 1) := by congr 2 <;> omega
    rw [hn] at h0 hle ⊢
    nlinarith [sq_nonneg (un μ l (n + 17) - un μ l (n + 17 + 1))]
  have hfin (N : ℕ) : ∑ n ∈ Finset.range N, (un μ l (n + 17) - un μ l (n + 18)) ^ 2 ≤
      un μ l 17 ^ 2 := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, (un μ l (n + 17) ^ 2 - un μ l (n + 18) ^ 2) := by
        exact Finset.sum_le_sum fun n _ => hterm n
      _ = un μ l 17 ^ 2 - un μ l (N + 17) ^ 2 := by
        simpa [add_assoc] using
          (Finset.sum_range_sub' (fun n => un μ l (n + 17) ^ 2) N)
      _ ≤ _ := by exact sub_le_self _ (sq_nonneg _)
  constructor
  · exact tsum_nonneg fun n => sq_nonneg _
  · exact Real.tsum_le_of_sum_range_le (fun n => sq_nonneg _) hfin

/-- **Gap-square tail.** The normalized gap-square tail is nonnegative and at most `u₁₇²`. -/
theorem tailT_bounds (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    0 ≤ tailT μ l ∧
      tailT μ l ≤ (Acoef μ l 17 * etaW μ l 17 / wbar μ l) ^ 2 := by
  obtain ⟨h0, hle⟩ := tailT_bounds_aux h hl hlm
  refine ⟨h0, hle.trans_eq ?_⟩
  rw [← scaled_u_actual (μ := μ) l 17]
  simp [ScaledLB.u, prefixFactor_actual, en, div_mul_eq_mul_div, mul_div_assoc]

private lemma sum_Icc16 (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 16, f n) = ∑ n ∈ Finset.range 16, f (n + 1) := by
  rw [show Finset.Icc 1 16 = Finset.Ico 1 17 by ext n; simp; omega,
    Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.add_comm 1 n]

private lemma mMom_eq_w_mul_un (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : mMom μ l n = wbar μ l * un μ l n := by
  unfold un
  field_simp [(wbar_pos_f10 h hl hlm).ne']

private lemma Ssc_div_normalized (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    Ssc μ l / wbar μ l ^ 2 = ∑' n : ℕ, un μ l (n + 1) ^ 2 := by
  unfold Ssc
  rw [← tsum_div_const]
  apply tsum_congr
  intro n
  rw [mMom_eq_w_mul_un h hl hlm]
  field_simp [(wbar_pos_f10 h hl hlm).ne']

private lemma Tsc_div_normalized (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    Tsc μ l / wbar μ l ^ 2 = ∑' n : ℕ, un μ l (n + 1) * un μ l (n + 2) := by
  unfold Tsc
  rw [← tsum_div_const]
  apply tsum_congr
  intro n
  rw [mMom_eq_w_mul_un h hl hlm, mMom_eq_w_mul_un h hl hlm]
  field_simp [(wbar_pos_f10 h hl hlm).ne']

private lemma summable_un_sq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : Summable (fun n : ℕ => un μ l (n + 1) ^ 2) := by
  have hs := (summable_Ssc h hl hlm).div_const (wbar μ l ^ 2)
  exact hs.congr fun n => by
    unfold un
    rw [div_pow]

private lemma summable_un_cross (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : Summable (fun n : ℕ => un μ l (n + 1) * un μ l (n + 2)) := by
  have hs := (summable_Tsc h hl hlm).div_const (wbar μ l ^ 2)
  exact hs.congr fun n => by
    unfold un
    field_simp

private lemma summable_un_gap (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : Summable (fun n : ℕ => (un μ l (n + 1) - un μ l (n + 2)) ^ 2) := by
  have hs := summable_un_sq h hl hlm
  have hshift : Summable (fun n : ℕ => un μ l (n + 2) ^ 2) :=
    (summable_nat_add_iff 1).2 hs
  have ht := (summable_un_cross h hl hlm).mul_left 2
  exact ((hs.add hshift).sub ht).congr fun n => by ring

private lemma normalized_gap_identity (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    2 * (Ssc μ l / wbar μ l ^ 2 - Tsc μ l / wbar μ l ^ 2) =
      un μ l 1 ^ 2 + ∑' n : ℕ, (un μ l (n + 1) - un μ l (n + 2)) ^ 2 := by
  have hs := summable_un_sq h hl hlm
  have hshift : Summable (fun n : ℕ => un μ l (n + 2) ^ 2) :=
    (summable_nat_add_iff 1).2 hs
  have ht := summable_un_cross h hl hlm
  have hg := summable_un_gap h hl hlm
  have hsplit := hs.sum_add_tsum_nat_add 1
  have hshift_tsum : (∑' n : ℕ, un μ l (n + 2) ^ 2) =
      (∑' n : ℕ, un μ l (n + 1) ^ 2) - un μ l 1 ^ 2 := by
    simp only [Finset.sum_range_one] at hsplit
    linarith
  rw [Ssc_div_normalized h hl hlm, Tsc_div_normalized h hl hlm]
  have hgap_sum : (∑' n : ℕ, (un μ l (n + 1) - un μ l (n + 2)) ^ 2) =
      (∑' n : ℕ, un μ l (n + 1) ^ 2) + (∑' n : ℕ, un μ l (n + 2) ^ 2) -
        2 * ∑' n : ℕ, un μ l (n + 1) * un μ l (n + 2) := by
    calc
      _ = ∑' n : ℕ, (un μ l (n + 1) ^ 2 + un μ l (n + 2) ^ 2 -
          2 * (un μ l (n + 1) * un μ l (n + 2))) := by
        apply tsum_congr
        intro n
        ring
      _ = _ := by
        rw [(hs.add hshift).tsum_sub (ht.mul_left 2), hs.tsum_add hshift,
          tsum_mul_left]
  rw [hgap_sum, hshift_tsum]
  ring

private lemma Ssc_normalized (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    Ssc μ l = wbar μ l ^ 2 *
      ScaledLB.P (xS μ l) (l - 1) (en μ l) (tailR μ l) := by
  have hs := (summable_Ssc h hl hlm).sum_add_tsum_nat_add 16
  have hw := wbar_pos_f10 h hl hlm
  unfold ScaledLB.P
  rw [sum_Icc16]
  calc
    Ssc μ l = (∑ n ∈ Finset.range 16, mMom μ l (n + 1) ^ 2) +
        ∑' n : ℕ, mMom μ l (n + 17) ^ 2 := by
      change (∑' n : ℕ, mMom μ l (n + 1) ^ 2) = _
      simpa [add_assoc] using hs.symm
    _ = (∑ n ∈ Finset.range 16, wbar μ l ^ 2 * un μ l (n + 1) ^ 2) +
        ∑' n : ℕ, wbar μ l ^ 2 * un μ l (n + 17) ^ 2 := by
      congr 1
      · apply Finset.sum_congr rfl
        intro n hn
        rw [mMom_eq_w_mul_un h hl hlm]
        ring
      · apply tsum_congr
        intro n
        rw [mMom_eq_w_mul_un h hl hlm]
        ring
    _ = _ := by
      have hupre : (∑ n ∈ Finset.range 16, un μ l (n + 1) ^ 2) =
          ∑ n ∈ Finset.range 16, ScaledLB.u (xS μ l) (l - 1) (en μ l) (n + 1) ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [scaled_u_actual]
      have htail : (∑' n : ℕ, un μ l (n + 17) ^ 2) = tailR μ l := rfl
      rw [← Finset.mul_sum, tsum_mul_left, ← mul_add, hupre, htail]

private lemma D_normalized (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    Ssc μ l - Tsc μ l = wbar μ l ^ 2 *
      ScaledLB.D (xS μ l) (l - 1) (en μ l) (tailT μ l) := by
  have hw := wbar_pos_f10 h hl hlm
  have hgap := normalized_gap_identity h hl hlm
  have hsplit := (summable_un_gap h hl hlm).sum_add_tsum_nat_add 16
  unfold ScaledLB.D
  rw [sum_Icc16]
  have hsplit' : (∑ n ∈ Finset.range 16, (un μ l (n + 1) - un μ l (n + 2)) ^ 2) +
      (∑' n : ℕ, (un μ l (n + 17) - un μ l (n + 18)) ^ 2) =
      ∑' n : ℕ, (un μ l (n + 1) - un μ l (n + 2)) ^ 2 := by
    simpa [add_assoc] using hsplit
  simp only [tailT_eq_un, scaled_u_actual, scaled_gap_actual]
  have hsplit'' : (∑ n ∈ Finset.range 16, (un μ l (n + 1) - un μ l (n + 1 + 1)) ^ 2) +
      (∑' n : ℕ, (un μ l (n + 17) - un μ l (n + 18)) ^ 2) =
      ∑' n : ℕ, (un μ l (n + 1) - un μ l (n + 2)) ^ 2 := by
    simpa only [Nat.add_one] using hsplit'
  rw [add_assoc, hsplit'', ← hgap]
  field_simp [hw.ne'] <;> ring

private lemma Tsc_normalized (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    Tsc μ l = wbar μ l ^ 2 *
      (ScaledLB.P (xS μ l) (l - 1) (en μ l) (tailR μ l) -
        ScaledLB.D (xS μ l) (l - 1) (en μ l) (tailT μ l)) := by
  have hS := Ssc_normalized h hl hlm
  have hD := D_normalized h hl hlm
  nlinarith

private lemma gamS_actual (l : ℝ) : gamS l = ScaledLB.gamma (l - 1) := by
  unfold gamS ScaledLB.gamma
  rw [certK_actual]
  ring

private lemma PgQ_normalized (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    Ssc μ l - gamS l * Tsc μ l = wbar μ l ^ 2 *
      ScaledLB.PgQ (xS μ l) (l - 1) (en μ l) (tailR μ l) (tailT μ l) := by
  rw [gamS_actual, Ssc_normalized h hl hlm, Tsc_normalized h hl hlm]
  unfold ScaledLB.PgQ ScaledLB.gamma
  rw [certK_actual]
  have hk := kS_pos hl
  have hk2 := kS_sq hl
  have hk2' : (kS l - 1) ^ 2 = l - 2 * kS l + 1 := by nlinarith
  rw [hk2']
  field_simp [hk.ne'] <;> ring

private lemma hsc_normalized (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    hsc μ l = wbar μ l *
      ScaledLB.H (xS μ l) (l - 1) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) := by
  have hw := wbar_pos_f10 h hl hlm
  have hk := kS_pos hl
  have hk2 := kS_sq hl
  unfold hsc ScaledLB.H ScaledLB.J
  rw [Ssc_normalized h hl hlm, Tsc_normalized h hl hlm,
    mMom_eq_w_mul_un h hl hlm, ← scaled_u_actual, certK_actual]
  have hk2' : (kS l - 1) ^ 2 = l - 2 * kS l + 1 := by nlinarith
  rw [hk2']
  field_simp [hw.ne', hk.ne'] <;> ring

private lemma Ccoef_normalized (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) :
    Ccoef μ l n = ScaledLB.C (xS μ l) (l - 1) (wbar μ l) (en μ l) n := by
  have hw := wbar_pos_f10 h hl hlm
  unfold Ccoef ScaledLB.C
  rw [certK_actual, mMom_eq_w_mul_un h hl hlm, mMom_eq_w_mul_un h hl hlm,
    mMom_eq_w_mul_un h hl hlm, ← scaled_u_actual, ← scaled_u_actual, ← scaled_u_actual]
  congr 1
  ring

private lemma hsc_pos_a1b (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : 0 < hsc μ l := by
  exact (div_pos (mMom_one_pos_f10 h hl hlm) (by norm_num)).trans_le
    (hsc_bounds h hl hlm).1

private lemma G_normalized (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) :
    ScaledLB.G (xS μ l) (l - 1) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) n =
      2 * hsc μ l * Dcoef μ l n / wbar μ l ^ 2 := by
  have hw := wbar_pos_f10 h hl hlm
  have hh := hsc_pos_a1b h hl hlm
  have hV : Vsc μ l = wbar μ l ^ 2 *
      ScaledLB.P (xS μ l) (l - 1) (en μ l) (tailR μ l) / (2 * hsc μ l) := by
    rw [Vsc_eq h hl hlm, Ssc_normalized h hl hlm]
  have hH : ScaledLB.H (xS μ l) (l - 1) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) =
      hsc μ l / wbar μ l := by
    rw [hsc_normalized h hl hlm]
    field_simp [hw.ne']
  unfold ScaledLB.G Dcoef
  rw [hH, ← Ccoef_normalized h hl hlm,
    mMom_eq_w_mul_un h hl hlm, ← scaled_u_actual, hV]
  field_simp [hw.ne', hh.ne'] <;> ring

/-- At the actual law, `Gₙ` is nonnegative and bounded by `2u₁uₙ`. -/
theorem actual_G_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ ScaledLB.G (xS μ l) (l - 1) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) n ∧
    ScaledLB.G (xS μ l) (l - 1) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) n ≤
      2 * un μ l 1 * un μ l n := by
  have hw := wbar_pos_f10 h hl hlm
  have hh := hsc_pos_a1b h hl hlm
  have hD := Dcoef_mem μ h hl hlm hn
  have hhu : hsc μ l / wbar μ l ≤ un μ l 1 := by
    apply (div_le_iff₀ hw).2
    rw [show un μ l 1 * wbar μ l = mMom μ l 1 by
      rw [mMom_eq_w_mul_un h hl hlm]; ring]
    exact (hsc_bounds h hl hlm).2
  have hDu : Dcoef μ l n / wbar μ l ≤ un μ l n := by
    apply (div_le_iff₀ hw).2
    rw [show un μ l n * wbar μ l = mMom μ l n by
      rw [mMom_eq_w_mul_un h hl hlm]; ring]
    exact hD.2
  rw [G_normalized h hl hlm]
  constructor
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hh.le) hD.1) (sq_nonneg _)
  · have hform : 2 * hsc μ l * Dcoef μ l n / wbar μ l ^ 2 =
        2 * (hsc μ l / wbar μ l) * (Dcoef μ l n / wbar μ l) := by
      field_simp [hw.ne'] <;> ring
    rw [hform]
    calc
      2 * (hsc μ l / wbar μ l) * (Dcoef μ l n / wbar μ l) ≤
          2 * un μ l 1 * (Dcoef μ l n / wbar μ l) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hhu (by norm_num)) (div_nonneg hD.1 hw.le)
      _ ≤ 2 * un μ l 1 * un μ l n := by
        exact mul_le_mul_of_nonneg_left hDu
          (mul_nonneg (by norm_num) (un_nonneg h hl hlm 1))

/-- The actual-law `S - γT` lower bound required by `ScaledDomain`. -/
theorem actual_PgQ_ge (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    (l - 1) * ScaledLB.P (xS μ l) (l - 1) (en μ l) (tailR μ l) /
        (2 * (1 + (l - 1))) ≤
      ScaledLB.PgQ (xS μ l) (l - 1) (en μ l) (tailR μ l) (tailT μ l) := by
  have hw := wbar_pos_f10 h hl hlm
  have hw2 : 0 < wbar μ l ^ 2 := sq_pos_of_pos hw
  apply (mul_le_mul_iff_right₀ hw2).mp
  calc
    wbar μ l ^ 2 * ((l - 1) * ScaledLB.P (xS μ l) (l - 1) (en μ l) (tailR μ l) /
        (2 * (1 + (l - 1)))) = (l - 1) * Ssc μ l / (2 * l) := by
      rw [Ssc_normalized h hl hlm]
      field_simp [hw.ne'] <;> ring
    _ ≤ Ssc μ l - gamS l * Tsc μ l := (S_sub_gamT μ h hl hlm).1
    _ = _ := PgQ_normalized h hl hlm

private lemma ell_tail_lower (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (hn : 17 ≤ n) :
    -un μ l n / (n : ℝ) ≤
      ScaledLB.ell (xS μ l) (l - 1) (tW μ l) (wbar μ l) (en μ l) n := by
  have hu := un_nonneg h hl hlm n
  have hA := Acoef_nonneg h hl n
  have hAle : Acoef μ l n ≤ 1 / (n : ℝ) := by
    simpa [Acoef, AcoefProv, iota, iotaProv, xS, xSProv, pBrProv, pBr, kS, kSProv,
      Qgeo, QgeoProv] using (Acoef_le μ hl (n := n) (by omega) (pBr_pos h)).1
  have hcurv : 0 ≤ ScaledLB.curv (xS μ l) (l - 1) n := by
    rw [curv_actual hl]
    unfold cn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hnum : 0 ≤ (l - 1) ^ 2 * (n : ℝ) * ((n : ℝ) ^ 2 - 1) := by
      have hs : 0 ≤ (n : ℝ) ^ 2 - 1 := by nlinarith
      positivity
    exact div_nonneg hnum (by
      positivity [xS_pos (μ := μ) h hl, Real.rpow_pos_of_pos (by linarith : 0 < l) (3 / 2 : ℝ)])
  have hM : 0 ≤ 1 - wbar μ l * (2 - tW μ l) := by
    have hm : 0 ≤ Mtwo μ l := by
      unfold Mtwo
      positivity
    rw [Mtwo_normalized h hl hlm] at hm
    linarith
  rw [ScaledLB.ell, if_neg (by omega : n ≠ 1), scaled_u_actual, prefixFactor_actual]
  have hbracket : -1 ≤ ScaledLB.curv (xS μ l) (l - 1) n - 1 +
      2 * (n : ℝ) * Acoef μ l n * (1 - wbar μ l * (2 - tW μ l)) := by
    have hp : 0 ≤ 2 * (n : ℝ) * Acoef μ l n * (1 - wbar μ l * (2 - tW μ l)) := by
      positivity
    linarith
  calc
    -un μ l n / (n : ℝ) ≤ -(un μ l n * Acoef μ l n) := by
      have hh := mul_le_mul_of_nonneg_left hAle hu
      have hh' : un μ l n * Acoef μ l n ≤ un μ l n / (n : ℝ) := by
        simpa [div_eq_mul_inv, mul_assoc] using hh
      simpa only [neg_div] using neg_le_neg hh'
    _ ≤ un μ l n * Acoef μ l n *
        (ScaledLB.curv (xS μ l) (l - 1) n - 1 +
          2 * (n : ℝ) * Acoef μ l n * (1 - wbar μ l * (2 - tW μ l))) := by
      have hh := mul_le_mul_of_nonneg_left hbracket (mul_nonneg hu hA)
      nlinarith

private lemma tail_deriv_lower (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (hn : 17 ≤ n) :
    -2 * un μ l 1 * un μ l n ^ 2 / 17 ≤
      ScaledLB.G (xS μ l) (l - 1) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) n *
        (dx μ (fun y => mMom μ y n) l / wbar μ l) := by
  obtain ⟨hG0, hGle⟩ := actual_G_mem h hl hlm (by omega : 1 ≤ n)
  have hel0 := ell_tail_lower h hl hlm hn
  have hell := ell_le_dx h hl hlm (by omega : 1 ≤ n)
  have hu := un_nonneg h hl hlm n
  have hu1 := un_nonneg h hl hlm 1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnl : un μ l n / (n : ℝ) ≤ un μ l n / 17 := by
    apply div_le_div_of_nonneg_left hu (by norm_num) (by exact_mod_cast hn)
  have hchain :
      (2 * un μ l 1 * un μ l n) * (-un μ l n / 17) ≤
        ScaledLB.G (xS μ l) (l - 1) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) n *
          ScaledLB.ell (xS μ l) (l - 1) (tW μ l) (wbar μ l) (en μ l) n := by
    calc
      _ ≤ (2 * un μ l 1 * un μ l n) * (-un μ l n / (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [neg_div] using neg_le_neg hnl
      _ ≤ ScaledLB.G (xS μ l) (l - 1) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) n *
          (-un μ l n / (n : ℝ)) := by
        apply mul_le_mul_of_nonpos_right hGle
        simpa only [neg_div] using neg_nonpos.mpr (div_nonneg hu hnR.le)
      _ ≤ _ := mul_le_mul_of_nonneg_left hel0 hG0
  calc
    -2 * un μ l 1 * un μ l n ^ 2 / 17 =
        (2 * un μ l 1 * un μ l n) * (-un μ l n / 17) := by ring
    _ ≤ _ := hchain
    _ ≤ _ := mul_le_mul_of_nonneg_left hell hG0

private lemma normalized_mark (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    2 * hsc μ l ^ 2 * dx μ (Vsc μ) l / wbar μ l ^ 3 =
      wbar μ l * ScaledLB.P (xS μ l) (l - 1) (en μ l) (tailR μ l) *
        ScaledLB.PgQ (xS μ l) (l - 1) (en μ l) (tailR μ l) (tailT μ l) +
      ∑' n : ℕ,
        ScaledLB.G (xS μ l) (l - 1) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) (n + 1) *
          (dx μ (fun y => mMom μ y (n + 1)) l / wbar μ l) := by
  have hw := wbar_pos_f10 h hl hlm
  have hh := hsc_pos_a1b h hl hlm
  obtain ⟨hs, heq⟩ := scaled_mark μ h hl hlm
  have hf : Summable (fun n : ℕ =>
      ScaledLB.G (xS μ l) (l - 1) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) (n + 1) *
        (dx μ (fun y => mMom μ y (n + 1)) l / wbar μ l)) := by
    apply (hs.mul_left (2 * hsc μ l / wbar μ l ^ 3)).congr
    intro n
    rw [G_normalized h hl hlm]
    field_simp [hw.ne'] <;> ring
  calc
    2 * hsc μ l ^ 2 * dx μ (Vsc μ) l / wbar μ l ^ 3 =
        (2 * hsc μ l / wbar μ l ^ 3) * (hsc μ l * dx μ (Vsc μ) l) := by ring
    _ = (2 * hsc μ l / wbar μ l ^ 3) *
        (Vsc μ l * (Ssc μ l - gamS l * Tsc μ l) +
          ∑' n : ℕ, Dcoef μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l) := by rw [heq]
    _ = (2 * hsc μ l / wbar μ l ^ 3) * (Vsc μ l * (Ssc μ l - gamS l * Tsc μ l)) +
        ∑' n : ℕ, (2 * hsc μ l / wbar μ l ^ 3) *
          (Dcoef μ l (n + 1) * dx μ (fun y => mMom μ y (n + 1)) l) := by
      rw [mul_add, ← tsum_mul_left]
    _ = _ := by
      congr 1
      · rw [Vsc_eq h hl hlm, PgQ_normalized h hl hlm, Ssc_normalized h hl hlm]
        field_simp [hw.ne', hh.ne'] <;> ring
      · apply tsum_congr
        intro n
        rw [G_normalized h hl hlm]
        field_simp [hw.ne'] <;> ring

/-- **Proof of Lemma A.1, normalized derivative.** The retained 16-term lower bound
minorizes the normalized scaled derivative at the actual law. -/
theorem normalized_derivative_ge (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hw : 4 / 9 < wbar μ l) :
    let w := wbar μ l; let e := fun n => etaW μ l n / w
    scaledLowerBound (xS μ l) (l - 1) (tW μ l) w e (tailR μ l) (tailT μ l) ≤
      2 * hsc μ l ^ 2 * dx μ (Vsc μ) l / w ^ 3 := by
  dsimp only
  have hw0 := wbar_pos_f10 h hl hlm
  have hnmark := normalized_mark h hl hlm
  have hs := (scaled_mark μ h hl hlm).1
  let f : ℕ → ℝ := fun n =>
    ScaledLB.G (xS μ l) (l - 1) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) (n + 1) *
      (dx μ (fun y => mMom μ y (n + 1)) l / wbar μ l)
  have hf : Summable f := by
    apply (hs.mul_left (2 * hsc μ l / wbar μ l ^ 3)).congr
    intro n
    dsimp [f]
    rw [G_normalized h hl hlm]
    field_simp [hw0.ne'] <;> ring
  have hprefix : (∑ n ∈ Finset.range 16,
      ScaledLB.G (xS μ l) (l - 1) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) (n + 1) *
        ScaledLB.ell (xS μ l) (l - 1) (tW μ l) (wbar μ l) (en μ l) (n + 1)) ≤
      ∑ n ∈ Finset.range 16, f n := by
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_left (ell_le_dx h hl hlm (by omega : 1 ≤ n + 1))
      (actual_G_mem h hl hlm (by omega : 1 ≤ n + 1)).1
  have hftail : Summable (fun n : ℕ => f (n + 16)) := (summable_nat_add_iff 16).2 hf
  have hR : Summable (fun n : ℕ => un μ l (n + 17) ^ 2) := by
    simpa [add_assoc] using (summable_nat_add_iff 16).2 (summable_un_sq h hl hlm)
  have htail : (∑' n : ℕ, -2 * un μ l 1 * un μ l (n + 17) ^ 2 / 17) ≤
      ∑' n : ℕ, f (n + 16) := by
    have hsum := (hR.mul_left (-2 * un μ l 1 / 17)).tsum_le_tsum
      (fun n => by
        have hh := tail_deriv_lower h hl hlm (n := n + 17) (by omega)
        dsimp [f]
        convert hh using 1 <;> ring) hftail
    simpa only [f, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, add_assoc] using hsum
  have htail' : -2 * un μ l 1 * tailR μ l / 17 ≤ ∑' n : ℕ, f (n + 16) := by
    have heq : -2 * un μ l 1 * tailR μ l / 17 =
        ∑' n : ℕ, -2 * un μ l 1 * un μ l (n + 17) ^ 2 / 17 := by
      unfold tailR
      rw [← tsum_mul_left, ← tsum_div_const]
      apply tsum_congr
      intro n
      dsimp [un] <;> ring
    rw [heq]
    exact htail
  have hsplit := hf.sum_add_tsum_nat_add 16
  have hmain : scaledLowerBound (xS μ l) (l - 1) (tW μ l) (wbar μ l) (en μ l)
      (tailR μ l) (tailT μ l) ≤
      wbar μ l * ScaledLB.P (xS μ l) (l - 1) (en μ l) (tailR μ l) *
        ScaledLB.PgQ (xS μ l) (l - 1) (en μ l) (tailR μ l) (tailT μ l) + ∑' n, f n := by
    rw [← hsplit]
    unfold scaledLowerBound
    rw [sum_Icc16]
    change _ - 2 * ScaledLB.u (xS μ l) (l - 1) (en μ l) 1 * tailR μ l / 17 ≤ _
    rw [scaled_u_actual]
    dsimp [f] at hprefix htail' ⊢
    linarith
  change scaledLowerBound (xS μ l) (l - 1) (tW μ l) (wbar μ l) (en μ l)
    (tailR μ l) (tailT μ l) ≤ _
  rw [hnmark]
  exact hmain

/-- All hypotheses of `CertACovers` (the conditions of `ScaledDomain`) hold at the
actual law. -/
theorem actual_scaledDomain (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hx : xS μ l ≤ 1 / 4) (ha : l - 1 ≤ 4 / 5)
    (hw : 4 / 9 < wbar μ l) :
    ScaledDomain (xS μ l) (l - 1) (tW μ l) (wbar μ l) (en μ l) (tailR μ l) (tailT μ l) := by
  have hm := normalized_moments h hl hlm
  refine
    { x_pos := xS_pos h hl
      x_le := hx
      a_pos := by linarith
      a_le := ha
      w_gt := hw
      w_le_t := hm.1
      t_le_one := hm.2.1
      e_one := hm.2.2.1
      e_two := hm.2.2.2.1
      e_bounds := hm.2.2.2.2.1
      defect_bounds := hm.2.2.2.2.2.1
      R_nonneg := (tailR_bounds h hl hlm).1
      R_le := ?_
      T_nonneg := (tailT_bounds_aux h hl hlm).1
      T_le := by rw [scaled_u_actual]; exact (tailT_bounds_aux h hl hlm).2
      PgQ_ge := actual_PgQ_ge h hl hlm
      G_nonneg := ?_ }
  · rw [certIota_actual]
    exact (tailR_bounds_aux h hl hlm).2
  · intro n hn
    exact (actual_G_mem h hl hlm (Finset.mem_Icc.mp hn).1).1

end LPPMonotonicityProof.Analytic
