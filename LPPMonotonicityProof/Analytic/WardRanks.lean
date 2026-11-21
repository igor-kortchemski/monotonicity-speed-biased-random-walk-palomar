module

public import LPPMonotonicityProof.Analytic.Ward
public import LPPMonotonicityProof.Analytic.LogResponse
public import LPPMonotonicityProof.Analytic.ScaledSeries.Identities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ward's inequality in rank form

This module expands the lower bound of `Ward.lean` in the ranks of `Ylaw`, as in
Proposition 5.2 (`prop:ward-ranks`): the rank expansion of the cost, nonnegativity of
the `f_θ` ranks, and persistence of nonnegative `g_θ` ranks.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

/-- The response-potential moment of rank `j`. -/
noncomputable def phiRank (l : ℝ) (j : ℕ) : ℝ :=
  ∫ T, (kS l * Yt l T) ^ j * (1 - Yt l T) ^ 2 *
    phiResp l (escape l T) ∂GW μ

/-- The two endpoint values of the quadratic `gθ`.  The relation `r = v/(l-1)` is the
explicit hypothesis `hrv` here. -/
theorem gθ_endpoints {l r θ v : ℝ} (hl : 1 < l) (_hr : 0 < r) (hv : v < 1)
    (hrv : r = v / (l - 1)) :
    gθ l r θ 0 = -2 * l * r ∧
      gθ l r θ (1 / l) = (1 - 1 / l) * (1 - v) := by
  have hl0 : 0 < l := by linarith
  have ha : 0 < l - 1 := by linarith
  constructor
  · simp [gθ] <;> ring
  · rw [hrv]
    unfold gθ
    field_simp [hl0.ne', ha.ne'] <;> ring

private lemma integrable_on_Ylaw_continuous
    (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    {F : ℝ → ℝ} (hF : Continuous F) : Integrable F (Ylaw μ l) := by
  letI : IsProbabilityMeasure (Ylaw μ l) := by
    unfold Ylaw
    infer_instance
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) (1 / l)) hF.continuousOn
  apply (integrable_const C).mono' hF.measurable.aemeasurable.aestronglyMeasurable
  filter_upwards [ae_Ylaw_mem μ h hl hlm] with y hy
  exact hC y ⟨hy.1.le, hy.2.le⟩

private lemma integral_Ylaw_weight (l : ℝ) (j : ℕ) {F : ℝ → ℝ}
    (hF : Measurable F) :
    (∫ y, (kS l * y) ^ j * F y ∂Ylaw μ l) = muJ μ l j F := by
  unfold Ylaw muJ
  have hm : Measurable (fun y : ℝ => (kS l * y) ^ j * F y) :=
    ((measurable_const.mul measurable_id).pow_const j).mul hF
  rw [integral_map (measurable_Yt l).aemeasurable hm.aestronglyMeasurable]

private lemma map_integral_fθ (l : ℝ) (θ : ℝ) :
    (∫ y, fθ l (rr μ l) θ y ∂Ylaw μ l) =
      ∫ T, fθ l (rr μ l) θ (Yt l T) ∂GW μ := by
  unfold Ylaw
  rw [integral_map (measurable_Yt l).aemeasurable]
  unfold fθ
  fun_prop

/-- **Proposition 5.2, signs of the `fθ` ranks.** -/
theorem muJ_fθ_nonneg (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {θ : ℝ} (hθ : Admissible μ l θ) (j : ℕ) :
    0 ≤ muJ μ l j (fθ l (rr μ l) θ) := by
  letI : IsProbabilityMeasure (Ylaw μ l) := by
    unfold Ylaw
    infer_instance
  obtain ⟨c, hc, hneg, hpos⟩ :=
    fθ_single_crossing hl (rr_pos μ h hl hlm) hθ.1
  let F : ℝ → ℝ := fθ l (rr μ l) θ
  let w : ℝ → ℝ := fun y => (kS l * y) ^ j
  have hFc : Continuous F := by dsimp [F]; unfold fθ; fun_prop
  have hF : Measurable F := hFc.measurable
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hY : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l) :=
    (ae_Ylaw_mem μ h hl hlm).mono fun _ hy => ⟨hy.1.le, hy.2.le⟩
  have hFi : Integrable F (Ylaw μ l) := integrable_on_Ylaw_continuous μ h hl hlm hFc
  have hFw : Integrable (F * w) (Ylaw μ l) := by
    apply integrable_on_Ylaw_continuous μ h hl hlm
    exact hFc.mul (by dsimp [w]; fun_prop)
  have hcross : w c * ∫ y, F y ∂Ylaw μ l ≤ ∫ y, F y * w y ∂Ylaw μ l :=
    single_crossing hY
      (fun y hy hyc => hneg y hy hyc) (fun y hy hcy => hpos y hy hcy)
      (by
        intro y hy z hz hyz
        have hy0 : 0 ≤ y := by
          rcases hy with hy | hy
          · exact hy.1
          · rw [Set.mem_singleton_iff.mp hy]
            exact hc.1.le
        exact pow_le_pow_left₀ (mul_nonneg (kS_pos hl).le hy0)
          (mul_le_mul_of_nonneg_left hyz (kS_pos hl).le) j)
      (Set.mem_union_right _ (Set.mem_singleton c)) hFi hFw
  have hwc : 0 ≤ w c := pow_nonneg (mul_nonneg (kS_pos hl).le hc.1.le) j
  have hmean : 0 ≤ ∫ y, F y ∂Ylaw μ l := by
    rw [map_integral_fθ]
    exact hθ.2
  have hout := (mul_nonneg hwc hmean).trans hcross
  rw [show (∫ y, F y * w y ∂Ylaw μ l) = ∫ y, w y * F y ∂Ylaw μ l by
    apply integral_congr_ae
    filter_upwards with y
    ring] at hout
  rw [integral_Ylaw_weight μ l j hF] at hout
  exact hout

/-- The quadratic `gθ` crosses once from nonpositive to nonnegative on
`[0,1/l]`. -/
private lemma gθ_single_crossing {l r θ v : ℝ} (hl : 1 < l) (hr : 0 < r)
    (hv : v < 1) (hrv : r = v / (l - 1)) :
    ∃ c ∈ Set.Ioo 0 (1 / l),
      (∀ y ∈ Set.Icc 0 (1 / l), y < c → gθ l r θ y ≤ 0) ∧
      (∀ y ∈ Set.Icc 0 (1 / l), c < y → 0 ≤ gθ l r θ y) := by
  have hl0 : 0 < l := by linarith
  have hu : 0 < 1 / l := one_div_pos.mpr hl0
  obtain ⟨hg0, hgu⟩ := gθ_endpoints hl hr hv hrv (θ := θ)
  let A : ℝ := -l - 2 * θ * l - l * r * (1 + l)
  let B : ℝ := l + 2 * θ + l * r * (3 + l)
  let C : ℝ := -2 * l * r
  let q : ℝ → ℝ := fun y => A * y ^ 2 + B * y + C
  have hq (y : ℝ) : gθ l r θ y = q y := by
    dsimp [q, A, B, C]
    unfold gθ
    ring
  have hq0 : q 0 < 0 := by rw [← hq, hg0]; nlinarith [mul_pos hl0 hr]
  have hqu : 0 < q (1 / l) := by
    rw [← hq, hgu]
    have h1 : 0 < 1 - 1 / l := by
      rw [sub_pos, div_lt_one hl0]
      exact hl
    exact mul_pos h1 (sub_pos.mpr hv)
  have hcont : Continuous q := by dsimp [q]; fun_prop
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hu.le hcont.continuousOn
    (show 0 ∈ Set.Icc (q 0) (q (1 / l)) from ⟨hq0.le, hqu.le⟩)
  have hc0 : 0 < c := by
    rcases hc.1.eq_or_lt with heq | hlt
    · exfalso; rw [← heq] at hfc; linarith
    · exact hlt
  have hcu : c < 1 / l := by
    rcases hc.2.eq_or_lt with heq | hlt
    · exfalso; rw [heq] at hfc; linarith
    · exact hlt
  let L : ℝ → ℝ := fun y => A * (y + c) + B
  have hfactor (y : ℝ) : q y = (y - c) * L y := by
    dsimp [q, L] at *
    nlinarith [hfc]
  have hL0 : 0 < L 0 := by
    have h := hfactor 0
    rw [hfc] at *
    nlinarith
  have hLu : 0 < L (1 / l) := by
    have h := hfactor (1 / l)
    nlinarith
  have hL (y : ℝ) (hy : y ∈ Set.Icc 0 (1 / l)) : 0 < L y := by
    by_cases hA : 0 ≤ A
    · have hAy : A * (0 + c) ≤ A * (y + c) :=
        mul_le_mul_of_nonneg_left (by linarith [hy.1]) hA
      have hle : L 0 ≤ L y := add_le_add_left hAy B
      exact hL0.trans_le hle
    · have hA' : A ≤ 0 := le_of_not_ge hA
      have hAy : A * (1 / l + c) ≤ A * (y + c) :=
        mul_le_mul_of_nonpos_left (by linarith [hy.2]) hA'
      have hle : L (1 / l) ≤ L y := add_le_add_left hAy B
      exact hLu.trans_le hle
  refine ⟨c, ⟨hc0, hcu⟩, ?_, ?_⟩
  · intro y hy hyc
    rw [hq, hfactor]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hL y hy).le
  · intro y hy hcy
    rw [hq, hfactor]
    exact mul_nonneg (by linarith) (hL y hy).le

/-- **Proposition 5.2, persistence of nonnegative `gθ` ranks.** -/
theorem muJ_gθ_persist (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {θ : ℝ} (_hθ : Admissible μ l θ) {K j : ℕ}
    (hKj : K ≤ j) (hK : 0 ≤ muJ μ l K (gθ l (rr μ l) θ)) :
    0 ≤ muJ μ l j (gθ l (rr μ l) θ) := by
  letI : IsProbabilityMeasure (Ylaw μ l) := by
    unfold Ylaw
    infer_instance
  have hr : 0 < rr μ l := rr_pos μ h hl hlm
  have hv : speedValueProv μ l < 1 := speedValue_lt_one μ h (by linarith) hlm
  have hrv : rr μ l = speedValueProv μ l / (l - 1) := rfl
  obtain ⟨c, hc, hneg, hpos⟩ := gθ_single_crossing hl hr hv hrv (θ := θ)
  let G : ℝ → ℝ := gθ l (rr μ l) θ
  let F : ℝ → ℝ := fun y => (kS l * y) ^ K * G y
  let w : ℝ → ℝ := fun y => (kS l * y) ^ (j - K)
  have hG : Measurable G := by dsimp [G]; unfold gθ; fun_prop
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hY : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l) :=
    (ae_Ylaw_mem μ h hl hlm).mono fun _ hy => ⟨hy.1.le, hy.2.le⟩
  have hFc : Continuous F := by dsimp [F, G]; unfold gθ; fun_prop
  have hFwc : Continuous (F * w) := by
    apply hFc.mul
    dsimp [w]
    fun_prop
  have hFi : Integrable F (Ylaw μ l) := integrable_on_Ylaw_continuous μ h hl hlm hFc
  have hFw : Integrable (F * w) (Ylaw μ l) := integrable_on_Ylaw_continuous μ h hl hlm hFwc
  have hcross : w c * ∫ y, F y ∂Ylaw μ l ≤ ∫ y, F y * w y ∂Ylaw μ l := by
    apply single_crossing hY
    · intro y hy hyc
      exact mul_nonpos_of_nonneg_of_nonpos
        (pow_nonneg (mul_nonneg (kS_pos hl).le hy.1) K) (hneg y hy hyc)
    · intro y hy hcy
      exact mul_nonneg (pow_nonneg (mul_nonneg (kS_pos hl).le hy.1) K) (hpos y hy hcy)
    · intro y hy z hz hyz
      have hy0 : 0 ≤ y := by
        rcases hy with hy | hy
        · exact hy.1
        · rw [Set.mem_singleton_iff.mp hy]
          exact hc.1.le
      exact pow_le_pow_left₀ (mul_nonneg (kS_pos hl).le hy0)
        (mul_le_mul_of_nonneg_left hyz (kS_pos hl).le) (j - K)
    · exact Set.mem_union_right _ (Set.mem_singleton c)
    · exact hFi
    · exact hFw
  have hwc : 0 ≤ w c := pow_nonneg (mul_nonneg (kS_pos hl).le hc.1.le) (j - K)
  have hmean : 0 ≤ ∫ y, F y ∂Ylaw μ l := by
    rw [show (∫ y, F y ∂Ylaw μ l) = muJ μ l K G from integral_Ylaw_weight μ l K hG]
    exact hK
  have hout := (mul_nonneg hwc hmean).trans hcross
  rw [show (∫ y, F y * w y ∂Ylaw μ l) = muJ μ l j G by
    calc
      (∫ y, F y * w y ∂Ylaw μ l) = ∫ y, (kS l * y) ^ j * G y ∂Ylaw μ l := by
        apply integral_congr_ae
        filter_upwards with y
        dsimp [F, w]
        calc
          (kS l * y) ^ K * G y * (kS l * y) ^ (j - K) =
              ((kS l * y) ^ K * (kS l * y) ^ (j - K)) * G y := by ring
          _ = (kS l * y) ^ j * G y := by rw [← pow_add, Nat.add_sub_cancel' hKj]
      _ = muJ μ l j G := integral_Ylaw_weight μ l j hG] at hout
  exact hout


private lemma hasSum_kernel_coeff_rank {x : ℝ} (hx : ‖x‖ < 1) (e : ℕ)
    (he : e = 1 ∨ e = 2) :
    HasSum (fun n : ℕ => (if e = 1 then 1 else (n + 1 : ℝ)) * x ^ n)
      (1 / (1 - x) ^ e) := by
  rcases he with rfl | rfl
  · simpa using hasSum_geometric_of_norm_lt_one hx
  · simpa using hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hx

/-- The kernel expansion `integral_kernel_series` of `Analytic/Tools.lean`, with the
first factor in `L¹`, rather than bounded.  This is needed for
`phiResp`, whose only global domination is by the integrable response. -/
private lemma integral_kernel_series_left_integrable {l : ℝ} (hl : 1 < l)
    {ρ ρ' : Measure ℝ} [IsProbabilityMeasure ρ] [IsProbabilityMeasure ρ']
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc 0 (1 / l))
    (hρ' : ∀ᵐ t ∂ρ', t ∈ Set.Icc 0 (1 / l))
    {f g : ℝ → ℝ} (hf : Integrable f ρ) (hg : AEMeasurable g ρ')
    (hg_bdd : ∃ C, ∀ t ∈ Set.Icc 0 (1 / l), |g t| ≤ C)
    (e : ℕ) (he : e = 1 ∨ e = 2) :
    Summable (fun n : ℕ => (if e = 1 then 1 else (n + 1 : ℝ)) * l ^ n *
      (∫ y, y ^ n * f y ∂ρ) * ∫ t, t ^ n * g t ∂ρ') ∧
    ∫ p, f p.1 * g p.2 / (1 - l * p.1 * p.2) ^ e ∂ρ.prod ρ' =
      ∑' n : ℕ, (if e = 1 then 1 else (n + 1 : ℝ)) * l ^ n *
        (∫ y, y ^ n * f y ∂ρ) * ∫ t, t ^ n * g t ∂ρ' := by
  let r : ℝ := 1 / l
  let c : ℕ → ℝ := fun n => if e = 1 then 1 else (n + 1 : ℝ)
  let A : ℕ → ℝ → ℝ := fun n y => y ^ n * f y
  let B : ℕ → ℝ → ℝ := fun n t => t ^ n * g t
  let F : ℕ → ℝ × ℝ → ℝ := fun n p => c n * l ^ n * A n p.1 * B n p.2
  have hl0 : 0 < l := zero_lt_one.trans hl
  have hr0 : 0 ≤ r := one_div_nonneg.mpr hl0.le
  have hr1 : r < 1 := by
    dsimp [r]
    exact (div_lt_iff₀ hl0).mpr (by nlinarith)
  have hlr : l * r = 1 := by dsimp [r]; field_simp
  have hlr2 : l * r ^ 2 = r := by rw [sq, ← mul_assoc, hlr, one_mul]
  obtain ⟨Cg, hCg⟩ := hg_bdd
  have hCg0 : 0 ≤ Cg := by
    obtain ⟨t, ht⟩ := hρ'.exists
    exact (abs_nonneg (g t)).trans (hCg t ht)
  have hAr (n : ℕ) : ∀ᵐ y ∂ρ, ‖A n y‖ ≤ r ^ n * ‖f y‖ := by
    filter_upwards [hρ] with y hy
    have hy' : y ∈ Set.Icc 0 r := hy
    have hy_norm : ‖y‖ ≤ r := by rw [Real.norm_of_nonneg hy'.1]; exact hy'.2
    calc
      ‖A n y‖ = ‖y‖ ^ n * ‖f y‖ := by simp [A, norm_mul, norm_pow]
      _ ≤ r ^ n * ‖f y‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg y) hy_norm n)
          (norm_nonneg _)
  have hBr (n : ℕ) : ∀ᵐ t ∂ρ', ‖B n t‖ ≤ Cg * r ^ n := by
    filter_upwards [hρ'] with t ht
    have ht' : t ∈ Set.Icc 0 r := ht
    have ht_norm : ‖t‖ ≤ r := by rw [Real.norm_of_nonneg ht'.1]; exact ht'.2
    calc
      ‖B n t‖ = ‖t‖ ^ n * ‖g t‖ := by simp [B, norm_mul, norm_pow]
      _ ≤ r ^ n * Cg := by
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg t) ht_norm n)
          (by simpa [Real.norm_eq_abs] using hCg t ht) (norm_nonneg _)
          (pow_nonneg hr0 _)
      _ = Cg * r ^ n := by ring
  have hAi (n : ℕ) : Integrable (A n) ρ := by
    apply (hf.norm.const_mul (r ^ n)).mono' _ (hAr n)
    exact ((aemeasurable_id.pow_const n).mul hf.aemeasurable).aestronglyMeasurable
  have hBi (n : ℕ) : Integrable (B n) ρ' := by
    apply (integrable_const (Cg * r ^ n)).mono' _ (hBr n)
    exact ((aemeasurable_id.pow_const n).mul hg).aestronglyMeasurable
  have hFi (n : ℕ) : Integrable (F n) (ρ.prod ρ') :=
    ((hAi n).const_mul (c n * l ^ n)).mul_prod (hBi n)
  have hFb (n : ℕ) : ∀ᵐ p ∂ρ.prod ρ',
      ‖F n p‖ ≤ (n + 1 : ℝ) * Cg * r ^ n * ‖f p.1‖ := by
    have hAprod := (Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := ρ')).ae (hAr n)
    have hBprod := (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := ρ')).ae (hBr n)
    filter_upwards [hAprod, hBprod] with p hpA hpB
    have hc0 : 0 ≤ c n := by dsimp [c]; split_ifs <;> positivity
    have hcle : c n ≤ (n + 1 : ℝ) := by dsimp [c]; split_ifs <;> simp
    calc
      ‖F n p‖ = c n * l ^ n * ‖A n p.1‖ * ‖B n p.2‖ := by
        simp only [F, norm_mul, norm_pow, Real.norm_of_nonneg hc0,
          Real.norm_of_nonneg hl0.le]
      _ ≤ (n + 1 : ℝ) * l ^ n * (r ^ n * ‖f p.1‖) * (Cg * r ^ n) := by
        gcongr
      _ = (n + 1 : ℝ) * Cg * r ^ n * ‖f p.1‖ := by
        calc
          (n + 1 : ℝ) * l ^ n * (r ^ n * ‖f p.1‖) * (Cg * r ^ n) =
              (n + 1 : ℝ) * Cg * (l * r ^ 2) ^ n * ‖f p.1‖ := by ring
          _ = _ := by rw [hlr2]
  have hHi (n : ℕ) : Integrable
      (fun p : ℝ × ℝ => (n + 1 : ℝ) * Cg * r ^ n * ‖f p.1‖) (ρ.prod ρ') :=
    (hf.norm.comp_fst ρ').const_mul ((n + 1 : ℝ) * Cg * r ^ n)
  have hFib (n : ℕ) : ∫ p, ‖F n p‖ ∂ρ.prod ρ' ≤
      (n + 1 : ℝ) * Cg * r ^ n * ∫ y, ‖f y‖ ∂ρ := by
    have hi := integral_mono_ae (hFi n).norm (hHi n) (hFb n)
    rw [integral_const_mul, integral_fun_fst (μ := ρ) (ν := ρ') (fun y => ‖f y‖)] at hi
    simpa [measureReal_def] using hi
  have hnormr : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr0] using hr1
  have hbase : Summable (fun n : ℕ => (n + 1 : ℝ) * r ^ n) := by
    simpa using (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnormr)
  have hmajor : Summable
      (fun n : ℕ => (n + 1 : ℝ) * Cg * r ^ n * ∫ y, ‖f y‖ ∂ρ) := by
    apply Summable.congr (hbase.mul_left (Cg * ∫ y, ‖f y‖ ∂ρ))
    intro n
    ring
  have hsum : Summable (fun n : ℕ => ∫ p, ‖F n p‖ ∂ρ.prod ρ') := by
    apply hmajor.of_norm_bounded
    intro n
    rw [Real.norm_of_nonneg (integral_nonneg fun p => norm_nonneg (F n p))]
    exact hFib n
  have hIntF (n : ℕ) : (∫ p, F n p ∂ρ.prod ρ') =
      (if e = 1 then 1 else (n + 1 : ℝ)) * l ^ n *
        (∫ y, y ^ n * f y ∂ρ) * ∫ t, t ^ n * g t ∂ρ' := by
    dsimp [F]
    rw [integral_prod_mul (fun y => c n * l ^ n * A n y) (B n), integral_const_mul]
  have hsumInt : Summable (fun n : ℕ => ∫ p, F n p ∂ρ.prod ρ') := by
    apply hsum.of_norm_bounded
    intro n
    exact norm_integral_le_integral_norm _
  have hsumCoeff : Summable (fun n : ℕ =>
      (if e = 1 then 1 else (n + 1 : ℝ)) * l ^ n *
        (∫ y, y ^ n * f y ∂ρ) * ∫ t, t ^ n * g t ∂ρ') := by
    apply Summable.congr hsumInt
    exact hIntF
  refine ⟨hsumCoeff, ?_⟩
  have hρfst : ∀ᵐ p ∂ρ.prod ρ', p.1 ∈ Set.Icc 0 (1 / l) :=
    (Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := ρ')).ae hρ
  have hρsnd : ∀ᵐ p ∂ρ.prod ρ', p.2 ∈ Set.Icc 0 (1 / l) :=
    (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := ρ')).ae hρ'
  have hseries : ∀ᵐ p ∂ρ.prod ρ',
      f p.1 * g p.2 / (1 - l * p.1 * p.2) ^ e = ∑' n, F n p := by
    filter_upwards [hρfst, hρsnd] with p hp hp'
    have hz0 : 0 ≤ l * p.1 * p.2 :=
      mul_nonneg (mul_nonneg hl0.le hp.1) hp'.1
    have hly : l * p.1 ≤ 1 := by
      calc
        l * p.1 ≤ l * (1 / l) := mul_le_mul_of_nonneg_left hp.2 hl0.le
        _ = 1 := by field_simp
    have hzle : l * p.1 * p.2 ≤ 1 / l := by
      calc
        l * p.1 * p.2 ≤ 1 * p.2 := mul_le_mul_of_nonneg_right hly hp'.1
        _ = p.2 := one_mul _
        _ ≤ 1 / l := hp'.2
    have hz : ‖l * p.1 * p.2‖ < 1 := by
      rw [Real.norm_of_nonneg hz0]
      exact hzle.trans_lt hr1
    have H := (hasSum_kernel_coeff_rank hz e he).mul_left (f p.1 * g p.2)
    calc
      f p.1 * g p.2 / (1 - l * p.1 * p.2) ^ e =
          f p.1 * g p.2 * (1 / (1 - l * p.1 * p.2) ^ e) := by ring
      _ = ∑' n : ℕ, f p.1 * g p.2 *
          ((if e = 1 then 1 else (n + 1 : ℝ)) * (l * p.1 * p.2) ^ n) := H.tsum_eq.symm
      _ = ∑' n, F n p := by
        apply tsum_congr
        intro n
        dsimp [F, A, B, c]
        rw [mul_pow, mul_pow]
        ring
  calc
    ∫ p, f p.1 * g p.2 / (1 - l * p.1 * p.2) ^ e ∂ρ.prod ρ' =
        ∫ p, ∑' n, F n p ∂ρ.prod ρ' := integral_congr_ae hseries
    _ = ∑' n, ∫ p, F n p ∂ρ.prod ρ' := (integral_tsum_of_summable_integral_norm hFi hsum).symm
    _ = _ := tsum_congr hIntF


private noncomputable def betaY (l y : ℝ) : ℝ := (l - 1) * y / (1 - y)

private noncomputable def phiClosed (l b : ℝ) : ℝ :=
  b / (l - 1) *
    ((l - 1 + b) * Real.log (1 + (l - 1) / b) / Real.log l - l)

private noncomputable def phiY (l y : ℝ) : ℝ :=
  2 * (1 - y) ^ 2 * phiResp l (betaY l y)

private noncomputable def phiYClosed (l y : ℝ) : ℝ :=
  2 * (1 - y) ^ 2 * phiClosed l (betaY l y)

private lemma measurable_phiClosed (l : ℝ) : Measurable (phiClosed l) := by
  unfold phiClosed
  fun_prop

private lemma measurable_phiYClosed (l : ℝ) : Measurable (phiYClosed l) := by
  unfold phiYClosed betaY
  exact (measurable_const.mul
    ((measurable_const.sub measurable_id).pow_const 2)).mul
      ((measurable_phiClosed l).comp
        ((measurable_const.mul measurable_id).div (measurable_const.sub measurable_id)))

private lemma betaY_Yt {l : ℝ} (hl : 1 < l) (T : Tree) :
    betaY l (Yt l T) = escape l T := by
  have hl0 : 0 < l := by linarith
  have ha : l - 1 ≠ 0 := by linarith
  have hd : 0 < l - 1 + escape l T := by
    have := (escape_mem_Icc hl0 T).1
    positivity
  unfold betaY Yt
  field_simp [hd.ne', ha] <;> ring

private lemma betaY_mem {l y : ℝ} (hl : 1 < l) (hy : y ∈ Set.Ioo 0 (1 / l)) :
    betaY l y ∈ Set.Ioo 0 1 := by
  have hl0 : 0 < l := by linarith
  have hu : y < 1 := hy.2.trans (by rw [div_lt_one hl0]; exact hl)
  have ha : 0 < l - 1 := by linarith
  have hden : 0 < 1 - y := by linarith
  constructor
  · exact div_pos (mul_pos ha hy.1) hden
  · rw [betaY, div_lt_one hden]
    have hy' : l * y < 1 := by
      calc
        l * y < l * (1 / l) := mul_lt_mul_of_pos_left hy.2 hl0
        _ = 1 := by field_simp
    nlinarith

private lemma phiY_eq_ae (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    ∀ᵐ y ∂Ylaw μ l, phiY l y = phiYClosed l y := by
  filter_upwards [ae_Ylaw_mem μ h hl hlm] with y hy
  unfold phiY phiYClosed phiClosed
  rw [phiResp_closed hl (betaY_mem hl hy).1 (betaY_mem hl hy).2.le]

private lemma aemeasurable_phiY (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : AEMeasurable (phiY l) (Ylaw μ l) :=
  (measurable_phiYClosed l).aemeasurable.congr
    ((phiY_eq_ae μ h hl hlm).mono fun _ hy => hy.symm)

private lemma Yt_nonneg_rank {l : ℝ} (hl : 1 < l) (T : Tree) : 0 ≤ Yt l T := by
  have hl0 : 0 < l := by linarith
  exact div_nonneg (escape_mem_Icc hl0 T).1
    (add_nonneg (by linarith) (escape_mem_Icc hl0 T).1)

private lemma Yt_lt_inv_rank {l : ℝ} (hl : 1 < l) (T : Tree) : Yt l T < 1 / l := by
  have hl0 : 0 < l := by linarith
  have hden : 0 < l - 1 + escape l T := by
    have := (escape_mem_Icc hl0 T).1
    positivity
  rw [Yt, div_lt_div_iff₀ hden hl0]
  nlinarith [escape_lt_one hl0 T]

private lemma kernelQ_pos {l : ℝ} (hl : 1 < l) (T U : Tree) :
    0 < 1 - l * Yt l T * Yt l U := by
  have hl0 : 0 < l := by linarith
  have hy : l * Yt l T < 1 := by
    calc
      l * Yt l T < l * (1 / l) := mul_lt_mul_of_pos_left (Yt_lt_inv_rank hl T) hl0
      _ = 1 := by field_simp
  have hz : l * Yt l T * Yt l U < 1 / l := by
    calc
      l * Yt l T * Yt l U ≤ 1 * Yt l U :=
        mul_le_mul_of_nonneg_right hy.le (Yt_nonneg_rank hl U)
      _ < 1 / l := by simpa using Yt_lt_inv_rank hl U
  have hu : 1 / l < 1 := by rw [div_lt_one hl0]; exact hl
  linarith

private lemma Dfun_eq_kernelQ {l : ℝ} (hl : 1 < l) (T U : Tree) :
    (l - 1) * DfunProv l (escape l T) (escape l U) =
      (l - 1 + escape l T) * (l - 1 + escape l U) *
        (1 - l * Yt l T * Yt l U) := by
  have hl0 : 0 < l := by linarith
  have hT : 0 < l - 1 + escape l T := by
    have := (escape_mem_Icc hl0 T).1
    positivity
  have hU : 0 < l - 1 + escape l U := by
    have := (escape_mem_Icc hl0 U).1
    positivity
  unfold DfunProv Yt
  have hQ := (kernelQ_pos hl T U).ne'
  field_simp [hT.ne', hU.ne', hQ] <;> nlinarith

private noncomputable def staticWardIntegrand (l θ : ℝ) (p : Tree × Tree) : ℝ :=
  l * ((escape l p.1 * escape l p.2 - speedValueProv μ l *
      tau (escape l p.1) (escape l p.2)) /
      DfunProv l (escape l p.1) (escape l p.2) ^ 2) +
    2 * θ * (escape l p.1 * escape l p.2 * (1 - escape l p.2) /
      DfunProv l (escape l p.1) (escape l p.2) ^ 2)

private noncomputable def staticRankIntegrand (l θ : ℝ) (p : Tree × Tree) : ℝ :=
  Yt l p.1 * (1 - Yt l p.1) * gθ l (rr μ l) θ (Yt l p.2) /
    (1 - l * Yt l p.1 * Yt l p.2) ^ 2

private lemma staticWard_add_swap {l : ℝ} (hl : 1 < l) (θ : ℝ) (p : Tree × Tree) :
    staticWardIntegrand μ l θ p + staticWardIntegrand μ l θ p.swap =
      staticRankIntegrand μ l θ p + staticRankIntegrand μ l θ p.swap := by
  have hl0 : 0 < l := by linarith
  have ha : 0 < l - 1 := by linarith
  have hT : 0 < l - 1 + escape l p.1 := by
    have := (escape_mem_Icc hl0 p.1).1
    positivity
  have hU : 0 < l - 1 + escape l p.2 := by
    have := (escape_mem_Icc hl0 p.2).1
    positivity
  have hQ : 1 - l * Yt l p.1 * Yt l p.2 ≠ 0 := (kernelQ_pos hl p.1 p.2).ne'
  have hDpos : 0 < DfunProv l (escape l p.1) (escape l p.2) := by
    have hb := escape_mem_Icc hl0 p.1
    have hb' := escape_mem_Icc hl0 p.2
    have hn := mul_nonneg hb.1 (sub_nonneg.mpr hb'.2)
    unfold DfunProv
    nlinarith
  have hD : DfunProv l (escape l p.1) (escape l p.2) ≠ 0 := hDpos.ne' 
  have hDswap : DfunProv l (escape l p.2) (escape l p.1) =
      DfunProv l (escape l p.1) (escape l p.2) := by
    unfold DfunProv
    ring
  have hDrev : DfunProv l (escape l p.2) (escape l p.1) ≠ 0 := hDswap.symm ▸ hD
  have hQrev : 1 - l * Yt l p.2 * Yt l p.1 ≠ 0 := by
    have := (kernelQ_pos hl p.2 p.1).ne'
    simpa [mul_comm] using this
  have hvr : speedValueProv μ l = (l - 1) * rr μ l := by
    unfold rr
    field_simp [ha.ne']
  have hQeq : 1 - l * Yt l p.1 * Yt l p.2 =
      (l - 1) * DfunProv l (escape l p.1) (escape l p.2) /
        ((l - 1 + escape l p.1) * (l - 1 + escape l p.2)) := by
    rw [Dfun_eq_kernelQ hl]
    field_simp [hT.ne', hU.ne']
  have hQeqrev : 1 - l * Yt l p.2 * Yt l p.1 =
      (l - 1) * DfunProv l (escape l p.2) (escape l p.1) /
        ((l - 1 + escape l p.2) * (l - 1 + escape l p.1)) := by
    rw [Dfun_eq_kernelQ hl]
    field_simp [hT.ne', hU.ne']
  unfold staticWardIntegrand staticRankIntegrand
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [hQeq, hQeqrev]
  unfold gθ tau Yt
  rw [hvr, hDswap]
  field_simp [hT.ne', hU.ne', hD, hDrev] <;> ring


private lemma integrable_phiY (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : Integrable (phiY l) (Ylaw μ l) := by
  have hc : Integrable (phiYClosed l) (Ylaw μ l) := by
    unfold Ylaw
    apply (integrable_map_measure (measurable_phiYClosed l).aestronglyMeasurable
      (measurable_Yt l).aemeasurable).2
    apply ((integrable_resp h ⟨by linarith, hlm⟩).const_mul 2).mono'
      ((measurable_phiYClosed l).comp (measurable_Yt l)).aestronglyMeasurable
    filter_upwards [ae_regTree h, ae_escape_mem_Ioo h (by linarith) hlm] with T hT hb
    have hy : Yt l T ∈ Set.Ioo 0 (1 / l) := Yt_mem hl hb.1
    have hEq : phiYClosed l (Yt l T) =
        2 * (1 - Yt l T) ^ 2 * phiResp l (escape l T) := by
      unfold phiYClosed phiClosed
      rw [betaY_Yt hl, ← phiResp_closed hl hb.1 hb.2.le]
    have hp0 : 0 ≤ phiResp l (escape l T) := phiResp_nonneg hl ⟨hb.1, hb.2.le⟩
    have hpr : phiResp l (escape l T) ≤ resp l T := phiResp_le_resp h hT hl hlm
    have hr : 0 ≤ resp l T := hp0.trans hpr
    have hy1 : 0 ≤ 1 - Yt l T := by
      have hu : 1 / l ≤ 1 := (div_le_one (by linarith)).mpr hl.le
      linarith [hy.2]
    have hy1le : 1 - Yt l T ≤ 1 := by linarith [hy.1]
    have hsq : (1 - Yt l T) ^ 2 ≤ 1 := by nlinarith
    rw [Function.comp_apply, hEq, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) hp0)]
    calc
      2 * (1 - Yt l T) ^ 2 * phiResp l (escape l T) ≤ 2 * 1 * resp l T := by
        gcongr
      _ = 2 * resp l T := by ring
  exact hc.congr ((phiY_eq_ae μ h hl hlm).mono fun _ hy => hy.symm)

private lemma Dfun_lower_rank {l : ℝ} (hl : 1 < l) (T U : Tree) :
    l - 1 ≤ DfunProv l (escape l T) (escape l U) := by
  have hb := escape_mem_Icc (by linarith : 0 < l) T
  have hb' := escape_mem_Icc (by linarith : 0 < l) U
  have hn := mul_nonneg hb.1 (sub_nonneg.mpr hb'.2)
  have hrest : 0 ≤ escape l T * (1 - escape l U) + escape l U := add_nonneg hn hb'.1
  unfold DfunProv
  nlinarith

private lemma Dfun_pos_rank {l : ℝ} (hl : 1 < l) (T U : Tree) :
    0 < DfunProv l (escape l T) (escape l U) :=
  (by linarith : 0 < l - 1).trans_le (Dfun_lower_rank hl T U)

private lemma integrable_RW (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    Integrable (fun p : Tree × Tree => escape l p.1 * escape l p.2 *
      (1 - escape l p.2) / DfunProv l (escape l p.1) (escape l p.2) ^ 2)
      ((GW μ).prod (GW μ)) := by
  have ha : 0 < l - 1 := by linarith
  apply (integrable_const (1 / (l - 1) ^ 2)).mono'
  · have hT : Measurable (fun p : Tree × Tree => escape l p.1) :=
      (measurable_escape l).comp measurable_fst
    have hU : Measurable (fun p : Tree × Tree => escape l p.2) :=
      (measurable_escape l).comp measurable_snd
    exact (((hT.mul hU).mul (measurable_const.sub hU)).div
      (by unfold DfunProv; fun_prop)).aestronglyMeasurable
  · filter_upwards with p
    have hb := escape_mem_Icc (by linarith : 0 < l) p.1
    have hb' := escape_mem_Icc (by linarith : 0 < l) p.2
    have hD := Dfun_pos_rank hl p.1 p.2
    have hnum : |escape l p.1 * escape l p.2 * (1 - escape l p.2)| ≤ 1 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hb.1, abs_of_nonneg hb'.1,
        abs_of_nonneg (sub_nonneg.mpr hb'.2)]
      have hbb : escape l p.1 * escape l p.2 ≤ 1 := by
        calc
          escape l p.1 * escape l p.2 ≤ 1 * 1 :=
            mul_le_mul hb.2 hb'.2 hb'.1 zero_le_one
          _ = 1 := one_mul 1
      have hbb0 : 0 ≤ escape l p.1 * escape l p.2 := mul_nonneg hb.1 hb'.1
      calc
        escape l p.1 * escape l p.2 * (1 - escape l p.2) ≤
            escape l p.1 * escape l p.2 * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [hb'.1]) hbb0
        _ ≤ 1 := by simpa using hbb
    have hDs : (l - 1) ^ 2 ≤ DfunProv l (escape l p.1) (escape l p.2) ^ 2 :=
      (sq_le_sq₀ ha.le hD.le).mpr (Dfun_lower_rank hl p.1 p.2)
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hD]
    calc
      |escape l p.1 * escape l p.2 * (1 - escape l p.2)| /
          DfunProv l (escape l p.1) (escape l p.2) ^ 2 ≤
        1 / DfunProv l (escape l p.1) (escape l p.2) ^ 2 :=
          div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ ≤ 1 / (l - 1) ^ 2 := by
        exact (div_le_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos ha)).2 (by nlinarith)

private lemma integrable_staticWard (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (θ : ℝ) :
    Integrable (staticWardIntegrand μ l θ) ((GW μ).prod (GW μ)) := by
  exact ((integrable_Hval_kernel h ⟨by linarith, hlm⟩).const_mul l).add
    ((integrable_RW μ h hl hlm).const_mul (2 * θ))

private lemma kernelQ_lower {l : ℝ} (hl : 1 < l) (T U : Tree) :
    1 - 1 / l ≤ 1 - l * Yt l T * Yt l U := by
  have hl0 : 0 < l := by linarith
  have hy : l * Yt l T ≤ 1 := by
    calc
      l * Yt l T ≤ l * (1 / l) := mul_le_mul_of_nonneg_left (Yt_lt_inv_rank hl T).le hl0.le
      _ = 1 := by field_simp
  have hz : l * Yt l T * Yt l U ≤ 1 / l := by
    calc
      l * Yt l T * Yt l U ≤ 1 * Yt l U :=
        mul_le_mul_of_nonneg_right hy (Yt_nonneg_rank hl U)
      _ ≤ 1 / l := by simpa using (Yt_lt_inv_rank hl U).le
  linarith

private lemma integrable_staticRank (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (θ : ℝ) :
    Integrable (staticRankIntegrand μ l θ) ((GW μ).prod (GW μ)) := by
  have hl0 : 0 < l := by linarith
  have hd : 0 < 1 - 1 / l := by rw [sub_pos, div_lt_one hl0]; exact hl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) (1 / l))
    (show Continuous (gθ l (rr μ l) θ) by unfold gθ; fun_prop).continuousOn
  apply (integrable_const (C / (1 - 1 / l) ^ 2)).mono'
  · have hT : Measurable (fun p : Tree × Tree => Yt l p.1) :=
      (measurable_Yt l).comp measurable_fst
    have hU : Measurable (fun p : Tree × Tree => Yt l p.2) :=
      (measurable_Yt l).comp measurable_snd
    have hg : Measurable (fun p : Tree × Tree => gθ l (rr μ l) θ (Yt l p.2)) := by
      unfold gθ
      fun_prop
    exact (((hT.mul (measurable_const.sub hT)).mul hg).div
      (by fun_prop)).aestronglyMeasurable
  · filter_upwards with p
    have hy : Yt l p.1 ∈ Set.Icc 0 (1 / l) :=
      ⟨Yt_nonneg_rank hl _, (Yt_lt_inv_rank hl _).le⟩
    have hy' : Yt l p.2 ∈ Set.Icc 0 (1 / l) :=
      ⟨Yt_nonneg_rank hl _, (Yt_lt_inv_rank hl _).le⟩
    have hQ : 0 < 1 - l * Yt l p.1 * Yt l p.2 := kernelQ_pos hl _ _
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ hy')
    have hnum : |Yt l p.1 * (1 - Yt l p.1) * gθ l (rr μ l) θ (Yt l p.2)| ≤ C := by
      have hout : |Yt l p.1 * (1 - Yt l p.1)| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hy.1, abs_of_nonneg (by
          have hu : 1 / l ≤ 1 := (div_le_one hl0).mpr hl.le
          linarith [hy.2])]
        have hu : 1 / l ≤ 1 := (div_le_one hl0).mpr hl.le
        have hY1 : 1 - Yt l p.1 ≤ 1 := by linarith [hy.1]
        have hY0 : 0 ≤ 1 - Yt l p.1 := by linarith [hy.2]
        calc
          Yt l p.1 * (1 - Yt l p.1) ≤ 1 * 1 :=
            mul_le_mul (by linarith [hy.2]) hY1 hY0 zero_le_one
          _ = 1 := one_mul 1
      calc
        |Yt l p.1 * (1 - Yt l p.1) * gθ l (rr μ l) θ (Yt l p.2)| =
            |Yt l p.1 * (1 - Yt l p.1)| * ‖gθ l (rr μ l) θ (Yt l p.2)‖ := by
              rw [abs_mul, Real.norm_eq_abs]
        _ ≤ 1 * C := mul_le_mul hout (hC _ hy') (norm_nonneg _) (by linarith)
        _ = C := one_mul _
    have hQs : (1 - 1 / l) ^ 2 ≤ (1 - l * Yt l p.1 * Yt l p.2) ^ 2 :=
      (sq_le_sq₀ hd.le hQ.le).mpr (kernelQ_lower hl _ _)
    unfold staticRankIntegrand
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hQ]
    calc
      |Yt l p.1 * (1 - Yt l p.1) * gθ l (rr μ l) θ (Yt l p.2)| /
          (1 - l * Yt l p.1 * Yt l p.2) ^ 2 ≤
        C / (1 - l * Yt l p.1 * Yt l p.2) ^ 2 :=
          div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ ≤ C / (1 - 1 / l) ^ 2 := by
        exact (div_le_div_iff₀ (sq_pos_of_pos hQ) (sq_pos_of_pos hd)).2 (mul_le_mul_of_nonneg_left hQs hC0)

private lemma integral_staticWard_eq_rank (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (θ : ℝ) :
    (∫ p, staticWardIntegrand μ l θ p ∂(GW μ).prod (GW μ)) =
      ∫ p, staticRankIntegrand μ l θ p ∂(GW μ).prod (GW μ) := by
  let S := staticWardIntegrand μ l θ
  let B := staticRankIntegrand μ l θ
  have hS : Integrable S ((GW μ).prod (GW μ)) := integrable_staticWard μ h hl hlm θ
  have hB : Integrable B ((GW μ).prod (GW μ)) := integrable_staticRank μ h hl hlm θ
  have hSS : (∫ p, (S p + S p.swap) ∂(GW μ).prod (GW μ)) =
      2 * ∫ p, S p ∂(GW μ).prod (GW μ) := by
    have hS' : Integrable (fun p => S p.swap) ((GW μ).prod (GW μ)) := hS.swap
    rw [integral_add hS hS', integral_prod_swap]
    ring
  have hBB : (∫ p, (B p + B p.swap) ∂(GW μ).prod (GW μ)) =
      2 * ∫ p, B p ∂(GW μ).prod (GW μ) := by
    have hB' : Integrable (fun p => B p.swap) ((GW μ).prod (GW μ)) := hB.swap
    rw [integral_add hB hB', integral_prod_swap]
    ring
  have heq : (∫ p, (S p + S p.swap) ∂(GW μ).prod (GW μ)) =
      ∫ p, (B p + B p.swap) ∂(GW μ).prod (GW μ) := by
    apply integral_congr_ae
    filter_upwards with p
    exact staticWard_add_swap μ hl θ p
  dsimp [S, B] at hSS hBB heq
  linarith


private noncomputable def phiRankIntegrand (l θ : ℝ) (p : Tree × Tree) : ℝ :=
  2 * phiResp l (escape l p.1) * (1 - Yt l p.1) ^ 2 *
    fθ l (rr μ l) θ (Yt l p.2) / (1 - l * Yt l p.1 * Yt l p.2) ^ 2

private noncomputable def phiRankClosedIntegrand (l θ : ℝ) (p : Tree × Tree) : ℝ :=
  2 * phiClosed l (escape l p.1) * (1 - Yt l p.1) ^ 2 *
    fθ l (rr μ l) θ (Yt l p.2) / (1 - l * Yt l p.1 * Yt l p.2) ^ 2

private lemma phiRankIntegrand_eq_ae (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (θ : ℝ) :
    ∀ᵐ p ∂(GW μ).prod (GW μ),
      phiRankIntegrand μ l θ p = phiRankClosedIntegrand μ l θ p := by
  have hb := (Measure.quasiMeasurePreserving_fst (μ := GW μ) (ν := GW μ)).ae
    (ae_escape_mem_Ioo h (by linarith) hlm)
  filter_upwards [hb] with p hp
  unfold phiRankIntegrand phiRankClosedIntegrand phiClosed
  rw [phiResp_closed hl hp.1 hp.2.le]

private lemma integrable_phiRankIntegrand (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (θ : ℝ) :
    Integrable (phiRankIntegrand μ l θ) ((GW μ).prod (GW μ)) := by
  have hl0 : 0 < l := by linarith
  have hd : 0 < 1 - 1 / l := by rw [sub_pos, div_lt_one hl0]; exact hl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) (1 / l))
    (show Continuous (fθ l (rr μ l) θ) by unfold fθ; fun_prop).continuousOn
  have hC0 : 0 ≤ C := by
    have hy : (0 : ℝ) ∈ Set.Icc 0 (1 / l) := ⟨le_rfl, one_div_nonneg.mpr hl0.le⟩
    exact (norm_nonneg _).trans (hC 0 hy)
  have hmeas : AEStronglyMeasurable (phiRankIntegrand μ l θ) ((GW μ).prod (GW μ)) := by
    have hc : AEStronglyMeasurable (phiRankClosedIntegrand μ l θ)
        ((GW μ).prod (GW μ)) := by
      have hT : Measurable (fun p : Tree × Tree => escape l p.1) :=
        (measurable_escape l).comp measurable_fst
      have hYT : Measurable (fun p : Tree × Tree => Yt l p.1) :=
        (measurable_Yt l).comp measurable_fst
      have hYU : Measurable (fun p : Tree × Tree => Yt l p.2) :=
        (measurable_Yt l).comp measurable_snd
      have hg : Measurable (fun p : Tree × Tree => fθ l (rr μ l) θ (Yt l p.2)) := by
        unfold fθ
        fun_prop
      exact (((measurable_const.mul ((measurable_phiClosed l).comp hT)).mul
        ((measurable_const.sub hYT).pow_const 2)).mul hg).div
          (by fun_prop) |>.aestronglyMeasurable
    exact hc.congr ((phiRankIntegrand_eq_ae μ h hl hlm θ).mono fun _ hp => hp.symm)
  apply ((integrable_resp h ⟨by linarith, hlm⟩).comp_fst (GW μ) |>.const_mul
    (2 * C / (1 - 1 / l) ^ 2)).mono' hmeas
  have hb := (Measure.quasiMeasurePreserving_fst (μ := GW μ) (ν := GW μ)).ae
    (ae_escape_mem_Ioo h (by linarith) hlm)
  have hr := (Measure.quasiMeasurePreserving_fst (μ := GW μ) (ν := GW μ)).ae (ae_regTree h)
  filter_upwards [hb, hr] with p hp hreg
  have hp0 : 0 ≤ phiResp l (escape l p.1) := phiResp_nonneg hl ⟨hp.1, hp.2.le⟩
  have hpr : phiResp l (escape l p.1) ≤ resp l p.1 := phiResp_le_resp h hreg hl hlm
  have hresp : 0 ≤ resp l p.1 := hp0.trans hpr
  have hy : Yt l p.1 ∈ Set.Icc 0 (1 / l) :=
    ⟨Yt_nonneg_rank hl _, (Yt_lt_inv_rank hl _).le⟩
  have hy' : Yt l p.2 ∈ Set.Icc 0 (1 / l) :=
    ⟨Yt_nonneg_rank hl _, (Yt_lt_inv_rank hl _).le⟩
  have hy1 : 0 ≤ 1 - Yt l p.1 := by
    have hu : 1 / l ≤ 1 := (div_le_one hl0).mpr hl.le
    linarith [hy.2]
  have hy1le : 1 - Yt l p.1 ≤ 1 := by linarith [hy.1]
  have hsq : (1 - Yt l p.1) ^ 2 ≤ 1 := by nlinarith
  have hQ : 0 < 1 - l * Yt l p.1 * Yt l p.2 := kernelQ_pos hl _ _
  have hQs : (1 - 1 / l) ^ 2 ≤ (1 - l * Yt l p.1 * Yt l p.2) ^ 2 :=
    (sq_le_sq₀ hd.le hQ.le).mpr (kernelQ_lower hl _ _)
  have hnum : |2 * phiResp l (escape l p.1) * (1 - Yt l p.1) ^ 2 *
      fθ l (rr μ l) θ (Yt l p.2)| ≤ 2 * C * resp l p.1 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2),
      abs_of_nonneg hp0, abs_of_nonneg (sq_nonneg _)]
    calc
      2 * phiResp l (escape l p.1) * (1 - Yt l p.1) ^ 2 *
          |fθ l (rr μ l) θ (Yt l p.2)| ≤
        2 * resp l p.1 * 1 * C := by
          have hf : |fθ l (rr μ l) θ (Yt l p.2)| ≤ C := by
            simpa [Real.norm_eq_abs] using hC _ hy'
          gcongr
      _ = 2 * C * resp l p.1 := by ring
  unfold phiRankIntegrand
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hQ]
  calc
    |2 * phiResp l (escape l p.1) * (1 - Yt l p.1) ^ 2 *
        fθ l (rr μ l) θ (Yt l p.2)| /
        (1 - l * Yt l p.1 * Yt l p.2) ^ 2 ≤
      (2 * C * resp l p.1) / (1 - l * Yt l p.1 * Yt l p.2) ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ (2 * C * resp l p.1) / (1 - 1 / l) ^ 2 := by
      exact (div_le_div_iff₀ (sq_pos_of_pos hQ) (sq_pos_of_pos hd)).2
        (mul_le_mul_of_nonneg_left hQs (mul_nonneg (by positivity) hresp))
    _ = (2 * C / (1 - 1 / l) ^ 2) * resp l p.1 := by ring

private lemma integral_ward_residual (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (θ : ℝ) :
    2 * ∫ T, phiResp l (escape l T) *
      (Gam μ l (escape l T) - θ * Gam2 μ l (escape l T)) ∂GW μ =
      ∫ p, phiRankIntegrand μ l θ p ∂(GW μ).prod (GW μ) := by
  have hi := integrable_phiRankIntegrand μ h hl hlm θ
  rw [integral_prod _ hi]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_escape_mem_Ioo h (by linarith) hlm] with T hb
  rw [Gam_sub_Gam2 μ h hl hlm ⟨hb.1.le, hb.2.le⟩ θ]
  unfold phiRankIntegrand
  simp only [Prod.fst, Prod.snd]
  change 2 * (phiResp l (escape l T) *
      ((1 - Yt l T) ^ 2 * ∫ U, fθ l (rr μ l) θ (Yt l U) /
        (1 - l * Yt l T * Yt l U) ^ 2 ∂GW μ)) = _
  rw [show 2 * (phiResp l (escape l T) *
      ((1 - Yt l T) ^ 2 * ∫ U, fθ l (rr μ l) θ (Yt l U) /
        (1 - l * Yt l T * Yt l U) ^ 2 ∂GW μ)) =
      (2 * phiResp l (escape l T) * (1 - Yt l T) ^ 2) *
        ∫ U, fθ l (rr μ l) θ (Yt l U) /
          (1 - l * Yt l T * Yt l U) ^ 2 ∂GW μ by ring]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with U
  ring

private noncomputable def staticRankY (l θ : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * (1 - p.1) * gθ l (rr μ l) θ p.2 / (1 - l * p.1 * p.2) ^ 2

private noncomputable def phiRankY (l θ : ℝ) (p : ℝ × ℝ) : ℝ :=
  phiY l p.1 * fθ l (rr μ l) θ p.2 / (1 - l * p.1 * p.2) ^ 2

private lemma integral_pair_Yt (l : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : AEStronglyMeasurable F ((Ylaw μ l).prod (Ylaw μ l))) :
    (∫ p, F (Yt l p.1, Yt l p.2) ∂(GW μ).prod (GW μ)) =
      ∫ q, F q ∂(Ylaw μ l).prod (Ylaw μ l) := by
  have hmap : (Ylaw μ l).prod (Ylaw μ l) =
      Measure.map (Prod.map (Yt l) (Yt l)) ((GW μ).prod (GW μ)) := by
    unfold Ylaw
    exact Measure.map_prod_map _ _ (measurable_Yt l) (measurable_Yt l)
  have hF' : AEStronglyMeasurable F
      (Measure.map (Prod.map (Yt l) (Yt l)) ((GW μ).prod (GW μ))) := hmap ▸ hF
  rw [hmap, integral_map ((measurable_Yt l).prodMap (measurable_Yt l)).aemeasurable hF']
  rfl

private lemma integral_staticRank_map (l θ : ℝ) :
    (∫ p, staticRankIntegrand μ l θ p ∂(GW μ).prod (GW μ)) =
      ∫ q, staticRankY μ l θ q ∂(Ylaw μ l).prod (Ylaw μ l) := by
  change (∫ p, staticRankY μ l θ (Yt l p.1, Yt l p.2) ∂(GW μ).prod (GW μ)) = _
  apply integral_pair_Yt
  exact (show Measurable (staticRankY μ l θ) by
    unfold staticRankY gθ
    fun_prop).aestronglyMeasurable

private lemma integral_phiRank_map (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (θ : ℝ) :
    (∫ p, phiRankIntegrand μ l θ p ∂(GW μ).prod (GW μ)) =
      ∫ q, phiRankY μ l θ q ∂(Ylaw μ l).prod (Ylaw μ l) := by
  rw [show (fun p : Tree × Tree => phiRankIntegrand μ l θ p) =
      (fun p => phiRankY μ l θ (Yt l p.1, Yt l p.2)) by
    funext p
    unfold phiRankIntegrand phiRankY phiY
    rw [betaY_Yt hl]
    ring]
  apply integral_pair_Yt
  have hc : AEStronglyMeasurable (fun q : ℝ × ℝ =>
      phiYClosed l q.1 * fθ l (rr μ l) θ q.2 / (1 - l * q.1 * q.2) ^ 2)
      ((Ylaw μ l).prod (Ylaw μ l)) := by
    exact ((((measurable_phiYClosed l).comp measurable_fst).mul
      (show Measurable (fun q : ℝ × ℝ => fθ l (rr μ l) θ q.2) by
        unfold fθ; fun_prop)).div (by fun_prop)).aestronglyMeasurable
  have heq : ∀ᵐ q ∂(Ylaw μ l).prod (Ylaw μ l),
      phiRankY μ l θ q = phiYClosed l q.1 * fθ l (rr μ l) θ q.2 /
        (1 - l * q.1 * q.2) ^ 2 := by
    have hy := (Measure.quasiMeasurePreserving_fst (μ := Ylaw μ l) (ν := Ylaw μ l)).ae
      (phiY_eq_ae μ h hl hlm)
    filter_upwards [hy] with q hq
    unfold phiRankY
    rw [hq]
  exact hc.congr (heq.mono fun _ hq => hq.symm)


private lemma muJ_eq_factor (l : ℝ) (j : ℕ) {F : ℝ → ℝ}
    (hF : Measurable F) :
    muJ μ l j F = kS l ^ j * ∫ y, y ^ j * F y ∂Ylaw μ l := by
  rw [← integral_Ylaw_weight μ l j hF]
  simp_rw [mul_pow]
  calc
    (∫ y, kS l ^ j * y ^ j * F y ∂Ylaw μ l) =
        ∫ y, kS l ^ j * (y ^ j * F y) ∂Ylaw μ l := by
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = _ := integral_const_mul _ _

private lemma two_phiRank_eq_factor (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (j : ℕ) :
    2 * phiRank μ l j = kS l ^ j * ∫ y, y ^ j * phiY l y ∂Ylaw μ l := by
  have hm : AEMeasurable (fun y : ℝ => y ^ j * phiY l y) (Ylaw μ l) :=
    (aemeasurable_id.pow_const j).mul (aemeasurable_phiY μ h hl hlm)
  unfold Ylaw
  rw [integral_map (measurable_Yt l).aemeasurable hm.aestronglyMeasurable]
  unfold phiRank phiY
  calc
    2 * ∫ T, (kS l * Yt l T) ^ j * (1 - Yt l T) ^ 2 *
        phiResp l (escape l T) ∂GW μ =
      ∫ T, 2 * ((kS l * Yt l T) ^ j * (1 - Yt l T) ^ 2 *
        phiResp l (escape l T)) ∂GW μ := (integral_const_mul _ _).symm
    _ = ∫ T, kS l ^ j * (Yt l T ^ j *
        (2 * (1 - Yt l T) ^ 2 * phiResp l (betaY l (Yt l T)))) ∂GW μ := by
      apply integral_congr_ae
      filter_upwards with T
      rw [betaY_Yt hl, mul_pow]
      ring
    _ = _ := integral_const_mul _ _

/-- **Proposition 5.2** (`prop:ward-ranks`), Ward's lower bound expanded in ranks. -/
theorem cost_ge_rank_series (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {θ : ℝ} (hθ : Admissible μ l θ) :
    Summable (fun j : ℕ => (j + 1) *
      (PJ μ l j * muJ μ l j (gθ l (rr μ l) θ) +
        2 * phiRank μ l j * muJ μ l j (fθ l (rr μ l) θ))) ∧
    ∑' j : ℕ, (j + 1) *
      (PJ μ l j * muJ μ l j (gθ l (rr μ l) θ) +
        2 * phiRank μ l j * muJ μ l j (fθ l (rr μ l) θ)) ≤ cost μ l := by
  letI : IsProbabilityMeasure (Ylaw μ l) := by
    unfold Ylaw
    infer_instance
  have hY : ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l) :=
    (ae_Ylaw_mem μ h hl hlm).mono fun _ hy => ⟨hy.1.le, hy.2.le⟩
  let F0 : ℝ → ℝ := fun y => y * (1 - y)
  let G : ℝ → ℝ := gθ l (rr μ l) θ
  let F : ℝ → ℝ := fθ l (rr μ l) θ
  have hF0c : Continuous F0 := by dsimp [F0]; fun_prop
  have hGc : Continuous G := by dsimp [G]; unfold gθ; fun_prop
  have hFc : Continuous F := by dsimp [F]; unfold fθ; fun_prop
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) (1 / l)) hGc.continuousOn
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) (1 / l)) hFc.continuousOn
  have hS := integral_kernel_series_left_integrable hl hY hY
    (f := F0) (g := G) (integrable_on_Ylaw_continuous μ h hl hlm hF0c)
    hGc.measurable.aemeasurable
    ⟨Cg, fun y hy => by simpa [Real.norm_eq_abs] using hCg y hy⟩ 2 (Or.inr rfl)
  have hP := integral_kernel_series_left_integrable hl hY hY
    (f := phiY l) (g := F) (integrable_phiY μ h hl hlm) hFc.measurable.aemeasurable
    ⟨Cf, fun y hy => by simpa [Real.norm_eq_abs] using hCf y hy⟩ 2 (Or.inr rfl)
  have hstatic : (∫ q, staticRankY μ l θ q ∂(Ylaw μ l).prod (Ylaw μ l)) =
      ∑' j : ℕ, (j + 1 : ℝ) * l ^ j *
        (∫ y, y ^ j * F0 y ∂Ylaw μ l) * ∫ t, t ^ j * G t ∂Ylaw μ l := by
    simpa only [staticRankY, F0, G, Nat.cast_add, Nat.cast_one, if_false,
      show (2 : ℕ) ≠ 1 by omega] using hS.2
  have hphi : (∫ q, phiRankY μ l θ q ∂(Ylaw μ l).prod (Ylaw μ l)) =
      ∑' j : ℕ, (j + 1 : ℝ) * l ^ j *
        (∫ y, y ^ j * phiY l y ∂Ylaw μ l) * ∫ t, t ^ j * F t ∂Ylaw μ l := by
    simpa only [phiRankY, F, Nat.cast_add, Nat.cast_one, if_false,
      show (2 : ℕ) ≠ 1 by omega] using hP.2
  have hcS (j : ℕ) :
      (j + 1 : ℝ) * l ^ j * (∫ y, y ^ j * F0 y ∂Ylaw μ l) *
          (∫ t, t ^ j * G t ∂Ylaw μ l) =
        (j + 1 : ℝ) * (PJ μ l j * muJ μ l j G) := by
    rw [muJ_eq_factor μ l j hGc.measurable]
    have hPJ : PJ μ l j = kS l ^ j * ∫ y, y ^ j * F0 y ∂Ylaw μ l := by
      exact muJ_eq_factor μ l j hF0c.measurable
    rw [hPJ, lpow_eq_kS hl]
    ring
  have hcP (j : ℕ) :
      (j + 1 : ℝ) * l ^ j * (∫ y, y ^ j * phiY l y ∂Ylaw μ l) *
          (∫ t, t ^ j * F t ∂Ylaw μ l) =
        (j + 1 : ℝ) * (2 * phiRank μ l j * muJ μ l j F) := by
    rw [muJ_eq_factor μ l j hFc.measurable, two_phiRank_eq_factor μ h hl hlm j,
      lpow_eq_kS hl]
    ring
  have hul : AEMeasurable (fun T => phiResp l (escape l T)) (GW μ) := by
    apply AEMeasurable.congr ((measurable_phiClosed l).comp (measurable_escape l)).aemeasurable
    filter_upwards [ae_escape_mem_Ioo h (by linarith) hlm] with T hb
    exact (phiResp_closed hl hb.1 hb.2.le).symm
  have h0 : ∀ᵐ T ∂GW μ, 0 ≤ phiResp l (escape l T) ∧
      phiResp l (escape l T) ≤ resp l T := by
    filter_upwards [ae_regTree h, ae_escape_mem_Ioo h (by linarith) hlm] with T hT hb
    exact ⟨phiResp_nonneg hl ⟨hb.1, hb.2.le⟩, phiResp_le_resp h hT hl hlm⟩
  have hw := ward_lower h hl hlm hθ hul h0
  have hstaticWard : l * Hval μ l + 2 * θ * RW μ l =
      ∫ p, staticWardIntegrand μ l θ p ∂(GW μ).prod (GW μ) := by
    unfold staticWardIntegrand Hval RW pairE
    rw [integral_add ((integrable_Hval_kernel h ⟨by linarith, hlm⟩).const_mul l)
      ((integrable_RW μ h hl hlm).const_mul (2 * θ)), integral_const_mul,
      integral_const_mul]
  rw [hstaticWard, integral_staticWard_eq_rank μ h hl hlm θ,
    integral_ward_residual μ h hl hlm θ, integral_staticRank_map,
    integral_phiRank_map μ h hl hlm θ, hstatic, hphi] at hw
  have hsS : Summable (fun j : ℕ => (j + 1 : ℝ) * l ^ j *
      (∫ y, y ^ j * F0 y ∂Ylaw μ l) * ∫ t, t ^ j * G t ∂Ylaw μ l) := by
    simpa only [Nat.cast_add, Nat.cast_one, if_false, show (2 : ℕ) ≠ 1 by omega] using hS.1
  have hsP : Summable (fun j : ℕ => (j + 1 : ℝ) * l ^ j *
      (∫ y, y ^ j * phiY l y ∂Ylaw μ l) * ∫ t, t ^ j * F t ∂Ylaw μ l) := by
    simpa only [Nat.cast_add, Nat.cast_one, if_false, show (2 : ℕ) ≠ 1 by omega] using hP.1
  let S : ℕ → ℝ := fun j => (j + 1 : ℝ) * l ^ j *
    (∫ y, y ^ j * F0 y ∂Ylaw μ l) * ∫ t, t ^ j * G t ∂Ylaw μ l
  let P : ℕ → ℝ := fun j => (j + 1 : ℝ) * l ^ j *
    (∫ y, y ^ j * phiY l y ∂Ylaw μ l) * ∫ t, t ^ j * F t ∂Ylaw μ l
  have hsum : Summable (fun j : ℕ => (j + 1 : ℝ) *
      (PJ μ l j * muJ μ l j G + 2 * phiRank μ l j * muJ μ l j F)) := by
    apply Summable.congr (hsS.add hsP)
    intro j
    rw [hcS, hcP]
    ring
  refine ⟨hsum, ?_⟩
  calc
    ∑' j : ℕ, (j + 1 : ℝ) *
        (PJ μ l j * muJ μ l j G + 2 * phiRank μ l j * muJ μ l j F) =
      ∑' j : ℕ, (S j + P j) := by
        apply tsum_congr
        intro j
        dsimp [S, P]
        rw [hcS, hcP]
        ring
    _ = (∑' j, S j) + ∑' j, P j := hsS.tsum_add hsP
    _ ≤ cost μ l := hw

end LPPMonotonicityProof.Analytic
