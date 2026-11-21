module

public import LPPMonotonicityProof.Analytic.Comparison
public import LPPMonotonicityProof.Analytic.FirstSplit2
public import LPPMonotonicityProof.Analytic.Tools

/-!
# The moment series in scaled form: algebraic part

Expansion of Proposition 3.1 (`prop:collapse`) in the scaled moments of Section 4.3:
`N/p = xS`, `Z = 2xh`, `V = S/(2h)`, `m₁/2 ≤ h ≤ m₁`, and `m_{n+1} ≤ mₙ/k`, together
with the geometric bound `0 ≤ mₙ ≤ k·k⁻ⁿ` that makes all the moment series summable.

`Vsc` is defined in `Analytic/Defs.lean` through `speedValueProv`, which unfolds to
`Nval / Zval` of `Speed/Signed/TwoCopy.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-! ### Scalars -/

theorem pBr_le_one' (h : OffspringHyp μ) : pBr μ ≤ 1 := by
  have hp := p1_add_pBr h
  have hq : 0 ≤ p1 μ := ENNReal.toReal_nonneg
  linarith

theorem xS_pos (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) : 0 < xS μ l :=
  div_pos (pBr_pos h) (by linarith)

theorem sub_one_mul_xS {l : ℝ} (hl : 1 < l) : (l - 1) * xS μ l = pBr μ := by
  have ha : l - 1 ≠ 0 := (show (0 : ℝ) < l - 1 by linarith).ne'
  rw [xS]
  field_simp

theorem kS_pos {l : ℝ} (hl : 1 < l) : 0 < kS l := Real.sqrt_pos.mpr (by linarith)

theorem one_lt_kS {l : ℝ} (hl : 1 < l) : 1 < kS l := by
  unfold kS
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt zero_le_one hl

theorem kS_sq {l : ℝ} (hl : 1 < l) : kS l ^ 2 = l := Real.sq_sqrt (by linarith)

theorem lpow_eq_kS {l : ℝ} (hl : 1 < l) (n : ℕ) : l ^ n = (kS l ^ n) ^ 2 := by
  rw [← pow_mul, mul_comm n 2, pow_mul, kS_sq hl]

theorem Qgeo_succ' (l : ℝ) (n : ℕ) : Qgeo l (n + 1) = 1 + l * Qgeo l n := by
  have h : Qgeo l (n + 1) = l * Qgeo l n + 1 := by
    unfold Qgeo
    rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
    congr 1
    exact Finset.sum_congr rfl fun i _ => pow_succ' l i
  linarith

theorem Qgeo_nonneg {l : ℝ} (hl : 0 ≤ l) (n : ℕ) : 0 ≤ Qgeo l n :=
  Finset.sum_nonneg fun i _ => pow_nonneg hl i

theorem pow_le_Qgeo {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 1 ≤ n) : l ^ (n - 1) ≤ Qgeo l n := by
  unfold Qgeo
  exact Finset.single_le_sum (f := fun i => l ^ i) (fun i _ => pow_nonneg hl i)
    (Finset.mem_range.mpr (by omega))

/-! ### The moments `ηₙ` and `mₙ` -/

theorem integrable_Wt_pow' (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (n : ℕ) : Integrable (fun T => Wt l T ^ n) (splitLaw μ) := by
  letI := splitLaw_prob h
  apply Integrable.of_bound ((measurable_Wt l).pow_const n).aestronglyMeasurable 1
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hT.1.le _)]
  exact pow_le_one₀ hT.1.le hT.2.le

theorem etaW_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    0 ≤ etaW μ l n ∧ etaW μ l n ≤ 1 := by
  letI := splitLaw_prob h
  have hae := ae_Wt_mem h hl hlm
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [hae] with T hT
    exact pow_nonneg hT.1.le n
  · calc etaW μ l n ≤ ∫ _T, (1 : ℝ) ∂splitLaw μ := by
          apply integral_mono_ae (integrable_Wt_pow' h hl hlm n) (integrable_const _)
          filter_upwards [hae] with T hT
          exact pow_le_one₀ hT.1.le hT.2.le
      _ = 1 := by simp

theorem etaW_succ_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    etaW μ l (n + 1) ≤ etaW μ l n := by
  apply integral_mono_ae (integrable_Wt_pow' h hl hlm (n + 1)) (integrable_Wt_pow' h hl hlm n)
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  exact pow_le_pow_of_le_one hT.1.le hT.2.le (Nat.le_succ n)

theorem Acoef_nonneg (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) : 0 ≤ Acoef μ l n := by
  unfold Acoef iota
  exact mul_nonneg (pow_nonneg (kS_pos hl).le _)
    (inv_nonneg.mpr (add_nonneg (xS_pos h hl).le (Qgeo_nonneg (by linarith) n)))

/-- `Aₙ ≤ k^{-(n-1)} = k · k⁻ⁿ`, since `Qₙ ≥ l^{n-1} = k^{2(n-1)}`. -/
theorem Acoef_le_geom (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) {n : ℕ} (hn : 1 ≤ n) :
    Acoef μ l n ≤ kS l * (kS l)⁻¹ ^ n := by
  have hk := kS_pos hl
  have hk0 := hk.ne'
  have hx := xS_pos h hl
  have hl0 : 0 ≤ l := by linarith
  have hQ := pow_le_Qgeo hl0 hn
  have hkn : 0 < kS l ^ (n - 1) := pow_pos hk _
  have hlk : l ^ (n - 1) = (kS l ^ (n - 1)) ^ 2 := lpow_eq_kS hl (n - 1)
  have hden : (kS l ^ (n - 1)) ^ 2 ≤ xS μ l + Qgeo l n := by linarith
  have hrhs : kS l * (kS l)⁻¹ ^ n = (kS l ^ (n - 1))⁻¹ := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, inv_pow, pow_succ, mul_inv, ← mul_assoc, mul_comm (kS l),
      mul_assoc, mul_inv_cancel₀ hk0, mul_one]
  rw [hrhs, Acoef, iota]
  calc kS l ^ (n - 1) * (xS μ l + Qgeo l n)⁻¹
      ≤ kS l ^ (n - 1) * ((kS l ^ (n - 1)) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hkn.le
        exact inv_anti₀ (by positivity) hden
    _ = (kS l ^ (n - 1))⁻¹ := by
        rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hkn.ne', one_mul]

/-- The geometric envelope of the scaled moments: `0 ≤ mₙ ≤ k · k⁻ⁿ` for every `n`. -/
theorem mMom_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    0 ≤ mMom μ l n ∧ mMom μ l n ≤ kS l * (kS l)⁻¹ ^ n := by
  have hk := kS_pos hl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mMom, eq_self_iff_true, if_true, pow_zero, mul_one]
    exact ⟨le_rfl, hk.le⟩
  · unfold mMom
    rw [if_neg (by omega)]
    obtain ⟨he0, he1⟩ := etaW_mem h hl hlm n
    have hA0 := Acoef_nonneg h hl n
    have hA1 := Acoef_le_geom h hl (n := n) hn
    refine ⟨mul_nonneg hA0 he0, ?_⟩
    calc Acoef μ l n * etaW μ l n ≤ Acoef μ l n * 1 := mul_le_mul_of_nonneg_left he1 hA0
      _ ≤ _ := by rw [mul_one]; exact hA1

theorem kS_inv_mem {l : ℝ} (hl : 1 < l) : 0 ≤ (kS l)⁻¹ ∧ (kS l)⁻¹ < 1 :=
  ⟨inv_nonneg.mpr (kS_pos hl).le, inv_lt_one_of_one_lt₀ (one_lt_kS hl)⟩

/-- Summability of any bilinear moment series `∑ m_{n+i} m_{n+j}`. -/
theorem summable_mMom_mul (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (i j : ℕ) : Summable fun n => mMom μ l (n + i) * mMom μ l (n + j) := by
  have hk := kS_pos hl
  obtain ⟨hr0, hr1⟩ := kS_inv_mem hl
  have hg : Summable fun n : ℕ => kS l * kS l * (kS l)⁻¹ ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (mMom_mem h hl hlm _).1
    (mMom_mem h hl hlm _).1) _ hg
  intro n
  obtain ⟨ha0, ha1⟩ := mMom_mem h hl hlm (n + i)
  obtain ⟨hb0, hb1⟩ := mMom_mem h hl hlm (n + j)
  have hpi : (kS l)⁻¹ ^ (n + i) ≤ (kS l)⁻¹ ^ n := pow_le_pow_of_le_one hr0 hr1.le (by omega)
  have hpj : (kS l)⁻¹ ^ (n + j) ≤ 1 := pow_le_one₀ hr0 hr1.le
  calc mMom μ l (n + i) * mMom μ l (n + j)
      ≤ (kS l * (kS l)⁻¹ ^ (n + i)) * (kS l * (kS l)⁻¹ ^ (n + j)) :=
        mul_le_mul ha1 hb1 hb0 (by positivity)
    _ ≤ (kS l * (kS l)⁻¹ ^ n) * (kS l * 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hpi hk.le)
          (mul_le_mul_of_nonneg_left hpj hk.le) (by positivity) (by positivity)
    _ = kS l * kS l * (kS l)⁻¹ ^ n := by ring

theorem summable_Ssc (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    Summable fun n => mMom μ l (n + 1) ^ 2 := by
  simpa only [sq] using summable_mMom_mul h hl hlm 1 1

theorem summable_Tsc (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    Summable fun n => mMom μ l (n + 1) * mMom μ l (n + 2) :=
  summable_mMom_mul h hl hlm 1 2

/-! ### Moments of `Y` in the scaled normalization -/

private lemma Ylaw_prob (l : ℝ) : IsProbabilityMeasure (Ylaw μ l) :=
  inferInstanceAs (IsProbabilityMeasure ((GW μ).map (Yt l)))

private lemma Ylaw_moment (l : ℝ) (n : ℕ) : ∫ y, y ^ n ∂Ylaw μ l = momY μ l n := by
  unfold Ylaw momY
  exact integral_map (measurable_Yt l).aemeasurable (continuous_pow n).aestronglyMeasurable

private lemma momY_zero (l : ℝ) : momY μ l 0 = 1 := by
  simp [momY]

/-- `E Y^{n+1} = x k⁻ⁿ m_{n+1}`. -/
private lemma momY_succ (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    momY μ l (n + 1) = xS μ l * (kS l ^ n)⁻¹ * mMom μ l (n + 1) := by
  rw [momY_eq_mMom h hl hlm (n + 1) (by omega)]
  have he : (1 : ℤ) - ((n + 1 : ℕ) : ℤ) = -(n : ℤ) := by push_cast; ring
  rw [he, zpow_neg, zpow_natCast]

private lemma momY_one (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    momY μ l 1 = xS μ l * mMom μ l 1 := by
  have h0 := momY_succ h hl hlm 0
  simp only [zero_add, pow_zero, inv_one, mul_one] at h0
  exact h0

private lemma term_sq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    l ^ n * (momY μ l (n + 1) * momY μ l (n + 1)) = xS μ l ^ 2 * mMom μ l (n + 1) ^ 2 := by
  rw [momY_succ h hl hlm, lpow_eq_kS hl]
  have hk : kS l ^ n ≠ 0 := (pow_pos (kS_pos hl) n).ne'
  calc (kS l ^ n) ^ 2 * (xS μ l * (kS l ^ n)⁻¹ * mMom μ l (n + 1) *
        (xS μ l * (kS l ^ n)⁻¹ * mMom μ l (n + 1)))
      = xS μ l ^ 2 * mMom μ l (n + 1) ^ 2 * (kS l ^ n * (kS l ^ n)⁻¹) ^ 2 := by ring
    _ = _ := by rw [mul_inv_cancel₀ hk, one_pow, mul_one]

private lemma term_cross (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    l ^ (n + 1) * (momY μ l (n + 1 + 1) * momY μ l (n + 1)) =
      xS μ l ^ 2 * kS l * (mMom μ l (n + 1) * mMom μ l (n + 2)) := by
  rw [show mMom μ l (n + 2) = mMom μ l (n + 1 + 1) from rfl]
  rw [momY_succ h hl hlm (n + 1), momY_succ h hl hlm n, lpow_eq_kS hl, pow_succ]
  have hk : kS l ≠ 0 := (kS_pos hl).ne'
  have hkn : kS l ^ n ≠ 0 := pow_ne_zero n hk
  calc (kS l ^ n * kS l) ^ 2 * (xS μ l * (kS l ^ n * kS l)⁻¹ * mMom μ l (n + 1 + 1) *
        (xS μ l * (kS l ^ n)⁻¹ * mMom μ l (n + 1)))
      = xS μ l ^ 2 * kS l * (mMom μ l (n + 1) * mMom μ l (n + 1 + 1)) *
          ((kS l ^ n * kS l) * (kS l ^ n * kS l)⁻¹) * (kS l ^ n * (kS l ^ n)⁻¹) := by ring
    _ = _ := by
        rw [mul_inv_cancel₀ (mul_ne_zero hkn hk), mul_inv_cancel₀ hkn, mul_one, mul_one]

/-! ### The kernel integrals -/

private lemma Ylaw_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    ∀ᵐ y ∂Ylaw μ l, y ∈ Set.Icc 0 (1 / l) := by
  filter_upwards [ae_Ylaw_mem μ h hl hlm] with y hy
  exact ⟨hy.1.le, hy.2.le⟩

private lemma integrable_kernel {l : ℝ} (hl : 1 < l) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc 0 (1 / l)) {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ y ∈ Set.Icc 0 (1 / l), |f y| ≤ 1) (hgb : ∀ y ∈ Set.Icc 0 (1 / l), |g y| ≤ 1) :
    Integrable (fun p : ℝ × ℝ => f p.1 * g p.2 / (1 - l * p.1 * p.2)) (ρ.prod ρ) := by
  have hl0 : 0 < l := by linarith
  have hmeas : Measurable (fun p : ℝ × ℝ => f p.1 * g p.2 / (1 - l * p.1 * p.2)) :=
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).div
      (measurable_const.sub ((measurable_const.mul measurable_fst).mul measurable_snd))
  apply Integrable.of_bound hmeas.aestronglyMeasurable (l / (l - 1))
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := ρ)).ae hρ
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := ρ)).ae hρ
  filter_upwards [h1, h2] with p hp1 hp2
  have hly : l * p.1 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hp1.2 hl0.le
    rwa [mul_one_div_cancel hl0.ne'] at this
  have hz : l * p.1 * p.2 ≤ 1 / l := by
    calc l * p.1 * p.2 ≤ 1 * p.2 := mul_le_mul_of_nonneg_right hly hp2.1
      _ ≤ 1 / l := by rw [one_mul]; exact hp2.2
  have hdpos : 0 < (l - 1) / l := div_pos (by linarith) hl0
  have hd : (l - 1) / l ≤ 1 - l * p.1 * p.2 := by
    have : (l - 1) / l = 1 - 1 / l := by field_simp
    linarith
  have hnum : |f p.1 * g p.2| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (hfb _ hp1) (abs_nonneg _) (hgb _ hp2)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hdpos.trans_le hd)]
  calc |f p.1 * g p.2| / (1 - l * p.1 * p.2) ≤ 1 / (1 - l * p.1 * p.2) :=
        div_le_div_of_nonneg_right hnum (hdpos.trans_le hd).le
    _ ≤ 1 / ((l - 1) / l) := one_div_le_one_div_of_le hdpos hd
    _ = l / (l - 1) := by field_simp

private lemma abs_id_le {l : ℝ} (hl : 1 < l) : ∀ y ∈ Set.Icc (0 : ℝ) (1 / l), |y| ≤ 1 := by
  intro y hy
  rw [abs_of_nonneg hy.1]
  exact hy.2.trans ((div_le_one (by linarith)).2 hl.le)

private lemma abs_one_le {l : ℝ} :
    ∀ y ∈ Set.Icc (0 : ℝ) (1 / l), |(fun _ : ℝ => (1 : ℝ)) y| ≤ 1 := by
  intro y _
  simp

private lemma integral_pow_mul_self (l : ℝ) (n : ℕ) :
    ∫ y, y ^ n * y ∂Ylaw μ l = momY μ l (n + 1) := by
  rw [← Ylaw_moment]
  congr 1

private lemma integral_pow_mul_one (l : ℝ) (n : ℕ) :
    ∫ y, y ^ n * 1 ∂Ylaw μ l = momY μ l n := by
  rw [← Ylaw_moment]
  simp

/-- The kernel `E[Y Y'/(1 - lYY')]` as a moment series. -/
private lemma kernel_yy (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    ∫ p, p.1 * p.2 / (1 - l * p.1 * p.2) ∂(Ylaw μ l).prod (Ylaw μ l) =
      xS μ l ^ 2 * Ssc μ l := by
  haveI := Ylaw_prob (μ := μ) l
  have hρ := Ylaw_mem h hl hlm
  have hX := integral_kernel_series hl hρ hρ (f := fun y => y) (g := fun y => y)
    aemeasurable_id aemeasurable_id ⟨1, abs_id_le hl⟩ ⟨1, abs_id_le hl⟩ 1 (Or.inl rfl)
  simp only [pow_one, eq_self_iff_true, if_true] at hX
  rw [hX, Ssc, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [integral_pow_mul_self, one_mul, mul_assoc, term_sq h hl hlm]

/-- The kernel `E[Y/(1 - lYY')]` as a moment series. -/
private lemma kernel_y1 (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    ∫ p, p.1 * 1 / (1 - l * p.1 * p.2) ∂(Ylaw μ l).prod (Ylaw μ l) =
      ∑' n : ℕ, l ^ n * (momY μ l (n + 1) * momY μ l n) := by
  haveI := Ylaw_prob (μ := μ) l
  have hρ := Ylaw_mem h hl hlm
  have hX := integral_kernel_series hl hρ hρ (f := fun y => y) (g := fun _ => (1 : ℝ))
    aemeasurable_id aemeasurable_const ⟨1, abs_id_le hl⟩ ⟨1, abs_one_le⟩ 1 (Or.inl rfl)
  simp only [pow_one, eq_self_iff_true, if_true] at hX
  rw [hX]
  apply tsum_congr
  intro n
  rw [integral_pow_mul_self, integral_pow_mul_one]
  ring

/-- The kernel `E[Y'/(1 - lYY')]` as a moment series. -/
private lemma kernel_1y (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    ∫ p, 1 * p.2 / (1 - l * p.1 * p.2) ∂(Ylaw μ l).prod (Ylaw μ l) =
      ∑' n : ℕ, l ^ n * (momY μ l (n + 1) * momY μ l n) := by
  haveI := Ylaw_prob (μ := μ) l
  have hρ := Ylaw_mem h hl hlm
  have hX := integral_kernel_series hl hρ hρ (f := fun _ => (1 : ℝ)) (g := fun y => y)
    aemeasurable_const aemeasurable_id ⟨1, abs_one_le⟩ ⟨1, abs_id_le hl⟩ 1 (Or.inl rfl)
  simp only [pow_one, eq_self_iff_true, if_true] at hX
  rw [hX]
  apply tsum_congr
  intro n
  rw [integral_pow_mul_self, integral_pow_mul_one]
  ring

/-- `∑ lⁿ E Y^{n+1} E Yⁿ = x m₁ + x² k T`. -/
private lemma cross_series (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    ∑' n : ℕ, l ^ n * (momY μ l (n + 1) * momY μ l n) =
      xS μ l * mMom μ l 1 + xS μ l ^ 2 * kS l * Tsc μ l := by
  have hsum : Summable fun n : ℕ => l ^ n * (momY μ l (n + 1) * momY μ l n) := by
    apply (summable_nat_add_iff 1).mp
    refine ((summable_Tsc h hl hlm).mul_left (xS μ l ^ 2 * kS l)).congr ?_
    intro n
    exact (term_cross h hl hlm n).symm
  rw [hsum.tsum_eq_zero_add, tsum_congr (fun n => term_cross h hl hlm n), tsum_mul_left,
    ← Tsc, momY_zero, pow_zero, one_mul, mul_one, zero_add, momY_one h hl hlm]

/-! ### The scaled identities -/

/-- `N/p = xS`. -/
theorem Nval_div_p_eq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    Nval μ l / pBr μ = xS μ l * Ssc μ l := by
  rw [Nval_eq_NY μ h hl hlm, NY]
  have hsplit : ∫ p, (l - 1) * p.1 * p.2 / (1 - l * p.1 * p.2) ∂(Ylaw μ l).prod (Ylaw μ l) =
      (l - 1) * ∫ p, p.1 * p.2 / (1 - l * p.1 * p.2) ∂(Ylaw μ l).prod (Ylaw μ l) := by
    rw [← integral_const_mul]
    congr 1
    funext p
    ring
  have hp := (pBr_pos h).ne'
  rw [hsplit, kernel_yy h hl hlm]
  calc (l - 1) * (xS μ l ^ 2 * Ssc μ l) / pBr μ
      = ((l - 1) * xS μ l) * (xS μ l * Ssc μ l) / pBr μ := by ring
    _ = pBr μ * (xS μ l * Ssc μ l) / pBr μ := by rw [sub_one_mul_xS hl]
    _ = xS μ l * Ssc μ l := by field_simp

/-- `Z = 2xh` (Section 4.3). -/
theorem Zval_eq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    Zval μ l = 2 * xS μ l * hsc μ l := by
  haveI := Ylaw_prob (μ := μ) l
  have hρ := Ylaw_mem h hl hlm
  rw [Zval_eq_ZY μ h hl hlm, ZY]
  have hsplit : ∫ p, (p.1 * (1 - p.2) + p.2 * (1 - l * p.1)) / (1 - l * p.1 * p.2)
      ∂(Ylaw μ l).prod (Ylaw μ l) =
      ∫ p, ((p.1 * 1 / (1 - l * p.1 * p.2) + 1 * p.2 / (1 - l * p.1 * p.2)) -
          (1 + l) * (p.1 * p.2 / (1 - l * p.1 * p.2))) ∂(Ylaw μ l).prod (Ylaw μ l) := by
    congr 1
    funext p
    ring
  have hA := integrable_kernel hl hρ (f := fun y => y) (g := fun _ => (1 : ℝ))
    measurable_id measurable_const (abs_id_le hl) abs_one_le
  have hB := integrable_kernel hl hρ (f := fun _ => (1 : ℝ)) (g := fun y => y)
    measurable_const measurable_id abs_one_le (abs_id_le hl)
  have hC := integrable_kernel hl hρ (f := fun y => y) (g := fun y => y)
    measurable_id measurable_id (abs_id_le hl) (abs_id_le hl)
  have hAB : Integrable (fun p : ℝ × ℝ =>
      p.1 * 1 / (1 - l * p.1 * p.2) + 1 * p.2 / (1 - l * p.1 * p.2))
      ((Ylaw μ l).prod (Ylaw μ l)) := hA.add hB
  rw [hsplit, integral_sub hAB (hC.const_mul _), integral_add hA hB, integral_const_mul,
    kernel_y1 h hl hlm, kernel_1y h hl hlm, kernel_yy h hl hlm, cross_series h hl hlm, hsc]
  ring

/-- `V = S/(2h)`. -/
theorem Vsc_eq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    Vsc μ l = Ssc μ l / (2 * hsc μ l) := by
  have hx := (xS_pos h hl).ne'
  have hNZ : NvalProv μ l / ZvalProv μ l / pBr μ = Nval μ l / pBr μ / Zval μ l := by
    change Nval μ l / Zval μ l / pBr μ = _
    ring
  rw [Vsc, speedValueProv, if_neg (by linarith : l ≠ 0), hNZ, Nval_div_p_eq h hl hlm,
    Zval_eq h hl hlm, show 2 * xS μ l * hsc μ l = xS μ l * (2 * hsc μ l) by ring,
    mul_div_mul_left _ _ hx]

/-- `m₁/2 ≤ h ≤ m₁`, from `EY ≤ Z ≤ 2EY`. -/
theorem hsc_bounds (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    mMom μ l 1 / 2 ≤ hsc μ l ∧ hsc μ l ≤ mMom μ l 1 := by
  have hx := xS_pos h hl
  obtain ⟨h1, h2⟩ := muY_le_Zval_le μ h hl hlm
  have hmu : muY μ l = xS μ l * mMom μ l 1 := by
    have hm : muY μ l = momY μ l 1 := by simp [muY, momY]
    rw [hm, momY_one h hl hlm]
  rw [Zval_eq h hl hlm, hmu] at h1 h2
  constructor
  · have : xS μ l * (mMom μ l 1 / 2) ≤ xS μ l * hsc μ l := by nlinarith
    exact le_of_mul_le_mul_left this hx
  · have : xS μ l * hsc μ l ≤ xS μ l * mMom μ l 1 := by nlinarith
    exact le_of_mul_le_mul_left this hx

/-- `m_{n+1} ≤ mₙ/k`, from `x + Q_{n+1} = l(x + Qₙ) + q`. -/
theorem mMom_succ_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    {n : ℕ} (hn : 1 ≤ n) : mMom μ l (n + 1) ≤ mMom μ l n / kS l := by
  have hk := kS_pos hl
  have hx := xS_pos h hl
  have hl0 : 0 ≤ l := by linarith
  have he := etaW_succ_le h hl hlm n
  have he0 := (etaW_mem h hl hlm (n + 1)).1
  have hA0 := Acoef_nonneg h hl (n + 1)
  have hA0' := Acoef_nonneg h hl n
  have hD : 0 < xS μ l + Qgeo l n := by have := Qgeo_nonneg hl0 n; linarith
  have hD' : 0 < xS μ l + Qgeo l (n + 1) := by have := Qgeo_nonneg hl0 (n + 1); linarith
  -- `l (x + Qₙ) ≤ x + Q_{n+1}` because `(l - 1) x = p ≤ 1`
  have hrec : l * (xS μ l + Qgeo l n) ≤ xS μ l + Qgeo l (n + 1) := by
    rw [Qgeo_succ']
    have hpx := sub_one_mul_xS (μ := μ) hl
    have := pBr_le_one' h
    nlinarith
  have hA : Acoef μ l (n + 1) * kS l ≤ Acoef μ l n := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    simp only [Acoef, iota, Nat.add_sub_cancel]
    have hkj : 0 < kS l ^ j := pow_pos hk j
    rw [show kS l ^ (j + 1) * (xS μ l + Qgeo l (j + 1 + 1))⁻¹ * kS l =
        kS l ^ j * (kS l ^ 2 / (xS μ l + Qgeo l (j + 1 + 1))) by ring, kS_sq hl]
    apply mul_le_mul_of_nonneg_left _ hkj.le
    rw [div_le_iff₀ hD', inv_mul_eq_div, le_div_iff₀ hD]
    linarith
  unfold mMom
  rw [if_neg (by omega), if_neg (by omega), le_div_iff₀ hk]
  calc Acoef μ l (n + 1) * etaW μ l (n + 1) * kS l
      = (Acoef μ l (n + 1) * kS l) * etaW μ l (n + 1) := by ring
    _ ≤ Acoef μ l n * etaW μ l n := mul_le_mul hA he he0 hA0'

end LPPMonotonicityProof.Analytic
