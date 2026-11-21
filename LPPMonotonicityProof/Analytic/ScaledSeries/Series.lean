module

public import LPPMonotonicityProof.Analytic.ScaledSeries.Deriv
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Differentiation of the moment series

Term-by-term differentiation of the scaled moment series of Section 4.3:

* the closed form `Aₙ = (l-1) k^{n-1}/(p + lⁿ - 1)` and its derivative `Aderiv`,
  with `|∂Aₙ| ≤ (1 + (a-1)⁻¹)(n+1) Aₙ` on `[a, ∞)`;
* `mMom' μ l n := deriv (fun l => mMom μ l n) l`, with `hasDerivAt_mMom`;
* the uniform envelope `|mₙ| + |mₙ'| ≤ C (n+1) ρⁿ` on compact subintervals of `(1, m)`
  (`mMom'_summable_bound`, `mMom'_summable_bound_compact`);
* term-by-term differentiation of `S`, `T` and `h` (`hasDerivAt_Ssc`, `hasDerivAt_Tsc`,
  `hasDerivAt_hsc`), and the algebraic identity `dx_Vsc`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-! ### The prefix coefficient `Aₙ` -/

/-- `Aₙ = (l-1) k^{n-1} / (p + lⁿ - 1)` for `l > 1`. -/
theorem Acoef_eq_closed {l : ℝ} (hl : 1 < l) (n : ℕ) :
    Acoef μ l n = (l - 1) * kS l ^ (n - 1) * (pBr μ + l ^ n - 1)⁻¹ := by
  have ha : l - 1 ≠ 0 := ne_of_gt (by linarith)
  have hQ : Qgeo l n * (l - 1) = l ^ n - 1 := geom_sum_mul_of_one_le hl.le n
  have hden : xS μ l + Qgeo l n = (pBr μ + l ^ n - 1) / (l - 1) := by
    unfold xS
    field_simp
    nlinarith [hQ]
  rw [Acoef, iota, hden, inv_div]
  ring

theorem hasDerivAt_sqrt_pow {l : ℝ} (hl : 0 < l) (m : ℕ) :
    HasDerivAt (fun y => Real.sqrt y ^ m) ((m : ℝ) / (2 * l) * Real.sqrt l ^ m) l := by
  have hs0 : Real.sqrt l ≠ 0 := (Real.sqrt_pos.2 hl).ne'
  have hss : Real.sqrt l * Real.sqrt l = l := Real.mul_self_sqrt hl.le
  refine ((Real.hasDerivAt_sqrt hl.ne').fun_pow m).congr_deriv ?_
  rcases m with _ | j
  · simp
  · have key : ∀ s : ℝ, s ≠ 0 → ((j + 1 : ℕ) : ℝ) * s ^ j * (1 / (2 * s)) =
        ((j + 1 : ℕ) : ℝ) / (2 * (s * s)) * s ^ (j + 1) := by
      intro s hs
      calc ((j + 1 : ℕ) : ℝ) * s ^ j * (1 / (2 * s))
          = ((j + 1 : ℕ) : ℝ) * s ^ j * (1 / (2 * s)) * (s * s⁻¹) := by
            rw [mul_inv_cancel₀ hs, mul_one]
        _ = _ := by ring
    have hk := key (Real.sqrt l) hs0
    rw [hss] at hk
    simp only [Nat.add_sub_cancel]
    exact hk

/-- The derivative of `Aₙ` in `l`. -/
noncomputable def Aderiv (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) (n : ℕ) : ℝ :=
  kS l ^ (n - 1) * (pBr μ + l ^ n - 1)⁻¹ +
    Acoef μ l n * (((n - 1 : ℕ) : ℝ) / (2 * l) - n * l ^ (n - 1) / (pBr μ + l ^ n - 1))

theorem hasDerivAt_Acoef (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (n : ℕ) :
    HasDerivAt (fun y => Acoef μ y n) (Aderiv μ l n) l := by
  have hp := pBr_pos h
  have hl0 : 0 < l := by linarith
  have hD : 0 < pBr μ + l ^ n - 1 := by
    have := one_le_pow₀ hl.le (n := n); linarith
  have hu : HasDerivAt (fun y : ℝ => y - 1) 1 l := (hasDerivAt_id' (x := l)).sub_const 1
  have hv := hasDerivAt_sqrt_pow hl0 (n - 1)
  have hw : HasDerivAt (fun y : ℝ => (pBr μ + y ^ n - 1)⁻¹)
      (-((n : ℝ) * l ^ (n - 1)) / (pBr μ + l ^ n - 1) ^ 2) l :=
    (((hasDerivAt_pow n l).const_add (pBr μ)).sub_const 1).fun_inv hD.ne'
  have hprod := (hu.fun_mul hv).fun_mul hw
  refine (hprod.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [Aderiv, Acoef_eq_closed hl n]
    unfold kS
    generalize pBr μ + l ^ n - 1 = D
    ring
  · filter_upwards [lt_mem_nhds hl] with y hy
    exact Acoef_eq_closed hy n

/-- `|∂Aₙ| ≤ (1 + (a-1)⁻¹)(n+1) Aₙ` for `l ≥ a > 1`. -/
theorem abs_Aderiv_le (h : OffspringHyp μ) {a l : ℝ} (ha : 1 < a) (hal : a ≤ l) (n : ℕ) :
    |Aderiv μ l n| ≤ (1 + (a - 1)⁻¹) * (n + 1) * Acoef μ l n := by
  have hl : 1 < l := by linarith
  have hl0 : 0 < l := by linarith
  have hp := pBr_pos h
  have hDpos : 0 < pBr μ + l ^ n - 1 := by
    have := one_le_pow₀ hl.le (n := n); linarith
  have hAc := Acoef_eq_closed (μ := μ) hl n
  have hA0 := Acoef_nonneg h hl n
  rw [Aderiv]
  set D := pBr μ + l ^ n - 1 with hD_def
  set v := kS l ^ (n - 1) with hv_def
  set A := Acoef μ l n with hA_def
  set c := ((n - 1 : ℕ) : ℝ) / (2 * l) with hc_def
  set d := (n : ℝ) * l ^ (n - 1) / D with hd_def
  set t := (a - 1)⁻¹ with ht_def
  have ht0 : 0 ≤ t := inv_nonneg.2 (by linarith)
  have hv0 : 0 ≤ v := pow_nonneg (kS_pos hl).le _
  have hvD0 : 0 ≤ v * D⁻¹ := mul_nonneg hv0 (inv_nonneg.2 hDpos.le)
  have hvw : v * D⁻¹ ≤ A * t := by
    have h1 : v * D⁻¹ * (l - 1) = A := by rw [hAc]; ring
    have h2 : v * D⁻¹ * (a - 1) ≤ A := by
      rw [← h1]
      exact mul_le_mul_of_nonneg_left (by linarith) hvD0
    have hne : a - 1 ≠ 0 := ne_of_gt (by linarith)
    calc v * D⁻¹ = v * D⁻¹ * ((a - 1) * t) := by rw [ht_def, mul_inv_cancel₀ hne, mul_one]
      _ = v * D⁻¹ * (a - 1) * t := by ring
      _ ≤ A * t := mul_le_mul_of_nonneg_right h2 ht0
  have hc0 : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hc : c ≤ n := by
    calc c ≤ ((n - 1 : ℕ) : ℝ) := div_le_self (Nat.cast_nonneg _) (by linarith)
      _ ≤ n := Nat.cast_le.mpr (Nat.sub_le n 1)
  have hd0 : 0 ≤ d := div_nonneg (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hl0.le _)) hDpos.le
  have hd : d ≤ n * t := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hd_def, hn]
      simp
    · have hpow : l ^ n = l ^ (n - 1) * l := by rw [← pow_succ, Nat.sub_add_cancel hn]
      have hl1 : 1 ≤ l ^ (n - 1) := one_le_pow₀ hl.le
      have hkey : (l - 1) * l ^ (n - 1) ≤ D := by rw [hD_def, hpow]; nlinarith
      calc d ≤ n / (l - 1) := by
            rw [hd_def, div_le_div_iff₀ hDpos (by linarith)]
            nlinarith [mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg n)]
        _ ≤ n / (a - 1) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by linarith) (by linarith)
        _ = n * t := div_eq_mul_inv _ _
  have hcd : |c - d| ≤ c + d := by
    calc |c - d| ≤ |c| + |d| := abs_sub _ _
      _ = c + d := by rw [abs_of_nonneg hc0, abs_of_nonneg hd0]
  calc |v * D⁻¹ + A * (c - d)| ≤ |v * D⁻¹| + |A * (c - d)| := abs_add_le _ _
    _ = v * D⁻¹ + A * |c - d| := by rw [abs_of_nonneg hvD0, abs_mul, abs_of_nonneg hA0]
    _ ≤ A * t + A * (n + n * t) := by
        apply add_le_add hvw
        apply mul_le_mul_of_nonneg_left _ hA0
        linarith
    _ ≤ (1 + t) * (n + 1) * A := by
        have : (1 + t) * (n + 1) * A - (A * t + A * (n + n * t)) = A := by ring
        linarith

/-! ### `mMom'` -/

/-- The `l`-derivative of `mₙ`. -/
noncomputable def mMom' (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) (n : ℕ) : ℝ :=
  deriv (fun l' => mMom μ l' n) l

private theorem mMom_zero_fun : (fun y => mMom μ y 0) = fun _ => (0 : ℝ) := by
  funext y
  simp [mMom]

theorem mMom'_zero (l : ℝ) : mMom' μ l 0 = 0 := by
  unfold mMom'
  rw [mMom_zero_fun, deriv_const]

theorem hasDerivAt_mMom_explicit (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt (fun y => mMom μ y n)
      (Aderiv μ l n * etaW μ l n + Acoef μ l n * deriv (fun y => etaW μ y n) l) l := by
  have he : (fun y => mMom μ y n) = fun y => Acoef μ y n * etaW μ y n := by
    funext y
    rw [mMom, if_neg (by omega)]
  rw [he]
  exact (hasDerivAt_Acoef h hl n).fun_mul (hasDerivAt_etaW h hl hlm n).differentiableAt.hasDerivAt

theorem mMom'_eq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    {n : ℕ} (hn : 1 ≤ n) :
    mMom' μ l n = Aderiv μ l n * etaW μ l n + Acoef μ l n * deriv (fun y => etaW μ y n) l :=
  (hasDerivAt_mMom_explicit h hl hlm hn).deriv

/-- `mₙ` is differentiable on `(1, m)`, with derivative `mMom'`. -/
theorem hasDerivAt_mMom (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    HasDerivAt (fun l => mMom μ l n) (mMom' μ l n) l := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [mMom'_zero, mMom_zero_fun]
    exact hasDerivAt_const l 0
  · exact (hasDerivAt_mMom_explicit h hl hlm hn).differentiableAt.hasDerivAt

/-! ### The uniform envelope on compact subintervals -/

/-- On `[a, b] ⊂ (1, m)`: `|mₙ| + |mₙ'| ≤ C (n+1) ρⁿ` with `ρ < 1`. -/
theorem mMom'_summable_bound (h : OffspringHyp μ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hb : b < mean μ) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ l ∈ Set.Icc a b, ∀ n : ℕ,
      |mMom μ l n| + |mMom' μ l n| ≤ C * (n + 1) * ρ ^ n := by
  letI := splitLaw_prob h
  set E := ∫ T, (childEnv a b T + 1) / (a - 1) ∂splitLaw μ with hE
  have hE0 : 0 ≤ E := integral_nonneg fun T =>
    div_nonneg (by linarith [childEnv_nonneg a b T]) (by linarith)
  set t := (a - 1)⁻¹ with ht_def
  have ht0 : 0 ≤ t := inv_nonneg.2 (by linarith)
  have hkb : 0 < kS b := kS_pos (by linarith)
  have hC0 : 0 ≤ kS b * (2 + t + E) := mul_nonneg hkb.le (by linarith)
  refine ⟨kS b * (2 + t + E), (kS a)⁻¹, hC0, (kS_inv_mem ha).1, (kS_inv_mem ha).2, ?_⟩
  intro l hlI n
  have hl1 : 1 < l := by linarith [hlI.1]
  have hlm : l < mean μ := by linarith [hlI.2]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hm0 : mMom μ l 0 = 0 := by simp [mMom]
    simp only [mMom'_zero, hm0, abs_zero, add_zero, Nat.cast_zero, zero_add, pow_zero, mul_one]
    exact hC0
  · have hmm : mMom μ l n = Acoef μ l n * etaW μ l n := by rw [mMom, if_neg (by omega)]
    obtain ⟨he0, he1⟩ := etaW_mem h hl1 hlm n
    have hA0 := Acoef_nonneg h hl1 n
    have hA' := abs_Aderiv_le h ha hlI.1 n
    have hη' := abs_deriv_etaW_le h ha hab hb hlI n
    have hAg := Acoef_le_geom h hl1 hn
    have hkl : kS l * (kS l)⁻¹ ^ n ≤ kS b * (kS a)⁻¹ ^ n := by
      apply mul_le_mul (Real.sqrt_le_sqrt hlI.2)
        (pow_le_pow_left₀ (inv_nonneg.2 (kS_pos hl1).le)
          (inv_anti₀ (kS_pos ha) (Real.sqrt_le_sqrt hlI.1)) n)
        (pow_nonneg (inv_nonneg.2 (kS_pos hl1).le) n) hkb.le
    rw [mMom'_eq h hl1 hlm hn, hmm]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hB0 : 0 ≤ (1 + t) * (n + 1) * Acoef μ l n :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hA0
    have h1 : |Acoef μ l n * etaW μ l n| ≤ Acoef μ l n := by
      rw [abs_of_nonneg (mul_nonneg hA0 he0)]
      calc Acoef μ l n * etaW μ l n ≤ Acoef μ l n * 1 := mul_le_mul_of_nonneg_left he1 hA0
        _ = Acoef μ l n := mul_one _
    have h2 : |Aderiv μ l n * etaW μ l n + Acoef μ l n * deriv (fun y => etaW μ y n) l| ≤
        (1 + t) * (n + 1) * Acoef μ l n + Acoef μ l n * (n * E) := by
      calc _ ≤ |Aderiv μ l n * etaW μ l n| + |Acoef μ l n * deriv (fun y => etaW μ y n) l| :=
            abs_add_le _ _
        _ = |Aderiv μ l n| * etaW μ l n + Acoef μ l n * |deriv (fun y => etaW μ y n) l| := by
            rw [abs_mul, abs_mul, abs_of_nonneg he0, abs_of_nonneg hA0]
        _ ≤ (1 + t) * (n + 1) * Acoef μ l n * 1 + Acoef μ l n * (n * E) :=
            add_le_add (mul_le_mul hA' he1 he0 hB0) (mul_le_mul_of_nonneg_left hη' hA0)
        _ = _ := by ring
    have hsum : (n + 1) * (2 + t + E) * Acoef μ l n -
        (Acoef μ l n + ((1 + t) * (n + 1) * Acoef μ l n + Acoef μ l n * (n * E))) =
          Acoef μ l n * (n + E) := by ring
    have hpos : 0 ≤ Acoef μ l n * (n + E) := mul_nonneg hA0 (by linarith)
    calc _ ≤ Acoef μ l n + ((1 + t) * (n + 1) * Acoef μ l n + Acoef μ l n * (n * E)) :=
          add_le_add h1 h2
      _ ≤ (n + 1) * (2 + t + E) * Acoef μ l n := by linarith
      _ ≤ (n + 1) * (2 + t + E) * (kS b * (kS a)⁻¹ ^ n) :=
          mul_le_mul_of_nonneg_left (hAg.trans hkl) (mul_nonneg (by linarith) (by linarith))
      _ = kS b * (2 + t + E) * (n + 1) * (kS a)⁻¹ ^ n := by ring

/-- The same envelope on an arbitrary compact `I ⊂ (1, m)`. -/
theorem mMom'_summable_bound_compact (h : OffspringHyp μ) {I : Set ℝ} (hI : IsCompact I)
    (hIsub : I ⊆ Set.Ioo 1 (mean μ)) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ l ∈ I, ∀ n : ℕ,
      |mMom μ l n| + |mMom' μ l n| ≤ C * (n + 1) * ρ ^ n := by
  rcases Set.eq_empty_or_nonempty I with hI0 | hne
  · exact ⟨0, 0, le_rfl, le_rfl, zero_lt_one, fun l hl => by simp [hI0] at hl⟩
  · have hamem := hI.sInf_mem hne
    have hbmem := hI.sSup_mem hne
    obtain ⟨C, ρ, hC, hρ0, hρ1, hB⟩ := mMom'_summable_bound h (hIsub hamem).1
      (csInf_le_csSup hne hI.bddBelow hI.bddAbove) (hIsub hbmem).2
    exact ⟨C, ρ, hC, hρ0, hρ1, fun l hl n =>
      hB l ⟨csInf_le hI.bddBelow hl, le_csSup hI.bddAbove hl⟩ n⟩

/-! ### Term-by-term differentiation -/

theorem summable_sq_mul_geom {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ 2 * r ^ n := by
  have hr : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hmaj : Summable fun n : ℕ => 2 * ((n : ℝ) ^ 2 * r ^ n) + 2 * r ^ n :=
    ((summable_pow_mul_geometric_of_norm_lt_one 2 hr).mul_left 2).add
      ((summable_geometric_of_lt_one hr0 hr1).mul_left 2)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (pow_nonneg hr0 n))
    (fun n => ?_) hmaj
  have hrn := pow_nonneg hr0 n
  nlinarith [mul_nonneg (sq_nonneg ((n : ℝ) - 1)) hrn]

private theorem prod_bound {C ρ : ℝ} (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {x y : ℝ}
    {n i j : ℕ} (hi : i ≤ 2) (hj : j ≤ 2)
    (hx : |x| ≤ C * (((n + i : ℕ) : ℝ) + 1) * ρ ^ (n + i))
    (hy : |y| ≤ C * (((n + j : ℕ) : ℝ) + 1) * ρ ^ (n + j)) :
    |x * y| ≤ 9 * C ^ 2 * ((n : ℝ) + 1) ^ 2 * (ρ ^ 2) ^ n := by
  have hstep : ∀ k : ℕ, k ≤ 2 →
      C * (((n + k : ℕ) : ℝ) + 1) * ρ ^ (n + k) ≤ C * (3 * ((n : ℝ) + 1)) * ρ ^ n := by
    intro k hk
    have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    have hcast : ((n + k : ℕ) : ℝ) + 1 ≤ 3 * ((n : ℝ) + 1) := by
      push_cast; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hpow : ρ ^ (n + k) ≤ ρ ^ n := pow_le_pow_of_le_one hρ0 hρ1 (by omega)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hcast hC) hpow (pow_nonneg hρ0 _)
      (mul_nonneg hC (by positivity))
  rw [abs_mul]
  calc |x| * |y| ≤ (C * (3 * ((n : ℝ) + 1)) * ρ ^ n) * (C * (3 * ((n : ℝ) + 1)) * ρ ^ n) :=
        mul_le_mul (hx.trans (hstep i hi)) (hy.trans (hstep j hj)) (abs_nonneg _)
          (mul_nonneg (mul_nonneg hC (by positivity)) (pow_nonneg hρ0 _))
    _ = 9 * C ^ 2 * ((n : ℝ) + 1) ^ 2 * (ρ ^ 2) ^ n := by ring

/-- The derivative of `S = Σ m_{n+1}²`. -/
noncomputable def SscDeriv (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) : ℝ :=
  ∑' n : ℕ, 2 * mMom μ l (n + 1) * mMom' μ l (n + 1)

/-- The derivative of `T = Σ m_{n+1} m_{n+2}`. -/
noncomputable def TscDeriv (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) : ℝ :=
  ∑' n : ℕ, (mMom' μ l (n + 1) * mMom μ l (n + 2) + mMom μ l (n + 1) * mMom' μ l (n + 2))

/-- A neighbourhood interval with the uniform envelope, used for both series. -/
private theorem local_envelope (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    ∃ a b C ρ : ℝ, 1 < a ∧ a < l ∧ l < b ∧ b < mean μ ∧ 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ y ∈ Set.Ioo a b, ∀ n : ℕ, |mMom μ y n| ≤ C * (n + 1) * ρ ^ n ∧
        |mMom' μ y n| ≤ C * (n + 1) * ρ ^ n := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, hB⟩ := mMom'_summable_bound h (a := (1 + l) / 2)
    (b := (l + mean μ) / 2) (by linarith) (by linarith) (by linarith)
  refine ⟨(1 + l) / 2, (l + mean μ) / 2, C, ρ, by linarith, by linarith, by linarith,
    by linarith, hC, hρ0, hρ1, fun y hy n => ?_⟩
  have hb := hB y ⟨hy.1.le, hy.2.le⟩ n
  exact ⟨by linarith [abs_nonneg (mMom' μ y n)], by linarith [abs_nonneg (mMom μ y n)]⟩

/-- Term-by-term derivative of `S`. -/
theorem hasDerivAt_Ssc (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    HasDerivAt (Ssc μ) (SscDeriv μ l) l := by
  obtain ⟨a, b, C, ρ, ha, hal, hlb, hb, hC, hρ0, hρ1, hB⟩ := local_envelope h hl hlm
  have hu : Summable fun n : ℕ => 18 * C ^ 2 * (((n : ℝ) + 1) ^ 2 * (ρ ^ 2) ^ n) :=
    (summable_sq_mul_geom (sq_nonneg ρ) (by nlinarith)).mul_left _
  have hg : ∀ n : ℕ, ∀ y ∈ Set.Ioo a b, HasDerivAt (fun z => mMom μ z (n + 1) ^ 2)
      (2 * mMom μ y (n + 1) * mMom' μ y (n + 1)) y := by
    intro n y hy
    have hy1 : 1 < y := by linarith [hy.1]
    have hym : y < mean μ := by linarith [hy.2]
    refine ((hasDerivAt_mMom h hy1 hym (n + 1)).fun_pow 2).congr_deriv ?_
    norm_num
  have hg' : ∀ n : ℕ, ∀ y ∈ Set.Ioo a b,
      ‖2 * mMom μ y (n + 1) * mMom' μ y (n + 1)‖ ≤
        18 * C ^ 2 * (((n : ℝ) + 1) ^ 2 * (ρ ^ 2) ^ n) := by
    intro n y hy
    have hp := prod_bound hC hρ0 hρ1.le (n := n) (i := 1) (j := 1) (by norm_num) (by norm_num)
      (hB y hy (n + 1)).1 (hB y hy (n + 1)).2
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_two]
    linarith
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg' ⟨hal, hlb⟩
    (summable_Ssc h hl hlm) ⟨hal, hlb⟩

/-- Term-by-term derivative of `T`. -/
theorem hasDerivAt_Tsc (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    HasDerivAt (Tsc μ) (TscDeriv μ l) l := by
  obtain ⟨a, b, C, ρ, ha, hal, hlb, hb, hC, hρ0, hρ1, hB⟩ := local_envelope h hl hlm
  have hu : Summable fun n : ℕ => 18 * C ^ 2 * (((n : ℝ) + 1) ^ 2 * (ρ ^ 2) ^ n) :=
    (summable_sq_mul_geom (sq_nonneg ρ) (by nlinarith)).mul_left _
  have hg : ∀ n : ℕ, ∀ y ∈ Set.Ioo a b,
      HasDerivAt (fun z => mMom μ z (n + 1) * mMom μ z (n + 2))
        (mMom' μ y (n + 1) * mMom μ y (n + 2) + mMom μ y (n + 1) * mMom' μ y (n + 2)) y := by
    intro n y hy
    have hy1 : 1 < y := by linarith [hy.1]
    have hym : y < mean μ := by linarith [hy.2]
    exact (hasDerivAt_mMom h hy1 hym (n + 1)).fun_mul (hasDerivAt_mMom h hy1 hym (n + 2))
  have hg' : ∀ n : ℕ, ∀ y ∈ Set.Ioo a b,
      ‖mMom' μ y (n + 1) * mMom μ y (n + 2) + mMom μ y (n + 1) * mMom' μ y (n + 2)‖ ≤
        18 * C ^ 2 * (((n : ℝ) + 1) ^ 2 * (ρ ^ 2) ^ n) := by
    intro n y hy
    have hp1 := prod_bound hC hρ0 hρ1.le (n := n) (i := 1) (j := 2) (by norm_num) (by norm_num)
      (hB y hy (n + 1)).2 (hB y hy (n + 2)).1
    have hp2 := prod_bound hC hρ0 hρ1.le (n := n) (i := 1) (j := 2) (by norm_num) (by norm_num)
      (hB y hy (n + 1)).1 (hB y hy (n + 2)).2
    rw [Real.norm_eq_abs]
    calc _ ≤ |mMom' μ y (n + 1) * mMom μ y (n + 2)| + |mMom μ y (n + 1) * mMom' μ y (n + 2)| :=
          abs_add_le _ _
      _ ≤ _ := by linarith
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg' ⟨hal, hlb⟩
    (summable_Tsc h hl hlm) ⟨hal, hlb⟩

/-- The derivative of `h = m₁ - x((1+l)S/2 - kT)`. -/
noncomputable def hscDeriv (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) : ℝ :=
  mMom' μ l 1 - (-(pBr μ) / (l - 1) ^ 2 * ((1 + l) * Ssc μ l / 2 - kS l * Tsc μ l) +
    xS μ l * ((Ssc μ l + (1 + l) * SscDeriv μ l) / 2 -
      (1 / (2 * kS l) * Tsc μ l + kS l * TscDeriv μ l)))

theorem hasDerivAt_xS {l : ℝ} (hl : 1 < l) :
    HasDerivAt (fun y => xS μ y) (-(pBr μ) / (l - 1) ^ 2) l := by
  have := (hasDerivAt_const l (pBr μ)).fun_div ((hasDerivAt_id' (x := l)).sub_const 1)
    (ne_of_gt (by linarith))
  exact this.congr_deriv (by ring)

theorem hasDerivAt_kS {l : ℝ} (hl : 0 < l) : HasDerivAt (fun y => kS y) (1 / (2 * kS l)) l :=
  Real.hasDerivAt_sqrt hl.ne'

/-- Derivative of `h`, from those of `m₁`, `x`, `k`, `S` and `T`. -/
theorem hasDerivAt_hsc (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    HasDerivAt (hsc μ) (hscDeriv μ l) l := by
  have hm1 := hasDerivAt_mMom h hl hlm 1
  have hx := hasDerivAt_xS (μ := μ) hl
  have hk := hasDerivAt_kS (show 0 < l by linarith)
  have hS : HasDerivAt (fun y => Ssc μ y) (SscDeriv μ l) l := hasDerivAt_Ssc h hl hlm
  have hT : HasDerivAt (fun y => Tsc μ y) (TscDeriv μ l) l := hasDerivAt_Tsc h hl hlm
  have hinner := (((hasDerivAt_id' (x := l)).const_add 1).fun_mul hS).div_const 2
  have hbr := hinner.fun_sub (hk.fun_mul hT)
  have htot := hm1.fun_sub (hx.fun_mul hbr)
  refine htot.congr_deriv ?_
  rw [hscDeriv]
  ring

/-! ### The scaled derivative of `V` -/

/-- `∂ₓV = -s² v'` (pure algebra; no hypothesis is needed). -/
theorem dx_Vsc (l : ℝ) : dx μ (Vsc μ) l = -(sS μ l) ^ 2 * deriv (speedValueProv μ) l := by
  have hd : deriv (Vsc μ) l = deriv (speedValueProv μ) l / pBr μ := by
    show deriv (fun y => speedValueProv μ y / pBr μ) l = _
    exact deriv_div_const _
  rw [dx, hd, sS]
  ring

end LPPMonotonicityProof.Analytic
