module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Pi
public import LPPMonotonicityProof.RTL.LocallyFinite.Law

/-!
# Generic analytic tools

This module contains four generic tools: Chebyshev's covariance inequality, the
generic single-crossing inequality (first part of Lemma 3.4, `lem:single-crossing`),
exchangeability and splitting of i.i.d. families of trees, and the power-series
expansion of the two-copy kernels. The i.i.d. statements are stated for
`bienaymeLaw μ` (`GW μ` of `Analytic/Defs.lean` is the same abbreviation), so that this
module stays generic.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open LPPMonotonicityProof.RTL.LocallyFinite
open scoped ENNReal NNReal

namespace LPPMonotonicityProof.Analytic

/-- **Covariance inequality.** Chebyshev's covariance inequality for a monotone and an antitone
observable of the same random variable. -/
theorem integral_mul_le_of_monotone_antitone {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ} {f g : ℝ → ℝ} (s : Set ℝ)
    (hZ : ∀ᵐ ω ∂P, Z ω ∈ s) (hf : MonotoneOn f s) (hg : AntitoneOn g s)
    (hfi : Integrable (f ∘ Z) P) (hgi : Integrable (g ∘ Z) P)
    (hfgi : Integrable (fun ω => f (Z ω) * g (Z ω)) P) :
    ∫ ω, f (Z ω) * g (Z ω) ∂P ≤ (∫ ω, f (Z ω) ∂P) * ∫ ω, g (Z ω) ∂P := by
  let A : Ω → ℝ := fun ω => f (Z ω)
  let B : Ω → ℝ := fun ω => g (Z ω)
  have hAi : Integrable A P := hfi
  have hBi : Integrable B P := hgi
  have hABi : Integrable (fun ω => A ω * B ω) P := hfgi
  have hdiag₁ : Integrable (fun p : Ω × Ω => A p.1 * B p.1) (P.prod P) :=
    hABi.comp_fst P
  have hdiag₂ : Integrable (fun p : Ω × Ω => A p.2 * B p.2) (P.prod P) :=
    hABi.comp_snd P
  have hcross₁ : Integrable (fun p : Ω × Ω => A p.1 * B p.2) (P.prod P) :=
    hAi.mul_prod hBi
  have hcross₂ : Integrable (fun p : Ω × Ω => B p.1 * A p.2) (P.prod P) :=
    hBi.mul_prod hAi
  have hformula :
      (∫ p, (A p.1 - A p.2) * (B p.1 - B p.2) ∂P.prod P) =
        2 * (∫ ω, A ω * B ω ∂P) - 2 * (∫ ω, A ω ∂P) * ∫ ω, B ω ∂P := by
    rw [show (fun p : Ω × Ω => (A p.1 - A p.2) * (B p.1 - B p.2)) =
        (fun p => ((A p.1 * B p.1 + A p.2 * B p.2) -
          A p.1 * B p.2) - B p.1 * A p.2) by funext p; ring]
    rw [integral_sub
        (f := fun p : Ω × Ω => A p.1 * B p.1 + A p.2 * B p.2 - A p.1 * B p.2)
        (g := fun p => B p.1 * A p.2) ((hdiag₁.add hdiag₂).sub hcross₁) hcross₂,
      integral_sub (f := fun p : Ω × Ω => A p.1 * B p.1 + A p.2 * B p.2)
        (g := fun p => A p.1 * B p.2) (hdiag₁.add hdiag₂) hcross₁,
      integral_add hdiag₁ hdiag₂,
      integral_fun_fst (μ := P) (ν := P) (fun ω => A ω * B ω),
      integral_fun_snd (μ := P) (ν := P) (fun ω => A ω * B ω),
      integral_prod_mul A B, integral_prod_mul B A]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    ring
  have hZ₁ : ∀ᵐ p ∂P.prod P, Z p.1 ∈ s :=
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hZ
  have hZ₂ : ∀ᵐ p ∂P.prod P, Z p.2 ∈ s :=
    (Measure.quasiMeasurePreserving_snd (μ := P) (ν := P)).ae hZ
  have hpoint : ∀ᵐ p ∂P.prod P, (A p.1 - A p.2) * (B p.1 - B p.2) ≤ 0 := by
    filter_upwards [hZ₁, hZ₂] with p hp₁ hp₂
    dsimp only [A, B]
    rcases le_total (Z p.1) (Z p.2) with hle | hle
    · have hf' := hf hp₁ hp₂ hle
      have hg' := hg hp₁ hp₂ hle
      nlinarith
    · have hf' := hf hp₂ hp₁ hle
      have hg' := hg hp₂ hp₁ hle
      nlinarith
  have hnonpos : (∫ p, (A p.1 - A p.2) * (B p.1 - B p.2) ∂P.prod P) ≤ 0 := by
    have hnonneg : 0 ≤ ∫ p, -((A p.1 - A p.2) * (B p.1 - B p.2)) ∂P.prod P :=
      integral_nonneg_of_ae (hpoint.mono fun p hp => neg_nonneg.mpr hp)
    rw [integral_neg] at hnonneg
    linarith
  rw [hformula] at hnonpos
  change (∫ ω, A ω * B ω ∂P) ≤ (∫ ω, A ω ∂P) * ∫ ω, B ω ∂P
  linarith

/-- **Covariance inequality, monotone/monotone variant.** -/
theorem integral_mul_ge_of_monotone {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ} {f g : ℝ → ℝ} (s : Set ℝ)
    (hZ : ∀ᵐ ω ∂P, Z ω ∈ s) (hf : MonotoneOn f s) (hg : MonotoneOn g s)
    (hfi : Integrable (f ∘ Z) P) (hgi : Integrable (g ∘ Z) P)
    (hfgi : Integrable (fun ω => f (Z ω) * g (Z ω)) P) :
    (∫ ω, f (Z ω) ∂P) * ∫ ω, g (Z ω) ∂P ≤ ∫ ω, f (Z ω) * g (Z ω) ∂P := by
  have hneg : AntitoneOn (fun y => -g y) s := fun _ ha _ hb hab => neg_le_neg (hg ha hb hab)
  have hgi' : Integrable ((fun y => -g y) ∘ Z) P := by simpa [Function.comp_def] using hgi.neg
  have hfgi' : Integrable (fun ω => f (Z ω) * (-g (Z ω))) P := by
    apply hfgi.neg.congr
    exact Filter.Eventually.of_forall fun ω => by simp
  have h := integral_mul_le_of_monotone_antitone s hZ hf hneg hfi hgi' hfgi'
  simp only [integral_neg, mul_neg] at h
  linarith

/-- **Lemma 3.4** (`lem:single-crossing`), first part. The generic single-crossing
inequality.  Neither nonnegativity of
`h` nor a sign condition at `c` is needed. -/
theorem single_crossing {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {s : Set ℝ}
    (hs : ∀ᵐ y ∂ρ, y ∈ s) {g h : ℝ → ℝ} {c : ℝ}
    (hneg : ∀ y ∈ s, y < c → g y ≤ 0) (hpos : ∀ y ∈ s, c < y → 0 ≤ g y)
    (hh : MonotoneOn h (s ∪ {c})) (hc : c ∈ s ∪ {c})
    (hgi : Integrable g ρ) (hghi : Integrable (g * h) ρ) :
    h c * ∫ y, g y ∂ρ ≤ ∫ y, g y * h y ∂ρ := by
  have hpoint : ∀ᵐ y ∂ρ, 0 ≤ g y * (h y - h c) := by
    filter_upwards [hs] with y hy
    rcases lt_trichotomy y c with hyc | rfl | hcy
    · have hgc := hneg y hy hyc
      have hhc := hh (Set.mem_union_left _ hy) hc hyc.le
      exact mul_nonneg_of_nonpos_of_nonpos hgc (sub_nonpos.mpr hhc)
    · simp
    · have hgc := hpos y hy hcy
      have hhc := hh hc (Set.mem_union_left _ hy) hcy.le
      exact mul_nonneg hgc (sub_nonneg.mpr hhc)
  have hghi' : Integrable (fun y => g y * h y) ρ := hghi
  have hint : Integrable (fun y => g y * h y - h c * g y) ρ := by
    exact hghi'.sub (hgi.const_mul (h c))
  have hnonneg : 0 ≤ ∫ y, (g y * h y - h c * g y) ∂ρ := by
    apply integral_nonneg_of_ae
    filter_upwards [hpoint] with y hy
    convert hy using 1; ring
  rw [integral_sub hghi' (hgi.const_mul (h c)), integral_const_mul] at hnonneg
  linarith


/-- **Exchangeability.** Permuting the coordinates of an i.i.d. finite family preserves every
Bochner integral (including the convention for a nonintegrable integrand). -/
theorem integral_pi_comp_perm (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (F : (Fin n → Tree) → ℝ) :
    ∫ ts, F (ts ∘ σ) ∂Measure.pi (fun _ => bienaymeLaw μ) =
      ∫ ts, F ts ∂Measure.pi (fun _ => bienaymeLaw μ) := by
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => bienaymeLaw μ) σ.symm
  have he (ts : Fin n → Tree) :
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Tree) σ.symm) ts = ts ∘ σ := by
    funext i
    have hi := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => Tree) σ.symm ts (σ i)
    simpa using hi
  have hi := hp.integral_comp' F
  simp_rw [he] at hi
  exact hi

/-- **Exchangeability, `lintegral` permutation form.** -/
theorem lintegral_pi_comp_perm (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (F : (Fin n → Tree) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ts, F (ts ∘ σ) ∂Measure.pi (fun _ => bienaymeLaw μ) =
      ∫⁻ ts, F ts ∂Measure.pi (fun _ => bienaymeLaw μ) := by
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => bienaymeLaw μ) σ.symm
  have he (ts : Fin n → Tree) :
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Tree) σ.symm) ts = ts ∘ σ := by
    funext i
    have hi := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => Tree) σ.symm ts (σ i)
    simpa using hi
  have hi := hp.lintegral_comp hF
  simp_rw [he] at hi
  exact hi

/-- **Splitting.** Splitting off coordinate zero turns an i.i.d. `(n+1)`-fold product
into the product of the first law and the remaining `n`-fold law. -/
theorem integral_pi_succ (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (F : Tree → (Fin n → Tree) → ℝ)
    (_hF : Integrable (fun p : Tree × (Fin n → Tree) => F p.1 p.2)
      ((bienaymeLaw μ).prod (Measure.pi fun _ : Fin n => bienaymeLaw μ))) :
    ∫ ts, F (ts 0) (Fin.tail ts) ∂Measure.pi (fun _ : Fin (n + 1) => bienaymeLaw μ) =
      ∫ p, F p.1 p.2 ∂(bienaymeLaw μ).prod (Measure.pi fun _ : Fin n => bienaymeLaw μ) := by
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => bienaymeLaw μ) 0
  simpa only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv, Equiv.coe_fn_symm_mk, Fin.tail, Fin.removeNth, Fin.zero_succAbove,
    Function.comp_apply] using hp.integral_comp' (fun p : Tree × (Fin n → Tree) => F p.1 p.2)

/-- **Splitting, `lintegral` head/tail form.** -/
theorem lintegral_pi_succ (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (F : Tree → (Fin n → Tree) → ℝ≥0∞)
    (hF : Measurable (fun p : Tree × (Fin n → Tree) => F p.1 p.2)) :
    ∫⁻ ts, F (ts 0) (Fin.tail ts) ∂Measure.pi (fun _ : Fin (n + 1) => bienaymeLaw μ) =
      ∫⁻ p, F p.1 p.2 ∂(bienaymeLaw μ).prod (Measure.pi fun _ : Fin n => bienaymeLaw μ) := by
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => bienaymeLaw μ) 0
  simpa only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv, Equiv.coe_fn_symm_mk, Fin.tail, Fin.removeNth, Fin.zero_succAbove,
    Function.comp_apply] using hp.lintegral_comp hF


private lemma hasSum_kernel_coeff {x : ℝ} (hx : ‖x‖ < 1) (e : ℕ)
    (he : e = 1 ∨ e = 2) :
    HasSum (fun n : ℕ => (if e = 1 then 1 else (n + 1 : ℝ)) * x ^ n)
      (1 / (1 - x) ^ e) := by
  rcases he with rfl | rfl
  · simpa using hasSum_geometric_of_norm_lt_one hx
  · simpa using hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hx

/-- **Kernel expansion.** Power-series expansion of the two-copy kernels.  Measurability is
formulated a.e. (the pinned Mathlib has no `MeasurableOn` declaration); the
uniform bounds are required only on the almost-sure support interval. -/
theorem integral_kernel_series {l : ℝ} (hl : 1 < l) {ρ ρ' : Measure ℝ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ρ']
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc 0 (1 / l)) (hρ' : ∀ᵐ t ∂ρ', t ∈ Set.Icc 0 (1 / l))
    {f g : ℝ → ℝ} (hf : AEMeasurable f ρ) (hg : AEMeasurable g ρ')
    (hf_bdd : ∃ C, ∀ y ∈ Set.Icc 0 (1 / l), |f y| ≤ C)
    (hg_bdd : ∃ C, ∀ t ∈ Set.Icc 0 (1 / l), |g t| ≤ C)
    (e : ℕ) (he : e = 1 ∨ e = 2) :
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
  have hlr : l * r = 1 := by
    dsimp [r]
    field_simp
  obtain ⟨Cf, hCf⟩ := hf_bdd
  obtain ⟨Cg, hCg⟩ := hg_bdd
  have hCf0 : 0 ≤ Cf := by
    obtain ⟨y, hy⟩ := hρ.exists
    exact (abs_nonneg (f y)).trans (hCf y hy)
  have hCg0 : 0 ≤ Cg := by
    obtain ⟨t, ht⟩ := hρ'.exists
    exact (abs_nonneg (g t)).trans (hCg t ht)
  have hAr (n : ℕ) : ∀ᵐ y ∂ρ, ‖A n y‖ ≤ Cf * r ^ n := by
    filter_upwards [hρ] with y hy
    have hy' : y ∈ Set.Icc 0 r := hy
    have hy_norm : ‖y‖ ≤ r := by
      rw [Real.norm_of_nonneg hy'.1]
      exact hy'.2
    calc
      ‖A n y‖ = ‖y‖ ^ n * ‖f y‖ := by simp [A, norm_mul, norm_pow]
      _ ≤ r ^ n * Cf := by
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg y) hy_norm n)
          (by simpa [Real.norm_eq_abs] using hCf y hy) (norm_nonneg _)
          (pow_nonneg hr0 _)
      _ = Cf * r ^ n := by ring
  have hBr (n : ℕ) : ∀ᵐ t ∂ρ', ‖B n t‖ ≤ Cg * r ^ n := by
    filter_upwards [hρ'] with t ht
    have ht' : t ∈ Set.Icc 0 r := ht
    have ht_norm : ‖t‖ ≤ r := by
      rw [Real.norm_of_nonneg ht'.1]
      exact ht'.2
    calc
      ‖B n t‖ = ‖t‖ ^ n * ‖g t‖ := by simp [B, norm_mul, norm_pow]
      _ ≤ r ^ n * Cg := by
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg t) ht_norm n)
          (by simpa [Real.norm_eq_abs] using hCg t ht) (norm_nonneg _)
          (pow_nonneg hr0 _)
      _ = Cg * r ^ n := by ring
  have hAi (n : ℕ) : Integrable (A n) ρ := by
    apply (integrable_const (Cf * r ^ n)).mono' _ (hAr n)
    apply AEStronglyMeasurable.congr
      ((aemeasurable_id.pow_const n).mul hf).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => rfl
  have hBi (n : ℕ) : Integrable (B n) ρ' := by
    apply (integrable_const (Cg * r ^ n)).mono' _ (hBr n)
    apply AEStronglyMeasurable.congr
      ((aemeasurable_id.pow_const n).mul hg).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => rfl
  have hFi (n : ℕ) : Integrable (F n) (ρ.prod ρ') := by
    exact ((hAi n).const_mul (c n * l ^ n)).mul_prod (hBi n)
  have hFb (n : ℕ) : ∀ᵐ p ∂ρ.prod ρ',
      ‖F n p‖ ≤ (n + 1 : ℝ) * Cf * Cg * r ^ n := by
    have hAprod := (Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := ρ')).ae (hAr n)
    have hBprod := (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := ρ')).ae (hBr n)
    filter_upwards [hAprod, hBprod] with p hpA hpB
    have hc0 : 0 ≤ c n := by
      dsimp [c]
      split_ifs <;> positivity
    have hcle : c n ≤ (n + 1 : ℝ) := by
      dsimp [c]
      split_ifs <;> simp
    calc
      ‖F n p‖ = c n * l ^ n * ‖A n p.1‖ * ‖B n p.2‖ := by
        simp only [F, norm_mul, norm_pow, Real.norm_of_nonneg hc0,
          Real.norm_of_nonneg hl0.le]
      _ ≤ (n + 1 : ℝ) * l ^ n * (Cf * r ^ n) * (Cg * r ^ n) := by
        gcongr
      _ = (n + 1 : ℝ) * Cf * Cg * r ^ n := by
        calc
          (n + 1 : ℝ) * l ^ n * (Cf * r ^ n) * (Cg * r ^ n) =
              (n + 1 : ℝ) * Cf * Cg * (l * r) ^ n * r ^ n := by ring
          _ = (n + 1 : ℝ) * Cf * Cg * r ^ n := by rw [hlr, one_pow]; ring
  have hFib (n : ℕ) : ∫ p, ‖F n p‖ ∂ρ.prod ρ' ≤ (n + 1 : ℝ) * Cf * Cg * r ^ n := by
    simpa [measureReal_def] using integral_mono_ae (hFi n).norm
      (integrable_const ((n + 1 : ℝ) * Cf * Cg * r ^ n)) (hFb n)
  have hr : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr0] using hr1
  have hbase : Summable (fun n : ℕ => (n + 1 : ℝ) * r ^ n) := by
    simpa using (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr)
  have hmajor : Summable (fun n : ℕ => (n + 1 : ℝ) * Cf * Cg * r ^ n) := by
    apply Summable.congr (hbase.mul_left (Cf * Cg))
    intro n
    ring
  have hsum : Summable (fun n : ℕ => ∫ p, ‖F n p‖ ∂ρ.prod ρ') := by
    apply hmajor.of_norm_bounded
    intro n
    rw [Real.norm_of_nonneg (integral_nonneg fun p => norm_nonneg (F n p))]
    exact hFib n
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
    have H := (hasSum_kernel_coeff hz e he).mul_left (f p.1 * g p.2)
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
    _ = ∑' n : ℕ, (if e = 1 then 1 else (n + 1 : ℝ)) * l ^ n *
        (∫ y, y ^ n * f y ∂ρ) * ∫ t, t ^ n * g t ∂ρ' := by
      apply tsum_congr
      intro n
      dsimp [F]
      rw [integral_prod_mul (fun y => c n * l ^ n * A n y) (B n), integral_const_mul]

end LPPMonotonicityProof.Analytic
