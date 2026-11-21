module

public import LPPMonotonicityProof.Analytic.Terminal
public import LPPMonotonicityProof.Analytic.Comparison
public import LPPMonotonicityProof.Analytic.Tools
public import LPPMonotonicityProof.Analytic.Certificates
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Intermediate-range moment coordinates

This module proves Lemma 5.3 (`lem:scaled-binary`) and expresses the first two
moments of `Y` in the moment-box coordinates `d = 1 - w` and
`η = E[(1 - W)²] / d` used in the proof of Theorem 5.1 (`thm:joint`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private lemma integrable_Wt_pow_joint (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : Integrable (fun T => Wt l T ^ n) (splitLaw μ) := by
  letI := splitLaw_prob h
  apply (integrable_const (1 : ℝ)).mono' ((measurable_Wt l).pow_const n).aestronglyMeasurable
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hT.1.le _)]
  exact pow_le_one₀ hT.1.le hT.2.le

private lemma integral_one_sub_Wt_sq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    (∫ T, (1 - Wt l T) ^ 2 ∂splitLaw μ) = 1 - 2 * wbar μ l + etaW μ l 2 := by
  letI := splitLaw_prob h
  have hW : Integrable (Wt l) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow_joint h hl hlm 1
  have hW2 := integrable_Wt_pow_joint h hl hlm 2
  calc
    (∫ T, (1 - Wt l T) ^ 2 ∂splitLaw μ) =
        ∫ T, (1 - 2 * Wt l T) + Wt l T ^ 2 ∂splitLaw μ := by
      apply integral_congr_ae
      filter_upwards with T
      ring
    _ = (∫ T, (1 - 2 * Wt l T) ∂splitLaw μ) + ∫ T, Wt l T ^ 2 ∂splitLaw μ := by
      rw [integral_add (f := fun T => 1 - 2 * Wt l T) (g := fun T => Wt l T ^ 2)
        ((integrable_const (1 : ℝ)).sub (hW.const_mul 2)) hW2]
    _ = 1 - 2 * wbar μ l + etaW μ l 2 := by
      rw [integral_sub (integrable_const (1 : ℝ)) (hW.const_mul 2), integral_const_mul]
      simp [wbar, etaW]

private lemma etaW_two_eq_box (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    etaW μ l 2 = 1 - 2 * dW μ l + dW μ l * etaD μ l := by
  have hd := (dW_pos h hl hlm).ne'
  have hsq := integral_one_sub_Wt_sq h hl hlm
  unfold etaD
  field_simp [hd]
  unfold dW at *
  linarith

/-- Weighted Chebyshev covariance for two antitone observables.  This is the
real-integral form of the `A²`-tilt used in Lemma 5.3. -/
private lemma weighted_covariance_antitone {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z w : Ω → ℝ} {f g : ℝ → ℝ} (s : Set ℝ)
    (hZ : ∀ᵐ ω ∂P, Z ω ∈ s) (hw0 : ∀ᵐ ω ∂P, 0 ≤ w ω) (hwi : Integrable w P)
    (hf : AntitoneOn f s) (hg : AntitoneOn g s)
    (hwf : Integrable (fun ω => w ω * f (Z ω)) P)
    (hwg : Integrable (fun ω => w ω * g (Z ω)) P)
    (hwfg : Integrable (fun ω => w ω * (f (Z ω) * g (Z ω))) P) :
    (∫ ω, w ω * f (Z ω) ∂P) * (∫ ω, w ω * g (Z ω) ∂P) ≤
      (∫ ω, w ω ∂P) * ∫ ω, w ω * (f (Z ω) * g (Z ω)) ∂P := by
  let A : Ω → ℝ := fun ω => w ω * f (Z ω)
  let B : Ω → ℝ := fun ω => w ω * g (Z ω)
  let C : Ω → ℝ := w
  let D : Ω → ℝ := fun ω => w ω * (f (Z ω) * g (Z ω))
  have hAi : Integrable A P := hwf
  have hBi : Integrable B P := hwg
  have hCi : Integrable C P := hwi
  have hDi : Integrable D P := hwfg
  have hdiag₁ : Integrable (fun p : Ω × Ω => D p.1 * C p.2) (P.prod P) :=
    hDi.mul_prod hCi
  have hdiag₂ : Integrable (fun p : Ω × Ω => C p.1 * D p.2) (P.prod P) :=
    hCi.mul_prod hDi
  have hcross₁ : Integrable (fun p : Ω × Ω => A p.1 * B p.2) (P.prod P) :=
    hAi.mul_prod hBi
  have hcross₂ : Integrable (fun p : Ω × Ω => B p.1 * A p.2) (P.prod P) :=
    hBi.mul_prod hAi
  have hformula :
      (∫ p, C p.1 * C p.2 * ((f (Z p.1) - f (Z p.2)) * (g (Z p.1) - g (Z p.2)))
        ∂P.prod P) =
        2 * (∫ ω, C ω ∂P) * (∫ ω, D ω ∂P) -
          2 * (∫ ω, A ω ∂P) * ∫ ω, B ω ∂P := by
    have hpoint (p : Ω × Ω) :
        C p.1 * C p.2 * ((f (Z p.1) - f (Z p.2)) * (g (Z p.1) - g (Z p.2))) =
          (D p.1 * C p.2 + C p.1 * D p.2 - A p.1 * B p.2) - B p.1 * A p.2 := by
      dsimp [A, B, C, D]
      ring
    simp_rw [hpoint]
    rw [integral_sub (f := fun p : Ω × Ω => D p.1 * C p.2 + C p.1 * D p.2 - A p.1 * B p.2)
        (g := fun p : Ω × Ω => B p.1 * A p.2) ((hdiag₁.add hdiag₂).sub hcross₁) hcross₂,
      integral_sub (f := fun p : Ω × Ω => D p.1 * C p.2 + C p.1 * D p.2)
        (g := fun p : Ω × Ω => A p.1 * B p.2) (hdiag₁.add hdiag₂) hcross₁,
      integral_add hdiag₁ hdiag₂,
      integral_prod_mul D C, integral_prod_mul C D,
      integral_prod_mul A B, integral_prod_mul B A]
    ring
  have hZ₁ : ∀ᵐ p ∂P.prod P, Z p.1 ∈ s :=
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hZ
  have hZ₂ : ∀ᵐ p ∂P.prod P, Z p.2 ∈ s :=
    (Measure.quasiMeasurePreserving_snd (μ := P) (ν := P)).ae hZ
  have hw₁ : ∀ᵐ p ∂P.prod P, 0 ≤ C p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hw0
  have hw₂ : ∀ᵐ p ∂P.prod P, 0 ≤ C p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := P) (ν := P)).ae hw0
  have hpoint : ∀ᵐ p ∂P.prod P,
      0 ≤ C p.1 * C p.2 * ((f (Z p.1) - f (Z p.2)) * (g (Z p.1) - g (Z p.2))) := by
    filter_upwards [hZ₁, hZ₂, hw₁, hw₂] with p hp₁ hp₂ hpw₁ hpw₂
    apply mul_nonneg (mul_nonneg hpw₁ hpw₂)
    rcases le_total (Z p.1) (Z p.2) with hle | hle
    · have hf' := hf hp₁ hp₂ hle
      have hg' := hg hp₁ hp₂ hle
      nlinarith
    · have hf' := hf hp₂ hp₁ hle
      have hg' := hg hp₂ hp₁ hle
      nlinarith
  have hnonneg := integral_nonneg_of_ae hpoint
  rw [hformula] at hnonneg
  change (∫ ω, A ω ∂P) * (∫ ω, B ω ∂P) ≤ (∫ ω, C ω ∂P) * ∫ ω, D ω ∂P
  linarith

private noncomputable def binaryKernel (a s : ℝ) : ℝ := (1 + a * s)⁻¹ ^ 2

private lemma tilted_moment_ratio {νA νS : Measure ℝ}
    [IsProbabilityMeasure νA] [IsProbabilityMeasure νS]
    (hA : ∀ᵐ a ∂νA, 0 < a ∧ a ≤ 1) (hS : ∀ᵐ s ∂νS, 0 ≤ s) :
    (∫ a, a ∂νA) * (∫ p : ℝ × ℝ, p.1 ^ 2 * binaryKernel p.1 p.2 ∂νA.prod νS) ≤
      (∫ a, a ^ 2 ∂νA) * ∫ p : ℝ × ℝ, p.1 * binaryKernel p.1 p.2 ∂νA.prod νS := by
  let P := νA.prod νS
  let g : ℝ → ℝ := fun a => ∫ s, binaryKernel a s ∂νS
  have hKm : Measurable (Function.uncurry binaryKernel) := by
    exact ((measurable_const.add (measurable_fst.mul measurable_snd)).inv.pow_const 2)
  have hgm : StronglyMeasurable g := hKm.stronglyMeasurable.integral_prod_right'
  have hA₁ : ∀ᵐ p ∂P, 0 < p.1 ∧ p.1 ≤ 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := νA) (ν := νS)).ae hA
  have hS₂ : ∀ᵐ p ∂P, 0 ≤ p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := νA) (ν := νS)).ae hS
  have hK_nonneg (a s : ℝ) : 0 ≤ binaryKernel a s := sq_nonneg _
  have hK_le_one {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) : binaryKernel a s ≤ 1 := by
    have hd : 1 ≤ 1 + a * s := by nlinarith
    have hi : (1 + a * s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd
    exact pow_le_one₀ (inv_nonneg.mpr (by linarith)) hi
  have hKi {a : ℝ} (ha : 0 < a) : Integrable (binaryKernel a) νS := by
    apply Integrable.of_bound (hKm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    filter_upwards [hS] with s hs
    change |binaryKernel a s| ≤ 1
    rw [abs_of_nonneg (hK_nonneg a s)]
    exact hK_le_one ha hs
  have hg0 {a : ℝ} (ha : 0 < a) : 0 ≤ g a := by
    apply integral_nonneg_of_ae
    filter_upwards with s
    exact hK_nonneg a s
  have hg1 {a : ℝ} (ha : 0 < a) : g a ≤ 1 := by
    calc
      g a ≤ ∫ _s, (1 : ℝ) ∂νS := by
        apply integral_mono_ae (hKi ha) (integrable_const 1)
        filter_upwards [hS] with s hs
        exact hK_le_one ha hs
      _ = 1 := by simp
  have hint (c : ℝ) (hc : ‖c‖ ≤ 1) {F : ℝ × ℝ → ℝ}
      (hFm : AEStronglyMeasurable F P)
      (hF : ∀ᵐ p ∂P, ‖F p‖ ≤ 1) : Integrable F P :=
    Integrable.of_bound hFm 1 hF
  have hw : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) P := by
    apply Integrable.of_bound (measurable_fst.pow_const 2).aestronglyMeasurable 1
    filter_upwards [hA₁] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg p.1]
  have hwf : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * p.1⁻¹) P := by
    apply Integrable.of_bound (measurable_fst.pow_const 2 |>.mul measurable_fst.inv).aestronglyMeasurable 1
    filter_upwards [hA₁] with p hp
    change ‖p.1 ^ 2 * p.1⁻¹‖ ≤ 1
    have he : p.1 ^ 2 * p.1⁻¹ = p.1 := by field_simp [hp.1.ne']
    rw [he, Real.norm_eq_abs, abs_of_pos hp.1]
    exact hp.2
  have hwg : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * g p.1) P := by
    apply Integrable.of_bound ((measurable_fst.pow_const 2).mul (hgm.measurable.comp measurable_fst)).aestronglyMeasurable 1
    filter_upwards [hA₁] with p hp
    change ‖p.1 ^ 2 * g p.1‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hg0 hp.1))]
    nlinarith [sq_nonneg p.1, hg1 hp.1]
  have hwfg : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * (p.1⁻¹ * g p.1)) P := by
    apply Integrable.of_bound
      ((measurable_fst.pow_const 2).mul (measurable_fst.inv.mul (hgm.measurable.comp measurable_fst))).aestronglyMeasurable 1
    filter_upwards [hA₁] with p hp
    change ‖p.1 ^ 2 * (p.1⁻¹ * g p.1)‖ ≤ 1
    have he : p.1 ^ 2 * (p.1⁻¹ * g p.1) = p.1 * g p.1 := by field_simp [hp.1.ne']
    rw [he, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp.1.le (hg0 hp.1))]
    nlinarith [hg1 hp.1]
  have hgi : AntitoneOn g (Set.Ioi 0) := by
    intro a ha b hb hab
    change 0 < a at ha
    change 0 < b at hb
    apply integral_mono_ae (hKi hb) (hKi ha)
    filter_upwards [hS] with s hs
    have hd : 0 < 1 + a * s := by nlinarith
    have hle : 1 + a * s ≤ 1 + b * s := by nlinarith
    have hi := one_div_le_one_div_of_le hd hle
    exact pow_le_pow_left₀ (inv_nonneg.mpr (by linarith)) (by simpa only [one_div] using hi) 2
  have hfi : AntitoneOn (fun a : ℝ => a⁻¹) (Set.Ioi 0) := by
    intro a ha b hb hab
    simpa only [one_div] using one_div_le_one_div_of_le ha hab
  have hcov := weighted_covariance_antitone (P := P) (Z := fun p : ℝ × ℝ => p.1)
    (w := fun p => p.1 ^ 2) (f := fun a => a⁻¹) (g := g) (Set.Ioi 0)
    (hA₁.mono fun p hp => hp.1) (Filter.Eventually.of_forall fun p => sq_nonneg p.1) hw hfi hgi
    hwf hwg (by simpa only [mul_assoc] using hwfg)
  have hQ : (∫ p : ℝ × ℝ, p.1 ^ 2 * g p.1 ∂P) =
      ∫ p : ℝ × ℝ, p.1 ^ 2 * binaryKernel p.1 p.2 ∂P := by
    have hInt : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * binaryKernel p.1 p.2) P := by
      apply Integrable.of_bound
        ((measurable_fst.pow_const 2).mul hKm).aestronglyMeasurable 1
      filter_upwards [hA₁, hS₂] with p hp hs
      change |p.1 ^ 2 * binaryKernel p.1 p.2| ≤ 1
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hK_nonneg _ _))]
      nlinarith [sq_nonneg p.1, hK_le_one hp.1 hs]
    calc
      _ = ∫ a, a ^ 2 * g a ∂νA := by
        simpa using (integral_fun_fst (μ := νA) (ν := νS) (fun a => a ^ 2 * g a))
      _ = ∫ a, ∫ s, a ^ 2 * binaryKernel a s ∂νS ∂νA := by
        apply integral_congr_ae
        filter_upwards with a
        rw [integral_const_mul]
      _ = _ := by
        exact (integral_prod (fun p : ℝ × ℝ => p.1 ^ 2 * binaryKernel p.1 p.2) hInt).symm
  have hQA : (∫ p : ℝ × ℝ, p.1 ^ 2 * (p.1⁻¹ * g p.1) ∂P) =
      ∫ p : ℝ × ℝ, p.1 * binaryKernel p.1 p.2 ∂P := by
    have hInt : Integrable (fun p : ℝ × ℝ => p.1 * binaryKernel p.1 p.2) P := by
      apply Integrable.of_bound (measurable_fst.mul hKm).aestronglyMeasurable 1
      filter_upwards [hA₁, hS₂] with p hp hs
      change |p.1 * binaryKernel p.1 p.2| ≤ 1
      rw [abs_of_nonneg (mul_nonneg hp.1.le (hK_nonneg _ _))]
      nlinarith [hK_le_one hp.1 hs]
    calc
      _ = ∫ p : ℝ × ℝ, p.1 * g p.1 ∂P := by
        apply integral_congr_ae
        filter_upwards [hA₁] with p hp
        field_simp [hp.1.ne']
      _ = ∫ a, a * g a ∂νA := by
        simpa using (integral_fun_fst (μ := νA) (ν := νS) (fun a => a * g a))
      _ = ∫ a, ∫ s, a * binaryKernel a s ∂νS ∂νA := by
        apply integral_congr_ae
        filter_upwards with a
        rw [integral_const_mul]
      _ = _ := by
        exact (integral_prod (fun p : ℝ × ℝ => p.1 * binaryKernel p.1 p.2) hInt).symm
  rw [hQ, hQA] at hcov
  have hw_eq : (∫ p : ℝ × ℝ, p.1 ^ 2 ∂P) = ∫ a, a ^ 2 ∂νA := by
    simpa using (integral_fun_fst (μ := νA) (ν := νS) (fun a => a ^ 2))
  have hwf_eq : (∫ p : ℝ × ℝ, p.1 ^ 2 * p.1⁻¹ ∂P) = ∫ a, a ∂νA := by
    calc
      _ = ∫ p : ℝ × ℝ, p.1 ∂P := by
        apply integral_congr_ae
        filter_upwards [hA₁] with p hp
        field_simp [hp.1.ne']
      _ = _ := by simpa using (integral_fun_fst (μ := νA) (ν := νS) (fun a => a))
  rw [hw_eq, hwf_eq] at hcov
  exact hcov

private noncomputable def binaryA (l : ℝ) (T : Tree) : ℝ := 1 - Yt l T
private noncomputable def binaryS (l : ℝ) {n : ℕ} (ts : Fin n → Tree) : ℝ :=
  (∑ j, escape l (ts j)) / (l - 1)
private noncomputable def binaryX (l : ℝ) (T : Tree) : ℝ := 1 - Wt l T

private lemma measurable_binaryA (l : ℝ) : Measurable (binaryA l) :=
  measurable_const.sub (measurable_Yt l)

private lemma measurable_binaryS (l : ℝ) {n : ℕ} : Measurable (binaryS l (n := n)) :=
  (Finset.univ.measurable_sum fun j _ => (measurable_escape l).comp (measurable_pi_apply j)).div
    measurable_const

private lemma ae_binaryA (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : ∀ᵐ T ∂GW μ, 0 < binaryA l T ∧ binaryA l T < 1 := by
  filter_upwards [ae_escape_pos h (by positivity) hlm] with T hT
  have hy := Yt_mem hl hT
  have hl1 : (1 : ℝ) / l < 1 := (div_lt_one (by positivity)).2 hl
  exact ⟨by dsimp [binaryA]; linarith, by dsimp [binaryA]; linarith [hy.1]⟩

private lemma binary_node_factor (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    {n : ℕ} (i : Fin (n + 1)) (ts : Fin (n + 1) → Tree) :
    binaryX l (nodeFin (n + 1) ts) =
      binaryA l (ts i) / (1 + binaryA l (ts i) * binaryS l (i.removeNth ts)) := by
  have ha : 0 < l - 1 := by linarith
  have hsum : childSum l (nodeFin (n + 1) ts) =
      escape l (ts i) + ∑ j : Fin n, escape l (ts (i.succAbove j)) := by
    unfold childSum
    rw [degree_nodeFin]
    calc
      (∑ j : Fin (n + 1), escape l (child (nodeFin (n + 1) ts) (j.val + 1))) =
          ∑ j : Fin (n + 1), escape l (ts j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [children_nodeFin]
      _ = _ := Fin.sum_univ_succAbove (fun j => escape l (ts j)) i
  have hb : 0 ≤ escape l (ts i) := (escape_mem_Icc (by positivity) _).1
  have hR : 0 ≤ ∑ j : Fin n, escape l (ts (i.succAbove j)) :=
    Finset.sum_nonneg fun j _ => (escape_mem_Icc (by positivity) _).1
  have hden1 : 0 < l - 1 + escape l (ts i) := by positivity
  have hden2 : 0 < l - 1 + (escape l (ts i) +
      ∑ j : Fin n, escape l (ts (i.succAbove j))) := by positivity
  have hA : binaryA l (ts i) = (l - 1) / (l - 1 + escape l (ts i)) := by
    unfold binaryA Yt
    field_simp [hden1.ne']
    ring
  have hX : binaryX l (nodeFin (n + 1) ts) =
      (l - 1) / (l - 1 + (escape l (ts i) + ∑ j : Fin n, escape l (ts (i.succAbove j)))) := by
    unfold binaryX Wt
    rw [hsum]
    field_simp [hden2.ne']
    ring
  rw [hA, hX]
  unfold binaryS
  simp only [Fin.removeNth]
  field_simp [ha.ne', hden1.ne', hden2.ne']
  ring

private lemma integral_pi_succAbove (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (i : Fin (n + 1)) (F : Tree → (Fin n → Tree) → ℝ) :
    ∫ ts, F (ts i) (i.removeNth ts) ∂Measure.pi (fun _ : Fin (n + 1) => GW μ) =
      ∫ p, F p.1 p.2 ∂(GW μ).prod (Measure.pi fun _ : Fin n => GW μ) := by
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => GW μ) i
  have hi := hp.integral_comp' (fun p : Tree × (Fin n → Tree) => F p.1 p.2)
  have he (ts : Fin (n + 1) → Tree) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Tree) i) ts =
      (ts i, i.removeNth ts) := rfl
  simp_rw [he] at hi
  exact hi

private lemma binary_ratio_at_node (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (i : Fin (n + 1)) :
    (∫ T, binaryA l T ∂GW μ) * (∫ ts, binaryX l (nodeFin (n + 1) ts) ^ 2
        ∂Measure.pi (fun _ : Fin (n + 1) => GW μ)) ≤
      (∫ T, binaryA l T ^ 2 ∂GW μ) *
        ∫ ts, binaryX l (nodeFin (n + 1) ts) ^ 2 / binaryA l (ts i)
          ∂Measure.pi (fun _ : Fin (n + 1) => GW μ) := by
  let νA : Measure ℝ := (GW μ).map (binaryA l)
  let νS : Measure ℝ := (Measure.pi (fun _ : Fin n => GW μ)).map (binaryS l)
  have hA : ∀ᵐ a ∂νA, 0 < a ∧ a ≤ 1 := by
    have hm : ∀ᵐ a ∂νA, a ∈ Set.Ioo (0 : ℝ) 1 := by
      dsimp [νA]
      exact (ae_map_iff (measurable_binaryA l).aemeasurable measurableSet_Ioo).2
        (ae_binaryA h hl hlm)
    exact hm.mono fun a ha => ⟨ha.1, ha.2.le⟩
  have hS : ∀ᵐ s ∂νS, 0 ≤ s := by
    dsimp [νS]
    apply (ae_map_iff (measurable_binaryS l).aemeasurable measurableSet_Ici).2
    filter_upwards with ts
    exact div_nonneg (Finset.sum_nonneg fun j _ => (escape_mem_Icc (by positivity) _).1)
      (by linarith)
  have hr := tilted_moment_ratio hA hS
  have hc : (∫ a, a ∂νA) = ∫ T, binaryA l T ∂GW μ := by
    exact integral_map (measurable_binaryA l).aemeasurable measurable_id.aestronglyMeasurable
  have hB : (∫ a, a ^ 2 ∂νA) = ∫ T, binaryA l T ^ 2 ∂GW μ := by
    exact integral_map (measurable_binaryA l).aemeasurable (measurable_id.pow_const 2).aestronglyMeasurable
  rw [hc, hB] at hr
  have hQ : (∫ p : ℝ × ℝ, p.1 ^ 2 * binaryKernel p.1 p.2 ∂νA.prod νS) =
      ∫ ts, binaryX l (nodeFin (n + 1) ts) ^ 2 ∂Measure.pi (fun _ : Fin (n + 1) => GW μ) := by
    dsimp [νA, νS]
    rw [Measure.map_prod_map (GW μ) (Measure.pi (fun _ : Fin n => GW μ))
      (measurable_binaryA l) (measurable_binaryS l)]
    unfold binaryKernel
    have hmap := integral_map (μ := (GW μ).prod (Measure.pi (fun _ : Fin n => GW μ)))
      (φ := Prod.map (binaryA l) (binaryS l))
      (f := fun p : ℝ × ℝ => p.1 ^ 2 * (1 + p.1 * p.2)⁻¹ ^ 2)
      ((measurable_binaryA l).prodMap (measurable_binaryS l)).aemeasurable
      (((measurable_fst.pow_const 2).mul
        ((measurable_const.add (measurable_fst.mul measurable_snd)).inv.pow_const 2))).aestronglyMeasurable
    rw [hmap]
    calc
      _ = ∫ ts, binaryA l (ts i) ^ 2 *
          binaryKernel (binaryA l (ts i)) (binaryS l (i.removeNth ts))
          ∂Measure.pi (fun _ : Fin (n + 1) => GW μ) :=
        (integral_pi_succAbove μ i (fun a s => (binaryA l a) ^ 2 *
          binaryKernel (binaryA l a) (binaryS l s))).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ts
        rw [binary_node_factor h hl i ts]
        have hpos : 0 < binaryA l (ts i) := by
          have ha : 0 < l - 1 := by linarith
          have hb := (escape_mem_Icc (by positivity : 0 < l) (ts i)).1
          dsimp [binaryA, Yt]
          have hd : 0 < l - 1 + escape l (ts i) := by positivity
          exact sub_pos.mpr ((div_lt_one hd).2 (by linarith))
        have hden : 1 + binaryA l (ts i) * binaryS l (i.removeNth ts) ≠ 0 := by
          have hs : 0 ≤ binaryS l (i.removeNth ts) :=
            div_nonneg (Finset.sum_nonneg fun j _ => (escape_mem_Icc (by positivity) _).1)
              (by linarith)
          positivity
        dsimp [binaryKernel]
        field_simp [hden]
  have hQA : (∫ p : ℝ × ℝ, p.1 * binaryKernel p.1 p.2 ∂νA.prod νS) =
      ∫ ts, binaryX l (nodeFin (n + 1) ts) ^ 2 / binaryA l (ts i)
        ∂Measure.pi (fun _ : Fin (n + 1) => GW μ) := by
    dsimp [νA, νS]
    rw [Measure.map_prod_map (GW μ) (Measure.pi (fun _ : Fin n => GW μ))
      (measurable_binaryA l) (measurable_binaryS l)]
    unfold binaryKernel
    have hmap := integral_map (μ := (GW μ).prod (Measure.pi (fun _ : Fin n => GW μ)))
      (φ := Prod.map (binaryA l) (binaryS l))
      (f := fun p : ℝ × ℝ => p.1 * (1 + p.1 * p.2)⁻¹ ^ 2)
      ((measurable_binaryA l).prodMap (measurable_binaryS l)).aemeasurable
      ((measurable_fst.mul
        ((measurable_const.add (measurable_fst.mul measurable_snd)).inv.pow_const 2))).aestronglyMeasurable
    rw [hmap]
    calc
      _ = ∫ ts, binaryA l (ts i) *
          binaryKernel (binaryA l (ts i)) (binaryS l (i.removeNth ts))
          ∂Measure.pi (fun _ : Fin (n + 1) => GW μ) :=
        (integral_pi_succAbove μ i (fun a s => (binaryA l a) *
          binaryKernel (binaryA l a) (binaryS l s))).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ts
        rw [binary_node_factor h hl i ts]
        have ha : 0 < binaryA l (ts i) := by
          have ha' : 0 < l - 1 := by linarith
          have hb := (escape_mem_Icc (by positivity : 0 < l) (ts i)).1
          dsimp [binaryA, Yt]
          have hd : 0 < l - 1 + escape l (ts i) := by positivity
          exact sub_pos.mpr ((div_lt_one hd).2 (by linarith))
        have hden : 1 + binaryA l (ts i) * binaryS l (i.removeNth ts) ≠ 0 := by
          have hs : 0 ≤ binaryS l (i.removeNth ts) :=
            div_nonneg (Finset.sum_nonneg fun j _ => (escape_mem_Icc (by positivity) _).1)
              (by linarith)
          positivity
        dsimp [binaryKernel]
        field_simp [ha.ne', hden]
  rw [hQ, hQA] at hr
  exact hr

private lemma ae_escape_pi (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (k : ℕ) : ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => GW μ),
      ∀ i, 0 < escape l (ts i) := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (μ := fun _ : Fin k => GW μ) i).quasiMeasurePreserving.ae
    (ae_escape_pos h (by positivity) hlm)

private lemma binaryX_node_mem {l : ℝ} (hl : 1 < l) {k : ℕ} (ts : Fin k → Tree) :
    0 < binaryX l (nodeFin k ts) ∧ binaryX l (nodeFin k ts) ≤ 1 := by
  have ha : 0 < l - 1 := by linarith
  have hsum : 0 ≤ childSum l (nodeFin k ts) :=
    Finset.sum_nonneg fun i _ => (escape_mem_Icc (by positivity) _).1
  have hden : 0 < l - 1 + childSum l (nodeFin k ts) := by positivity
  unfold binaryX Wt
  constructor
  · exact sub_pos.mpr ((div_lt_one hden).2 (by linarith))
  · nlinarith [div_nonneg hsum hden.le]

private lemma binaryX_le_binaryA (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    {n : ℕ} (i : Fin (n + 1)) (ts : Fin (n + 1) → Tree) (hpos : ∀ j, 0 < escape l (ts j)) :
    binaryX l (nodeFin (n + 1) ts) ≤ binaryA l (ts i) := by
  rw [binary_node_factor h hl i ts]
  have ha : 0 < binaryA l (ts i) := by
    have hy := Yt_mem hl (hpos i)
    have hl1 : (1 : ℝ) / l < 1 := (div_lt_one (by positivity)).2 hl
    dsimp [binaryA]
    linarith
  have hs : 0 ≤ binaryS l (i.removeNth ts) :=
    div_nonneg (Finset.sum_nonneg fun j _ => (escape_mem_Icc (by positivity) _).1) (by linarith)
  have hden : 0 < 1 + binaryA l (ts i) * binaryS l (i.removeNth ts) := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith [mul_nonneg ha.le (mul_nonneg ha.le hs)]

private lemma integrable_binaryX_node {l : ℝ} (hl : 1 < l) {k : ℕ} (r : ℕ) :
    Integrable (fun ts => binaryX l (nodeFin k ts) ^ r)
      (Measure.pi (fun _ : Fin k => GW μ)) := by
  apply Integrable.of_bound
    (((measurable_const.sub (measurable_Wt l)).comp (measurable_nodeFin k)).pow_const r).aestronglyMeasurable 1
  filter_upwards with ts
  have hm := binaryX_node_mem hl ts
  change |binaryX l (nodeFin k ts) ^ r| ≤ 1
  rw [abs_of_nonneg (pow_nonneg hm.1.le _)]
  exact pow_le_one₀ hm.1.le hm.2

private lemma integrable_binary_ratio_node (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (i : Fin (n + 1)) :
    Integrable (fun ts => binaryX l (nodeFin (n + 1) ts) ^ 2 / binaryA l (ts i))
      (Measure.pi (fun _ : Fin (n + 1) => GW μ)) := by
  apply Integrable.of_bound
    ((((measurable_const.sub (measurable_Wt l)).comp (measurable_nodeFin (n + 1))).pow_const 2).div
      ((measurable_binaryA l).comp (measurable_pi_apply i))).aestronglyMeasurable 1
  filter_upwards [ae_escape_pi h hl hlm (n + 1)] with ts hts
  have hy := Yt_mem hl (hts i)
  have hl1 : (1 : ℝ) / l < 1 := (div_lt_one (by positivity)).2 hl
  have ha : 0 < binaryA l (ts i) := by dsimp [binaryA]; linarith
  have hx := binaryX_node_mem hl ts
  have hxa := binaryX_le_binaryA h hl i ts hts
  have hnonneg : 0 ≤ binaryX l (nodeFin (n + 1) ts) ^ 2 / binaryA l (ts i) :=
    div_nonneg (sq_nonneg _) ha.le
  have hle : binaryX l (nodeFin (n + 1) ts) ^ 2 / binaryA l (ts i) ≤ 1 := by
    calc
      _ ≤ binaryX l (nodeFin (n + 1) ts) := by
        apply (div_le_iff₀ ha).2
        nlinarith [sq_nonneg (binaryX l (nodeFin (n + 1) ts))]
      _ ≤ 1 := hx.2
  change |binaryX l (nodeFin (n + 1) ts) ^ 2 / binaryA l (ts i)| ≤ 1
  rw [abs_of_nonneg hnonneg]
  exact hle

private lemma binary_two_children_at_node (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) :
    (∫ ts, binaryX l (nodeFin (n + 1) ts) ^ 2 / binaryA l (ts i)
        ∂Measure.pi (fun _ : Fin (n + 1) => GW μ)) +
      (∫ ts, binaryX l (nodeFin (n + 1) ts) ^ 2 / binaryA l (ts j)
        ∂Measure.pi (fun _ : Fin (n + 1) => GW μ)) ≤
    (∫ ts, binaryX l (nodeFin (n + 1) ts) ∂Measure.pi (fun _ : Fin (n + 1) => GW μ)) +
      ∫ ts, binaryX l (nodeFin (n + 1) ts) ^ 2 ∂Measure.pi (fun _ : Fin (n + 1) => GW μ) := by
  rw [← integral_add (integrable_binary_ratio_node h hl hlm i) (integrable_binary_ratio_node h hl hlm j)]
  have hadd : (∫ ts, binaryX l (nodeFin (n + 1) ts) ∂Measure.pi (fun _ : Fin (n + 1) => GW μ)) +
      (∫ ts, binaryX l (nodeFin (n + 1) ts) ^ 2 ∂Measure.pi (fun _ : Fin (n + 1) => GW μ)) =
      ∫ ts, binaryX l (nodeFin (n + 1) ts) ^ 1 + binaryX l (nodeFin (n + 1) ts) ^ 2
        ∂Measure.pi (fun _ : Fin (n + 1) => GW μ) := by
    rw [integral_add (integrable_binaryX_node hl 1) (integrable_binaryX_node hl 2)]
    simp
  rw [hadd]
  apply integral_mono_ae ((integrable_binary_ratio_node h hl hlm i).add
    (integrable_binary_ratio_node h hl hlm j))
    ((integrable_binaryX_node hl 1).add (integrable_binaryX_node hl 2))
  filter_upwards with ts
  have ha : 0 < l - 1 := by linarith
  have hsum : childSum l (nodeFin (n + 1) ts) = ∑ r, escape l (ts r) := by
    unfold childSum
    rw [degree_nodeFin]
    apply Finset.sum_congr rfl
    intro r _
    rw [children_nodeFin]
  have hb (r : Fin (n + 1)) : 0 ≤ escape l (ts r) := (escape_mem_Icc (by positivity) _).1
  have hbij : escape l (ts i) + escape l (ts j) ≤ ∑ r, escape l (ts r) := by
    calc
      _ = ∑ r ∈ ({i, j} : Finset (Fin (n + 1))), escape l (ts r) := by simp [hij]
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro r _ _
        exact hb r
  have hS : 0 ≤ ∑ r, escape l (ts r) := Finset.sum_nonneg fun r _ => hb r
  have hden : 0 < l - 1 + ∑ r, escape l (ts r) := add_pos_of_pos_of_nonneg ha hS
  have hdi : 0 < l - 1 + escape l (ts i) := add_pos_of_pos_of_nonneg ha (hb i)
  have hdj : 0 < l - 1 + escape l (ts j) := add_pos_of_pos_of_nonneg ha (hb j)
  change binaryX l (nodeFin (n + 1) ts) ^ 2 / binaryA l (ts i) +
    binaryX l (nodeFin (n + 1) ts) ^ 2 / binaryA l (ts j) ≤
      binaryX l (nodeFin (n + 1) ts) ^ 1 + binaryX l (nodeFin (n + 1) ts) ^ 2
  have hX : binaryX l (nodeFin (n + 1) ts) =
      (l - 1) / (l - 1 + ∑ r, escape l (ts r)) := by
    unfold binaryX Wt
    rw [hsum]
    field_simp [hden.ne']
    ring
  have hAi : binaryA l (ts i) = (l - 1) / (l - 1 + escape l (ts i)) := by
    unfold binaryA Yt
    field_simp [hdi.ne']
    ring
  have hAj : binaryA l (ts j) = (l - 1) / (l - 1 + escape l (ts j)) := by
    unfold binaryA Yt
    field_simp [hdj.ne']
    ring
  rw [hX, hAi, hAj]
  field_simp [ha.ne', hden.ne', hdi.ne', hdj.ne']
  nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hbij)]

private lemma summable_splitWeight_joint (h : OffspringHyp μ) :
    Summable fun k : ℕ => (splitWeightProv μ k).toReal := by
  letI := splitLaw_prob h
  let ν : Measure ℕ := (splitLaw μ).map degree
  have hu : (⋃ k : ℕ, ({k} : Set ℕ)) = Set.univ := by ext k; simp
  have htop : (∑' k : ℕ, ν {k}) ≠ ∞ := by
    rw [← measure_iUnion]
    · rw [hu]
      exact measure_ne_top _ _
    · intro i j hij
      exact Set.disjoint_left.mpr fun x hi hj => hij (hi.symm.trans hj)
    · exact fun k => measurableSet_singleton k
  have hmass : Summable fun k : ℕ => (ν {k}).toReal := ENNReal.summable_toReal htop
  apply hmass.congr
  intro k
  congr 1
  dsimp [ν]
  rw [splitLaw_map_degree h]
  by_cases hk : 2 ≤ k
  · simp [Measure.smul_apply, Measure.restrict_apply, splitWeightProv, hk, div_eq_mul_inv,
      mul_comm]
  · have he : ({k} : Set ℕ) ∩ Set.Ici 2 = ∅ := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_Ici, Set.mem_empty_iff_false,
        iff_false]
      intro hr
      omega
    simp [Measure.smul_apply, Measure.restrict_apply, splitWeightProv, hk, he]

/-- **Lemma 5.3** (`lem:scaled-binary`). Comparison with two children. -/
theorem scaled_binary (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    etaD μ l * (1 - momY μ l 2) ≤ 1 - 2 * muY μ l + momY μ l 2 := by
  letI := splitLaw_prob h
  let c := ∫ T, binaryA l T ∂GW μ
  let B := ∫ T, binaryA l T ^ 2 ∂GW μ
  let q : ℕ → ℝ := fun k => ∫ ts, binaryX l (nodeFin k ts) ^ 2
    ∂Measure.pi (fun _ : Fin k => GW μ)
  let d : ℕ → ℝ := fun k => ∫ ts, binaryX l (nodeFin k ts)
    ∂Measure.pi (fun _ : Fin k => GW μ)
  let R : ℕ → ℝ := fun k => (splitWeightProv μ k).toReal * (2 * c * q k)
  let Z : ℕ → ℝ := fun k => (splitWeightProv μ k).toReal * (B * (d k + q k))
  have hq0 (k : ℕ) : 0 ≤ q k := by
    apply integral_nonneg_of_ae
    filter_upwards with ts
    exact sq_nonneg _
  have hd0 (k : ℕ) : 0 ≤ d k := by
    apply integral_nonneg_of_ae
    filter_upwards with ts
    exact (binaryX_node_mem hl ts).1.le
  have hq1 (k : ℕ) : q k ≤ 1 := by
    calc
      q k ≤ ∫ _ts, (1 : ℝ) ∂Measure.pi (fun _ : Fin k => GW μ) := by
        apply integral_mono_ae (integrable_binaryX_node hl 2) (integrable_const 1)
        filter_upwards with ts
        exact pow_le_one₀ (binaryX_node_mem hl ts).1.le (binaryX_node_mem hl ts).2
      _ = 1 := by simp
  have hd1 (k : ℕ) : d k ≤ 1 := by
    dsimp [d]
    calc
      d k ≤ ∫ _ts, (1 : ℝ) ∂Measure.pi (fun _ : Fin k => GW μ) := by
        change (∫ ts, binaryX l (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ)) ≤ _
        apply integral_mono_ae (by simpa only [pow_one] using
          (integrable_binaryX_node (μ := μ) hl (k := k) 1)) (integrable_const 1)
        filter_upwards with ts
        simpa only [pow_one] using (binaryX_node_mem hl ts).2
      _ = 1 := by simp
  have hws := summable_splitWeight_joint h
  have hqs : Summable fun k : ℕ => (splitWeightProv μ k).toReal * q k := by
    apply hws.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (hq0 k))]
    simpa using mul_le_mul_of_nonneg_left (hq1 k) (ENNReal.toReal_nonneg :
      0 ≤ (splitWeightProv μ k).toReal)
  have hds : Summable fun k : ℕ => (splitWeightProv μ k).toReal * d k := by
    apply hws.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (hd0 k))]
    simpa using mul_le_mul_of_nonneg_left (hd1 k) (ENNReal.toReal_nonneg :
      0 ≤ (splitWeightProv μ k).toReal)
  have hB0 : 0 ≤ B := by
    apply integral_nonneg_of_ae
    filter_upwards with T
    exact sq_nonneg _
  have hterm (k : ℕ) : R k ≤ Z k := by
    by_cases hk : 2 ≤ k
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
      let i : Fin (n + 2) := ⟨0, by omega⟩
      let j : Fin (n + 2) := ⟨1, by omega⟩
      have hij : i ≠ j := by
        intro he
        have hv := congrArg Fin.val he
        simp [i, j] at hv
      have hri := binary_ratio_at_node h hl hlm (n := n + 1) i
      have hrj := binary_ratio_at_node h hl hlm (n := n + 1) j
      have htwo := binary_two_children_at_node h hl hlm i j hij
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      dsimp [R, Z, q, d, c, B]
      calc
        2 * (∫ T, binaryA l T ∂GW μ) *
            (∫ ts, binaryX l (nodeFin (n + 2) ts) ^ 2 ∂Measure.pi (fun _ : Fin (n + 2) => GW μ)) =
            (∫ T, binaryA l T ∂GW μ) *
              (∫ ts, binaryX l (nodeFin (n + 2) ts) ^ 2 ∂Measure.pi (fun _ : Fin (n + 2) => GW μ)) +
            (∫ T, binaryA l T ∂GW μ) *
              (∫ ts, binaryX l (nodeFin (n + 2) ts) ^ 2 ∂Measure.pi (fun _ : Fin (n + 2) => GW μ)) := by ring
        _ ≤ _ := add_le_add hri hrj
        _ = (∫ T, binaryA l T ^ 2 ∂GW μ) *
            ((∫ ts, binaryX l (nodeFin (n + 2) ts) ^ 2 / binaryA l (ts i)
                ∂Measure.pi (fun _ : Fin (n + 2) => GW μ)) +
              ∫ ts, binaryX l (nodeFin (n + 2) ts) ^ 2 / binaryA l (ts j)
                ∂Measure.pi (fun _ : Fin (n + 2) => GW μ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left htwo hB0
    · have hwz : (splitWeightProv μ k).toReal = 0 := by simp [splitWeightProv, hk]
      simp [R, Z, hwz]
  have hRs : Summable R := by
    apply (hqs.mul_left (2 * c)).congr
    intro k
    dsimp [R]
    ring
  have hZs : Summable Z := by
    apply ((hds.add hqs).mul_left B).congr
    intro k
    dsimp [Z]
    ring
  have hsum := Summable.tsum_le_tsum hterm hRs hZs
  have hQint : Integrable (fun T => binaryX l T ^ 2) (splitLaw μ) := by
    apply Integrable.of_bound ((measurable_const.sub (measurable_Wt l)).pow_const 2).aestronglyMeasurable 1
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    have hd : 0 ≤ 1 - Wt l T := sub_nonneg.mpr hT.2.le
    have hd1 : 1 - Wt l T ≤ 1 := by linarith [hT.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ hd hd1
  have hDint : Integrable (binaryX l) (splitLaw μ) := by
    apply Integrable.of_bound (measurable_const.sub (measurable_Wt l)).aestronglyMeasurable 1
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    have hd : 0 ≤ 1 - Wt l T := sub_nonneg.mpr hT.2.le
    have hd1 : 1 - Wt l T ≤ 1 := by linarith [hT.1]
    change |1 - Wt l T| ≤ 1
    rw [abs_of_nonneg hd]
    exact hd1
  have hqroot : (∑' k : ℕ, (splitWeightProv μ k).toReal * q k) =
      ∫ T, binaryX l T ^ 2 ∂splitLaw μ := by
    dsimp [q]
    exact (integral_splitLaw_rootProv h hQint).symm
  have hdroot : (∑' k : ℕ, (splitWeightProv μ k).toReal * d k) =
      ∫ T, binaryX l T ∂splitLaw μ := by
    dsimp [d]
    exact (integral_splitLaw_rootProv h hDint).symm
  have hRval : (∑' k, R k) = 2 * c * ∫ T, binaryX l T ^ 2 ∂splitLaw μ := by
    calc
      _ = ∑' k, (2 * c) * ((splitWeightProv μ k).toReal * q k) := by
        apply tsum_congr
        intro k
        dsimp [R]
        ring
      _ = 2 * c * ∑' k, (splitWeightProv μ k).toReal * q k := by rw [tsum_mul_left]
      _ = _ := by rw [hqroot]
  have hDQ : (∑' k : ℕ, ((splitWeightProv μ k).toReal * d k +
      (splitWeightProv μ k).toReal * q k)) = (∫ T, binaryX l T ∂splitLaw μ) +
      ∫ T, binaryX l T ^ 2 ∂splitLaw μ := by
    rw [hds.tsum_add hqs, hdroot, hqroot]
  have hZval : (∑' k, Z k) = B * ((∫ T, binaryX l T ∂splitLaw μ) +
      ∫ T, binaryX l T ^ 2 ∂splitLaw μ) := by
    calc
      _ = ∑' k, B * ((splitWeightProv μ k).toReal * d k +
          (splitWeightProv μ k).toReal * q k) := by
        apply tsum_congr
        intro k
        dsimp [Z]
        ring
      _ = B * (∑' k, ((splitWeightProv μ k).toReal * d k +
          (splitWeightProv μ k).toReal * q k)) := by rw [tsum_mul_left]
      _ = _ := by rw [hDQ]
  rw [hRval, hZval] at hsum
  have hYint : Integrable (Yt l) (GW μ) := by
    apply Integrable.of_bound (measurable_Yt l).aestronglyMeasurable 1
    filter_upwards [ae_escape_pos h (by positivity) hlm] with T hT
    have hy := Yt_mem hl hT
    have hl1 : (1 : ℝ) / l < 1 := (div_lt_one (by positivity)).2 hl
    rw [Real.norm_eq_abs, abs_of_pos hy.1]
    linarith
  have hY2int : Integrable (fun T => Yt l T ^ 2) (GW μ) := by
    apply Integrable.of_bound ((measurable_Yt l).pow_const 2).aestronglyMeasurable 1
    filter_upwards [ae_escape_pos h (by positivity) hlm] with T hT
    have hy := Yt_mem hl hT
    have hl1 : (1 : ℝ) / l < 1 := (div_lt_one (by positivity)).2 hl
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (Yt l T)]
  have hc : c = 1 - muY μ l := by
    dsimp [c, binaryA, muY]
    rw [integral_sub (integrable_const 1) hYint]
    simp
  have hB : B = 1 - 2 * muY μ l + momY μ l 2 := by
    simp only [B, binaryA, show (fun T => (1 - Yt l T) ^ 2) =
      (fun T => (1 - 2 * Yt l T) + Yt l T ^ 2) by funext T; ring]
    rw [integral_add (f := fun T => 1 - 2 * Yt l T) (g := fun T => Yt l T ^ 2)
        ((integrable_const (1 : ℝ)).sub (hYint.const_mul 2)) hY2int,
      integral_sub (integrable_const (1 : ℝ)) (hYint.const_mul 2), integral_const_mul]
    simp [muY, momY]
  have hW : Integrable (Wt l) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow_joint h hl hlm 1
  have hD : (∫ T, binaryX l T ∂splitLaw μ) = dW μ l := by
    dsimp [binaryX, dW, wbar, etaW]
    simp only [pow_one]
    rw [integral_sub (integrable_const 1) hW]
    simp
  rw [hc, hB, hD] at hsum
  have hfinal : (∫ T, binaryX l T ^ 2 ∂splitLaw μ) * (1 - momY μ l 2) ≤
      (1 - 2 * muY μ l + momY μ l 2) * dW μ l := by
    nlinarith [hsum]
  have hdpos := dW_pos h hl hlm
  change (∫ T, (1 - Wt l T) ^ 2 ∂splitLaw μ) / dW μ l * (1 - momY μ l 2) ≤
    1 - 2 * muY μ l + momY μ l 2
  rw [div_mul_eq_mul_div, div_le_iff₀ hdpos]
  simpa only [binaryX] using hfinal

/-- The first transformed moment in moment-box coordinates (proof of Theorem 5.1). -/
theorem muY_eq_box (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    muY μ l = xS μ l / (1 + xS μ l) * (1 - dW μ l) := by
  have hm : muY μ l = momY μ l 1 := by simp [muY, momY]
  rw [hm, momY_eq h hl hlm]
  have hi : iota μ l 1 = (1 + xS μ l)⁻¹ := by
    simp [iota, Qgeo, add_comm]
  rw [hi]
  have hw : etaW μ l 1 = 1 - dW μ l := by
    simp [wbar, dW]
  rw [hw, div_eq_mul_inv]

/-- The second transformed moment in moment-box coordinates (proof of Theorem 5.1). -/
theorem momY2_eq_box (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    momY μ l 2 = xS μ l * iota μ l 2 * (1 - 2 * dW μ l + dW μ l * etaD μ l) := by
  rw [momY_eq h hl hlm, etaW_two_eq_box h hl hlm]

end LPPMonotonicityProof.Analytic
