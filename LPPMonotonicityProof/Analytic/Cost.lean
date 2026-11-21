module

public import LPPMonotonicityProof.Analytic.Cost.Bounds
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic.FunProp

/-! # Differentiating N and Z under the integral

This module differentiates `N` and `Z` under the expectation on `(0, m)`, as in the
proof of Proposition 2.6 (`prop:cost`), and shows that both derivatives are continuous.
The two-copy integrals use the fixed product Bienaymé law.  The partial derivatives of
the kernels come from `LPPMonotonicityProof.Analytic.Kernel`, and Proposition 2.5
(`prop:regularity`) controls the differentiated escapes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private noncomputable def pairDerivIntegrand (l : ℝ) (kl kb : ℝ → ℝ → ℝ → ℝ) (p : Tree × Tree) : ℝ :=
  kl l (escape l p.1) (escape l p.2) +
    kb l (escape l p.1) (escape l p.2) * deriv (fun t => escape t p.1) l +
    kb l (escape l p.2) (escape l p.1) * deriv (fun t => escape t p.2) l

/-- The integrated chain-rule expression for a symmetric two-copy kernel. -/
noncomputable def pairDeriv (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (kl kb : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ p : Tree × Tree, kl l (escape l p.1) (escape l p.2) +
    kb l (escape l p.1) (escape l p.2) * deriv (fun t => escape t p.1) l +
    kb l (escape l p.2) (escape l p.1) * deriv (fun t => escape t p.2) l ∂(GW μ).prod (GW μ)

private theorem ae_regTree_pair (h : OffspringHyp μ) :
    ∀ᵐ p : Tree × Tree ∂(GW μ).prod (GW μ), RegTree μ p.1 ∧ RegTree μ p.2 :=
  (Measure.quasiMeasurePreserving_fst.ae (ae_regTree h)).and
    (Measure.quasiMeasurePreserving_snd.ae (ae_regTree h))

private theorem hasDerivAt_escape_of_regTree {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    HasDerivAt (fun t => escape t T) (deriv (fun t => escape t T) l) l :=
  ((escape_contDiffOn hT).differentiableOn_one.differentiableAt
    (isOpen_Ioo.mem_nhds hl)).hasDerivAt

private theorem hasDerivAt_tree_F {T T' : Tree} (hT : RegTree μ T) (hT' : RegTree μ T')
    {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) (c : ℝ) :
    HasDerivAt
      (fun t => (escape t T * escape t T' - c * tau (escape t T) (escape t T')) /
        DfunProv t (escape t T) (escape t T'))
      (pairDerivIntegrand l
        (fun t x y => -(x * y - c * tau x y) / DfunProv t x y ^ 2)
        (fun t x y => Pol t c y / DfunProv t x y ^ 2) (T, T')) l := by
  have hx := hasDerivAt_escape_of_regTree hT hl
  have hy := hasDerivAt_escape_of_regTree hT' hl
  have hxy := hx.mul hy
  have hτ := (hx.add hy).sub hxy
  have hD := (((hasDerivAt_id l).sub_const 1).add hx).add hy |>.sub hxy
  have hp := ((hxy.sub (hτ.const_mul c)).div hD (DfunProv_pos_of_regTrees hT hT' hl).ne')
  refine hp.congr_deriv ?_
  simp only [pairDerivIntegrand, Pol, tau, DfunProv, id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  rw [show l - 1 + escape l T' + escape l T - escape l T' * escape l T =
    l - 1 + escape l T + escape l T' - escape l T * escape l T' by ring]
  ring

/-! The common integral argument is indexed by whether its numerator is `τ`. -/

private noncomputable def twoCopyKernel : Bool → ℝ → ℝ → ℝ → ℝ
  | false => fun l x y => x * y / DfunProv l x y
  | true => fun l x y => tau x y / DfunProv l x y

private noncomputable def biasPartial : Bool → ℝ → ℝ → ℝ → ℝ
  | false => kNl
  | true => kZl

private noncomputable def escapePartial : Bool → ℝ → ℝ → ℝ → ℝ
  | false => kNb
  | true => kZb

private theorem hasDerivAt_twoCopyKernel (z : Bool) {p : Tree × Tree}
    (hp : RegTree μ p.1 ∧ RegTree μ p.2) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    HasDerivAt (fun t => twoCopyKernel z t (escape t p.1) (escape t p.2))
      (pairDerivIntegrand l (biasPartial z) (escapePartial z) p) l := by
  obtain ⟨T, T'⟩ := p
  have h0 := hasDerivAt_tree_F hp.1 hp.2 hl 0
  cases z
  · simpa [twoCopyKernel, biasPartial, escapePartial, kNl, kNb, pairDerivIntegrand] using h0
  · have h1 := hasDerivAt_tree_F hp.1 hp.2 hl 1
    convert h0.sub h1 using 1
    · funext t
      simp only [twoCopyKernel, Pi.sub_apply, zero_mul, sub_zero, one_mul]
      ring
    · simp only [biasPartial, escapePartial, pairDerivIntegrand,
        kZl, kZb]
      ring

attribute [local fun_prop] measurable_escape

private theorem measurable_twoCopyKernel (z : Bool) (l : ℝ) :
    Measurable (fun p : Tree × Tree => twoCopyKernel z l (escape l p.1) (escape l p.2)) := by
  cases z <;> simp only [twoCopyKernel, tau, DfunProv] <;> fun_prop

private theorem integrable_twoCopyKernel (z : Bool) (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Integrable (fun p : Tree × Tree => twoCopyKernel z l (escape l p.1) (escape l p.2))
      ((GW μ).prod (GW μ)) := by
  let f : Tree × Tree → ℝ × ℝ := Prod.map (escape l) (escape l)
  have hf : Measurable f := (measurable_escape l).prodMap (measurable_escape l)
  have hmap : Measure.map f ((GW μ).prod (GW μ)) = (escLaw μ l).prod (escLaw μ l) :=
    (Measure.map_prod_map (GW μ) (GW μ) (measurable_escape l) (measurable_escape l)).symm
  have hi : Integrable (fun p : ℝ × ℝ => twoCopyKernel z l p.1 p.2)
      ((escLaw μ l).prod (escLaw μ l)) := by
    cases z
    · exact integrable_kernel_N μ h hl.1 hl.2
    · exact integrable_kernel_Z μ h hl.1 hl.2
  rw [← hmap] at hi
  exact hi.comp_measurable hf

private theorem measurable_partials (z : Bool) (l : ℝ) :
    Measurable (fun p : Tree × Tree => biasPartial z l (escape l p.1) (escape l p.2)) ∧
      Measurable (fun p : Tree × Tree => escapePartial z l (escape l p.1) (escape l p.2)) ∧
      Measurable (fun p : Tree × Tree => escapePartial z l (escape l p.2) (escape l p.1)) := by
  cases z <;> simp only [biasPartial, escapePartial, kNl, kNb, kZl, kZb, tau, Pol, DfunProv] <;>
    exact ⟨by fun_prop, by fun_prop, by fun_prop⟩

private theorem aestronglyMeasurable_pairDerivIntegrand (z : Bool) (h : OffspringHyp μ)
    {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    AEStronglyMeasurable (pairDerivIntegrand l (biasPartial z) (escapePartial z))
      ((GW μ).prod (GW μ)) := by
  have hd : AEMeasurable (fun T => deriv (fun t => escape t T) l) (GW μ) := by
    have heq : (fun T => (-l)⁻¹ * resp l T) = (fun T => deriv (fun t => escape t T) l) := by
      funext T
      rw [resp, ← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hl.1.ne'), one_mul]
    rw [← heq]
    exact (aemeasurable_resp_of_mem h hl).const_mul _
  obtain ⟨hlm, hbm, hbm'⟩ := measurable_partials z l
  exact (hlm.aestronglyMeasurable.add (hbm.aestronglyMeasurable.mul hd.aestronglyMeasurable.comp_fst)).add
    (hbm'.aestronglyMeasurable.mul hd.aestronglyMeasurable.comp_snd)

private theorem continuousOn_pairDerivIntegrand (z : Bool) {p : Tree × Tree}
    (hp : RegTree μ p.1 ∧ RegTree μ p.2) :
    ContinuousOn (fun l => pairDerivIntegrand l (biasPartial z) (escapePartial z) p)
      (Set.Ioo 0 (mean μ)) := by
  have hx := (escape_contDiffOn hp.1).continuousOn
  have hy := (escape_contDiffOn hp.2).continuousOn
  have hd₁ := (escape_contDiffOn hp.1).continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hd₂ := (escape_contDiffOn hp.2).continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hD (l : ℝ) (hl : l ∈ Set.Ioo 0 (mean μ)) :
      l - 1 + escape l p.1 + escape l p.2 - escape l p.1 * escape l p.2 ≠ 0 :=
    (DfunProv_pos_of_regTrees hp.1 hp.2 hl).ne'
  have hD' (l : ℝ) (hl : l ∈ Set.Ioo 0 (mean μ)) :
      l - 1 + escape l p.2 + escape l p.1 - escape l p.2 * escape l p.1 ≠ 0 :=
    (DfunProv_pos_of_regTrees hp.2 hp.1 hl).ne'
  have hpow (l : ℝ) (hl : l ∈ Set.Ioo 0 (mean μ)) := pow_ne_zero 2 (hD l hl)
  have hpow' (l : ℝ) (hl : l ∈ Set.Ioo 0 (mean μ)) := pow_ne_zero 2 (hD' l hl)
  cases z <;> simp only [pairDerivIntegrand, biasPartial, escapePartial,
    kNl, kNb, kZl, kZb, Pol, tau, DfunProv] <;>
    fun_prop (disch := first | exact hpow | exact hpow' | solve_by_elim)

private theorem exists_pairDeriv_bound (z : Bool) (h : OffspringHyp μ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ)
    (hregime : b * invMean μ < 1 ∨ 1 < a) :
    ∃ M : Tree × Tree → ℝ, Integrable M ((GW μ).prod (GW μ)) ∧
      ∀ᵐ p ∂(GW μ).prod (GW μ), ∀ l ∈ Set.Icc a b,
        ‖pairDerivIntegrand l (biasPartial z) (escapePartial z) p‖ ≤ M p := by
  let C := ((min (1 : ℝ) a)^2)⁻¹
  let K := fun T => (envelope a b T).toReal
  have hK : Integrable K (GW μ) :=
    integrable_toReal_of_lintegral_ne_top (measurable_envelope a b).aemeasurable
      (lintegral_envelope_lt_top h ha hab hb).ne
  suffices ∃ B : Tree × Tree → ℝ, Integrable B ((GW μ).prod (GW μ)) ∧
      ∀ p : Tree × Tree, RegTree μ p.1 → RegTree μ p.2 → ∀ l ∈ Set.Icc a b,
        |biasPartial z l (escape l p.1) (escape l p.2)| ≤ B p by
    obtain ⟨B, hB, hle⟩ := this
    refine ⟨fun p => B p + C * K p.1 + C * K p.2,
      (hB.add ((hK.comp_fst (GW μ)).const_mul C)).add ((hK.comp_snd (GW μ)).const_mul C), ?_⟩
    filter_upwards [ae_regTree_pair h] with p hp l hl
    have h₁ := escape_terms_le_envelope hp.1 hp.2 ha hab hb hl
    have h₂ := escape_terms_le_envelope hp.2 hp.1 ha hab hb hl
    have h₁' : |escapePartial z l (escape l p.1) (escape l p.2) *
        deriv (fun t => escape t p.1) l| ≤ C * K p.1 := by
      cases z
      · exact h₁.1
      · exact h₁.2
    have h₂' : |escapePartial z l (escape l p.2) (escape l p.1) *
        deriv (fun t => escape t p.2) l| ≤ C * K p.2 := by
      cases z
      · exact h₂.1
      · exact h₂.2
    rw [Real.norm_eq_abs, pairDerivIntegrand]
    refine (abs_add_le _ _).trans (add_le_add ?_ h₂')
    exact (abs_add_le _ _).trans (add_le_add (hle p hp.1 hp.2 l hl) h₁')
  rcases hregime with hA | hB
  · have hi := (integrable_inv_escape h (ha.trans_le hab) hA).2.comp_fst (GW μ)
    refine ⟨fun p => 2 / ((min 1 a)^2 * escape b p.1), ?_, ?_⟩
    · convert hi.const_mul (2 * C) using 1
      funext p
      simp only [C, div_eq_mul_inv, mul_inv_rev]
      ring
    · intro p hp hp' l hl
      have hle := explicit_terms_le_inv_escape hp hp' ha hb hl
      cases z
      · exact hle.1
      · exact hle.2
  · refine ⟨fun _ => 2 / (a - 1)^2, integrable_const _, ?_⟩
    intro p hp hp' l hl
    have hl' : l ∈ Set.Ioo 0 (mean μ) := ⟨ha.trans_le hl.1, hl.2.trans_lt hb⟩
    have hle := explicit_partials_le_const hB hl.1
      (escape_mem_Ioc_of_regTree hp hl') (escape_mem_Ioc_of_regTree hp' hl')
    cases z
    · exact hle.1
    · exact hle.2

private theorem hasDerivAt_integral_twoCopyKernel (z : Bool) (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    HasDerivAt (fun t => pairE μ t (twoCopyKernel z t))
      (pairDeriv μ l (biasPartial z) (escapePartial z)) l := by
  obtain ⟨a, b, ha, hal, hlb, hb, hr⟩ := regime_cover h hl
  obtain ⟨M, hM, hbound⟩ := exists_pairDeriv_bound z h ha (hal.trans hlb).le hb hr
  have hdiff : ∀ᵐ p : Tree × Tree ∂(GW μ).prod (GW μ), ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun t => twoCopyKernel z t (escape t p.1) (escape t p.2))
        (pairDerivIntegrand t (biasPartial z) (escapePartial z) p) t := by
    filter_upwards [ae_regTree_pair h] with p hp t ht
    exact hasDerivAt_twoCopyKernel z hp ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Icc_mem_nhds hal hlb)
    (Eventually.of_forall fun t => (measurable_twoCopyKernel z t).aestronglyMeasurable)
    (integrable_twoCopyKernel z h hl) (aestronglyMeasurable_pairDerivIntegrand z h hl)
    hbound hM hdiff).2

private theorem continuousOn_pairDeriv_twoCopyKernel (z : Bool) (h : OffspringHyp μ) :
    ContinuousOn (fun l => pairDeriv μ l (biasPartial z) (escapePartial z))
      (Set.Ioo 0 (mean μ)) := by
  intro l hl
  obtain ⟨a, b, ha, hal, hlb, hb, hr⟩ := regime_cover h hl
  obtain ⟨M, hM, hbound⟩ := exists_pairDeriv_bound z h ha (hal.trans hlb).le hb hr
  have hsub : Set.Icc a b ⊆ Set.Ioo 0 (mean μ) :=
    fun _ ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hc : ContinuousOn (fun t => pairDeriv μ t (biasPartial z) (escapePartial z))
      (Set.Icc a b) :=
    continuousOn_of_dominated
      (fun _ ht => aestronglyMeasurable_pairDerivIntegrand z h (hsub ht))
      (fun _ ht => hbound.mono fun _ hp => hp _ ht) hM
      ((ae_regTree_pair h).mono fun _ hp => (continuousOn_pairDerivIntegrand z hp).mono hsub)
  exact ((hc l ⟨hal.le, hlb.le⟩).continuousAt (Icc_mem_nhds hal hlb)).continuousWithinAt

/-- Differentiate the numerator `Speed.Nval` on the transient interval. -/
theorem hasDerivAt_Nval (h : OffspringHyp μ) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    HasDerivAt (Nval μ) (pairDeriv μ l kNl kNb) l := by
  have heq : Nval μ = fun t => pairE μ t (twoCopyKernel false t) := by
    funext t
    exact Nval_eq_pairE t
  rw [heq]
  exact hasDerivAt_integral_twoCopyKernel false h hl

/-- Differentiate the denominator `Speed.Zval` on the transient interval. -/
theorem hasDerivAt_Zval (h : OffspringHyp μ) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    HasDerivAt (Zval μ) (pairDeriv μ l kZl kZb) l := by
  have heq : Zval μ = fun t => pairE μ t (twoCopyKernel true t) := by
    funext t
    exact Zval_eq_pairE t
  rw [heq]
  exact hasDerivAt_integral_twoCopyKernel true h hl

/-- The numerator derivative is continuous throughout `(0, m)`. -/
theorem continuousOn_pairDeriv_N (h : OffspringHyp μ) :
    ContinuousOn (fun l => pairDeriv μ l kNl kNb) (Set.Ioo 0 (mean μ)) :=
  continuousOn_pairDeriv_twoCopyKernel false h

/-- The denominator derivative is continuous throughout `(0, m)`. -/
theorem continuousOn_pairDeriv_Z (h : OffspringHyp μ) :
    ContinuousOn (fun l => pairDeriv μ l kZl kZb) (Set.Ioo 0 (mean μ)) :=
  continuousOn_pairDeriv_twoCopyKernel true h

end LPPMonotonicityProof.Analytic
