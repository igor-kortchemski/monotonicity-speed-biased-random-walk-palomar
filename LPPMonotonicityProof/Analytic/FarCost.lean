module

public import LPPMonotonicityProof.Analytic.Cost
public import LPPMonotonicityProof.Speed.Close.Export
import Mathlib.Tactic.FunProp

/-! # The derivative cost identity (2.3) (`eq:far-cost`) of Proposition 2.6 -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

local notation "ρ" => Measure.prod (GW μ) (GW μ)

private theorem ae_regular_pair (h : OffspringHyp μ) :
    ∀ᵐ p : Tree × Tree ∂ρ, RegTree μ p.1 ∧ RegTree μ p.2 :=
  (Measure.quasiMeasurePreserving_fst.ae (ae_regTree h)).and
    (Measure.quasiMeasurePreserving_snd.ae (ae_regTree h))

private theorem integrable_bias_partials (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Integrable (fun p : Tree × Tree => kNl l (escape l p.1) (escape l p.2)) ρ ∧
      Integrable (fun p : Tree × Tree => kZl l (escape l p.1) (escape l p.2)) ρ := by
  obtain ⟨a, b, ha, hal, hlb, hb, hregime⟩ := regime_cover h hl
  have hab := hal.le.trans hlb.le
  have hI : l ∈ Set.Icc a b := ⟨hal.le, hlb.le⟩
  have hm (k : ℝ → ℝ → ℝ → ℝ) (hk : Measurable (fun p : ℝ × ℝ => k l p.1 p.2)) :
      AEStronglyMeasurable (fun p : Tree × Tree => k l (escape l p.1) (escape l p.2)) ρ :=
    (hk.comp ((measurable_escape l).prodMap (measurable_escape l))).aestronglyMeasurable
  have hN := hm kNl (by unfold kNl DfunProv; fun_prop)
  have hZ := hm kZl (by unfold kZl tau DfunProv; fun_prop)
  rcases hregime with hA | hB
  · have hi := ((integrable_inv_escape h (ha.trans_le hab) hA).2.comp_fst (GW μ)).const_mul
      (2 / (min 1 a)^2)
    have hi' : Integrable (fun p : Tree × Tree => 2 / ((min 1 a)^2 * escape b p.1)) ρ := by
      convert hi using 1
      funext p
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    constructor
    · apply hi'.mono' hN
      filter_upwards [ae_regular_pair h] with p hp
      simpa only [Real.norm_eq_abs] using (explicit_terms_le_inv_escape hp.1 hp.2 ha hb hI).1
    · apply hi'.mono' hZ
      filter_upwards [ae_regular_pair h] with p hp
      simpa only [Real.norm_eq_abs] using (explicit_terms_le_inv_escape hp.1 hp.2 ha hb hI).2
  · have hi : Integrable (fun _ : Tree × Tree => 2 / (a - 1)^2) ρ := integrable_const _
    constructor
    · apply hi.mono' hN
      filter_upwards [ae_regular_pair h] with p hp
      simpa only [Real.norm_eq_abs] using (explicit_partials_le_const hB hal.le
        (escape_mem_Ioc_of_regTree hp.1 hl) (escape_mem_Ioc_of_regTree hp.2 hl)).1
    · apply hi.mono' hZ
      filter_upwards [ae_regular_pair h] with p hp
      simpa only [Real.norm_eq_abs] using (explicit_partials_le_const hB hal.le
        (escape_mem_Ioc_of_regTree hp.1 hl) (escape_mem_Ioc_of_regTree hp.2 hl)).2

private theorem integrable_escape_partials (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Integrable (fun p : Tree × Tree => kNb l (escape l p.1) (escape l p.2) *
      deriv (fun t => escape t p.1) l) ρ ∧
    Integrable (fun p : Tree × Tree => kZb l (escape l p.1) (escape l p.2) *
      deriv (fun t => escape t p.1) l) ρ := by
  have hd : AEMeasurable (fun T => deriv (fun t => escape t T) l) (GW μ) := by
    convert (aemeasurable_resp_of_mem h hl).const_mul (-l)⁻¹ using 1
    funext T
    change _ = (-l)⁻¹ * (-l * _)
    rw [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hl.1.ne'), one_mul]
  have hd' := hd.aestronglyMeasurable.comp_fst (ν := GW μ)
  have hm (k : ℝ → ℝ → ℝ → ℝ) (hk : Measurable (fun p : ℝ × ℝ => k l p.1 p.2)) :
      AEStronglyMeasurable (fun p : Tree × Tree => k l (escape l p.1) (escape l p.2) *
        deriv (fun t => escape t p.1) l) ρ :=
    (hk.comp ((measurable_escape l).prodMap (measurable_escape l))).aestronglyMeasurable.mul hd'
  have hK := integrable_toReal_of_lintegral_ne_top (measurable_envelope l l).aemeasurable
    (lintegral_envelope_lt_top h hl.1 le_rfl hl.2).ne
  have hi := (hK.comp_fst (GW μ)).const_mul (((min 1 l)^2)⁻¹)
  constructor
  · apply hi.mono' (hm kNb (by unfold kNb Pol DfunProv; fun_prop))
    filter_upwards [ae_regular_pair h] with p hp
    simpa only [Real.norm_eq_abs] using
      (escape_terms_le_envelope hp.1 hp.2 hl.1 le_rfl hl.2 ⟨le_rfl, le_rfl⟩).1
  · apply hi.mono' (hm kZb (by unfold kZb Pol DfunProv; fun_prop))
    filter_upwards [ae_regular_pair h] with p hp
    simpa only [Real.norm_eq_abs] using
      (escape_terms_le_envelope hp.1 hp.2 hl.1 le_rfl hl.2 ⟨le_rfl, le_rfl⟩).2

private theorem bias_partial_sub (l c x y : ℝ) :
    kNl l x y - c * kZl l x y = -((x * y - c * tau x y) / DfunProv l x y ^ 2) := by
  simp only [kNl, kZl, div_eq_mul_inv]
  ring

private theorem escape_partial_sub (l c x y : ℝ) :
    kNb l x y - c * kZb l x y = Pol l c y / DfunProv l x y ^ 2 := by
  simp only [kNb, kZb, Pol, div_eq_mul_inv]
  ring

/-- Integrability of the two-copy kernel defining Hval. -/
theorem integrable_Hval_kernel (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Integrable (fun p : Tree × Tree => (escape l p.1 * escape l p.2 -
      speedValueProv μ l * tau (escape l p.1) (escape l p.2)) /
      DfunProv l (escape l p.1) (escape l p.2) ^ 2) ρ := by
  obtain ⟨hN, hZ⟩ := integrable_bias_partials h hl
  let c := speedValueProv μ l
  have hi : Integrable (fun p : Tree × Tree =>
      -(kNl l (escape l p.1) (escape l p.2) - c * kZl l (escape l p.1) (escape l p.2))) ρ :=
    (hN.sub (hZ.const_mul c)).neg
  simpa only [bias_partial_sub, neg_neg] using hi

private theorem integrable_Gam_deriv_kernel (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Integrable (fun p : Tree × Tree => Pol l (speedValueProv μ l) (escape l p.2) /
      DfunProv l (escape l p.1) (escape l p.2) ^ 2 * deriv (fun t => escape t p.1) l) ρ := by
  obtain ⟨hN, hZ⟩ := integrable_escape_partials h hl
  convert hN.sub (hZ.const_mul (speedValueProv μ l)) using 1
  funext p
  rw [← escape_partial_sub, sub_mul, mul_assoc]
  rfl

/-- Fubini with an outer weight on the first escape kernel. -/
theorem integral_Gam_weight {l : ℝ} (w : Tree → ℝ)
    (hw : Integrable (fun p : Tree × Tree => w p.1 * (Pol l (speedValueProv μ l) (escape l p.2) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2)) ρ) :
    (∫ p : Tree × Tree, w p.1 * (Pol l (speedValueProv μ l) (escape l p.2) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2) ∂ρ) =
      ∫ T, w T * Gam μ l (escape l T) ∂GW μ := by
  rw [integral_prod _ hw]
  simp only [integral_const_mul, Gam]

private theorem integrable_Gam_resp_kernel (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Integrable (fun p : Tree × Tree => resp l p.1 * (Pol l (speedValueProv μ l) (escape l p.2) /
      DfunProv l (escape l p.1) (escape l p.2) ^ 2)) ρ := by
  convert (integrable_Gam_deriv_kernel h hl).const_mul (-l) using 1
  funext p
  unfold resp
  ring

/-- The response-weighted one-copy expectation is integrable. -/
theorem integrable_resp_Gam (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Integrable (fun T => resp l T * Gam μ l (escape l T)) (GW μ) := by
  have hi := (integrable_Gam_resp_kernel h hl).integral_prod_left
  simpa only [integral_const_mul, Gam] using hi

/-- Quotient rule for the speed of the actual walk. -/
theorem hasDerivAt_speedValue (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    HasDerivAt (speedValue μ)
      ((pairDeriv μ l kNl kNb * Zval μ l - Nval μ l * pairDeriv μ l kZl kZb) /
        Zval μ l ^ 2) l := by
  have hZ := (Speed.Zval_pos μ hl.1 h hl.2).ne'
  exact ((hasDerivAt_Nval h hl).div (hasDerivAt_Zval h hl) hZ).congr_of_eventuallyEq
    (speedValue_eventuallyEq (μ := μ) hl.1)

private theorem pairDeriv_sub_speed (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    pairDeriv μ l kNl kNb - speedValueProv μ l * pairDeriv μ l kZl kZb =
      -Hval μ l + 2 * ∫ p : Tree × Tree, Pol l (speedValueProv μ l) (escape l p.2) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 * deriv (fun t => escape t p.1) l ∂ρ := by
  let c := speedValueProv μ l
  let A : Tree × Tree → ℝ := fun p => (escape l p.1 * escape l p.2 -
    c * tau (escape l p.1) (escape l p.2)) / DfunProv l (escape l p.1) (escape l p.2) ^ 2
  let B : Tree × Tree → ℝ := fun p => Pol l c (escape l p.2) /
    DfunProv l (escape l p.1) (escape l p.2) ^ 2 * deriv (fun t => escape t p.1) l
  let q (kl kb : ℝ → ℝ → ℝ → ℝ) (p : Tree × Tree) :=
    kl l (escape l p.1) (escape l p.2) +
      kb l (escape l p.1) (escape l p.2) * deriv (fun t => escape t p.1) l +
      kb l (escape l p.2) (escape l p.1) * deriv (fun t => escape t p.2) l
  obtain ⟨hNl, hZl⟩ := integrable_bias_partials h hl
  obtain ⟨hNb, hZb⟩ := integrable_escape_partials h hl
  have hN : Integrable (q kNl kNb) ρ := (hNl.add hNb).add hNb.swap
  have hZ : Integrable (q kZl kZb) ρ := (hZl.add hZb).add hZb.swap
  have hA : Integrable A ρ := integrable_Hval_kernel h hl
  have hB : Integrable B ρ := integrable_Gam_deriv_kernel h hl
  change (∫ p, q kNl kNb p ∂ρ) - c * (∫ p, q kZl kZb p ∂ρ) =
    -(∫ p, A p ∂ρ) + 2 * (∫ p, B p ∂ρ)
  rw [← integral_const_mul, ← integral_sub hN (hZ.const_mul c)]
  calc
    _ = ∫ p, -A p + B p + B p.swap ∂ρ := by
      congr 1
      funext p
      dsimp only [q, A, B, Prod.fst_swap, Prod.snd_swap]
      rw [← bias_partial_sub, ← escape_partial_sub, ← escape_partial_sub]
      ring
    _ = _ := by
      have hneg : Integrable (fun p => -A p) ρ := hA.neg
      have hsum : Integrable (fun p => -A p + B p) ρ := hneg.add hB
      have hswap : Integrable (fun p => B p.swap) ρ := hB.swap
      rw [integral_add hsum hswap, integral_add hneg hB, integral_neg, integral_prod_swap B]
      ring

/-- The far-cost identity on the open transient interval. -/
theorem cost_eq (h : OffspringHyp μ) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    cost μ l = l * Hval μ l + 2 * ∫ T, resp l T * Gam μ l (escape l T) ∂GW μ := by
  have hZ := (Speed.Zval_pos μ hl.1 h hl.2).ne'
  have hv : speedValueProv μ l = Nval μ l / Zval μ l := by
    rw [speedValueProv_eq, ite_eq_right hl.1.ne']
  have hd := (hasDerivAt_speedValue h hl).deriv
  change deriv (speedValueProv μ) l = _ at hd
  have hcost : cost μ l = -l *
      (pairDeriv μ l kNl kNb - speedValueProv μ l * pairDeriv μ l kZl kZb) := by
    unfold cost
    rw [hd, hv]
    change -l * Zval μ l * _ = _
    field_simp
  rw [hcost, pairDeriv_sub_speed h hl, ← integral_Gam_weight (resp l)
    (integrable_Gam_resp_kernel h hl)]
  have hresp : (∫ p : Tree × Tree, resp l p.1 * (Pol l (speedValueProv μ l) (escape l p.2) /
      DfunProv l (escape l p.1) (escape l p.2) ^ 2) ∂ρ) =
      -l * ∫ p : Tree × Tree, Pol l (speedValueProv μ l) (escape l p.2) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 * deriv (fun t => escape t p.1) l ∂ρ := by
    rw [← integral_const_mul]
    congr 1
    funext p
    unfold resp
    ring
  rw [hresp]
  ring

end LPPMonotonicityProof.Analytic
