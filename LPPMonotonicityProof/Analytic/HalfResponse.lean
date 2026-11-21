module

public import LPPMonotonicityProof.Analytic.FarCost
import Mathlib.Tactic.FunProp

/-! # The half-response identities (2.4) and (2.5) (`eq:half-response`, `eq:far-six`) -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

local notation "ρ" => Measure.prod (GW μ) (GW μ)

private theorem ae_regular_pair_half (h : OffspringHyp μ) :
    ∀ᵐ p : Tree × Tree ∂ρ, RegTree μ p.1 ∧ RegTree μ p.2 :=
  (Measure.quasiMeasurePreserving_fst.ae (ae_regTree h)).and
    (Measure.quasiMeasurePreserving_snd.ae (ae_regTree h))

omit [IsProbabilityMeasure μ] in
private theorem Dfun_lower_regular_pair {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ))
    {T T' : Tree} (hT : RegTree μ T) (hT' : RegTree μ T') :
    min 1 l * max (escape l T) (escape l T') ≤ DfunProv l (escape l T) (escape l T') :=
  (Dfun_bounds hl.1 (escape_mem_Ioc_of_regTree hT hl) (escape_mem_Ioc_of_regTree hT' hl)
    (fun hl1 => ⟨escape_ge hl.1 hl1 T (fun v hv => hT.1.1 v hv),
      escape_ge hl.1 hl1 T' (fun v hv => hT'.1.1 v hv)⟩)).1

/-- The reciprocal two-copy denominator is integrable in both domination regimes. -/
theorem integrable_inv_D (h : OffspringHyp μ) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Integrable (fun p : Tree × Tree => 1 / Dfun l (escape l p.1) (escape l p.2)) ρ := by
  change Integrable (fun p : Tree × Tree => 1 / DfunProv l (escape l p.1) (escape l p.2)) ρ
  have he := measurable_escape l
  have hm : Measurable (fun p : Tree × Tree => 1 / DfunProv l (escape l p.1) (escape l p.2)) := by
    unfold DfunProv
    fun_prop
  obtain ⟨a, b, _, hal, hlb, _, hregime⟩ := regime_cover h hl
  rcases hregime with hA | hB
  · have hU : l * invMean μ < 1 := (mul_le_mul_of_nonneg_right hlb.le
      ((div_nonneg zero_le_one (zero_lt_one.trans (one_lt_mean_of_hyp h)).le).trans
        (invMean_bounds h).1)).trans_lt hA
    have hi := ((integrable_inv_escape h hl.1 hU).2.comp_fst (GW μ)).const_mul (min 1 l)⁻¹
    apply hi.mono' hm.aestronglyMeasurable
    filter_upwards [ae_regular_pair_half h] with p hp
    have hx := (escape_mem_Ioc_of_regTree hp.1 hl).1
    have hs := lt_min zero_lt_one hl.1
    have hD := DfunProv_pos_of_regTrees hp.1 hp.2 hl
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    change 1 / _ ≤ (min 1 l)⁻¹ * (escape l p.1)⁻¹
    rw [← mul_inv, ← one_div]
    exact div_le_div_of_nonneg_left zero_le_one (mul_pos hs hx)
      ((mul_le_mul_of_nonneg_left (le_max_left _ _) hs.le).trans
        (Dfun_lower_regular_pair hl hp.1 hp.2))
  · have hl1 := hB.trans hal
    apply (integrable_const (1 / (l - 1))).mono' hm.aestronglyMeasurable
    filter_upwards [ae_regular_pair_half h] with p hp
    have hx := escape_mem_Ioc_of_regTree hp.1 hl
    have hy := escape_mem_Ioc_of_regTree hp.2 hl
    have hD := DfunProv_pos_of_regTrees hp.1 hp.2 hl
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_left zero_le_one (sub_pos.mpr hl1)
    have hτ := mul_nonneg (sub_nonneg.mpr hx.2) hy.1.le
    unfold DfunProv
    linarith [hx.1]

private theorem abs_Pol_le_D {l c x y : ℝ} (hl : 0 < l) (hc : c ∈ Set.Icc 0 1)
    (hy : y ∈ Set.Ioc 0 1) (hm : min 1 l * max x y ≤ DfunProv l x y)
    (ha : |l - 1| ≤ DfunProv l x y / min 1 l) :
    |Pol l c y| ≤ 4 * (DfunProv l x y / min 1 l) := by
  have hs := lt_min zero_lt_one hl
  have hyD : y ≤ DfunProv l x y / min 1 l := (le_div_iff₀ hs).2 (by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left (le_max_right _ _) hs.le).trans hm)
  have hy2 : y ^ 2 ≤ y := by nlinarith [mul_nonneg hy.1.le (sub_nonneg.mpr hy.2)]
  have hv : (1 + c) * y ≤ 2 :=
    (mul_le_mul_of_nonneg_left hy.2 (by linarith [hc.1])).trans (by linarith [hc.2])
  unfold Pol
  calc
    |y ^ 2 + (l - 1) * (1 + c) * y - (l - 1) * c| ≤
        |y ^ 2 + (l - 1) * (1 + c) * y| + |(l - 1) * c| := abs_sub _ _
    _ ≤ (|y ^ 2| + |(l - 1) * (1 + c) * y|) + |(l - 1) * c| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = y ^ 2 + |l - 1| * ((1 + c) * y) + |l - 1| * c := by
      rw [mul_assoc (l - 1), abs_mul (l - 1) ((1 + c) * y), abs_mul (l - 1) c,
        abs_of_nonneg (sq_nonneg y),
        abs_of_nonneg (mul_nonneg (by linarith [hc.1]) hy.1.le), abs_of_nonneg hc.1]
    _ ≤ 4 * (DfunProv l x y / min 1 l) := by
      have h₁ := mul_le_mul_of_nonneg_left hv (abs_nonneg (l - 1))
      have h₂ := mul_le_mul_of_nonneg_left hc.2 (abs_nonneg (l - 1))
      linarith

private theorem integrable_half_kernel (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Integrable (fun p : Tree × Tree => (1 - escape l p.1) *
      (Pol l (speedValueProv μ l) (escape l p.2) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2)) ρ := by
  let c := speedValueProv μ l
  let s := min 1 l
  have hs : 0 < s := lt_min zero_lt_one hl.1
  have hc : c ∈ Set.Icc 0 1 :=
    ⟨(speedValue_pos μ h l ⟨hl.1.le, hl.2⟩).le, (speedValue_lt_one μ h hl.1 hl.2).le⟩
  have he := measurable_escape l
  have hm : Measurable (fun p : Tree × Tree => (1 - escape l p.1) *
      (Pol l c (escape l p.2) / DfunProv l (escape l p.1) (escape l p.2) ^ 2)) := by
    unfold Pol DfunProv
    fun_prop
  apply ((integrable_inv_D h hl).const_mul (4 / s)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_regular_pair_half h] with p hp
  let x := escape l p.1
  let y := escape l p.2
  let D := DfunProv l x y
  have hx := escape_mem_Ioc_of_regTree hp.1 hl
  have hy := escape_mem_Ioc_of_regTree hp.2 hl
  have hlower : s * max x y ≤ D := Dfun_lower_regular_pair hl hp.1 hp.2
  have hD : 0 < D := DfunProv_pos_of_regTrees hp.1 hp.2 hl
  have ha : |l - 1| ≤ D / s := by
    rcases lt_or_ge l 1 with hl1 | hl1
    · rw [abs_of_neg (sub_neg.mpr hl1)]
      have hbase := escape_ge hl.1 hl1 p.1 (fun v hv => hp.1.1.1 v hv)
      apply (le_div_iff₀ hs).2
      rw [mul_comm]
      have hmax : -(l - 1) ≤ max x y := by
        simpa only [neg_sub] using hbase.trans (le_max_left x y)
      exact (mul_le_mul_of_nonneg_left hmax hs.le).trans hlower
    · have hτ := mul_nonneg (sub_nonneg.mpr hx.2) hy.1.le
      rw [abs_of_nonneg (sub_nonneg.mpr hl1)]
      have hs1 : s = 1 := min_eq_left hl1
      rw [hs1, div_one]
      change l - 1 ≤ l - 1 + x + y - x * y
      change 0 ≤ (1 - x) * y at hτ
      linarith [hx.1]
  change ‖(1 - x) * (Pol l c y / D ^ 2)‖ ≤ (4 / s) * (1 / D)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hx.2), abs_div,
    abs_of_nonneg (sq_nonneg D)]
  calc
    (1 - x) * (|Pol l c y| / D ^ 2) ≤ 1 * (|Pol l c y| / D ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith [hx.1]) (by positivity)
    _ ≤ 1 * ((4 * (D / s)) / D ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (abs_Pol_le_D hl.1 hc hy hlower ha) (sq_nonneg D)) zero_le_one
    _ = _ := by field_simp

private theorem Dfun_swap (l x y : ℝ) : DfunProv l y x = DfunProv l x y := by
  unfold DfunProv
  ring

private theorem integrable_K1_kernel (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Integrable (fun p : Tree × Tree => escape l p.1 /
      DfunProv l (escape l p.1) (escape l p.2)) ρ := by
  have he := measurable_escape l
  apply (integrable_inv_D h hl).mono'
  · apply Measurable.aestronglyMeasurable
    unfold DfunProv
    fun_prop
  · filter_upwards [ae_regular_pair_half h] with p hp
    have hx := escape_mem_Ioc_of_regTree hp.1 hl
    have hD := DfunProv_pos_of_regTrees hp.1 hp.2 hl
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx.1.le hD.le)]
    exact div_le_div_of_nonneg_right hx.2 hD.le

/-- The integrated half-response identity. -/
theorem half_response (h : OffspringHyp μ) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    l * Hval μ l + ∫ T, (1 - escape l T) * Gam μ l (escape l T) ∂GW μ =
      K1 μ l - speedValue μ l * K0 μ l := by
  let c := speedValueProv μ l
  let A : Tree × Tree → ℝ := fun p => (escape l p.1 * escape l p.2 -
    c * tau (escape l p.1) (escape l p.2)) / DfunProv l (escape l p.1) (escape l p.2) ^ 2
  let B : Tree × Tree → ℝ := fun p => (1 - escape l p.1) *
    (Pol l c (escape l p.2) / DfunProv l (escape l p.1) (escape l p.2) ^ 2)
  let C : Tree × Tree → ℝ := fun p => escape l p.1 / DfunProv l (escape l p.1) (escape l p.2)
  let E : Tree × Tree → ℝ := fun p => 1 / DfunProv l (escape l p.1) (escape l p.2)
  have hA : Integrable A ρ := integrable_Hval_kernel h hl
  have hB : Integrable B ρ := integrable_half_kernel h hl
  have hC : Integrable C ρ := integrable_K1_kernel h hl
  have hE : Integrable E ρ := integrable_inv_D h hl
  rw [← integral_Gam_weight (fun T => 1 - escape l T) hB]
  change l * (∫ p, A p ∂ρ) + (∫ p, B p ∂ρ) = (∫ p, C p ∂ρ) - c * (∫ p, E p ∂ρ)
  have hpoint : (fun p => l * A p + (1 / 2 : ℝ) * (B p + B p.swap)) =ᵐ[ρ]
      fun p => (1 / 2 : ℝ) * (C p + C p.swap) - c * E p := by
    filter_upwards [ae_regular_pair_half h] with p hp
    have hD := (DfunProv_pos_of_regTrees hp.1 hp.2 hl).ne'
    have hid := half_response_identity l c (escape l p.1) (escape l p.2)
    dsimp only [A, B, C, E, Prod.fst_swap, Prod.snd_swap]
    rw [Dfun_swap l (escape l p.1) (escape l p.2)]
    let x := escape l p.1
    let y := escape l p.2
    let D := DfunProv l x y
    calc
      _ = (l * (x * y - c * tau x y) +
        ((1 - x) * Pol l c y + (1 - y) * Pol l c x) / 2) / D ^ 2 := by
        simp only [div_eq_mul_inv]
        ring
      _ = D * ((x + y) / 2 - c) / D ^ 2 := by rw [hid]
      _ = _ := by
        field_simp [hD, show D ≠ 0 from hD]
        ring
  have hBswap : Integrable (fun p => B p.swap) ρ := hB.swap
  have hCswap : Integrable (fun p => C p.swap) ρ := hC.swap
  have hBsum : Integrable (fun p => B p + B p.swap) ρ := hB.add hBswap
  have hCsum : Integrable (fun p => C p + C p.swap) ρ := hC.add hCswap
  have hi := integral_congr_ae hpoint
  rw [integral_add (hA.const_mul l) (hBsum.const_mul (1 / 2 : ℝ)),
    integral_const_mul, integral_const_mul, integral_add hB hBswap, integral_prod_swap B,
    integral_sub (hCsum.const_mul (1 / 2 : ℝ)) (hE.const_mul c),
    integral_const_mul, integral_const_mul, integral_add hC hCswap, integral_prod_swap C] at hi
  linarith

private theorem two_mul_K1 (h : OffspringHyp μ) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    2 * K1 μ l = Nval μ l + Zval μ l := by
  let C : Tree × Tree → ℝ := fun p => escape l p.1 / DfunProv l (escape l p.1) (escape l p.2)
  let N : Tree × Tree → ℝ := fun p => escape l p.1 * escape l p.2 /
    DfunProv l (escape l p.1) (escape l p.2)
  let Z : Tree × Tree → ℝ := fun p => tau (escape l p.1) (escape l p.2) /
    DfunProv l (escape l p.1) (escape l p.2)
  have hC : Integrable C ρ := integrable_K1_kernel h hl
  have hmap := Measure.map_prod_map (GW μ) (GW μ) (measurable_escape l) (measurable_escape l)
  have hmeas := (measurable_escape l).prodMap (measurable_escape l)
  have hN : Integrable N ρ := by
    have hi := integrable_kernel_N μ h hl.1 hl.2
    change Integrable _ (((GW μ).map (escape l)).prod ((GW μ).map (escape l))) at hi
    rw [hmap] at hi
    exact hi.comp_measurable hmeas
  have hZ : Integrable Z ρ := by
    have hi := integrable_kernel_Z μ h hl.1 hl.2
    change Integrable _ (((GW μ).map (escape l)).prod ((GW μ).map (escape l))) at hi
    rw [hmap] at hi
    exact hi.comp_measurable hmeas
  have heq : (fun p => C p + C p.swap) =ᵐ[ρ] fun p => N p + Z p := by
    filter_upwards [ae_regular_pair_half h] with p hp
    dsimp only [C, N, Z, Prod.fst_swap, Prod.snd_swap]
    rw [Dfun_swap l (escape l p.1) (escape l p.2),
      ← add_div (escape l p.1 * escape l p.2) (tau (escape l p.1) (escape l p.2))]
    exact kernel_sum l _ _ (DfunProv_pos_of_regTrees hp.1 hp.2 hl).ne'
  have hCswap : Integrable (fun p => C p.swap) ρ := hC.swap
  have hi := integral_congr_ae heq
  rw [integral_add hC hCswap, integral_prod_swap C, integral_add hN hZ] at hi
  change 2 * K1 μ l = NvalProv μ l + ZvalProv μ l
  rw [Nval_eq_pairE, Zval_eq_pairE]
  change 2 * (∫ p, C p ∂ρ) = (∫ p, N p ∂ρ) + (∫ p, Z p ∂ρ)
  linarith

private theorem Zval_eq_K0 (h : OffspringHyp μ) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Zval μ l = 1 - (l - 1) * K0 μ l := by
  let E : Tree × Tree → ℝ := fun p => 1 / DfunProv l (escape l p.1) (escape l p.2)
  have hE : Integrable E ρ := integrable_inv_D h hl
  have heq : (fun p : Tree × Tree => tau (escape l p.1) (escape l p.2) /
      DfunProv l (escape l p.1) (escape l p.2)) =ᵐ[ρ] fun p => 1 - (l - 1) * E p := by
    filter_upwards [ae_regular_pair_half h] with p hp
    dsimp only [E]
    rw [mul_one_div]
    exact kernel_Z_eq l _ _ (DfunProv_pos_of_regTrees hp.1 hp.2 hl).ne'
  change ZvalProv μ l = _
  rw [Zval_eq_pairE, pairE, integral_congr_ae heq,
    integral_sub (integrable_const 1) (hE.const_mul (l - 1)), integral_const_mul]
  simp [K0, pairE, E]

/-- The half-response right side in terms of the reciprocal denominator. -/
theorem far_six (h : OffspringHyp μ) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    2 * (K1 μ l - speedValue μ l * K0 μ l) =
      1 + speedValue μ l - (l - 1 + (l + 1) * speedValue μ l) * K0 μ l := by
  have hZ := (Speed.Zval_pos μ hl.1 h hl.2).ne'
  have hv : Nval μ l = speedValue μ l * Zval μ l := by
    change Nval μ l = speedValueProv μ l * Zval μ l
    rw [speedValueProv_eq, ite_eq_right hl.1.ne', div_mul_cancel₀ _ hZ]
  calc
    _ = 2 * K1 μ l - 2 * speedValue μ l * K0 μ l := by ring
    _ = _ := by rw [two_mul_K1 h hl, hv, Zval_eq_K0 h hl]; ring

/-- The one-copy kernel has strictly positive expectation. -/
theorem K1_pos (h : OffspringHyp μ) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    0 < K1 μ l := by
  linarith [two_mul_K1 h hl, Speed.Nval_pos μ hl.1 h hl.2, Speed.Zval_pos μ hl.1 h hl.2]

end LPPMonotonicityProof.Analytic
