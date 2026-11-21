module

public import LPPMonotonicityProof.Analytic.FirstSplit2
public import LPPMonotonicityProof.Analytic.LowWindowScalar
public import LPPMonotonicityProof.Analytic.Regularity.Inverse
public import LPPMonotonicityProof.Analytic.Regularity.InverseMoment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal-escape estimates near bias one

This module contains the first two reciprocal-escape estimates of the proof of
Theorem 4.3 (`thm:low-window`): `A ≥ 3/8` and `M ≤ 1/A`.
`lowWindow_reciprocal_M_le` takes the two conclusions of Lemma 2.4
(`lem:inverse-moment`) as explicit hypotheses; `lowWindow_reciprocal_M_le'`
discharges them with `Regularity/InverseMoment.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private lemma p1_nonneg : 0 ≤ p1 μ := ENNReal.toReal_nonneg

private lemma sS_pos (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) : 0 < sS μ l :=
  div_pos (sub_pos.mpr hl) (pBr_pos h)

private lemma one_sub_pBr (h : OffspringHyp μ) : p1 μ = 1 - pBr μ := by
  linarith [p1_add_pBr h]

/-- **`A ≥ 3/8`.**  The low-window denominator is at least `3/8`. -/
theorem lowWindow_reciprocal_A_lower (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    let p := pBr μ
    let q := p1 μ
    let e := eJ μ
    let s := sS μ l
    let A := 1 - e - s * (q + p * e)
    3 / 8 ≤ A := by
  intro p q e s A
  have hp : 0 < p := pBr_pos h
  have hq : q = 1 - p := one_sub_pBr h
  have hp1 : p ≤ 1 := by
    have hq0 : 0 ≤ q := p1_nonneg
    linarith [p1_add_pBr h]
  have hs0 : 0 < s := sS_pos h hl
  have hA := lowWindow_A_bounds ⟨hp, hp1⟩ (eJ_mem h) ⟨hs0, hs⟩
  dsimp only at hA
  change 3 / 8 ≤ 1 - e - s * (q + p * e)
  rw [hq]
  exact hA.1

private lemma lowWindow_invMean_identity (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) :
    let p := pBr μ
    let q := p1 μ
    let e := eJ μ
    let s := sS μ l
    let A := 1 - e - s * (q + p * e)
    1 - l * invMean μ = p * A := by
  intro p q e s A
  have hp : 0 < p := pBr_pos h
  have hq : q = 1 - p := one_sub_pBr h
  have hU : invMean μ = q + p * e := invMean_eq_p1_add h
  rw [hU]
  dsimp only [A]
  rw [hq]
  dsimp only [s, p, sS]
  have hp' : pBr μ ≠ 0 := (pBr_pos h).ne'
  field_simp [hp']
  ring

/-- **`M ≤ 1/A`.**  Lemma 2.4 (`lem:inverse-moment`) gives `M ≤ 1/A` after the scalar
identity `1 - l * invMean μ = p * A`. -/
theorem lowWindow_reciprocal_M_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8)
    (hR2le : ∫⁻ T, (ENNReal.ofReal (escape l T))⁻¹ ∂GW μ ≤
      ENNReal.ofReal (1 - l * invMean μ)⁻¹)
    (hR2int : (∀ᵐ T ∂GW μ, 0 < escape l T) ∧
      Integrable (fun T => (escape l T)⁻¹) (GW μ)) :
    let p := pBr μ
    let q := p1 μ
    let e := eJ μ
    let s := sS μ l
    let A := 1 - e - s * (q + p * e)
    let M := ∫ T, p / escape l T ∂GW μ
    M ≤ 1 / A := by
  intro p q e s A M
  have hp : 0 < p := pBr_pos h
  have hAlower : 3 / 8 ≤ A := lowWindow_reciprocal_A_lower h hl hlm hs
  have hA : 0 < A := by linarith
  have hX : 1 - l * invMean μ = p * A := lowWindow_invMean_identity h hl
  have hXpos : 0 < 1 - l * invMean μ := by rw [hX]; exact mul_pos hp hA
  let I : ℝ := ∫ T, (escape l T)⁻¹ ∂GW μ
  have hI0 : 0 ≤ I := by
    apply integral_nonneg_of_ae
    filter_upwards [hR2int.1] with T hT
    exact inv_nonneg.mpr hT.le
  have hle : ENNReal.ofReal I ≤ ENNReal.ofReal ((1 - l * invMean μ)⁻¹) := by
    dsimp only [I]
    calc
      ENNReal.ofReal I = ∫⁻ T, ENNReal.ofReal ((escape l T)⁻¹) ∂GW μ :=
        ofReal_integral_eq_lintegral_ofReal hR2int.2
          (hR2int.1.mono fun T hT => inv_nonneg.mpr hT.le)
      _ = ∫⁻ T, (ENNReal.ofReal (escape l T))⁻¹ ∂GW μ := by
        apply lintegral_congr_ae
        filter_upwards [hR2int.1] with T hT
        rw [ENNReal.ofReal_inv_of_pos hT]
      _ ≤ ENNReal.ofReal (1 - l * invMean μ)⁻¹ := hR2le
  have hIle : I ≤ (1 - l * invMean μ)⁻¹ := by
    have hr := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).2 hle
    simpa only [ENNReal.toReal_ofReal hI0,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hXpos.le)] using hr
  have hM : M = p * I := by
    dsimp only [M, I]
    simp_rw [div_eq_mul_inv]
    rw [integral_const_mul]
  rw [hM]
  calc
    p * I ≤ p * (1 - l * invMean μ)⁻¹ := mul_le_mul_of_nonneg_left hIle hp.le
    _ = 1 / A := by
      rw [hX]
      field_simp [hp.ne', hA.ne']

/-- **`M ≤ 1/A`**, unconditional: Lemma 2.4 (`lintegral_inv_escape_le`,
`integrable_inv_escape` in `Regularity/InverseMoment.lean`) discharges the two
hypotheses of `lowWindow_reciprocal_M_le`; `l * invMean μ < 1` follows from
`1 - l * invMean μ = p * A` and `3/8 ≤ A`. -/
theorem lowWindow_reciprocal_M_le' (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    let p := pBr μ
    let q := p1 μ
    let e := eJ μ
    let s := sS μ l
    let A := 1 - e - s * (q + p * e)
    let M := ∫ T, p / escape l T ∂GW μ
    M ≤ 1 / A := by
  have hA : 3 / 8 ≤ 1 - eJ μ - sS μ l * (p1 μ + pBr μ * eJ μ) :=
    lowWindow_reciprocal_A_lower h hl hlm hs
  have hX : 1 - l * invMean μ = pBr μ * (1 - eJ μ - sS μ l * (p1 μ + pBr μ * eJ μ)) :=
    lowWindow_invMean_identity h hl
  have hU : l * invMean μ < 1 := by
    have hpos := mul_pos (pBr_pos h)
      (by linarith : (0 : ℝ) < 1 - eJ μ - sS μ l * (p1 μ + pBr μ * eJ μ))
    linarith
  have hl0 : (0 : ℝ) < l := by linarith
  exact lowWindow_reciprocal_M_le h hl hlm hs
    (lintegral_inv_escape_le h hl0 hU) (integrable_inv_escape h hl0 hU)

end LPPMonotonicityProof.Analytic
