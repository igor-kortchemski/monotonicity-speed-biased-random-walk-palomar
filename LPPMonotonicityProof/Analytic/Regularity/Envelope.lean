module

public import LPPMonotonicityProof.Analytic.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Response envelopes

This module defines the sibling factors `sib`, their path maxima `pathMax` and the
response envelope `envelope` of the path expansion in the proof of Proposition 2.5
(`prop:regularity`). They agree definitionally with the copies `sibProv`,
`pathMaxProv` and `envelopeProv` used by `GoodTree0` and `RegTree` in `Defs.lean`.
`Real.toNNReal` makes `sib` a total function with values in `ℝ≥0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

/-- The sibling factor on an edge, using only the escapes of the other children. -/
noncomputable def sib (lPos : ℝ) (T : Tree) (i : Fin (degree T)) : ℝ≥0 :=
  Real.toNNReal (lPos / (lPos + ∑ j ∈ Finset.univ.erase i, escape lPos (child T (j + 1))))

/-- Maximum product of sibling factors along a path of the given length. -/
noncomputable def pathMax (lPos : ℝ) : ℕ → Tree → ℝ≥0
  | 0, _ => 1
  | k + 1, T => Finset.univ.sup fun i : Fin (degree T) =>
      sib lPos T i * pathMax lPos k (child T (i + 1))

/-- The integrable response envelope on a compact bias interval. -/
noncomputable def envelope (lNeg lPos : ℝ) (T : Tree) : ℝ≥0∞ :=
  (ENNReal.ofReal lNeg)⁻¹ * ∑' k, (pathMax lPos (k + 1) T : ℝ≥0∞)

/-- Agreement with the copy `sibProv` used by `RegTree`. -/
theorem sib_eq_prov (lPos : ℝ) (T : Tree) (i : Fin (degree T)) :
    sib lPos T i = sibProv lPos T i := rfl

/-- Agreement with the copy `pathMaxProv`. -/
theorem pathMax_eq_prov (lPos : ℝ) (k : ℕ) (T : Tree) :
    pathMax lPos k T = pathMaxProv lPos k T := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
      simp only [pathMax, pathMaxProv, sib_eq_prov, ih]

/-- Agreement with the copy `envelopeProv` used by `RegTree`. -/
theorem envelope_eq_prov (lNeg lPos : ℝ) (T : Tree) :
    envelope lNeg lPos T = envelopeProv lNeg lPos T := by
  simp only [envelope, envelopeProv, pathMax_eq_prov]

theorem coe_sib {lPos : ℝ} (hl : 0 < lPos) (T : Tree) (i : Fin (degree T)) :
    (sib lPos T i : ℝ) =
      lPos / (lPos + ∑ j ∈ Finset.univ.erase i, escape lPos (child T (j + 1))) := by
  apply Real.coe_toNNReal
  apply div_nonneg hl.le
  apply add_nonneg hl.le
  exact Finset.sum_nonneg fun j _ => (escape_mem_Icc hl _).1

theorem sib_le_one {lPos : ℝ} (hl : 0 < lPos) (T : Tree) (i : Fin (degree T)) :
    sib lPos T i ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_sib hl]
  apply (div_le_one (add_pos_of_pos_of_nonneg hl
    (Finset.sum_nonneg fun j _ => (escape_mem_Icc hl _).1))).2
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => (escape_mem_Icc hl _).1)

theorem pathMax_le_one {lPos : ℝ} (hl : 0 < lPos) :
    ∀ (k : ℕ) (T : Tree), pathMax lPos k T ≤ 1 := by
  intro k
  induction k with
  | zero => intro T; exact le_rfl
  | succ k ih =>
      intro T
      apply Finset.sup_le
      intro i _
      exact (mul_le_mul (sib_le_one hl T i) (ih _) zero_le zero_le).trans_eq (one_mul 1)

/-- The sibling factor is nondecreasing in the upper endpoint. -/
theorem sib_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (T : Tree) (i : Fin (degree T)) :
    sib a T i ≤ sib b T i := by
  have hb : 0 < b := ha.trans_le hab
  have hnonneg (c : ℝ) (hc : 0 < c) :
      0 ≤ ∑ j ∈ Finset.univ.erase i, escape c (child T (j + 1)) :=
    Finset.sum_nonneg fun j _ => (escape_mem_Icc hc _).1
  have hsum : (∑ j ∈ Finset.univ.erase i, escape b (child T (j + 1))) ≤
      ∑ j ∈ Finset.univ.erase i, escape a (child T (j + 1)) := by
    apply Finset.sum_le_sum
    intro j _
    exact escape_antitoneOn _ ha hb hab
  rw [← NNReal.coe_le_coe, coe_sib ha, coe_sib hb]
  apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg ha (hnonneg a ha))
    (add_pos_of_pos_of_nonneg hb (hnonneg b hb))).2
  have h₁ := mul_le_mul_of_nonneg_left hsum ha.le
  have h₂ := mul_le_mul_of_nonneg_right hab (hnonneg b hb)
  nlinarith

/-- `pathMax` is nondecreasing in the upper endpoint. -/
theorem pathMax_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∀ (k : ℕ) (T : Tree), pathMax a k T ≤ pathMax b k T := by
  have hb : 0 < b := ha.trans_le hab
  intro k
  induction k with
  | zero => intro T; exact le_rfl
  | succ k ih =>
      intro T
      apply Finset.sup_le
      intro i _
      exact (mul_le_mul (sib_mono ha hab T i) (ih _) zero_le zero_le).trans
        (Finset.le_sup (f := fun j : Fin (degree T) => sib b T j * pathMax b k (child T (j + 1)))
          (Finset.mem_univ i))

/-- Monotonicity of the envelope in its two interval endpoints. -/
theorem envelope_mono {lNeg lPos lNeg' lPos' : ℝ} (hlNeg' : 0 < lNeg')
    (hlPos : 0 < lPos) (hNeg : lNeg' ≤ lNeg) (hPos : lPos ≤ lPos') (T : Tree) :
    envelope lNeg lPos T ≤ envelope lNeg' lPos' T := by
  have hlNeg : 0 < lNeg := hlNeg'.trans_le hNeg
  have hlow : (ENNReal.ofReal lNeg)⁻¹ ≤ (ENNReal.ofReal lNeg')⁻¹ := by
    apply ENNReal.inv_le_inv.mpr
    exact ENNReal.ofReal_le_ofReal hNeg
  apply mul_le_mul hlow _ (bot_le) (bot_le)
  apply ENNReal.tsum_le_tsum
  intro k
  exact ENNReal.coe_le_coe.mpr (pathMax_mono hlPos hPos (k + 1) T)

end LPPMonotonicityProof.Analytic
