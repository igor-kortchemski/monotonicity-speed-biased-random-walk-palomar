module

public import LPPMonotonicity.Model.Defs
public import LPPMonotonicityProof.Escape.FiniteFlow
public import LPPMonotonicityProof.Speed.Interface.Subtrees

/-!
# Bias and one-based address conventions
-/

@[expose] public section

open scoped NNReal ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicityProof.RTL.LocallyFinite

private theorem coe_real_toNNReal (x : ℝ) (hx : 0 ≤ x) :
    ((x.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal x := by
  rw [← ENNReal.ofReal_coe_nnreal]
  exact congrArg ENNReal.ofReal (Real.coe_toNNReal x hx)

private theorem coe_div_real_toNNReal {l : ℝ} (hl : 0 < l)
    (a : ℝ) (ha : 0 < a) :
    ((l.toNNReal / a.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (l / a) := by
  have ha0 : a.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr ha)
  rw [ENNReal.coe_div ha0, coe_real_toNNReal l hl.le, coe_real_toNNReal a ha.le,
    ← ENNReal.ofReal_div_of_pos ha]

/-- Convert a public real bias and an offspring count to the RTL `ofReal` weight. -/
theorem coe_bias_div (l : ℝ) (hl : 0 < l) (k : ℕ) :
    ((l.toNNReal / (l.toNNReal + k) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (l / (l + k)) := by
  have hden : l.toNNReal + (k : ℝ≥0) = (l + (k : ℝ)).toNNReal := by
    rw [Real.toNNReal_add hl.le (Nat.cast_nonneg k)]
    simp
  rw [hden]
  exact coe_div_real_toNNReal hl _ (by positivity)

/-- Convert a unit child weight with a public real bias to the RTL `ofReal` weight. -/
theorem coe_one_div (l : ℝ) (hl : 0 < l) (k : ℕ) :
    ((1 / (l.toNNReal + k) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (1 / (l + k)) := by
  have hd : 0 < l + (k : ℝ) := by positivity
  have hden : l.toNNReal + (k : ℝ≥0) = (l + (k : ℝ)).toNNReal := by
    rw [Real.toNNReal_add hl.le (Nat.cast_nonneg k)]
    simp
  rw [hden]
  have hd0 : (l + (k : ℝ)).toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hd)
  rw [ENNReal.coe_div hd0, coe_real_toNNReal _ hd.le]
  simpa using (ENNReal.ofReal_div_of_pos (x := (1 : ℝ)) hd).symm

/-- The finite-flow and public-model child addresses use the same one-based index. -/
@[simp] theorem offChild_eq (ω : List ℕ → ℕ) (v : List ℕ) (i : Fin (ω v)) :
    offChild ω v i = v ++ [i.val + 1] := rfl

/-- Descending to a one-based child agrees with rerooting at the appended address. -/
theorem child_subtree_interface (T : Tree) (v : Address) (i : Fin (T.val v)) :
    child (subtree T v) (i.val + 1) = subtree T (v ++ [i.val + 1]) :=
  child_subtree T v (i.val + 1)

end LPPMonotonicityProof.Speed
