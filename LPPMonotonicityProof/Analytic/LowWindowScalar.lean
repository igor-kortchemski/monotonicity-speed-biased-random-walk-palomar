module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Scalar bounds on the low-bias window

Denominator bounds used by the explicit positivity estimate in the proof of
Theorem 4.3 (`thm:low-window`), which `Analytic/LowWindowScalar2.lean` proves.
-/

@[expose] public section

namespace LPPMonotonicityProof.Analytic

/-- The denominator `A = 1 - e - sU` of the proof of Theorem 4.3 is in `[3/8,1)`. -/
theorem lowWindow_A_bounds {p e s : ℝ}
    (hp : 0 < p ∧ p ≤ 1) (he : 0 < e ∧ e ≤ 1 / 2)
    (hs : 0 < s ∧ s ≤ 1 / 8) :
    let q := 1 - p
    let U := q + p * e
    let A := 1 - e - s * U
    3 / 8 ≤ A ∧ A < 1 := by
  dsimp only
  have hU0 : 0 ≤ 1 - p + p * e :=
    add_nonneg (sub_nonneg.mpr hp.2) (mul_nonneg hp.1.le he.1.le)
  have hUpos : 0 < 1 - p + p * e := by
    nlinarith [mul_pos hp.1 he.1, mul_nonneg hp.1.le he.1.le]
  have hU1 : 1 - p + p * e ≤ 1 := by
    nlinarith [mul_nonneg hp.1.le (sub_nonneg.mpr he.2)]
  have hsU : s * (1 - p + p * e) ≤ 1 / 8 := by nlinarith
  constructor
  · linarith
  · have : 0 < e + s * (1 - p + p * e) := add_pos he.1 (mul_pos hs.1 hUpos)
    linarith

end LPPMonotonicityProof.Analytic
