module

public import LPPMonotonicityProof.Analytic.LowWindowScalar
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Scalar positivity on the low-bias window

This module proves the explicit scalar positivity on the small-`s` window, the last
step of the proof of Theorem 4.3 (`thm:low-window`).
-/

@[expose] public section

namespace LPPMonotonicityProof.Analytic

/-- The scalar lower bound for the low-window sign test is strictly positive. -/
theorem lowWindow_scalar {p e s V : ℝ}
    (hp : 0 < p ∧ p ≤ 1) (he : 0 < e ∧ e ≤ 1 / 2)
    (hs : 0 < s ∧ s ≤ 1 / 8) (hV : V ≤ 1 - 4 * e / 3) :
    let q := 1 - p
    let U := q + p * e
    let A := 1 - e - s * U
    let d := (1 - s * q ^ 2 / 2) / A - q * (1 + p) / 4
    let hh := 2 + s * (p + d)
    let L := s * (1 / A - p) / ((1 + s) * (3 + s / A))
    0 < 1 - V * d - hh * L := by
  intro q U A d hh L
  let c := 1 - 4 * e / 3
  let x := 1 / A
  have hq0 : 0 ≤ q := sub_nonneg.mpr hp.2
  have hq1 : q ≤ 1 := by dsimp only [q]; linarith [hp.1]
  have hU1 : U ≤ 1 := by
    dsimp only [U, q]
    nlinarith only [mul_nonneg hp.1.le (show 0 ≤ 1 - e by linarith [he.2])]
  have hA := lowWindow_A_bounds hp he hs
  change 3 / 8 ≤ A ∧ A < 1 at hA
  have hA0 : 0 < A := by linarith [hA.1]
  have hc : 1 / 3 ≤ c := by dsimp only [c]; linarith [he.2]
  have hc1 : c ≤ 1 := by dsimp only [c]; linarith [he.1]
  have hAx : A * x = 1 := mul_one_div_cancel hA0.ne'
  have hx1 : 1 ≤ x := (le_div_iff₀ hA0).2 (by simpa using hA.2.le)
  have hx3 : x ≤ 3 := (div_le_iff₀ hA0).2 (by linarith [hA.1])
  have hqprod : 0 ≤ q * (1 + p) := mul_nonneg hq0 (by linarith [hp.1])
  have hqprod2 : q * (1 + p) ≤ 2 :=
    calc
      q * (1 + p) ≤ 1 * 2 :=
        mul_le_mul hq1 (by linarith only [hp.2]) (by linarith only [hp.1]) zero_le_one
      _ = 2 := by ring
  have hsq : s * q ^ 2 ≤ 1 / 8 := by
    calc
      s * q ^ 2 ≤ (1 / 8) * 1 :=
        mul_le_mul hs.2 (by simpa [pow_two] using mul_le_mul hq1 hq1 hq0 zero_le_one)
          (sq_nonneg _) (by norm_num)
      _ = 1 / 8 := by ring
  have hdEq : d = (1 - s * q ^ 2 / 2) * x - q * (1 + p) / 4 := by
    dsimp only [d, x]
    rw [div_eq_mul_one_div (1 - s * q ^ 2 / 2) A]
  have hd0 : 0 < d := by
    rw [hdEq]
    have h := mul_le_mul (show (15 : ℝ) / 16 ≤ 1 - s * q ^ 2 / 2 by linarith only [hsq])
      hx1 (by norm_num) (by linarith only [hsq])
    linarith only [h, hqprod2]
  have hdx : d ≤ x := by
    rw [hdEq]
    have h := mul_nonneg (mul_nonneg hs.1.le (sq_nonneg q)) (show 0 ≤ x by linarith)
    linarith only [h, hqprod]
  -- Bound the loss using the positive denominator and d ≤ 1 / A.
  have hden : 0 < (1 + s) * (3 + s / A) :=
    mul_pos (by linarith only [hs.1]) (by linarith only [div_pos hs.1 hA0])
  have hsA : s / A = s * x := div_eq_mul_one_div s A
  have hhh : hh ≤ (2 / 3) * ((1 + s) * (3 + s / A)) := by
    rw [hsA]
    dsimp only [hh]
    have h := mul_nonneg hs.1.le (show 0 ≤ 6 - 3 * p - x by linarith only [hp.2, hx3])
    have hdifference := mul_nonneg hs.1.le (sub_nonneg.mpr hdx)
    have hquadratic := mul_nonneg (sq_nonneg s) (show 0 ≤ x by linarith)
    linarith only [h, hdifference, hquadratic]
  have hL : hh * L ≤ (2 / 3) * (s * (x - p)) := by
    change hh * (s * (x - p) / ((1 + s) * (3 + s / A))) ≤ _
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).2
    calc
      hh * (s * (x - p)) ≤ (2 / 3) * ((1 + s) * (3 + s / A)) * (s * (x - p)) :=
        mul_le_mul_of_nonneg_right hhh (mul_nonneg hs.1.le (by linarith))
      _ = _ := by ring
  have hAd : A * d = 1 - s * q ^ 2 / 2 - A * q * (1 + p) / 4 := by
    rw [hdEq]
    linear_combination (1 - s * q ^ 2 / 2) * hAx
  have hpA : 1 - p * A = (1 + p * s) * U := by
    dsimp only [A, U, q]
    ring
  -- Clear the factor 1 / A before splitting the resulting lower bound.
  have hscaled :
      A * (1 - c * d - (2 / 3) * (s * (x - p))) =
        e / 3 - s * (5 + 2 * p * s) * U / 3 +
          c * (A * q * (1 + p) / 4 + s * q ^ 2 / 2) := by
    have hAeq : A = 1 - e - s * U := rfl
    have hceq : c = 1 - 4 * e / 3 := rfl
    linear_combination -c * hAd - (2 * s / 3) * hAx -
      (2 * s / 3) * hpA + hAeq - hceq
  have hpe : 0 < 1 / 3 - s * (5 + 2 * p * s) / 3 := by
    have hps : p * s ≤ 1 / 8 := by simpa using mul_le_mul hp.2 hs.2 hs.1.le zero_le_one
    have h := mul_le_mul hs.2 (show 5 + 2 * p * s ≤ 21 / 4 by linarith only [hps])
      (show 0 ≤ 5 + 2 * p * s by nlinarith only [mul_nonneg hp.1.le hs.1.le])
      (show 0 ≤ (1 : ℝ) / 8 by norm_num)
    linarith only [h]
  have hpq : 0 ≤ c * (A - 2 * s) / 4 - 2 * s ^ 2 / 3 := by
    have h := mul_le_mul hc (show 1 / 8 ≤ A - 2 * s by linarith only [hA.1, hs.2])
      (show 0 ≤ (1 : ℝ) / 8 by norm_num) (show 0 ≤ c by linarith only [hc])
    have hs2 := mul_le_mul hs.2 hs.2 hs.1.le (show 0 ≤ (1 : ℝ) / 8 by norm_num)
    linarith only [h, hs2]
  have hq : 0 < e / 3 - 5 * s / 3 + c * (1 - e + s) / 4 := by
    calc
      0 < (32 * (e - 7 / 16) ^ 2 + 7 / 8) / 96 :=
        by nlinarith only [sq_nonneg (e - 7 / 16)]
      _ = e / 3 - 5 * (1 / 8) / 3 + c * (1 - e + 1 / 8) / 4 := by
        dsimp only [c]
        ring
      _ ≤ _ := by
        have h := mul_nonneg (sub_nonneg.mpr hs.2)
          (show 0 ≤ 5 / 3 - c / 4 by linarith only [hc1])
        linarith only [h]
  -- The split into pe, pq and q leaves a nonnegative remainder since U ≤ 1.
  have hdecomp :
      e / 3 - s * (5 + 2 * p * s) * U / 3 + c * (A * q * (1 + p) / 4 + s * q ^ 2 / 2) =
        p * e * (1 / 3 - s * (5 + 2 * p * s) / 3) +
        p * q * (c * (A - 2 * s) / 4 - 2 * s ^ 2 / 3) +
        q * (e / 3 - 5 * s / 3 + c * (1 - e + s) / 4) +
        c * s * q * (1 - U) / 4 := by
    dsimp only [A, U, q]
    ring
  have hpositive : 0 < 1 - c * d - (2 / 3) * (s * (x - p)) := by
    apply pos_of_mul_pos_right _ hA0.le
    rw [hscaled, hdecomp]
    have hrem : 0 ≤ c * s * q * (1 - U) / 4 := by
      have hc0 : 0 ≤ c := by linarith only [hc]
      exact div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hc0 hs.1.le) hq0) (sub_nonneg.mpr hU1))
        (by norm_num)
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg (mul_pos (mul_pos hp.1 he.1) hpe)
          (mul_nonneg (mul_nonneg hp.1.le hq0) hpq))
        (mul_nonneg hq0 hq.le))
      hrem
  have hVd : V * d ≤ c * d := mul_le_mul_of_nonneg_right hV hd0.le
  linarith only [hpositive, hVd, hL]


end LPPMonotonicityProof.Analytic
