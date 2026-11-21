module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Rational arithmetic for the high-bias theorem

This module formalizes the polynomial computation in the proof of
Theorem 3.7 (`thm:above-two`) of the paper.  It contains no analytic
reductions.  Coefficients are kept exact over `ℚ`; evaluation and positivity
are stated over `ℝ`.
-/

@[expose] public section

namespace LPPMonotonicityProof.HighBias

/-- The decreasing affine function `F` in the proof of Theorem 3.7. -/
def F (L q t : ℚ) : ℚ :=
  L * (2 * L ^ 3 - L * q - q ^ 2) -
    (L - q) * (L ^ 2 * (L + 1) - L * q - q ^ 2) * t

/-- The two-term upper bound `S₂ ≥ S(q)` in the proof of Theorem 3.7, with `L = 1+a`,
`q = 1-b`. -/
def S2 (a b : ℚ) : ℚ :=
  let L := 1 + a
  let q := 1 - b
  a * L / (L - q) ^ 2 + a * L ^ 2 / (L ^ 2 - q) ^ 2 +
    (L + 1) / (L ^ 2 * (L + 1) - 2 * q)

/-- The three-denominator product used in the clearing computation. -/
def clearingFactor (a b : ℚ) : ℚ :=
  let L := 1 + a
  let q := 1 - b
  (L - q) * (L ^ 2 - q) ^ 2 * (L ^ 2 * (L + 1) - 2 * q)

/-- The numerator obtained by clearing the three denominators of `S₂` in `F(S₂)`. -/
def clearedPolynomial (a b : ℚ) : ℚ :=
  let L := 1 + a
  let q := 1 - b
  let u := L - q
  let v := L ^ 2 - q
  let w := L ^ 2 * (L + 1) - 2 * q
  let constant := L * (2 * L ^ 3 - L * q - q ^ 2)
  let slope := L ^ 2 * (L + 1) - L * q - q ^ 2
  constant * u * v ^ 2 * w -
    slope * (a * L * v ^ 2 * w + a * L ^ 2 * u ^ 2 * w +
      (L + 1) * u ^ 2 * v ^ 2)

/-- On the line `24b+10a=8`, the proof of Theorem 3.7 puts `a=8/(10+9u)`. -/
def boundaryA (u : ℚ) : ℚ := 8 / (10 + 9 * u)

/-- On the line `24b+10a=8`, the proof of Theorem 3.7 puts `b=3u/(10+9u)`. -/
def boundaryB (u : ℚ) : ℚ := 3 * u / (10 + 9 * u)

/-- The normalization `(10+9u)^12/(2^20*10^5)` in the definition of `H(u)`. -/
def boundaryScale (u : ℚ) : ℚ := (10 + 9 * u) ^ 12 / (2 ^ 20 * 10 ^ 5)

/-- The exact power coefficients of `H`, in increasing degree.

These are the exact rationals obtained by expanding `H(u)`, not their floors. -/
def exactCoefficients : List ℚ :=
  [73598 / 3125, 9501939 / 200000, 439101 / 1600000,
    -444472083 / 6400000, -5963098257 / 102400000,
    679594941 / 204800000, 6492379959 / 204800000,
    4456513323 / 204800000, 12140651547 / 1638400000,
    4632571197 / 3276800000, 4782969 / 32768000,
    43046721 / 6553600000]

/-- The integer row printed in the proof of Theorem 3.7 (the coefficients of `H` rounded
down), in increasing degree. -/
def printedRow : List ℤ := [23, 47, 0, -70, -59, 3, 31, 21, 7, 1, 0, 0]

/-- The coefficients of the positivity remainder `R`, in increasing degree. -/
def rCoefficients : List ℚ := [23, 93, 163, 161, 98, 38, 9, 1]

/-- Horner evaluation over `ℚ`. -/
def evalRat : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: cs, u => c + u * evalRat cs u

/-- Horner evaluation over `ℝ` of an exact rational coefficient list. -/
def evalReal : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, u => (c : ℝ) + u * evalReal cs u

/-- The degree-eleven polynomial `H` over `ℚ`. -/
def H (u : ℚ) : ℚ := evalRat exactCoefficients u

/-- The degree-eleven polynomial `H` over `ℝ`. -/
def HReal (u : ℝ) : ℝ := evalReal exactCoefficients u

/-- The printed-row polynomial `h` over `ℝ`. -/
def h (u : ℝ) : ℝ := evalReal (printedRow.map (fun n : ℤ => (n : ℚ))) u

/-- The nonnegative-coefficient polynomial `R` of the identity `h_identity`. -/
def R (u : ℝ) : ℝ := evalReal rCoefficients u

/-- Real-valued version of `F`, used for the final boundary sign. -/
def FReal (L q t : ℝ) : ℝ :=
  L * (2 * L ^ 3 - L * q - q ^ 2) -
    (L - q) * (L ^ 2 * (L + 1) - L * q - q ^ 2) * t

/-- Real-valued version of `S2`. -/
noncomputable def S2Real (a b : ℝ) : ℝ :=
  let L := 1 + a
  let q := 1 - b
  a * L / (L - q) ^ 2 + a * L ^ 2 / (L ^ 2 - q) ^ 2 +
    (L + 1) / (L ^ 2 * (L + 1) - 2 * q)

/-- Real-valued version of `clearingFactor`. -/
def clearingFactorReal (a b : ℝ) : ℝ :=
  let L := 1 + a
  let q := 1 - b
  (L - q) * (L ^ 2 - q) ^ 2 * (L ^ 2 * (L + 1) - 2 * q)

/-- Real-valued version of `clearedPolynomial`. -/
def clearedPolynomialReal (a b : ℝ) : ℝ :=
  let L := 1 + a
  let q := 1 - b
  let u := L - q
  let v := L ^ 2 - q
  let w := L ^ 2 * (L + 1) - 2 * q
  let constant := L * (2 * L ^ 3 - L * q - q ^ 2)
  let slope := L ^ 2 * (L + 1) - L * q - q ^ 2
  constant * u * v ^ 2 * w -
    slope * (a * L * v ^ 2 * w + a * L ^ 2 * u ^ 2 * w +
      (L + 1) * u ^ 2 * v ^ 2)

/-- The boundary value `a=8/(10+9u)` over `ℝ`. -/
noncomputable def boundaryAReal (u : ℝ) : ℝ := 8 / (10 + 9 * u)

/-- The boundary value `b=3u/(10+9u)` over `ℝ`. -/
noncomputable def boundaryBReal (u : ℝ) : ℝ := 3 * u / (10 + 9 * u)

/-- The normalization `(10+9u)^12/(2^20*10^5)` over `ℝ`. -/
noncomputable def boundaryScaleReal (u : ℝ) : ℝ := (10 + 9 * u) ^ 12 / (2 ^ 20 * 10 ^ 5)

/-- The normalized cleared numerator on the boundary line, before identifying it with `H`. -/
def boundaryCleared (u : ℚ) : ℚ :=
  boundaryScale u * clearedPolynomial (boundaryA u) (boundaryB u)

/-- Proof of Theorem 3.7: clear all three positive
 denominators of `F(S₂)`. -/
theorem S2_clear_denominators (a b : ℚ)
    (hu : 1 + a - (1 - b) ≠ 0)
    (hv : (1 + a) ^ 2 - (1 - b) ≠ 0)
    (hw : (1 + a) ^ 2 * (1 + a + 1) - 2 * (1 - b) ≠ 0) :
    clearingFactor a b * F (1 + a) (1 - b) (S2 a b) = clearedPolynomial a b := by
  have hw' : (1 + a) ^ 2 * (1 + a + 1) - (1 - b) * 2 ≠ 0 := by
    simpa [mul_comm] using hw
  simp only [S2, F, clearingFactor, clearedPolynomial]
  field_simp [hu, hv, hw']

/-- Real version of `S2_clear_denominators`. -/
theorem S2Real_clear_denominators (a b : ℝ)
    (hu : 1 + a - (1 - b) ≠ 0)
    (hv : (1 + a) ^ 2 - (1 - b) ≠ 0)
    (hw : (1 + a) ^ 2 * (1 + a + 1) - 2 * (1 - b) ≠ 0) :
    clearingFactorReal a b * FReal (1 + a) (1 - b) (S2Real a b) =
      clearedPolynomialReal a b := by
  have hw' : (1 + a) ^ 2 * (1 + a + 1) - (1 - b) * 2 ≠ 0 := by
    simpa [mul_comm] using hw
  simp only [S2Real, FReal, clearingFactorReal, clearedPolynomialReal]
  field_simp [hu, hv, hw']

/-- Proof of Theorem 3.7, on the line `24b+10a=8`: the normalized boundary
 expression is exactly the polynomial with `exactCoefficients`. -/
theorem boundaryCleared_eq_H (u : ℚ) (hu : 0 ≤ u) : boundaryCleared u = H u := by
  have hs : 10 + 9 * u ≠ 0 := ne_of_gt (by positivity)
  simp only [boundaryCleared, boundaryScale, clearedPolynomial, boundaryA, boundaryB,
    H, evalRat, exactCoefficients]
  field_simp [hs]
  ring

/-- On `24b+10a=8`, the paper's normalized clearing factor times `F(S₂)` is exactly `H`. -/
theorem boundary_F_S2_cleared (u : ℚ) (hu : 0 ≤ u) :
    boundaryScale u * clearingFactor (boundaryA u) (boundaryB u) *
      F (1 + boundaryA u) (1 - boundaryB u)
        (S2 (boundaryA u) (boundaryB u)) = H u := by
  have hs : 10 + 9 * u ≠ 0 := ne_of_gt (by positivity)
  have hu_eq : 1 + boundaryA u - (1 - boundaryB u) =
      (8 + 3 * u) / (10 + 9 * u) := by
    simp only [boundaryA, boundaryB]
    field_simp [hs]
    ring
  have hv_eq : (1 + boundaryA u) ^ 2 - (1 - boundaryB u) =
      (27 * u ^ 2 + 174 * u + 224) / (10 + 9 * u) ^ 2 := by
    simp only [boundaryA, boundaryB]
    field_simp [hs]
    ring
  have hw_eq : (1 + boundaryA u) ^ 2 * (1 + boundaryA u + 1) -
      2 * (1 - boundaryB u) =
        (486 * u ^ 3 + 4320 * u ^ 2 + 10104 * u + 7072) / (10 + 9 * u) ^ 3 := by
    simp only [boundaryA, boundaryB]
    field_simp [hs]
    ring
  have hu' : 1 + boundaryA u - (1 - boundaryB u) ≠ 0 := by
    rw [hu_eq]
    positivity
  have hv' : (1 + boundaryA u) ^ 2 - (1 - boundaryB u) ≠ 0 := by
    rw [hv_eq]
    positivity
  have hw' : (1 + boundaryA u) ^ 2 * (1 + boundaryA u + 1) -
      2 * (1 - boundaryB u) ≠ 0 := by
    rw [hw_eq]
    positivity
  calc
    boundaryScale u * clearingFactor (boundaryA u) (boundaryB u) *
        F (1 + boundaryA u) (1 - boundaryB u)
          (S2 (boundaryA u) (boundaryB u)) =
      boundaryScale u * (clearingFactor (boundaryA u) (boundaryB u) *
        F (1 + boundaryA u) (1 - boundaryB u)
          (S2 (boundaryA u) (boundaryB u))) := by ring
    _ = boundaryScale u * clearedPolynomial (boundaryA u) (boundaryB u) := by
      rw [S2_clear_denominators (boundaryA u) (boundaryB u) hu' hv' hw']
    _ = H u := boundaryCleared_eq_H u hu

/-- On `24b+10a=8`, the normalized real clearing factor times `F(S₂)`
is exactly `HReal`. -/
theorem boundary_F_S2_cleared_real (u : ℝ) (hu : 0 ≤ u) :
    boundaryScaleReal u * clearingFactorReal (boundaryAReal u) (boundaryBReal u) *
      FReal (1 + boundaryAReal u) (1 - boundaryBReal u)
        (S2Real (boundaryAReal u) (boundaryBReal u)) = HReal u := by
  have hs : 10 + 9 * u ≠ 0 := ne_of_gt (by positivity)
  have hu_eq : 1 + boundaryAReal u - (1 - boundaryBReal u) =
      (8 + 3 * u) / (10 + 9 * u) := by
    simp only [boundaryAReal, boundaryBReal]
    field_simp [hs]
    ring
  have hv_eq : (1 + boundaryAReal u) ^ 2 - (1 - boundaryBReal u) =
      (27 * u ^ 2 + 174 * u + 224) / (10 + 9 * u) ^ 2 := by
    simp only [boundaryAReal, boundaryBReal]
    field_simp [hs]
    ring
  have hw_eq : (1 + boundaryAReal u) ^ 2 * (1 + boundaryAReal u + 1) -
      2 * (1 - boundaryBReal u) =
        (486 * u ^ 3 + 4320 * u ^ 2 + 10104 * u + 7072) / (10 + 9 * u) ^ 3 := by
    simp only [boundaryAReal, boundaryBReal]
    field_simp [hs]
    ring
  have hu' : 1 + boundaryAReal u - (1 - boundaryBReal u) ≠ 0 := by
    rw [hu_eq]
    positivity
  have hv' : (1 + boundaryAReal u) ^ 2 - (1 - boundaryBReal u) ≠ 0 := by
    rw [hv_eq]
    positivity
  have hw' : (1 + boundaryAReal u) ^ 2 * (1 + boundaryAReal u + 1) -
      2 * (1 - boundaryBReal u) ≠ 0 := by
    rw [hw_eq]
    positivity
  calc
    boundaryScaleReal u * clearingFactorReal (boundaryAReal u) (boundaryBReal u) *
        FReal (1 + boundaryAReal u) (1 - boundaryBReal u)
          (S2Real (boundaryAReal u) (boundaryBReal u)) =
      boundaryScaleReal u * (clearingFactorReal (boundaryAReal u) (boundaryBReal u) *
        FReal (1 + boundaryAReal u) (1 - boundaryBReal u)
          (S2Real (boundaryAReal u) (boundaryBReal u))) := by ring
    _ = boundaryScaleReal u * clearedPolynomialReal (boundaryAReal u) (boundaryBReal u) := by
      rw [S2Real_clear_denominators (boundaryAReal u) (boundaryBReal u) hu' hv' hw']
    _ = HReal u := by
      simp only [boundaryScaleReal, clearedPolynomialReal, boundaryAReal, boundaryBReal,
        HReal, evalReal, exactCoefficients]
      field_simp [hs]
      ring

/-- The normalization and all three clearing denominators are strictly
positive on the boundary line for every real `u ≥ 0`. -/
theorem boundary_prefactor_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < boundaryScaleReal u * clearingFactorReal (boundaryAReal u) (boundaryBReal u) := by
  have hs : 10 + 9 * u ≠ 0 := ne_of_gt (by positivity)
  have hu_eq : 1 + boundaryAReal u - (1 - boundaryBReal u) =
      (8 + 3 * u) / (10 + 9 * u) := by
    simp only [boundaryAReal, boundaryBReal]
    field_simp [hs]
    ring
  have hv_eq : (1 + boundaryAReal u) ^ 2 - (1 - boundaryBReal u) =
      (27 * u ^ 2 + 174 * u + 224) / (10 + 9 * u) ^ 2 := by
    simp only [boundaryAReal, boundaryBReal]
    field_simp [hs]
    ring
  have hw_eq : (1 + boundaryAReal u) ^ 2 * (1 + boundaryAReal u + 1) -
      2 * (1 - boundaryBReal u) =
        (486 * u ^ 3 + 4320 * u ^ 2 + 10104 * u + 7072) / (10 + 9 * u) ^ 3 := by
    simp only [boundaryAReal, boundaryBReal]
    field_simp [hs]
    ring
  have hscale : 0 < boundaryScaleReal u := by
    simp only [boundaryScaleReal]
    positivity
  have hclear : 0 < clearingFactorReal (boundaryAReal u) (boundaryBReal u) := by
    simp only [clearingFactorReal]
    rw [hu_eq, hv_eq, hw_eq]
    positivity
  exact mul_pos hscale hclear

/-- There are twelve coefficients through degree eleven, and the leading one
 is nonzero. -/
theorem H_degree_eleven :
    exactCoefficients.length = 12 ∧
      exactCoefficients.getLast? = some (43046721 / 6553600000) := by
  decide +kernel

/-- Every exact coefficient of `H` is at least the corresponding printed
 integer.  The kernel checks the finite rational comparisons. -/
theorem printedRow_le_exactCoefficients :
    List.Forall₂ (fun c d : ℚ => c ≤ d)
      (printedRow.map (fun n : ℤ => (n : ℚ))) exactCoefficients := by
  norm_num [printedRow, exactCoefficients]

/-- Horner evaluation is monotone in each coefficient for a nonnegative
 argument.  This is the soundness lemma for the coefficient-list check. -/
theorem evalReal_mono {lower upper : List ℚ} {u : ℝ} (hu : 0 ≤ u)
    (hcoeff : List.Forall₂ (fun c d : ℚ => c ≤ d) lower upper) :
    evalReal lower u ≤ evalReal upper u := by
  induction hcoeff with
  | nil => rfl
  | cons hcd _ ih =>
      simp only [evalReal]
      exact add_le_add (by exact_mod_cast hcd) (mul_le_mul_of_nonneg_left ih hu)

/-- Proof of Theorem 3.7: the exact polynomial dominates the printed-row polynomial. -/
theorem H_ge_h {u : ℝ} (hu : 0 ≤ u) : h u ≤ HReal u := by
  exact evalReal_mono hu printedRow_le_exactCoefficients

/-- The tangent inequality `h(u) ≥ (2+2u)u³` of the proof of Theorem 3.7 (tangent `2+2u`
 at `1` of the convex function `h(u)/u³`) is certified by the explicit
 square-times-remainder identity. -/
theorem h_identity (u : ℝ) :
    h u = (2 + 2 * u) * u ^ 3 + (u - 1) ^ 2 * R u := by
  norm_num [h, R, evalReal, printedRow, rCoefficients]
  ring

/-- The remainder is strictly positive on the whole required range. -/
theorem R_pos {u : ℝ} (hu : 0 ≤ u) : 0 < R u := by
  norm_num [R, evalReal, rCoefficients]
  positivity

/-- The zero endpoint is treated separately, as in the proof of Theorem 3.7 (`h(0)=23`). -/
theorem h_zero : h 0 = 23 := by
  norm_num [h, evalReal, printedRow]

/-- Proof of Theorem 3.7: `h` is strictly positive for every `u ≥ 0`. -/
theorem h_pos {u : ℝ} (hu : 0 ≤ u) : 0 < h u := by
  rcases eq_or_lt_of_le hu with rfl | hu'
  · rw [h_zero]
    norm_num
  · rw [h_identity]
    have hR : 0 < R u := R_pos hu
    have hcube : 0 < u ^ 3 := pow_pos hu' 3
    have hfirst : 0 < (2 + 2 * u) * u ^ 3 := mul_pos (by linarith) hcube
    have hsecond : 0 ≤ (u - 1) ^ 2 * R u := mul_nonneg (sq_nonneg _) hR.le
    linarith

/-- Proof of Theorem 3.7: `H` is strictly positive for every `u ≥ 0`. -/
theorem H_pos {u : ℝ} (hu : 0 ≤ u) : 0 < HReal u := by
  exact lt_of_lt_of_le (h_pos hu) (H_ge_h hu)

/-- Proof of Theorem 3.7: `F(S₂)` is strictly positive at every point of the
boundary line `24b+10a=8`, parametrized by a nonnegative real `u`. -/
theorem boundary_F_S2_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < FReal (1 + boundaryAReal u) (1 - boundaryBReal u)
      (S2Real (boundaryAReal u) (boundaryBReal u)) := by
  apply (mul_pos_iff_of_pos_left (boundary_prefactor_pos hu)).mp
  rw [boundary_F_S2_cleared_real u hu]
  exact H_pos hu

end LPPMonotonicityProof.HighBias
