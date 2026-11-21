module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Exact real values with rational enclosures

This is a small certificate-arithmetic layer in the namespace `CertA`, used by the
prefix-factor enclosure `prefixEnc` of `CertA/Prefix.lean`.  An `Enc`
contains an exact real value and a rational interval proved to contain it.
All operations are ordinary kernel-reducible definitions; none uses native
evaluation.
-/

@[expose] public section

namespace LPPMonotonicityProof.CertA

/-- An exact real value together with proved rational lower and upper bounds. -/
structure Enc where
  value : ℝ
  lower : ℚ
  upper : ℚ
  lower_le : (lower : ℝ) ≤ value
  le_upper : value ≤ (upper : ℝ)

namespace Enc

noncomputable section

/-- A rational constant, viewed as an exact real value. -/
def const (q : ℚ) : Enc where
  value := (q : ℝ)
  lower := q
  upper := q
  lower_le := le_rfl
  le_upper := le_rfl

/-- The fixed dyadic grid used to keep certificate data small. -/
def scale : ℚ := 2 ^ 20

/-- Round both endpoints outwards to `scale⁻¹ ℤ`. -/
def round (x : Enc) : Enc where
  value := x.value
  lower := (⌊x.lower * scale⌋ : ℚ) / scale
  upper := (⌈x.upper * scale⌉ : ℚ) / scale
  lower_le := by
    exact le_trans (by exact_mod_cast (show ((⌊x.lower * scale⌋ : ℚ) / scale) ≤ x.lower by
      apply (div_le_iff₀ (by norm_num [scale])).2
      exact Int.floor_le _)) x.lower_le
  le_upper := by
    exact le_trans x.le_upper (by exact_mod_cast (show x.upper ≤ ((⌈x.upper * scale⌉ : ℚ) / scale) by
      apply (le_div_iff₀ (by norm_num [scale])).2
      exact Int.le_ceil _))

/-- Addition of enclosures. -/
def add (x y : Enc) : Enc := round {
  value := x.value + y.value
  lower := x.lower + y.lower
  upper := x.upper + y.upper
  lower_le := by
    push_cast
    exact add_le_add x.lower_le y.lower_le
  le_upper := by
    push_cast
    exact add_le_add x.le_upper y.le_upper }

/-- Negation of an enclosure. -/
def neg (x : Enc) : Enc where
  value := -x.value
  lower := -x.upper
  upper := -x.lower
  lower_le := by
    push_cast
    exact neg_le_neg x.le_upper
  le_upper := by
    push_cast
    exact neg_le_neg x.lower_le

/-- Subtraction of enclosures. -/
def sub (x y : Enc) : Enc := add x (neg y)

/-- The four corner products used in general interval multiplication. -/
def mulLower (xl xu yl yu : ℚ) : ℚ :=
  min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu))

/-- The upper counterpart of `mulLower`. -/
def mulUpper (xl xu yl yu : ℚ) : ℚ :=
  max (max (xl * yl) (xl * yu)) (max (xu * yl) (xu * yu))

private lemma mul_min_le {xl xu yl yu x y : ℝ}
    (hxl : xl ≤ x) (hxu : x ≤ xu) (hyl : yl ≤ y) (hyu : y ≤ yu) :
    min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu)) ≤ x * y := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · by_cases hxl0 : 0 ≤ xl
    · by_cases hyl0 : 0 ≤ yl
      · calc
          min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu)) ≤ xl * yl :=
            le_trans (min_le_left _ _) (min_le_left _ _)
          _ ≤ x * yl := mul_le_mul_of_nonneg_right hxl hyl0
          _ ≤ x * y := mul_le_mul_of_nonneg_left hyl hx
      · have hz : min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu)) ≤ 0 :=
          le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
            (mul_nonpos_of_nonneg_of_nonpos (le_trans hx hxu) (le_of_not_ge hyl0))
        exact hz.trans (mul_nonneg hx hy)
    · have hz : min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu)) ≤ 0 :=
        le_trans (le_trans (min_le_left _ _) (min_le_right _ _))
          (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hxl0) (le_trans hy hyu))
      exact hz.trans (mul_nonneg hx hy)
  · calc
      min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu)) ≤ xu * yl :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      _ ≤ x * yl := mul_le_mul_of_nonpos_right hxu (le_trans hyl hy)
      _ ≤ x * y := mul_le_mul_of_nonneg_left hyl hx
  · calc
      min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu)) ≤ xl * yu :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      _ ≤ xl * y := mul_le_mul_of_nonpos_left hyu (le_trans hxl hx)
      _ ≤ x * y := mul_le_mul_of_nonneg_right hxl hy
  · by_cases hxu0 : xu ≤ 0
    · by_cases hyu0 : yu ≤ 0
      · calc
          min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu)) ≤ xu * yu :=
            le_trans (min_le_right _ _) (min_le_right _ _)
          _ ≤ x * yu := mul_le_mul_of_nonpos_right hxu hyu0
          _ ≤ x * y := mul_le_mul_of_nonpos_left hyu hx
      · have hz : min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu)) ≤ 0 :=
          le_trans (le_trans (min_le_left _ _) (min_le_right _ _))
            (mul_nonpos_of_nonpos_of_nonneg (le_trans hxl hx) (le_of_not_ge hyu0))
        exact hz.trans (mul_nonneg_of_nonpos_of_nonpos hx hy)
    · have hz : min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu)) ≤ 0 :=
        le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
          (mul_nonpos_of_nonneg_of_nonpos (le_of_not_ge hxu0) (le_trans hyl hy))
      exact hz.trans (mul_nonneg_of_nonpos_of_nonpos hx hy)

private lemma mul_le_max {xl xu yl yu x y : ℝ}
    (hxl : xl ≤ x) (hxu : x ≤ xu) (hyl : yl ≤ y) (hyu : y ≤ yu) :
    x * y ≤ max (max (xl * yl) (xl * yu)) (max (xu * yl) (xu * yu)) := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · calc
      x * y ≤ xu * y := mul_le_mul_of_nonneg_right hxu hy
      _ ≤ xu * yu := mul_le_mul_of_nonneg_left hyu (le_trans hx hxu)
      _ ≤ _ := le_trans (le_max_right _ _) (le_max_right _ _)
  · by_cases hyu0 : 0 ≤ yu
    · have hz : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hy
      exact hz.trans (le_trans (mul_nonneg (le_trans hx hxu) hyu0)
        (le_trans (le_max_right _ _) (le_max_right _ _)))
    · calc
        x * y ≤ x * yu := mul_le_mul_of_nonneg_left hyu hx
        _ ≤ xl * yu := mul_le_mul_of_nonpos_right hxl (le_of_not_ge hyu0)
        _ ≤ _ := le_trans (le_max_right _ _) (le_max_left _ _)
  · by_cases hxu0 : 0 ≤ xu
    · have hz : x * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx hy
      by_cases hyl0 : 0 ≤ yl
      · have hz' : (0 : ℝ) ≤ max (max (xl * yl) (xl * yu)) (max (xu * yl) (xu * yu)) :=
          le_trans (mul_nonneg hxu0 hyl0) (le_trans (le_max_left _ _) (le_max_right _ _))
        exact hz.trans hz'
      · have hz' : (0 : ℝ) ≤ max (max (xl * yl) (xl * yu)) (max (xu * yl) (xu * yu)) :=
          le_trans (mul_nonneg_of_nonpos_of_nonpos (le_trans hxl hx) (le_of_not_ge hyl0))
            (le_trans (le_max_left _ _) (le_max_left _ _))
        exact hz.trans hz'
    · calc
        x * y ≤ xu * y := mul_le_mul_of_nonneg_right hxu hy
        _ ≤ xu * yl := mul_le_mul_of_nonpos_left hyl (le_of_not_ge hxu0)
        _ ≤ _ := le_trans (le_max_left _ _) (le_max_right _ _)
  · calc
      x * y ≤ xl * y := mul_le_mul_of_nonpos_right hxl hy
      _ ≤ xl * yl := mul_le_mul_of_nonpos_left hyl (le_trans hxl hx)
      _ ≤ _ := le_trans (le_max_left _ _) (le_max_left _ _)

/-- General multiplication by all four endpoint products. -/
def mul (x y : Enc) : Enc := round {
  value := x.value * y.value
  lower := mulLower x.lower x.upper y.lower y.upper
  upper := mulUpper x.lower x.upper y.lower y.upper
  lower_le := by
    unfold mulLower
    push_cast
    exact mul_min_le x.lower_le x.le_upper y.lower_le y.le_upper
  le_upper := by
    unfold mulUpper
    push_cast
    exact mul_le_max x.lower_le x.le_upper y.lower_le y.le_upper }

/-- Multiplication of an enclosure by an exact rational constant. -/
def mulConst (q : ℚ) (x : Enc) : Enc := mul (const q) x

/-- Reciprocal with a proved positive lower endpoint. -/
def inv (x : Enc) (hpos : 0 < x.lower) : Enc := round {
  value := x.value⁻¹
  lower := x.upper⁻¹
  upper := x.lower⁻¹
  lower_le := by
    have hx : (0 : ℝ) < x.value := lt_of_lt_of_le (by exact_mod_cast hpos) x.lower_le
    simpa only [one_div, Rat.cast_inv] using one_div_le_one_div_of_le hx x.le_upper
  le_upper := by
    have hl : (0 : ℝ) < (x.lower : ℝ) := by exact_mod_cast hpos
    simpa only [one_div, Rat.cast_inv] using one_div_le_one_div_of_le hl x.lower_le }

/-- Division with a positive denominator enclosure. -/
def div (x y : Enc) (hpos : 0 < y.lower) : Enc := mul x (inv y hpos)

/-- Square an enclosure whose lower endpoint is nonnegative. -/
def sq (x : Enc) (hnonneg : 0 ≤ x.lower) : Enc := round {
  value := x.value ^ 2
  lower := x.lower ^ 2
  upper := x.upper ^ 2
  lower_le := by
    simp only [pow_two, Rat.cast_mul]
    have hx : (0 : ℝ) ≤ x.value := le_trans (by exact_mod_cast hnonneg) x.lower_le
    have hl : (0 : ℝ) ≤ (x.lower : ℝ) := by exact_mod_cast hnonneg
    nlinarith [x.lower_le]
  le_upper := by
    simp only [pow_two, Rat.cast_mul]
    have hx : (0 : ℝ) ≤ x.value := le_trans (by exact_mod_cast hnonneg) x.lower_le
    have hu : (0 : ℝ) ≤ (x.upper : ℝ) := le_trans hx x.le_upper
    nlinarith [x.le_upper] }

/-- Clamp an enclosure of a quantity known to lie in `[0,1]`. -/
def clip01 (x : Enc) (h0 : 0 ≤ x.value) (h1 : x.value ≤ 1) : Enc := round {
  value := x.value
  lower := max 0 (min 1 x.lower)
  upper := max 0 (min 1 x.upper)
  lower_le := by
    push_cast
    exact max_le h0 (le_trans (min_le_right _ _) x.lower_le)
  le_upper := by
    push_cast
    exact le_max_iff.mpr (Or.inr (le_min h1 x.le_upper)) }

/-- Keep the value and bounds, but replace the value by an equal expression. -/
def castValue (x : Enc) (v : ℝ) (hv : v = x.value) : Enc where
  value := v
  lower := x.lower
  upper := x.upper
  lower_le := hv ▸ x.lower_le
  le_upper := hv ▸ x.le_upper

/-- The exact value is below its rational upper endpoint. -/
theorem value_le (x : Enc) : x.value ≤ (x.upper : ℝ) := x.le_upper

/-- The rational lower endpoint is below the exact value. -/
theorem le_value (x : Enc) : (x.lower : ℝ) ≤ x.value := x.lower_le

end
end Enc
end LPPMonotonicityProof.CertA
