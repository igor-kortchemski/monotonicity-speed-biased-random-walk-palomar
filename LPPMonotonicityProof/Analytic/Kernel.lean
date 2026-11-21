module

public import LPPMonotonicityProof.Escape.FiniteFlow
public import LPPMonotonicityProof.Analytic.Defs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Pointwise calculus for the two-copy kernel

This module differentiates `F_c(b, b') = (bb' - c τ) / D(b, b')` in the bias and in
the first escape, and proves the pointwise algebraic identities used in the proof of
Proposition 2.6 (`prop:cost`).  The denominator `D` is `DfunProv`, the copy of
`Speed.Dfun` defined in `LPPMonotonicityProof.Analytic.Defs`.
-/

@[expose] public section

namespace LPPMonotonicityProof.Analytic

/-- Derivative in the bias of `F_c = (bb' - c τ) / D`. -/
theorem hasDerivAt_F_l (l c b b' : ℝ) (hD : DfunProv l b b' ≠ 0) :
    HasDerivAt (fun l => (b * b' - c * tau b b') / DfunProv l b b')
      (-(b * b' - c * tau b b') / DfunProv l b b' ^ 2) l := by
  have hderiv : HasDerivAt (fun l : ℝ => DfunProv l b b') 1 l := by
    convert ((hasDerivAt_id l).sub_const 1).add_const (b + b' - b * b') using 1
    funext x
    simp [DfunProv]
    ring
  convert ((hasDerivAt_const l (b * b' - c * tau b b')).div hderiv hD) using 1
  simp

/-- Derivative in the first escape argument of `F_c = (bb' - c τ) / D`. -/
theorem hasDerivAt_F_b (c l b' b : ℝ) (hD : DfunProv l b b' ≠ 0) :
    HasDerivAt (fun b => (b * b' - c * tau b b') / DfunProv l b b')
      (Pol l c b' / DfunProv l b b' ^ 2) b := by
  have hnum : HasDerivAt (fun b : ℝ => b * b' - c * tau b b')
      (b' - c * (1 - b')) b := by
    convert (((hasDerivAt_id b).mul_const b').sub
      ((hasDerivAt_const b c).mul
        (((hasDerivAt_id b).add_const b').sub ((hasDerivAt_id b).mul_const b')))) using 1
    · funext x
      simp [tau]
    · simp
  have hden : HasDerivAt (fun b : ℝ => DfunProv l b b') (1 - b') b := by
    convert ((((hasDerivAt_const b (l - 1)).add (hasDerivAt_id b)).add_const b').sub
      ((hasDerivAt_id b).mul_const b')) using 1
    · funext x
      simp [DfunProv]
    · simp
  convert hnum.div hden hD using 1
  field_simp
  simp only [Pol, tau, DfunProv] at *
  ring

/-- The pointwise identity behind equation (2.4) (`eq:half-response`), from the proof of
Proposition 2.6 (`prop:cost`). -/
theorem half_response_identity (l v b b' : ℝ) :
    l * (b * b' - v * tau b b') +
        ((1 - b) * Pol l v b' + (1 - b') * Pol l v b) / 2 =
      DfunProv l b b' * ((b + b') / 2 - v) := by
  simp only [Pol, tau, DfunProv]
  ring

/-- Sum of the two one-copy kernels. -/
theorem kernel_sum (l b b' : ℝ) (hD : DfunProv l b b' ≠ 0) :
    b / DfunProv l b b' + b' / DfunProv l b b' =
      (b * b' + tau b b') / DfunProv l b b' := by
  field_simp
  simp only [tau, DfunProv] at *
  ring

/-- The denominator of `Zval` is the complement of the reset kernel. -/
theorem kernel_Z_eq (l b b' : ℝ) (hD : DfunProv l b b' ≠ 0) :
    tau b b' / DfunProv l b b' = 1 - (l - 1) / DfunProv l b b' := by
  field_simp
  simp only [tau, DfunProv] at *
  ring

end LPPMonotonicityProof.Analytic
