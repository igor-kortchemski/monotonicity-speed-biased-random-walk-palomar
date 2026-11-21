module

public import LPPMonotonicityProof.Analytic.ScaledSeries.Identities
public import LPPMonotonicityProof.Analytic.ScaledSeries.Deriv
public import LPPMonotonicityProof.Analytic.ScaledSeries.Series

/-!
# Moment series, scaled form, differentiation

Re-export of the modules on the moment series of Section 4.3: expansion of
Proposition 3.1 (`prop:collapse`) in the scaled moments, the reparametrisation
`V = v/p`, and term-by-term differentiation.

* `ScaledSeries/Identities.lean`: `Nval_div_p_eq`, `Zval_eq`, `Vsc_eq`, `hsc_bounds`,
  `mMom_succ_le`, the geometric envelope `mMom_mem` (`0 ≤ mₙ ≤ k·k⁻ⁿ`) and the
  summability of `S` and `T`.
* `ScaledSeries/Deriv.lean`: the children envelope `childEnv` (integrable under
  `splitLaw`), `∂_l W` on regular trees, `hasDerivAt_etaW`, `abs_deriv_etaW_le`.
* `ScaledSeries/Series.lean`: the closed form of `Aₙ` and its derivative `Aderiv`,
  `mMom'` (defined as `deriv (fun l => mMom μ l n) l`), `hasDerivAt_mMom`,
  `mMom'_summable_bound` (on `[a, b] ⊂ (1, m)`) and `mMom'_summable_bound_compact`,
  `hasDerivAt_Ssc`, `hasDerivAt_Tsc`, `hasDerivAt_hsc` (with explicit derivatives
  `SscDeriv`, `TscDeriv`, `hscDeriv`), and `dx_Vsc`.

**Remarks on the statements.**
* `Vsc` is defined in `Analytic/Defs.lean` through `speedValueProv`; `dx_Vsc` is stated
  with `speedValueProv`, which has the same body as `Speed.speedValue`
  (`NvalProv`/`ZvalProv` are definitionally `Nval`/`Zval`). It needs no hypothesis.
* `hasDerivAt_etaW` holds for every `n`, including `n = 0`.
* `mMom'_summable_bound` also records `0 ≤ C` and `0 ≤ ρ`.
-/
