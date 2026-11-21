module

public import LPPMonotonicity.Model.Defs

/-!
# The closed propositions behind Lemmas A.1 and A.2

The propositions `CertACovers` and `CertBCovers` state what the interval verifications of
Lemmas A.1 and A.2 check. Their definitions are in `LPPMonotonicity/Model/Defs.lean`
(section `AppendixA`), next to the model, so that `Challenge.lean` restates them
identically; they involve no trees and no offspring law. The analytic development
(`Analytic/Defs.lean`, …) uses them as hypotheses; the two interval verifications that
prove them are not part of this repository. The coordinates are those of the paper,
`λ = 1 + a`, `k = √λ`, `x = p/a` (so `p = a x`, `q = 1 - a x`), `ιₙ = (x + Qₙ)⁻¹`,
`Aₙ = k^{n-1} ιₙ`, `E Lⁿ = x ιₙ`, `h₁ = E L = x/(1+x)`. The local helpers `certQ`,
`certIota`, `certK`, `prefixFactor`, `lMoment`, `kernelN`, `kernelZ` are
literally the formulas of `Qgeo`, `iota`, `kS`, `Acoef`, `geomY` moments, `NY`,
`ZY` of `Analytic/Defs.lean` written in `(x, a)`. Their bridges at
`x = xS μ l`, `a = l - 1` are one-line algebra.

Program line numbers below refer to the paper's verification programs, in the
`ancillary/` folder of the companion repository
`igor-kortchemski/monotonicity-speed-biased-random-walk` (commit `c561a03`):
`scaled-bands/cover.cpp`, `scaled-bands/prefix.hpp` and `scaled-bands/replay.sh` for
Lemma A.1, `joint/joint.cpp` and `joint/verify.py` for Lemma A.2. "cpp" stands for
`cover.cpp` in the first case and for `joint.cpp` in the second.

## 1. The two propositions and where the paper uses them

* `CertACovers` (Lemma A.1, `lem:large-finite`). Used by Theorem 4.8
  (`thm:upper-bands`). With `w := wbar`, `t := tW`, `e n := ηₙ/w`,
  `R := Σ_{n>16} uₙ²` and `T := Σ_{n>16} dₙ²` at the actual law, the development proves
  `scaledLowerBound x a t w e R T ≤ 2 h² ∂ₓV / w³` (proof of Lemma A.1) together with
  the fields of `ScaledDomain`: the normalized terminal-moment bounds and the tail bounds
  of the proof of Lemma A.1, and `PgQ_ge`, `G_nonneg` from Lemma 4.4 (`lem:scaled-mark`)
  and the proof of Lemma A.1. Then `CertACovers` gives `∂ₓV > 0`, the conclusion of
  Lemma A.1.
* `CertBCovers` (Lemma A.2, `lem:joint-finite`). Used by Theorem 5.1 (`thm:joint`)
  through the finite-rank box criterion of its proof. The development instantiates
  `ρ := (splitLaw μ).map (1 - Wt l ·)`, `x := xS μ l`, `a := l - 1`,
  `r := rr μ l = v/a`. It proves every field of `JointFeasible` (§3 below), and
  then turns each disjunct of `JointExit` into `v' < 0`, the conclusion of Lemma A.2.
  The disjuncts are, in order, `2dη = M ≥ 1` (Lemma 4.5 `lem:scaled-two-children` with
  `eq:scaled-mark`), `24b + 10a ≥ 8` (Theorem 3.7, `thm:above-two`), admissibility of
  `θ = 1` (Corollary 3.6, `cor:ward-source`) and the Ward partial-sum criterion
  (Proposition 5.2, `prop:ward-ranks`, in the proof of Theorem 5.1).
* The final assembly (the range cover at the end of Section 5) takes `CertACovers` and
  `CertBCovers` as hypotheses. Neither mentions `μ` or `l`.

## 2. Map: paper ↔ program lines ↔ Lean

`scaledLowerBound`: proof of Lemma A.1; `cover.cpp` 8–60, `prefix.hpp` 21–53.
* `uₙ = Aₙeₙ`, `e₁ = 1`, `e₂ = t`, moment enclosures: proof of Lemma A.1;
  cpp 15–20 (`moment`, `u`, `defect`).
* `Aₙ`, `ιₙ`, `Aₙ - Aₙ₊₁ = Aₙ(k-1+qιₙ₊₁)/k`: Section 4.3 and the proof of Lemma A.1;
  `prefix.hpp` 37–52 (`factor`, `gap`, `inv`); `ScaledLB.gap` is `uₙ - uₙ₊₁`.
* `P = Σ_{n≤16} uₙ² + R`, `P - Q = (u₁² + Σ_{n≤16} dₙ² + T)/2`: proof of Lemma A.1;
  cpp 22–30 (`S`, `D`, `tail`). These are `ScaledLB.P`, `ScaledLB.D`.
* `P - γQ = γ(P-Q) - (k-1)²P/(2k)`, `H = u₁ - xw[k(P-Q) + (k-1)²P/2]`:
  Lemma 4.4 and the proof of Lemma A.1; cpp 31–37 (`B`, `J`, `hh`). These are
  `ScaledLB.PgQ`, `ScaledLB.J`, `ScaledLB.H`.
* `Cₙ = 1_{n=1} + xw[k(uₙ₋₁+uₙ₊₁) - (1+λ)uₙ]`: Lemma 4.4 and the proof of Lemma A.1;
  cpp 43–44 (written there as `k(dₙ₋₁-dₙ) - (k-1)²uₙ`, equal when `k² = λ`).
* `Gₙ = 2Huₙ - PCₙ`: proof of Lemma A.1; cpp 46–48.
* `ℓ₁`, `ℓₙ`, `cₙ = a²n(n²-1)/(12xλk)`, `M = 2(1-w(2-t))`: Lemma 4.5 and the proof of
  Lemma A.1; cpp 40, 49–54.
* `wP(P-γQ) + Σ_{n≤16} Gₙℓₙ - 2u₁R/17`: proof of Lemma A.1; cpp 38, 39,
  55–60 (exact Bernstein form of the product of affine functions of `w`, as in the
  paper's description of the boxes).
`CertACovers`: the domain of Lemma A.1, and the boxes and target `2⁻²⁴` of its proof;
cpp 5, 62–101 (bisection), 111–113; `replay.sh` 13 (`x ∈ [0,1/4]`, `a ∈ [0,13/16]`).

`rankPoly*`: Proposition 5.2 and the proof of Theorem 5.1 (after averaging in `L`, the
factors are polynomials in `X = 1 - W`), with `E Lⁿ = xιₙ` from Lemma 4.1.
`joint.cpp` 83–143. The rows are the paper's quantities divided by `h₁`:
* `rankPolyP` ↔ `c.p` (122), `P_low/P_high` (135–136).
* `rankPolyF` ↔ `Y_low - θ·Y2_high - R·f_speed_high` (126–127, 140–142, 293).
* `rankPolyG` ↔ `λP_low + 2θQ_low - R·g_speed_high` (122–125, 137–138, 292),
  `Q = μⱼ(y(1-λy))`.
* `rankPolyFJ` ↔ `c.fl`, `floor_low` (117, 132, 139); Proposition 5.2.
`rTwoPoint`, `wPlus`, `yPlus`: Lemma 5.4 (`lem:terminal-speed`) and the speed series of
the proof of Lemma A.2; cpp 248–272.
`JointExit`: proof of Lemma A.2 and the finite-rank criterion of the proof of
Theorem 5.1; cpp 273–318 (θ, Ward loop), 345–351 (the `M` and high-bias tests),
280–283 (`θ = 1`).
`JointFeasible`: Lemma A.2 and its proof, Lemma 5.3, Lemma 5.4; cpp 227–246, 320–344,
390–395; `verify.py` 19–27, 70–72 (`ax > 1` rectangles are VOID).

## 3. Points where the programs check something different from the paper's text

Lemma A.1 (`cover.cpp`, `prefix.hpp`):
* (a1) The domain is `a ∈ [0,13/16]` (`replay.sh` 13, cpp 112), but Lemma A.1 has
  `a ≤ 4/5`. The `w`-range is `[7/16, t₊]` (cpp 10, 34), but Lemma A.1 has
  `w > 4/9`. The `x`-range includes `x = 0`. The program covers more than
  needed. Lean keeps the physical `0 < x ≤ 1/4`, `0 < a ≤ 4/5`, `4/9 < w ≤ t ≤ 1`.
* (a2) `P - γQ` is enclosed by `imax(γD - (k-1)²S/(2k), aS/(2λ))` (cpp 32). The second
  branch is the bound `S - γT ≥ aS/(2λ)` of Lemma 4.4 (`lem:scaled-mark`), which
  Appendix A never mentions. That bound holds at the actual law only, not for
  free normalized data. Hence the field `ScaledDomain.PgQ_ge`.
* (a3) The positive `1/x` term of `ℓ₁` uses `x₊` (cpp 40; the proof of Lemma A.1 says
  so). The curvature `cₙ` also uses `a₋²`, `x₊` and an upper bound on `λk` (cpp 52),
  which the paper does not mention. Replacing `ℓₙ` by a smaller number lowers `Gₙℓₙ`
  only because `Gₙ ≥ 0` (proof of Lemma A.1, true at the actual law). Hence the field
  `ScaledDomain.G_nonneg`. Without it the program's leaves do not imply the
  proposition.
* (a4) The tails use the interval forms `R ∈ [0, e₁₇²ι₁₆]` with `e₁₇ ≤ t₊`, and
  `T ∈ [0, u₁₇²]` (cpp 28–30). The remainder `-2u₁R/17` reuses the same enclosure of `R`
  (cpp 39). This matches the tail bounds of the proof of Lemma A.1.
* (a5) The clamps `one(·)` on `1-t`, `dₙ` and `p = ax` (cpp 11, 24, `prefix.hpp` 26–27)
  are consequences of the domain. The program enforces `Uₙ ≥ n`
  (`prefix.hpp` 43). The acceptance margin `2⁻²⁴` (cpp 5) is stronger than
  the Lean target `0 <`.

Lemma A.2 (`joint.cpp`, `verify.py`):
* (b1) **The `R = r/h₁` trap.** The variable `R` of `joint.cpp` is `r/h₁`, with
  `r = v/a` and `h₁ = x/(1+x)`. It is not `r`. Its initial range `[0, 1+x]` (395) means
  `r ≤ x`. Its clamp `w(1+x)/(1+xd)` (244) is `r ≤ EY/(1-EY)`, from the proof of
  Lemma A.2. `num`, `denom` (251–271) are `(N₊/a)/h₁²` and `Z₊/h₁`, so
  `num/denom = r₊/h₁` (272). `y = EY/h₁`, `y2 = EY²/h₁`, `pzero = E[Y(1-Y)]/h₁`
  (234, 238–240). `vh = E[(1-Y)(1-λY)]` is **not** divided (235–236).
* (b2) Every Ward row is the paper's factor divided by `h₁` (comment 39–41). In
  `pre` (86–100) the division happens only when `j + d > 0`. Rank `0` is handled by
  `rankfactor = 1` and the `gp`-weighted `c.u`, `c.v` (113, 128–131). The two
  speed rows `g_speed_high = λ[μⱼ((1-y)²) + μⱼ((1-y)(1-λy))]` and
  `f_speed_high = μⱼ((1-y)(1-λy))` are undivided (138, 142) and multiplied by
  `R = r/h₁`. So each row is exactly the paper's quantity divided by `h₁`, and the score
  is the paper's partial sum times `h₁⁻²`. The Lean statements use the paper's
  unnormalized quantities and `r`. A verification must instantiate the program's `R`
  as `r/h₁` and its rows as `(∫ rankPoly* dρ)/h₁`. Using `R` as `r` proves a different
  proposition.
* (b3) The speed bound also uses `r ≤ EY/(1-EY)` (244). The proof of Lemma A.2 states
  this, but the lemma does not list it as a hypothesis. It also uses the lower
  bound `Z₊/h₁ ≥ 1 - d_hi` (241, a weakening of the paper's `Z₊ ≥ EY₊ ≥ EY`).
  Hence `JointFeasible.r_le_mean`. `Z₊ ≥ EY₊` is a fact about the explicit
  two-point law of Lemma 5.4, proved once.
* (b4) The two-point moments are intersected with the direct formula
  `1 - (d₀/η₀)(1-(1-η₀)ʲ)` (255–258). That formula is exact, so this only
  tightens the enclosure.
* (b5) A box inherits the speed bound of its parent (`Rbox`, 279, 353, 377–380).
  The paper is silent on this. It is sound because a parent's corner `(d₀,η₀)`
  satisfies `d₀ ≤ d`, `η ≤ η₀ ≤ 1` for every feasible point of the child. Hence the
  hypothesis `JointFeasible.r_le_twoPoint` quantifies over **all** such
  corners. Putting `∀ d₀ η₀` in front of the conclusion instead would force a
  verification to handle the corner `d₀ = 0`.
* (b6) θ is clamped to `[0,1]` (273–278). When the computed bound is negative it
  falls back on `θ = 0` with no check. That needs `E f₀(Y) ≥ 0`
  (Lemma 3.3 (ii), `lem:speed-ceiling`, with the admissibility of Section 3.2). Hence
  `JointFeasible.theta_zero`. `θ = 1` is detected through `pzero` (276).
* (b7) The Ward loop clamps the lower bounds of `Pⱼ, Fⱼ, μⱼ(f_θ)` at `0`
  (295, 308–309). Before the crossing it uses the upper bound of `Pⱼ` (302–306).
  After the first nonnegative `μ_K(g_θ)` it clamps `μⱼ(g_θ)` at `0` (296–299).
  These are the sign facts of Proposition 5.2 (`prop:ward-ranks`), which hold at
  the actual law. Hence the fields `P_nonneg`, `FJ_nonneg`, `F_nonneg` and
  `G_persist`. Ranks stop at `22` (`M`, 22, 288; as in the proof of Lemma A.2).
* (b8) The binary narrowing is iterated four times on the upper `η` endpoint
  (334–344). Boxes with `η_hi < d_lo`, `d_lo·x > 1` or a narrowed `η_hi < d_lo`
  are excluded (324–327, 338–341). In a Lean verification, a leaf for an excluded
  box refutes `JointFeasible`.
* (b9) The domain is `a ∈ [0,13/16]` (390, `verify.py` 27), but Lemma A.2 has
  `a ≤ 4/5`. Rectangles with `x₋a₋ > 1` are VOID (`verify.py` 70–72). The program
  does not use the physical `d > 0`, `d < 5/9` strictly (start box
  `[0, min(5/9,1/x)]`, 394).
* (b10) The Bernstein check uses integer-index coordinates `c₀ + l i + c i²`
  with directed rounding (203–213; the Bernstein certificate of the proof of
  Lemma A.2). This is the same inequality `E P(X) ≥ c₀ + 28d(l + c(1+27η))`.
* (b11) The paper uses the symbol `d₀` both for `a/log λ` (Section 5.1) and for the
  two-point parameter (Lemma 5.4). This is not an error, but the Lean names keep them
  apart.

No contradiction between the paper's formulas and the programs was found. All
differences above are either over-coverage or uses of facts the paper proves
elsewhere. Each such fact is a named field of `ScaledDomain`/`JointFeasible`.
-/
