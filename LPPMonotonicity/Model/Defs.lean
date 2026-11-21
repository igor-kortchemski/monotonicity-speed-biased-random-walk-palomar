module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The model of Theorem 1.1

The Mathlib-only model on which the public statement of Theorem 1.1
(`thm:main`) of *The speed of biased random walk on leafless
Bienaymé trees is monotone* rests: the Bienaymé tree as an i.i.d.
offspring field, the biased walk and its path law. `Challenge.lean` repeats
these definitions verbatim.

## Model (Section 2.1)

* The **offspring law** is a probability mass function `μ : PMF ℕ`.
* The **Bienaymé tree** is encoded in Ulam–Harris–Neveu form by an i.i.d.
  field `ω : List ℕ → ℕ` with law `μ` at every address (`treeLaw μ`). The root
  is `[]`; the vertex `v` has `ω v` children `v ++ [1], …, v ++ [ω v]`. The
  vertices of the tree are the addresses reached from the root this way; the
  field's values elsewhere are never read by the walk.
* The **walk state** is a vertex `vtx v` or the artificial parent `rootParent`
  of the root (`ϱ_*` in the paper, at height `-1`).
* The **`λ`-biased walk** (bias `l : ℝ≥0`) jumps from a vertex with `k`
  children to its parent with probability `l/(l+k)` and to each child with
  probability `1/(l+k)`; from `rootParent` it returns to the root. The case `l = 0`,
  `k = 0` (a leaf at bias zero, never visited when `μ 0 = 0`) is completed by a
  move to the parent (`rootParent` for the root) so that the kernel is Markov.
  Since `μ 0 = 0` and the addresses are countable, almost every field has
  `ω v ≥ 1` at every address, so this completion is almost surely never used.
* `walkLaw ω l` is the law of the walk path `ℕ → WalkState` started at the
  root, built with Mathlib's Ionescu-Tulcea construction
  `ProbabilityTheory.Kernel.trajMeasure`. By induction on time, the path stays
  almost surely in the tree reached from the root plus `rootParent`.
* `height` is the generation: `v.length` at `vtx v`, and `-1` at `rootParent`.

## The propositions behind Lemmas A.1 and A.2

The section `AppendixA` defines the closed propositions `CertACovers` and
`CertBCovers` (in `LPPMonotonicityProof.Analytic`) that the interval verifications
of Lemmas A.1 and A.2 check, with the quantities they use. They are stated here,
next to the model and with the same imports as `Challenge.lean`, so that both files
elaborate them identically; `LPPMonotonicityProof/Analytic/Certificates.lean`
documents them.
-/

@[expose] public section

section Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LPPMonotonicity

/-- A state of the walk: the artificial parent `rootParent` of the root, or the
vertex with Ulam–Harris address `v`. -/
inductive WalkState where
  | rootParent : WalkState
  | vtx (v : List ℕ) : WalkState

namespace WalkState

/-- `WalkState` is in bijection with `Option (List ℕ)`. -/
def equivOption : WalkState ≃ Option (List ℕ) where
  toFun
    | rootParent => none
    | vtx v => some v
  invFun
    | none => rootParent
    | some v => vtx v
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance : Countable WalkState := Countable.of_equiv _ equivOption.symm

/-- The discrete σ-algebra on the countable state space. -/
instance : MeasurableSpace WalkState := ⊤

instance : MeasurableSingletonClass WalkState := ⟨fun _ => trivial⟩

end WalkState

open WalkState

/-- The parent of the vertex `v`: `rootParent` for the root, otherwise the address
with its last entry removed. -/
def parentState (v : List ℕ) : WalkState :=
  if v = [] then rootParent else vtx v.dropLast

/-- The generation of a state: the length of the address, and `-1` at `rootParent`. -/
def height : WalkState → ℤ
  | rootParent => -1
  | vtx v => v.length

/-- One step of the `l`-biased walk on the tree with offspring field `ω`. -/
noncomputable def stepMeasure (l : ℝ≥0) (ω : List ℕ → ℕ) : WalkState → Measure WalkState
  | rootParent => Measure.dirac (vtx [])
  | vtx v =>
    if l = 0 ∧ ω v = 0 then Measure.dirac (parentState v)
    else
      ((l / (l + ω v) : ℝ≥0) : ℝ≥0∞) • Measure.dirac (parentState v)
        + ∑ i : Fin (ω v),
            ((1 / (l + ω v) : ℝ≥0) : ℝ≥0∞) • Measure.dirac (vtx (v ++ [i.val + 1]))

/-- The transition kernel of the `l`-biased walk. -/
noncomputable def stepKernel (l : ℝ≥0) (ω : List ℕ → ℕ) : Kernel WalkState WalkState :=
  Kernel.ofFunOfCountable (stepMeasure l ω)

instance isMarkovKernel_stepKernel (l : ℝ≥0) (ω : List ℕ → ℕ) :
    IsMarkovKernel (stepKernel l ω) := by
  refine ⟨fun x => ⟨?_⟩⟩
  cases x with
  | rootParent => simp [stepKernel, Kernel.ofFunOfCountable, stepMeasure]
  | vtx v =>
    simp only [stepKernel, Kernel.ofFunOfCountable, Kernel.coe_mk, stepMeasure]
    split_ifs with h
    · simp
    · have hpos : l + (ω v : ℝ≥0) ≠ 0 := by
        intro h0
        apply h
        refine ⟨?_, ?_⟩
        · exact (add_eq_zero.mp h0).1
        · exact_mod_cast (add_eq_zero.mp h0).2
      simp only [Measure.coe_add, Measure.coe_finsetSum, Measure.coe_smul, Pi.add_apply,
        Finset.sum_apply, Pi.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
        smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_eq_one]
      field_simp

/-- The kernel giving the next state from the path up to time `n`: it reads
only the current state. -/
noncomputable def walkKernel (l : ℝ≥0) (ω : List ℕ → ℕ) (n : ℕ) :
    Kernel (Π _ : Finset.Iic n, WalkState) WalkState :=
  (stepKernel l ω).comap (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance (l : ℝ≥0) (ω : List ℕ → ℕ) (n : ℕ) : IsMarkovKernel (walkKernel l ω n) := by
  unfold walkKernel
  infer_instance

/-- The quenched law of the path `ℕ → WalkState` of the `l`-biased walk started
at the root, on the tree with offspring field `ω`. -/
noncomputable def walkLaw (ω : List ℕ → ℕ) (l : ℝ≥0) : Measure (ℕ → WalkState) :=
  Kernel.trajMeasure (X := fun _ => WalkState) (Measure.dirac (vtx [])) (walkKernel l ω)

/-- The law of the offspring field of the Bienaymé tree: i.i.d. with law `μ`
at every address. -/
noncomputable def treeLaw (μ : PMF ℕ) : Measure (List ℕ → ℕ) :=
  Measure.infinitePi (fun _ : List ℕ => μ.toMeasure)

/-- The mean `m = E ν` of the offspring law, in `[0, ∞]`. -/
noncomputable def offspringMean (μ : PMF ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, (n : ℝ≥0∞) * μ n

/-- `E[1/ν]`, with the convention `1/0 = 0`, so that the term at `n = 0`
vanishes; in the theorem `μ 0 = 0`. -/
noncomputable def inverseMean (μ : PMF ℕ) : ℝ :=
  ∑' n : ℕ, (μ n).toReal / n

end LPPMonotonicity

end Model

/-! ## The closed propositions behind Lemmas A.1 and A.2 -/

section AppendixA

open MeasureTheory
open scoped BigOperators ENNReal

namespace LPPMonotonicityProof.Analytic

noncomputable section

/-! ## Common closed coordinates -/

/-- `Qₙ(l) = Σ_{i<n} lⁱ` (the formula of `Qgeo`). -/
def certQ (l : ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, l ^ i

/-- `ιₙ = (x + Qₙ(1+a))⁻¹`. -/
def certIota (x a : ℝ) (n : ℕ) : ℝ := (x + certQ (1 + a) n)⁻¹

/-- `k = √(1+a) = √λ`. -/
def certK (a : ℝ) : ℝ := Real.sqrt (1 + a)

/-- The prefix factor `Aₙ = k^{n-1} ιₙ` (Section 4.3; `factor` in the program `prefix.hpp`). -/
def prefixFactor (x a : ℝ) (n : ℕ) : ℝ := certK a ^ (n - 1) * certIota x a n

/-- `E Lⁿ = x ιₙ` for `L = λ^{-G}`, `G ~ Geom(ax)` on `{1,2,…}` (Lemma 4.1). -/
def lMoment (x a : ℝ) (n : ℕ) : ℝ := x * certIota x a n

/-! ## Certificate A: Lemma A.1 (`lem:large-finite`) -/

namespace ScaledLB

/-- `uₙ = Aₙ eₙ`, with `u₀ = 0` (Lemma 4.4 and the proof of Lemma A.1). -/
def u (x a : ℝ) (e : ℕ → ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else prefixFactor x a n * e n

/-- `dₙ = uₙ - uₙ₊₁` (proof of Lemma A.1). -/
def gap (x a : ℝ) (e : ℕ → ℝ) (n : ℕ) : ℝ := u x a e n - u x a e (n + 1)

/-- `P = S/w² = Σ_{n≤16} uₙ² + R`, with `R` the square tail `R₁₆` (proof of Lemma A.1). -/
def P (x a : ℝ) (e : ℕ → ℝ) (R : ℝ) : ℝ := (∑ n ∈ Finset.Icc 1 16, u x a e n ^ 2) + R

/-- `P - Q = (u₁² + Σ_{n≤16} dₙ² + T)/2`, with `T` the tail of `Σ dₙ²` (proof of Lemma A.1). -/
def D (x a : ℝ) (e : ℕ → ℝ) (T : ℝ) : ℝ :=
  (u x a e 1 ^ 2 + (∑ n ∈ Finset.Icc 1 16, gap x a e n ^ 2) + T) / 2

/-- `γ = (1+λ)/(2k)` (Lemma 4.4). -/
def gamma (a : ℝ) : ℝ := (2 + a) / (2 * certK a)

/-- `P - γQ = γ(P-Q) - (k-1)²P/(2k)` (exact when `k² = λ`; `cover.cpp` 32, first branch). -/
def PgQ (x a : ℝ) (e : ℕ → ℝ) (R T : ℝ) : ℝ :=
  gamma a * D x a e T - (certK a - 1) ^ 2 * P x a e R / (2 * certK a)

/-- `(1+λ)P/2 - kQ = k(P-Q) + (k-1)²P/2` (`cover.cpp` 33). -/
def J (x a : ℝ) (e : ℕ → ℝ) (R T : ℝ) : ℝ :=
  certK a * D x a e T + (certK a - 1) ^ 2 * P x a e R / 2

/-- `H = h/w = u₁ - xw[(1+λ)P/2 - kQ]` (proof of Lemma A.1). -/
def H (x a w : ℝ) (e : ℕ → ℝ) (R T : ℝ) : ℝ := u x a e 1 - x * w * J x a e R T

/-- The normalized `Cₙ = 1_{n=1} + xw[k(uₙ₋₁+uₙ₊₁) - (1+λ)uₙ]` (Lemma 4.4, proof of Lemma A.1). -/
def C (x a w : ℝ) (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  (if n = 1 then 1 else 0) +
    x * w * (certK a * (u x a e (n - 1) + u x a e (n + 1)) - (2 + a) * u x a e n)

/-- `Gₙ = 2Huₙ - PCₙ = 2HDₙ/w` (proof of Lemma A.1). -/
def G (x a w : ℝ) (e : ℕ → ℝ) (R T : ℝ) (n : ℕ) : ℝ :=
  2 * H x a w e R T * u x a e n - P x a e R * C x a w e n

/-- `cₙ = a²n(n²-1)/(12xλ^{3/2})`, with `λ^{3/2} = λk` (Lemma 4.5). -/
def curv (x a : ℝ) (n : ℕ) : ℝ :=
  a ^ 2 * (n : ℝ) * ((n : ℝ) ^ 2 - 1) / (12 * x * (1 + a) * certK a)

/-- The lower bounds `ℓₙ` for `∂ₓmₙ/w` (proof of Lemma A.1), at the exact point. -/
def ell (x a t w : ℝ) (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 1 then prefixFactor x a 1 * ((1 - t) / x - prefixFactor x a 1)
  else u x a e n * prefixFactor x a n *
    (curv x a n - 1 + 2 * (n : ℝ) * prefixFactor x a n * (1 - w * (2 - t)))

end ScaledLB

open ScaledLB in
/-- The retained lower bound of the proof of Lemma A.1 (`K = 16`), as one real
function of the normalized data. At the actual law, with `R = Σ_{n>16} uₙ²` and
`T = Σ_{n>16} dₙ²`, the development proves `scaledLowerBound … ≤ 2h²∂ₓV/w³`. -/
def scaledLowerBound (x a t w : ℝ) (e : ℕ → ℝ) (R T : ℝ) : ℝ :=
  w * P x a e R * PgQ x a e R T +
    (∑ n ∈ Finset.Icc 1 16, G x a w e R T n * ell x a t w e n) -
    2 * u x a e 1 * R / 17

/-- The domain of Lemma A.1 (`lem:large-finite`) in normalized coordinates. The first group
of fields is the domain of the lemma, the second the bounds on the normalized terminal moments
and the third the bounds on the tails, both from its proof. The last two fields are facts at the
actual law that the program uses without stating them: `S - γT ≥ aS/(2λ)` (Lemma 4.4) and
`Gₙ ≥ 0` (proof of Lemma A.1); see items (a2) and (a3) of `Analytic/Certificates.lean`. -/
structure ScaledDomain (x a t w : ℝ) (e : ℕ → ℝ) (R T : ℝ) : Prop where
  x_pos : 0 < x
  x_le : x ≤ 1 / 4
  a_pos : 0 < a
  a_le : a ≤ 4 / 5
  w_gt : 4 / 9 < w
  w_le_t : w ≤ t
  t_le_one : t ≤ 1
  e_one : e 1 = 1
  e_two : e 2 = t
  e_bounds : ∀ n : ℕ, 2 ≤ n → t ^ (n - 1) ≤ e n ∧ e n ≤ t
  defect_bounds : ∀ n : ℕ, 1 ≤ n → 0 ≤ e n - e (n + 1) ∧ e n - e (n + 1) ≤ 1 - t
  R_nonneg : 0 ≤ R
  R_le : R ≤ e 17 ^ 2 * certIota x a 16
  T_nonneg : 0 ≤ T
  T_le : T ≤ ScaledLB.u x a e 17 ^ 2
  /-- `S - γT ≥ aS/(2λ)` (Lemma 4.4) divided by `w²`; it justifies `imax` in `cover.cpp` 32. -/
  PgQ_ge : a * ScaledLB.P x a e R / (2 * (1 + a)) ≤ ScaledLB.PgQ x a e R T
  /-- `Gₙ = 2HDₙ/w ≥ 0` (Lemma 4.4, proof of Lemma A.1). It justifies the endpoint
  substitutions in `ℓₙ`. -/
  G_nonneg : ∀ n ∈ Finset.Icc 1 16, 0 ≤ ScaledLB.G x a w e R T n

/-- **Certificate A.** The closed proposition behind Lemma A.1 (`lem:large-finite`): the retained
lower bound is strictly positive for all normalized data in `ScaledDomain`. This is what the
interval verification of Lemma A.1 checks; at the actual law it gives the lemma. -/
def CertACovers : Prop :=
  ∀ (x a t w : ℝ) (e : ℕ → ℝ) (R T : ℝ),
    ScaledDomain x a t w e R T → 0 < scaledLowerBound x a t w e R T

/-! ## Certificate B: Lemma A.2 (`lem:joint-finite`) -/

/-- `E_L[(kLw)ʲ (c₀ + c₁·Lw + c₂·(Lw)²)]` at `w = 1 - X`, for `L` independent of `W`.
It uses `E Lⁿ = xιₙ`. This is the averaging in `L` of the proof of Theorem 5.1. -/
def rankQuad (x a : ℝ) (j : ℕ) (c₀ c₁ c₂ X : ℝ) : ℝ :=
  certK a ^ j *
    (c₀ * (1 - X) ^ j * lMoment x a j + c₁ * (1 - X) ^ (j + 1) * lMoment x a (j + 1) +
      c₂ * (1 - X) ^ (j + 2) * lMoment x a (j + 2))

/-- `Pⱼ = μⱼ(y(1-y)) = E[rankPolyP(X)]` (Section 5.1). The program's row is this divided by `h₁`. -/
def rankPolyP (x a : ℝ) (j : ℕ) (X : ℝ) : ℝ := rankQuad x a j 0 1 (-1) X

/-- `μⱼ(f_θ) = E[rankPolyF(X)]`, `f_θ(y) = y - θy² - r(1-y)(1-λy)` (Sections 3.2 and 5.1). -/
def rankPolyF (x a r θ : ℝ) (j : ℕ) (X : ℝ) : ℝ :=
  rankQuad x a j (-r) (1 + r * (2 + a)) (-θ - r * (1 + a)) X

/-- `μⱼ(g_θ) = E[rankPolyG(X)]`, with
`g_θ(y) = λy(1-y) + 2θy(1-λy) - λr(1-y)(2-(1+λ)y)` (Proposition 5.2). -/
def rankPolyG (x a r θ : ℝ) (j : ℕ) (X : ℝ) : ℝ :=
  rankQuad x a j (-2 * (1 + a) * r) ((1 + a) + 2 * θ + (1 + a) * r * (4 + a))
    (-(1 + a) - 2 * θ * (1 + a) - (1 + a) * r * (2 + a)) X

/-- `Fⱼ = E[rankPolyFJ(X)]`, with `n = j+1` and `q = 1 - ax` (Proposition 5.2). -/
def rankPolyFJ (x a : ℝ) (j : ℕ) (X : ℝ) : ℝ :=
  certK a ^ j * lMoment x a (j + 1) * (1 - X) ^ (j + 1) *
    ((1 - a * x) * (1 + a) ^ (j + 1) * certIota x a (j + 1) * certIota x a (j + 2) +
      (a / (2 + a) + (1 - a * x) * certIota x a (j + 2)) * X + X ^ 2 / 2)

/-- The rank factors as integrals against the law `ρ` of `X = 1 - W`. -/
def rankP (x a : ℝ) (ρ : Measure ℝ) (j : ℕ) : ℝ := ∫ X, rankPolyP x a j X ∂ρ
def rankF (x a : ℝ) (ρ : Measure ℝ) (r θ : ℝ) (j : ℕ) : ℝ := ∫ X, rankPolyF x a r θ j X ∂ρ
def rankG (x a : ℝ) (ρ : Measure ℝ) (r θ : ℝ) (j : ℕ) : ℝ := ∫ X, rankPolyG x a r θ j X ∂ρ
def rankFJ (x a : ℝ) (ρ : Measure ℝ) (j : ℕ) : ℝ := ∫ X, rankPolyFJ x a j X ∂ρ

/-- `d = E X = 1 - w`. -/
def dMean (ρ : Measure ℝ) : ℝ := ∫ X, X ∂ρ

/-- `η = E X²/d`. -/
def etaMean (ρ : Measure ℝ) : ℝ := (∫ X, X ^ 2 ∂ρ) / dMean ρ

/-- `E Y = h₁(1-d)` (proof of Theorem 5.1). -/
def muBox (x d : ℝ) : ℝ := x / (1 + x) * (1 - d)

/-- `E Y² = E L²·(1 - 2d + dη)` (proof of Theorem 5.1). -/
def m2Box (x a d η : ℝ) : ℝ := lMoment x a 2 * (1 - 2 * d + d * η)

/-- Lemma 5.3 (`lem:scaled-binary`) in box coordinates: `η(1 - m₂) ≤ 1 - 2μ + m₂`. -/
def binaryConstraint (x a d η : ℝ) : Prop :=
  η * (1 - m2Box x a d η) ≤ 1 - 2 * muBox x d + m2Box x a d η

/-- Admissibility of `θ` (Section 3.2): `θ ≤ 1` and `E f_θ(Y) = μ₀(f_θ) ≥ 0`. -/
def thetaAdmissible (x a : ℝ) (ρ : Measure ℝ) (r θ : ℝ) : Prop :=
  θ ≤ 1 ∧ 0 ≤ rankF x a ρ r θ 0

/-- The partial sum through rank `Jm` of `eq:scaled-profile` (Proposition 5.2), as in the
proof of Theorem 5.1. -/
def wardPartialSum (x a : ℝ) (ρ : Measure ℝ) (r θ : ℝ) (Jm : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Jm + 1),
    ((j : ℝ) + 1) * (rankP x a ρ j * rankG x a ρ r θ j + 2 * rankFJ x a ρ j * rankF x a ρ r θ j)

/-! ### The two-point speed bound (Lemma 5.4, `lem:terminal-speed`) -/

/-- The law of `L = λ^{-G}`, `P(G = g+1) = p qᵍ`, `p = ax` (Lemma 4.1). -/
def lawL (x a : ℝ) : Measure ℝ :=
  Measure.sum fun g : ℕ =>
    ENNReal.ofReal (a * x * (1 - a * x) ^ g) • Measure.dirac (((1 + a) ^ (g + 1))⁻¹)

/-- `W₊`: `1 - η₀` with probability `d₀/η₀`, `1` otherwise. Lean's `d₀/0 = 0` gives `W₊ = 1`
at `d₀ = η₀ = 0`, the convention of Lemma 5.4. -/
def wPlus (d₀ η₀ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (d₀ / η₀) • Measure.dirac (1 - η₀) +
    ENNReal.ofReal (1 - d₀ / η₀) • Measure.dirac 1

/-- The law of `Y₊ = L·W₊`, with `L` independent of `W₊` (Lemma 5.4). -/
def yPlus (x a d₀ η₀ : ℝ) : Measure ℝ :=
  ((lawL x a).prod (wPlus d₀ η₀)).map fun q => q.1 * q.2

/-- `N` in transformed variables: `E[aYY'/(1-λYY')]` (Proposition 3.1; the formula of `NY`). -/
def kernelN (a : ℝ) (ρ ρ' : Measure ℝ) : ℝ :=
  ∫ q, a * q.1 * q.2 / (1 - (1 + a) * q.1 * q.2) ∂ρ.prod ρ'

/-- `Z` in transformed variables: `E[τ/D]` (Proposition 3.1; the formula of `ZY`). -/
def kernelZ (a : ℝ) (ρ ρ' : Measure ℝ) : ℝ :=
  ∫ q, (q.1 * (1 - q.2) + q.2 * (1 - (1 + a) * q.1)) / (1 - (1 + a) * q.1 * q.2) ∂ρ.prod ρ'

/-- `r₊ = N₊/(aZ₊)`. Lemma 5.4 (`lem:terminal-speed`) gives `r = v/a ≤ r₊`. -/
def rTwoPoint (x a d₀ η₀ : ℝ) : ℝ :=
  kernelN a (yPlus x a d₀ η₀) (yPlus x a d₀ η₀) /
    (a * kernelZ a (yPlus x a d₀ η₀) (yPlus x a d₀ η₀))

/-- The four exits of the proof of Lemma A.2 for the law `ρ` of `X = 1 - W` at `(x, a)`, with
speed ratio `r = v/a` (**not** the program's `R = r/h₁`). Each disjunct is exactly the
hypothesis of the analytic lemma that turns it into `v' < 0`. They are, in order, `exit_M`,
`exit_highBias`, `exit_theta_one` and the Ward criterion `deriv_neg_of_ward_partial`. -/
def JointExit (x a : ℝ) (ρ : Measure ℝ) (r : ℝ) : Prop :=
  1 ≤ 2 * dMean ρ * etaMean ρ ∨
  8 ≤ 24 * (a * muBox x (dMean ρ) / (1 - muBox x (dMean ρ))) + 10 * a ∨
  thetaAdmissible x a ρ r 1 ∨
  ∃ θ : ℝ, thetaAdmissible x a ρ r θ ∧ ∃ K Jm : ℕ, K ≤ Jm ∧
    0 ≤ rankG x a ρ r θ K ∧ 0 < wardPartialSum x a ρ r θ Jm

/-- The hypotheses of Lemma A.2 (`lem:joint-finite`) at a law `ρ` of `X = 1 - W` and a speed
ratio `r`. At the actual law, each field is a result of the paper, proved in the development.
* The domain (Lemma A.2 and its proof) and the support and moments of `ρ` (Lemma 4.1).
* `binary`: Lemma 5.3 (`lem:scaled-binary`) in the box coordinates of the proof of Theorem 5.1.
* The speed bounds: Lemma 5.4 (`lem:terminal-speed`), Lemma 3.3 (i) (`lem:speed-ceiling`) and
  the bound `r ≤ EY/(1-EY)` of the proof of Lemma A.2.
* `theta_zero`: Lemma 3.3 (ii).
* The Ward signs: Proposition 5.2 (`prop:ward-ranks`) and the endpoint signs in its proof. -/
structure JointFeasible (x a : ℝ) (ρ : Measure ℝ) (r : ℝ) : Prop where
  x_ge : 1 / 4 ≤ x
  x_le : x ≤ 8
  a_pos : 0 < a
  a_le : a ≤ 4 / 5
  ax_le : a * x ≤ 1
  prob : IsProbabilityMeasure ρ
  support : ∀ᵐ X ∂ρ, X ∈ Set.Icc (0 : ℝ) 1
  d_pos : 0 < dMean ρ
  d_lt : dMean ρ < 5 / 9
  d_mul_x_le : dMean ρ * x ≤ 1
  d_le_eta : dMean ρ ≤ etaMean ρ
  eta_le : etaMean ρ ≤ 1
  binary : binaryConstraint x a (dMean ρ) (etaMean ρ)
  r_nonneg : 0 ≤ r
  /-- `r ≤ EY/(1-EY)` (proof of Lemma A.2; `joint.cpp` 244). -/
  r_le_mean : r ≤ muBox x (dMean ρ) / (1 - muBox x (dMean ρ))
  /-- Lemma 5.4 at every admissible corner (item (b5) of `Analytic/Certificates.lean`). -/
  r_le_twoPoint : ∀ d₀ η₀ : ℝ, 0 ≤ d₀ → d₀ ≤ dMean ρ → etaMean ρ ≤ η₀ → η₀ ≤ 1 →
    r ≤ rTwoPoint x a d₀ η₀
  /-- `θ = 0` is admissible (item (b6) of `Analytic/Certificates.lean`). -/
  theta_zero : thetaAdmissible x a ρ r 0
  P_nonneg : ∀ j : ℕ, 0 ≤ rankP x a ρ j
  FJ_nonneg : ∀ j : ℕ, 0 ≤ rankFJ x a ρ j
  F_nonneg : ∀ θ : ℝ, thetaAdmissible x a ρ r θ → ∀ j : ℕ, 0 ≤ rankF x a ρ r θ j
  G_persist : ∀ θ : ℝ, thetaAdmissible x a ρ r θ → ∀ K j : ℕ, K ≤ j →
    0 ≤ rankG x a ρ r θ K → 0 ≤ rankG x a ρ r θ j

/-- **Certificate B.** The closed proposition behind Lemma A.2 (`lem:joint-finite`): every
feasible law and speed ratio has an exit. This is what the interval verification of Lemma A.2
checks; at the actual law it gives the lemma. -/
def CertBCovers : Prop :=
  ∀ (x a : ℝ) (ρ : Measure ℝ) (r : ℝ), JointFeasible x a ρ r → JointExit x a ρ r

end

end LPPMonotonicityProof.Analytic

end AppendixA
