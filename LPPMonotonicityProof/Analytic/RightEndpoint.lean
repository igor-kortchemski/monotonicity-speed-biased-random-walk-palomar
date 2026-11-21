module

public import LPPMonotonicityProof.Analytic.Interface2
public import LPPMonotonicityProof.Analytic.RegularityExport
public import LPPMonotonicityProof.Analytic.Critical
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The right endpoint at zero

This module proves the statements of Proposition 2.6 (`prop:cost`) at zero bias,
following the right-neighbourhood argument in its proof. For an offspring law with
`P(ν = 0) = 0` and `1 < m < ∞`, the speed `v = Speed.speedValue μ` satisfies

* `v(l) → 1` as `l → 0+` (`tendsto_speedValue_zero`);
* `v'₊(0) = -2 E[1/ν]` (`hasDerivWithinAt_speedValue_zero`), the right-derivative
  clause of Theorem 1.1, also stated for the public `PMF` model
  (`hasDerivWithinAt_speedValue_zero_pmf`);
* `v'(l) → -2 E[1/ν]` as `l → 0+` (`tendsto_deriv_speedValue_zero`).

**Route.** Put `A_l = aidE μ l 1` and `C_l = aidE μ l k`, so that
`aidE μ l (k ± l) = C_l ± l A_l` and, by the Aïdékon quotient (2.1),
`v = (C - lA)/(C + lA)` on `(0, 1/2]`. There, on regular trees, `β ∈ [1 - l, 1]`, so
the Aïdékon denominator is at least `ν/2`; with `|β̇| ≤ 2` both the integrands and
their `l`-derivatives are bounded by constants. Dominated convergence gives
`A → E[1/ν]`, `C → 1`; differentiation under the integral gives `A`, `C`
differentiable on `(0, 1/2)` with derivatives bounded by `48`. The slope is
`(v l - 1)/l = -2A/(C + lA)`, and `v' = (2l(AC' - CA') - 2AC)/(C + lA)²`.

(The paper writes `1 - v = 2λ E f / E[(ν+λ) f]` with `f = β₀/(a+β₀+S)`; the split
into `A` and `C` keeps the weight independent of `l` for differentiation.)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-! ### Pointwise facts on regular trees for small bias -/

omit [IsProbabilityMeasure μ] in
private lemma re_escape_bounds {T : Tree} (hT : RegTree μ T) {l : ℝ} (hl : 0 < l)
    (hl1 : l < 1) : 1 - l ≤ escape l T ∧ escape l T ≤ 1 :=
  ⟨escape_ge hl hl1 T (fun v hv => Nat.lt_of_lt_of_le Nat.zero_lt_one (hT.1.1 v hv)),
    (escape_mem_Icc hl T).2⟩

omit [IsProbabilityMeasure μ] in
private lemma re_one_le_degree {T : Tree} (hT : RegTree μ T) : (1 : ℝ) ≤ degree T := by
  have h1 : 1 ≤ degree T := hT.1.1 [] (present_nil T)
  exact_mod_cast h1

private lemma re_childSum_lower {T : Tree} (hT : RegTree μ T) {l : ℝ} (hl : 0 < l)
    (hl1 : l < 1) : (degree T : ℝ) * (1 - l) ≤ childSum l T := by
  have h1 : ∑ _i : Fin (degree T), (1 - l) ≤
      ∑ i : Fin (degree T), escape l (child T (i.val + 1)) :=
    Finset.sum_le_sum fun i _ => (re_escape_bounds (regTree_child hT i) hl hl1).1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  exact h1

private lemma re_den_ge {T T' : Tree} (hT : RegTree μ T) (hT' : RegTree μ T') {l : ℝ}
    (hl : 0 < l) (hl2 : l ≤ 1 / 2) :
    (degree T : ℝ) / 2 ≤ l - 1 + escape l T' + childSum l T := by
  have hl1 : l < 1 := by linarith
  have hb := (re_escape_bounds hT' hl hl1).1
  have hS := re_childSum_lower hT hl hl1
  have hν := re_one_le_degree hT
  have hprod : 0 ≤ (degree T : ℝ) * (1 / 2 - l) := mul_nonneg (by linarith) (by linarith)
  nlinarith

omit [IsProbabilityMeasure μ] in
private lemma tendsto_escape_zero {T : Tree} (hT : RegTree μ T) :
    Tendsto (fun l => escape l T) (𝓝[>] 0) (𝓝 1) := by
  have hid : Tendsto (fun l : ℝ => l) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hlow0 : Tendsto (fun l : ℝ => 1 - l) (𝓝[>] (0 : ℝ)) (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hid
  have hlow : Tendsto (fun l : ℝ => 1 - l) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using hlow0
  have hev : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hev] with l hl
    exact (re_escape_bounds hT hl.1 hl.2).1
  · filter_upwards [hev] with l hl
    exact (re_escape_bounds hT hl.1 hl.2).2

private lemma tendsto_childSum_zero {T : Tree} (hT : RegTree μ T) :
    Tendsto (fun l => childSum l T) (𝓝[>] 0) (𝓝 (degree T : ℝ)) := by
  have h1 : Tendsto (fun l => ∑ i : Fin (degree T), escape l (child T (i.val + 1)))
      (𝓝[>] 0) (𝓝 (∑ _i : Fin (degree T), (1 : ℝ))) :=
    tendsto_finsetSum _ fun i _ => tendsto_escape_zero (regTree_child hT i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h1
  exact h1

private lemma ae_reg_pair (h : OffspringHyp μ) :
    ∀ᵐ p ∂(GW μ).prod (GW μ), RegTree μ p.1 ∧ RegTree μ p.2 := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := GW μ) (ν := GW μ)).ae
      (ae_regTree h),
    (Measure.quasiMeasurePreserving_snd (μ := GW μ) (ν := GW μ)).ae (ae_regTree h)]
    with p h1 h2
  exact ⟨h1, h2⟩

/-! ### The Aïdékon integrand and its `l`-derivative -/

/-- The integrand of `aidE μ l g`. -/
private noncomputable def aidF (g : ℕ → ℝ) (l : ℝ) (p : Tree × Tree) : ℝ :=
  g (degree p.1) * escape l p.2 / (l - 1 + escape l p.2 + childSum l p.1)

/-- The Aïdékon denominator `a + β₀ + S`. -/
private noncomputable def aidD (l : ℝ) (p : Tree × Tree) : ℝ :=
  l - 1 + escape l p.2 + childSum l p.1

private noncomputable def dEsc (l : ℝ) (T : Tree) : ℝ := deriv (fun x => escape x T) l

private noncomputable def dChild (l : ℝ) (T : Tree) : ℝ :=
  ∑ i : Fin (degree T), dEsc l (child T (i.val + 1))

/-- The `l`-derivative of `aidF g · p` on regular pairs. -/
private noncomputable def aidF' (g : ℕ → ℝ) (l : ℝ) (p : Tree × Tree) : ℝ :=
  g (degree p.1) * (dEsc l p.2 * aidD l p - escape l p.2 * (1 + dEsc l p.2 + dChild l p.1)) /
    aidD l p ^ 2

private lemma measurable_aidF (g : ℕ → ℝ) (l : ℝ) : Measurable (aidF g l) := by
  show Measurable (fun p : Tree × Tree =>
    g (degree p.1) * escape l p.2 / (l - 1 + escape l p.2 + childSum l p.1))
  exact (((measurable_of_countable g).comp
    (continuous_degree.measurable.comp measurable_fst)).mul
    ((measurable_escape l).comp measurable_snd)).div
    (((measurable_const.sub measurable_const).add
      ((measurable_escape l).comp measurable_snd)).add
      ((measurable_childSum l).comp measurable_fst))

private lemma abs_aidF_le {g : ℕ → ℝ} (hg : ∀ k : ℕ, |g k| ≤ (k : ℝ) + 1)
    {p : Tree × Tree} (hp : RegTree μ p.1 ∧ RegTree μ p.2) {l : ℝ} (hl : 0 < l)
    (hl2 : l ≤ 1 / 2) : |aidF g l p| ≤ 4 := by
  have hl1 : l < 1 := by linarith
  have hν := re_one_le_degree hp.1
  have hD := re_den_ge hp.1 hp.2 hl hl2
  have hb := re_escape_bounds hp.2 hl hl1
  have hb0 : 0 ≤ escape l p.2 := by linarith [hb.1]
  have hDpos : 0 < l - 1 + escape l p.2 + childSum l p.1 := by linarith
  have hgk := hg (degree p.1)
  unfold aidF
  rw [abs_div, abs_mul, abs_of_nonneg hb0, abs_of_pos hDpos, div_le_iff₀ hDpos]
  have : |g (degree p.1)| * escape l p.2 ≤ |g (degree p.1)| :=
    mul_le_of_le_one_right (abs_nonneg _) hb.2
  linarith

private lemma re_hasDerivAt_escape {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) : HasDerivAt (fun x => escape x T) (dEsc l T) l :=
  (((escape_contDiffOn hT).differentiableOn (by norm_num) l hl).differentiableAt
    (isOpen_Ioo.mem_nhds hl)).hasDerivAt

private lemma hasDerivAt_aidF {g : ℕ → ℝ} {p : Tree × Tree}
    (hp : RegTree μ p.1 ∧ RegTree μ p.2) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ))
    (hD : aidD l p ≠ 0) : HasDerivAt (fun x => aidF g x p) (aidF' g l p) l := by
  have hb := re_hasDerivAt_escape hp.2 hl
  have hS : HasDerivAt (fun x => childSum x p.1) (dChild l p.1) l := by
    unfold childSum dChild
    exact HasDerivAt.fun_sum fun i _ => re_hasDerivAt_escape (regTree_child hp.1 i) hl
  have hDen : HasDerivAt (fun x => x - 1 + escape x p.2 + childSum x p.1)
      (1 + dEsc l p.2 + dChild l p.1) l :=
    (((hasDerivAt_id' l).sub_const 1).add hb).add hS
  have hNum : HasDerivAt (fun x => g (degree p.1) * escape x p.2)
      (g (degree p.1) * dEsc l p.2) l := hb.const_mul _
  have hq := hNum.div hDen hD
  unfold aidF aidF'
  convert hq using 1
  unfold aidD
  ring

private lemma abs_aidF'_le (h : OffspringHyp μ) {g : ℕ → ℝ}
    (hg : ∀ k : ℕ, |g k| ≤ (k : ℝ) + 1) {p : Tree × Tree}
    (hp : RegTree μ p.1 ∧ RegTree μ p.2) {l : ℝ} (hl : 0 < l) (hl2 : l ≤ 1 / 2) :
    |aidF' g l p| ≤ 48 := by
  have hl1 : l < 1 := by linarith
  have hν := re_one_le_degree hp.1
  have hD : (degree p.1 : ℝ) / 2 ≤ aidD l p := re_den_ge hp.1 hp.2 hl hl2
  have hb := re_escape_bounds hp.2 hl hl1
  have hb0 : 0 ≤ escape l p.2 := by linarith [hb.1]
  have hDpos : 0 < aidD l p := by linarith
  have hb' : |dEsc l p.2| ≤ 2 := abs_deriv_escape_le_two h hp.2 hl hl2
  have hS' : |dChild l p.1| ≤ 2 * degree p.1 := by
    unfold dChild
    calc |∑ i : Fin (degree p.1), dEsc l (child p.1 (i.val + 1))|
        ≤ ∑ i : Fin (degree p.1), |dEsc l (child p.1 (i.val + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (degree p.1), (2 : ℝ) :=
          Finset.sum_le_sum fun i _ =>
            abs_deriv_escape_le_two h (regTree_child hp.1 i) hl hl2
      _ = 2 * degree p.1 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hb'' := abs_le.mp hb'
  have hS'' := abs_le.mp hS'
  have hDer : |1 + dEsc l p.2 + dChild l p.1| ≤ 3 + 2 * degree p.1 := by
    rw [abs_le]; constructor <;> linarith [hb''.1, hb''.2, hS''.1, hS''.2]
  have e1 : |dEsc l p.2 * aidD l p| ≤ 2 * aidD l p := by
    rw [abs_mul, abs_of_pos hDpos]
    exact mul_le_mul_of_nonneg_right hb' hDpos.le
  have e2 : |escape l p.2 * (1 + dEsc l p.2 + dChild l p.1)| ≤ 3 + 2 * degree p.1 := by
    rw [abs_mul, abs_of_nonneg hb0]
    calc escape l p.2 * |1 + dEsc l p.2 + dChild l p.1|
        ≤ 1 * |1 + dEsc l p.2 + dChild l p.1| :=
          mul_le_mul_of_nonneg_right hb.2 (abs_nonneg _)
      _ ≤ 3 + 2 * degree p.1 := by rw [one_mul]; exact hDer
  have hX : |dEsc l p.2 * aidD l p - escape l p.2 * (1 + dEsc l p.2 + dChild l p.1)|
      ≤ 2 * aidD l p + 5 * degree p.1 := by
    have e1' := abs_le.mp e1
    have e2' := abs_le.mp e2
    rw [abs_le]; constructor <;> linarith [e1'.1, e1'.2, e2'.1, e2'.2]
  have hgk : |g (degree p.1)| ≤ 2 * degree p.1 := by linarith [hg (degree p.1)]
  have hprod : |g (degree p.1)| *
      |dEsc l p.2 * aidD l p - escape l p.2 * (1 + dEsc l p.2 + dChild l p.1)|
      ≤ (2 * degree p.1) * (2 * aidD l p + 5 * degree p.1) :=
    mul_le_mul hgk hX (abs_nonneg _) (by linarith)
  have hν2D : (degree p.1 : ℝ) ≤ 2 * aidD l p := by linarith
  have k1 := mul_le_mul_of_nonneg_left hν2D (by linarith : (0 : ℝ) ≤ 4 * aidD l p)
  have k2 := mul_le_mul hν2D hν2D (by linarith) (by linarith)
  unfold aidF'
  rw [abs_div, abs_mul, abs_of_pos (pow_pos hDpos 2), div_le_iff₀ (pow_pos hDpos 2)]
  nlinarith

/-! ### Integrability, bounds, limits and derivatives of `aidE` -/

private lemma integrable_aidF (h : OffspringHyp μ) {g : ℕ → ℝ}
    (hg : ∀ k : ℕ, |g k| ≤ (k : ℝ) + 1) {l : ℝ} (hl : 0 < l) (hl2 : l ≤ 1 / 2) :
    Integrable (aidF g l) ((GW μ).prod (GW μ)) := by
  refine Integrable.of_bound (measurable_aidF g l).aestronglyMeasurable 4 ?_
  filter_upwards [ae_reg_pair h] with p hp
  rw [Real.norm_eq_abs]
  exact abs_aidF_le hg hp hl hl2

private lemma abs_aidE_le (h : OffspringHyp μ) {g : ℕ → ℝ}
    (hg : ∀ k : ℕ, |g k| ≤ (k : ℝ) + 1) {l : ℝ} (hl : 0 < l) (hl2 : l ≤ 1 / 2) :
    |aidE μ l g| ≤ 4 := by
  have hb : ∀ᵐ p ∂(GW μ).prod (GW μ), ‖aidF g l p‖ ≤ 4 := by
    filter_upwards [ae_reg_pair h] with p hp
    rw [Real.norm_eq_abs]
    exact abs_aidF_le hg hp hl hl2
  have := norm_integral_le_of_norm_le_const hb
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
  exact this

private lemma abs_integral_aidF'_le (h : OffspringHyp μ) {g : ℕ → ℝ}
    (hg : ∀ k : ℕ, |g k| ≤ (k : ℝ) + 1) {l : ℝ} (hl : 0 < l) (hl2 : l ≤ 1 / 2) :
    |∫ p, aidF' g l p ∂(GW μ).prod (GW μ)| ≤ 48 := by
  have hb : ∀ᵐ p ∂(GW μ).prod (GW μ), ‖aidF' g l p‖ ≤ 48 := by
    filter_upwards [ae_reg_pair h] with p hp
    rw [Real.norm_eq_abs]
    exact abs_aidF'_le h hg hp hl hl2
  have := norm_integral_le_of_norm_le_const hb
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
  exact this

private lemma tendsto_aidF {g : ℕ → ℝ} {p : Tree × Tree}
    (hp : RegTree μ p.1 ∧ RegTree μ p.2) :
    Tendsto (fun l => aidF g l p) (𝓝[>] 0) (𝓝 (g (degree p.1) / degree p.1)) := by
  have hb := tendsto_escape_zero hp.2
  have hS := tendsto_childSum_zero hp.1
  have hid : Tendsto (fun l : ℝ => l) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hD : Tendsto (fun l => l - 1 + escape l p.2 + childSum l p.1) (𝓝[>] 0)
      (𝓝 (0 - 1 + 1 + degree p.1)) := ((hid.sub_const 1).add hb).add hS
  have hν := re_one_le_degree hp.1
  have hne : (0 : ℝ) - 1 + 1 + degree p.1 ≠ 0 :=
    (by linarith : (0 : ℝ) < 0 - 1 + 1 + degree p.1).ne'
  have hq := (hb.const_mul (g (degree p.1))).div hD hne
  have hfun : (fun l => aidF g l p) =
      (fun l => g (degree p.1) * escape l p.2) /
        (fun l => l - 1 + escape l p.2 + childSum l p.1) := rfl
  rw [hfun]
  convert hq using 2
  ring

private lemma tendsto_aidE (h : OffspringHyp μ) {g : ℕ → ℝ}
    (hg : ∀ k : ℕ, |g k| ≤ (k : ℝ) + 1) :
    Tendsto (fun l => aidE μ l g) (𝓝[>] 0)
      (𝓝 (∫ p, g (degree p.1) / degree p.1 ∂(GW μ).prod (GW μ))) := by
  have hev : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  show Tendsto (fun l => ∫ p, aidF g l p ∂(GW μ).prod (GW μ)) _ _
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (4 : ℝ))
    (Filter.Eventually.of_forall fun l => (measurable_aidF g l).aestronglyMeasurable) ?_
    (integrable_const _) ?_
  · filter_upwards [hev] with l hl
    filter_upwards [ae_reg_pair h] with p hp
    rw [Real.norm_eq_abs]
    exact abs_aidF_le hg hp hl.1 hl.2.le
  · filter_upwards [ae_reg_pair h] with p hp
    exact tendsto_aidF hp

private lemma hasDerivAt_of_ae_hasDerivAt {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {F : ℝ → α → ℝ} {F' : α → ℝ} {x₀ : ℝ} (hF : ∀ x, Measurable (F x))
    (hd : ∀ᵐ a ∂ν, HasDerivAt (fun x => F x a) (F' a) x₀) : AEStronglyMeasurable F' ν := by
  let t : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ))⁻¹
  have ht0 : Tendsto t atTop (𝓝 0) := by
    simpa only [t, Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht0, Filter.Eventually.of_forall fun n => ?_⟩
    change (((n + 1 : ℕ) : ℝ))⁻¹ ≠ 0
    exact inv_ne_zero (by positivity)
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n a => (t n)⁻¹ • (F (x₀ + t n) a - F x₀ a)) (fun n => ?_) ?_
  · exact (((hF (x₀ + t n)).sub (hF x₀)).const_smul (t n)⁻¹).aestronglyMeasurable
  · filter_upwards [hd] with a ha
    exact ha.tendsto_slope_zero.comp ht

private lemma hasDerivAt_aidE (h : OffspringHyp μ) {g : ℕ → ℝ}
    (hg : ∀ k : ℕ, |g k| ≤ (k : ℝ) + 1) {l₀ : ℝ} (hl₀ : l₀ ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt (fun l => aidE μ l g) (∫ p, aidF' g l₀ p ∂(GW μ).prod (GW μ)) l₀ := by
  have hm := one_lt_mean_of_hyp h
  have hs : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝 l₀ := isOpen_Ioo.mem_nhds hl₀
  have hdiff : ∀ᵐ p ∂(GW μ).prod (GW μ), ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2),
      HasDerivAt (fun y => aidF g y p) (aidF' g x p) x := by
    filter_upwards [ae_reg_pair h] with p hp x hx
    have hD : (degree p.1 : ℝ) / 2 ≤ aidD x p := re_den_ge hp.1 hp.2 hx.1 hx.2.le
    have hν := re_one_le_degree hp.1
    exact hasDerivAt_aidF hp ⟨hx.1, by linarith [hx.2]⟩
      (by linarith : (0 : ℝ) < aidD x p).ne'
  have hmeas : AEStronglyMeasurable (fun p => aidF' g l₀ p) ((GW μ).prod (GW μ)) := by
    apply hasDerivAt_of_ae_hasDerivAt (F := fun x p => aidF g x p) (x₀ := l₀)
      (fun x => measurable_aidF g x)
    filter_upwards [hdiff] with p hp
    exact hp l₀ hl₀
  have hbound : ∀ᵐ p ∂(GW μ).prod (GW μ), ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ‖aidF' g x p‖ ≤ (48 : ℝ) := by
    filter_upwards [ae_reg_pair h] with p hp x hx
    rw [Real.norm_eq_abs]
    exact abs_aidF'_le h hg hp hx.1 hx.2.le
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => (48 : ℝ))
    (F := fun x p => aidF g x p) (F' := fun x p => aidF' g x p) hs
    (Filter.Eventually.of_forall fun x => (measurable_aidF g x).aestronglyMeasurable)
    (integrable_aidF h hg hl₀.1 hl₀.2.le) hmeas hbound (integrable_const _) hdiff).2

/-! ### The two weights `A` and `C` -/

private lemma one_growth : ∀ k : ℕ, |(fun _ : ℕ => (1 : ℝ)) k| ≤ (k : ℝ) + 1 := fun k => by
  show |(1 : ℝ)| ≤ (k : ℝ) + 1
  rw [abs_one]
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

private lemma cast_growth : ∀ k : ℕ, |(fun k : ℕ => (k : ℝ)) k| ≤ (k : ℝ) + 1 := fun k => by
  show |(k : ℝ)| ≤ (k : ℝ) + 1
  rw [abs_of_nonneg (Nat.cast_nonneg k)]
  linarith

/-- `A_l = E[β₀/(a+β₀+S)]`. -/
private noncomputable def Af (ν : Measure ℕ) [IsProbabilityMeasure ν] (l : ℝ) : ℝ :=
  aidE ν l (fun _ => 1)

/-- `C_l = E[ν β₀/(a+β₀+S)]`. -/
private noncomputable def Cf (ν : Measure ℕ) [IsProbabilityMeasure ν] (l : ℝ) : ℝ :=
  aidE ν l (fun k => (k : ℝ))

private noncomputable def dAf (ν : Measure ℕ) [IsProbabilityMeasure ν] (l : ℝ) : ℝ :=
  ∫ p, aidF' (fun _ : ℕ => (1 : ℝ)) l p ∂(GW ν).prod (GW ν)

private noncomputable def dCf (ν : Measure ℕ) [IsProbabilityMeasure ν] (l : ℝ) : ℝ :=
  ∫ p, aidF' (fun k : ℕ => (k : ℝ)) l p ∂(GW ν).prod (GW ν)

private lemma aidE_plus (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hl2 : l ≤ 1 / 2) :
    aidE μ l (fun k : ℕ => (k : ℝ) + l) = Cf μ l + l * Af μ l := by
  have hC := integrable_aidF h (g := fun k : ℕ => (k : ℝ)) cast_growth hl hl2
  have hA := (integrable_aidF h (g := fun _ : ℕ => (1 : ℝ)) one_growth hl hl2).const_mul l
  show (∫ p, aidF (fun k : ℕ => (k : ℝ) + l) l p ∂(GW μ).prod (GW μ)) =
    (∫ p, aidF (fun k : ℕ => (k : ℝ)) l p ∂(GW μ).prod (GW μ)) +
      l * ∫ p, aidF (fun _ : ℕ => (1 : ℝ)) l p ∂(GW μ).prod (GW μ)
  rw [← integral_const_mul, ← integral_add hC hA]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [aidF]
  ring

private lemma aidE_minus (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hl2 : l ≤ 1 / 2) :
    aidE μ l (fun k : ℕ => (k : ℝ) - l) = Cf μ l - l * Af μ l := by
  have hC := integrable_aidF h (g := fun k : ℕ => (k : ℝ)) cast_growth hl hl2
  have hA := (integrable_aidF h (g := fun _ : ℕ => (1 : ℝ)) one_growth hl hl2).const_mul l
  show (∫ p, aidF (fun k : ℕ => (k : ℝ) - l) l p ∂(GW μ).prod (GW μ)) =
    (∫ p, aidF (fun k : ℕ => (k : ℝ)) l p ∂(GW μ).prod (GW μ)) -
      l * ∫ p, aidF (fun _ : ℕ => (1 : ℝ)) l p ∂(GW μ).prod (GW μ)
  rw [← integral_const_mul, ← integral_sub hC hA]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [aidF]
  ring

private lemma B_pos (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hl2 : l ≤ 1 / 2) :
    0 < Cf μ l + l * Af μ l := by
  have hpos := aidE_pos h hl (by linarith [one_lt_mean_of_hyp h] : l < mean μ)
  rwa [aidE_plus h hl hl2] at hpos

/-- The Aïdékon quotient (2.1) on `(0, 1/2]`: `v = (C - lA)/(C + lA)`. -/
private lemma speedValue_eq_CA (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hl2 : l ≤ 1 / 2) :
    Speed.speedValue μ l = (Cf μ l - l * Af μ l) / (Cf μ l + l * Af μ l) := by
  rw [speedValue_eq_speedValueProv,
    speedValue_eq_aid h hl (by linarith [one_lt_mean_of_hyp h]),
    aidE_plus h hl hl2, aidE_minus h hl hl2]

private lemma integral_fst_degree (F : ℕ → ℝ) :
    ∫ p, F (degree p.1) ∂(GW μ).prod (GW μ) = ∫ k, F k ∂μ := by
  have h1 : ∫ p, F (degree p.1) ∂(GW μ).prod (GW μ) =
      (GW μ).real Set.univ • ∫ T, F (degree T) ∂GW μ :=
    integral_fun_fst (fun T : Tree => F (degree T))
  have h2 : ∫ k, F k ∂(GW μ).map degree = ∫ T, F (degree T) ∂GW μ :=
    integral_map continuous_degree.measurable.aemeasurable
      (measurable_of_countable F).aestronglyMeasurable
  rw [h1, ← h2, bienaymeLaw_map_degree, probReal_univ, one_smul]

private lemma tendsto_Af (h : OffspringHyp μ) :
    Tendsto (Af μ) (𝓝[>] 0) (𝓝 (invMean μ)) := by
  have h1 : Tendsto (Af μ) (𝓝[>] 0)
      (𝓝 (∫ p, (1 : ℝ) / (degree p.1 : ℝ) ∂(GW μ).prod (GW μ))) :=
    tendsto_aidE (g := fun _ : ℕ => (1 : ℝ)) h one_growth
  have h3 : (∫ p, (1 : ℝ) / (degree p.1 : ℝ) ∂(GW μ).prod (GW μ)) =
      ∫ k : ℕ, (1 : ℝ) / (k : ℝ) ∂μ :=
    integral_fst_degree (fun k : ℕ => (1 : ℝ) / (k : ℝ))
  rw [h3] at h1
  simpa only [invMean, one_div] using h1

private lemma tendsto_Cf (h : OffspringHyp μ) : Tendsto (Cf μ) (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (Cf μ) (𝓝[>] 0)
      (𝓝 (∫ p, (degree p.1 : ℝ) / (degree p.1 : ℝ) ∂(GW μ).prod (GW μ))) :=
    tendsto_aidE (g := fun k : ℕ => (k : ℝ)) h cast_growth
  have h3 : (∫ p, (degree p.1 : ℝ) / (degree p.1 : ℝ) ∂(GW μ).prod (GW μ)) =
      ∫ k : ℕ, (k : ℝ) / (k : ℝ) ∂μ :=
    integral_fst_degree (fun k : ℕ => (k : ℝ) / (k : ℝ))
  have hae : ∀ᵐ k ∂μ, k ≠ 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h.zero] with k hk
    simpa using hk
  have h4 : (∫ k : ℕ, (k : ℝ) / (k : ℝ) ∂μ) = 1 := by
    rw [integral_congr_ae (g := fun _ => (1 : ℝ)) (by
      filter_upwards [hae] with k hk
      exact div_self (Nat.cast_ne_zero.mpr hk))]
    simp
  rw [h3, h4] at h1
  exact h1

private lemma deriv_speedValue_eq (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    deriv (Speed.speedValue μ) l =
      (2 * l * (Af μ l * dCf μ l - Cf μ l * dAf μ l) - 2 * Af μ l * Cf μ l) /
        (Cf μ l + l * Af μ l) ^ 2 := by
  have hA : HasDerivAt (Af μ) (dAf μ l) l :=
    hasDerivAt_aidE (g := fun _ : ℕ => (1 : ℝ)) h one_growth hl
  have hC : HasDerivAt (Cf μ) (dCf μ l) l :=
    hasDerivAt_aidE (g := fun k : ℕ => (k : ℝ)) h cast_growth hl
  have hB := B_pos h hl.1 hl.2.le
  have hnum := hC.sub ((hasDerivAt_id' l).mul hA)
  have hden := hC.add ((hasDerivAt_id' l).mul hA)
  have hq := hnum.div hden hB.ne'
  have heq : Speed.speedValue μ =ᶠ[𝓝 l]
      fun x => (Cf μ x - x * Af μ x) / (Cf μ x + x * Af μ x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hl] with x hx
    exact speedValue_eq_CA h hx.1 hx.2.le
  rw [(hq.congr_of_eventuallyEq heq).deriv]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  ring

/-! ### The speed and its derivative near zero bias -/

/-- The speed tends to one at zero bias. -/
theorem tendsto_speedValue_zero (h : OffspringHyp μ) :
    Tendsto (Speed.speedValue μ) (𝓝[>] 0) (𝓝 1) := by
  have hev : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have hA := tendsto_Af h
  have hC := tendsto_Cf h
  have hid : Tendsto (fun l : ℝ => l) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hnum := hC.sub (hid.mul hA)
  have hden := hC.add (hid.mul hA)
  have hq := hnum.div hden (by norm_num)
  rw [show ((1 : ℝ) - 0 * invMean μ) / (1 + 0 * invMean μ) = 1 by simp] at hq
  refine hq.congr' ?_
  filter_upwards [hev] with l hl
  exact (speedValue_eq_CA h hl.1 hl.2.le).symm

/-- Proposition 2.6 (`prop:cost`): the right derivative of the speed at zero is
`-2 E[1/ν]`. -/
theorem hasDerivWithinAt_speedValue_zero (h : OffspringHyp μ) :
    HasDerivWithinAt (Speed.speedValue μ) (-2 * invMean μ) (Set.Ici 0) 0 := by
  have hev : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have hA := tendsto_Af h
  have hC := tendsto_Cf h
  have hid : Tendsto (fun l : ℝ => l) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hden := hC.add (hid.mul hA)
  have hq := (hA.const_mul (-2)).div hden (by norm_num)
  rw [show -2 * invMean μ / (1 + 0 * invMean μ) = -2 * invMean μ by simp] at hq
  apply hasDerivWithinAt_Ioi_iff_Ici.mp
  rw [hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (0 : ℝ)) (lt_irrefl (0 : ℝ))]
  refine hq.congr' ?_
  filter_upwards [hev] with l hl
  have hB := B_pos h hl.1 hl.2.le
  have hB' : Cf μ l + l * Af μ l ≠ 0 := hB.ne'
  have hl0 : l ≠ 0 := hl.1.ne'
  simp only [Pi.div_apply]
  rw [slope_def_field, speedValue_eq_CA h hl.1 hl.2.le, Speed.speedValue_zero, sub_zero,
    div_sub_one hB', div_div, div_eq_div_iff hB' (mul_ne_zero hB' hl0)]
  ring

/-- The derivative of the speed tends to `-2 E[1/ν]` at zero. -/
theorem tendsto_deriv_speedValue_zero (h : OffspringHyp μ) :
    Tendsto (deriv (Speed.speedValue μ)) (𝓝[>] 0) (𝓝 (-2 * invMean μ)) := by
  have hev : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have hA := tendsto_Af h
  have hC := tendsto_Cf h
  have hid : Tendsto (fun l : ℝ => l) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hE : Tendsto (fun l => 2 * l * (Af μ l * dCf μ l - Cf μ l * dAf μ l))
      (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun l : ℝ => 2 * l * 384) ?_ ?_
    · filter_upwards [hev] with l hl
      have hl2 : l ≤ 1 / 2 := hl.2.le
      have h1 : |Af μ l| ≤ 4 := abs_aidE_le (g := fun _ : ℕ => (1 : ℝ)) h one_growth hl.1 hl2
      have h2 : |Cf μ l| ≤ 4 := abs_aidE_le (g := fun k : ℕ => (k : ℝ)) h cast_growth hl.1 hl2
      have h3 : |dAf μ l| ≤ 48 :=
        abs_integral_aidF'_le (g := fun _ : ℕ => (1 : ℝ)) h one_growth hl.1 hl2
      have h4 : |dCf μ l| ≤ 48 :=
        abs_integral_aidF'_le (g := fun k : ℕ => (k : ℝ)) h cast_growth hl.1 hl2
      have e1 : |Af μ l * dCf μ l| ≤ 4 * 48 := by
        rw [abs_mul]; exact mul_le_mul h1 h4 (abs_nonneg _) (by norm_num)
      have e2 : |Cf μ l * dAf μ l| ≤ 4 * 48 := by
        rw [abs_mul]; exact mul_le_mul h2 h3 (abs_nonneg _) (by norm_num)
      have hX : |Af μ l * dCf μ l - Cf μ l * dAf μ l| ≤ 384 := by
        have e1' := abs_le.mp e1
        have e2' := abs_le.mp e2
        rw [abs_le]; constructor <;> linarith [e1'.1, e1'.2, e2'.1, e2'.2]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos hl.1]
      exact mul_le_mul_of_nonneg_left hX (by linarith [hl.1])
    · have := (hid.const_mul 2).mul_const 384
      simpa using this
  have hnum := hE.sub ((hA.const_mul 2).mul hC)
  have hden := (hC.add (hid.mul hA)).pow 2
  have hq := hnum.div hden (by norm_num)
  rw [show ((0 : ℝ) - 2 * invMean μ * 1) / (1 + 0 * invMean μ) ^ 2 = -2 * invMean μ by ring]
    at hq
  refine hq.congr' ?_
  filter_upwards [hev] with l hl
  exact (deriv_speedValue_eq h hl).symm

/-- The right-derivative clause of Theorem 1.1 in the form of the public statement: for
the public offspring model the right derivative
of `speedValue μ'.toMeasure` at zero is `-2 * inverseMean μ'`. -/
theorem hasDerivWithinAt_speedValue_zero_pmf (μ' : PMF ℕ) (hμ0 : μ' 0 = 0)
    (hm1 : 1 < LPPMonotonicity.offspringMean μ')
    (hmfin : LPPMonotonicity.offspringMean μ' < ∞) :
    HasDerivWithinAt (Speed.speedValue μ'.toMeasure)
      (-2 * LPPMonotonicity.inverseMean μ') (Set.Ici 0) 0 := by
  rw [inverseMean_eq μ' hμ0]
  exact hasDerivWithinAt_speedValue_zero (offspringHyp_of μ' hμ0 hm1 hmfin)

end LPPMonotonicityProof.Analytic
