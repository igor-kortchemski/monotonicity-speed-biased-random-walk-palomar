module

public import LPPMonotonicityProof.Analytic.ChildResponse.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# The exact child-response recursion and its pointwise lower bound

This module proves, tree by tree, the child-response formula for `B = -s ∂ₛ W` in the
proof of Lemma 4.5 (`lem:scaled-two-children`), and its lower bound by the
`δᵢ²`-weighted child terms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- The response of a child's transformed escape.  The measurable `limUnder`
representative agrees with the derivative at every point where the derivative
exists, while remaining measurable on every tree. -/
noncomputable def Yresp (l : ℝ) (T : Tree) : ℝ :=
  -(l - 1) * limUnder atTop (fun n : ℕ =>
    slope (fun x => Yt x T) l (l + (((n + 1 : ℕ) : ℝ))⁻¹))

theorem measurable_Yresp (l : ℝ) : Measurable (Yresp l) := by
  apply measurable_const.mul
  have hm (n : ℕ) : StronglyMeasurable (fun T : Tree =>
      slope (fun x => Yt x T) l (l + (((n + 1 : ℕ) : ℝ))⁻¹)) := by
    simp only [slope_def_module, add_sub_cancel_left]
    exact (((measurable_Yt (l + (((n + 1 : ℕ) : ℝ))⁻¹)).sub
      (measurable_Yt l)).const_smul ((((n + 1 : ℕ) : ℝ))⁻¹)⁻¹).stronglyMeasurable
  exact (StronglyMeasurable.limUnder hm).measurable

/-- The weighted child term whose average gives the two terms of the child-response
recursion. -/
noncomputable def childTerm (l : ℝ) (n : ℕ) (T : Tree) : ℝ :=
  Yt l T ^ (n - 1) * Yresp l T

theorem measurable_childTerm (l : ℝ) (n : ℕ) : Measurable (childTerm l n) :=
  (measurable_Yt l).pow_const (n - 1) |>.mul (measurable_Yresp l)

private theorem differentiableAt_escape'' {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) : DifferentiableAt ℝ (fun x => escape x T) l :=
  ((escape_contDiffOn hT).differentiableOn (by norm_num) l ⟨hl, hlm⟩).differentiableAt
    (isOpen_Ioo.mem_nhds ⟨hl, hlm⟩)

theorem hasDerivAt_Yt {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    HasDerivAt (fun x => Yt x T)
      ((deriv (fun x => escape x T) l * (l - 1 + escape l T) -
        escape l T * (1 + deriv (fun x => escape x T) l)) /
        (l - 1 + escape l T) ^ 2) l := by
  have hβ := (differentiableAt_escape'' hT (by linarith) hlm).hasDerivAt
  have hD : l - 1 + escape l T ≠ 0 := by
    have := (escape_mem_Icc (by linarith : 0 < l) T).1
    positivity
  exact hβ.fun_div (((hasDerivAt_id' (x := l)).sub_const 1).fun_add hβ) hD

theorem Yresp_eq_deriv {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    Yresp l T = -(l - 1) * deriv (fun l' => Yt l' T) l := by
  let t : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ))⁻¹
  have ht0 : Tendsto t atTop (𝓝 0) := by
    simpa only [t, Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht0, Filter.Eventually.of_forall fun n => ?_⟩
    change (((n + 1 : ℕ) : ℝ))⁻¹ ≠ 0
    exact inv_ne_zero (by positivity)
  have hl' := (hasDerivAt_Yt hT hl hlm).differentiableAt.hasDerivAt.tendsto_slope_zero.comp ht
  have hlim : Tendsto (fun n : ℕ => slope (fun x => Yt x T) l (l + t n)) atTop
      (𝓝 (deriv (fun x => Yt x T) l)) := by
    simpa only [slope_def_module, add_sub_cancel_left, Function.comp_def] using hl'
  have hlu : Tendsto (fun n : ℕ => slope (fun x => Yt x T) l (l + t n)) atTop
      (𝓝 (limUnder atTop (fun n : ℕ => slope (fun x => Yt x T) l (l + t n)))) :=
    tendsto_nhds_limUnder ⟨_, hlim⟩
  have heq : limUnder atTop (fun n : ℕ => slope (fun x => Yt x T) l (l + t n)) =
      deriv (fun x => Yt x T) l := tendsto_nhds_unique hlu hlim
  unfold Yresp
  change -(l - 1) * limUnder atTop (fun n : ℕ =>
    slope (fun x => Yt x T) l (l + t n)) = _
  rw [heq]

/-- The corresponding measurable representative of the split response. -/
noncomputable def Wresp (l : ℝ) (T : Tree) : ℝ :=
  -(l - 1) * limUnder atTop (fun n : ℕ =>
    slope (fun x => Wt x T) l (l + (((n + 1 : ℕ) : ℝ))⁻¹))

theorem measurable_Wresp (l : ℝ) : Measurable (Wresp l) := by
  apply measurable_const.mul
  have hm (n : ℕ) : StronglyMeasurable (fun T : Tree =>
      slope (fun x => Wt x T) l (l + (((n + 1 : ℕ) : ℝ))⁻¹)) := by
    simp only [slope_def_module, add_sub_cancel_left]
    exact (((measurable_Wt (l + (((n + 1 : ℕ) : ℝ))⁻¹)).sub
      (measurable_Wt l)).const_smul ((((n + 1 : ℕ) : ℝ))⁻¹)⁻¹).stronglyMeasurable
  exact (StronglyMeasurable.limUnder hm).measurable

theorem Wresp_eq_deriv {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    Wresp l T = -(l - 1) * deriv (fun l' => Wt l' T) l := by
  let t : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ))⁻¹
  have ht0 : Tendsto t atTop (𝓝 0) := by
    simpa only [t, Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht0, Filter.Eventually.of_forall fun n => ?_⟩
    change (((n + 1 : ℕ) : ℝ))⁻¹ ≠ 0
    exact inv_ne_zero (by positivity)
  have hl' := (hasDerivAt_Wt hT hl hlm).differentiableAt.hasDerivAt.tendsto_slope_zero.comp ht
  have hlim : Tendsto (fun n : ℕ => slope (fun x => Wt x T) l (l + t n)) atTop
      (𝓝 (deriv (fun x => Wt x T) l)) := by
    simpa only [slope_def_module, add_sub_cancel_left, Function.comp_def] using hl'
  have hlu : Tendsto (fun n : ℕ => slope (fun x => Wt x T) l (l + t n)) atTop
      (𝓝 (limUnder atTop (fun n : ℕ => slope (fun x => Wt x T) l (l + t n)))) :=
    tendsto_nhds_limUnder ⟨_, hlim⟩
  have heq : limUnder atTop (fun n : ℕ => slope (fun x => Wt x T) l (l + t n)) =
      deriv (fun x => Wt x T) l := tendsto_nhds_unique hlu hlim
  unfold Wresp
  change -(l - 1) * limUnder atTop (fun n : ℕ =>
    slope (fun x => Wt x T) l (l + t n)) = _
  rw [heq]

theorem Bresp_eq_Wresp {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : Bresp l T = Wresp l T := by
  rw [Bresp, Wresp_eq_deriv hT hl hlm]

theorem Yresp_eq_direct {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    Yresp l T = ((l - 1) * escape l T - (l - 1) ^ 2 *
      deriv (fun x => escape x T) l) / (l - 1 + escape l T) ^ 2 := by
  rw [Yresp_eq_deriv hT hl hlm, (hasDerivAt_Yt hT hl hlm).deriv]
  ring

theorem Yresp_nonneg {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : 0 ≤ Yresp l T := by
  rw [Yresp_eq_direct hT hl hlm]
  have hβ := (escape_mem_Icc (by linarith : 0 < l) T).1
  have hd := deriv_escape_nonpos_of_reg hT (by linarith) hlm
  have hD : 0 < l - 1 + escape l T := by linarith
  apply div_nonneg _ (sq_nonneg _)
  have hsecond : 0 ≤ -(l - 1) ^ 2 * deriv (fun x => escape x T) l := by
    have := mul_nonneg (sq_nonneg (l - 1)) (neg_nonneg.mpr hd)
    nlinarith
  nlinarith [mul_nonneg (by linarith : 0 ≤ l - 1) hβ]

theorem Yt_le_Wt {l : ℝ} (hl : 1 < l) (T : Tree) (i : Fin (degree T)) :
    Yt l (child T (i + 1)) ≤ Wt l T := by
  have hβ0 : ∀ j : Fin (degree T), 0 ≤ escape l (child T (j + 1)) :=
    fun j => (escape_mem_Icc (by linarith) _).1
  have hβle : escape l (child T (i + 1)) ≤ childSum l T :=
    Finset.single_le_sum (fun j _ => hβ0 j) (Finset.mem_univ i)
  have hS : 0 ≤ childSum l T := Finset.sum_nonneg fun j _ => hβ0 j
  have hD : 0 < l - 1 + childSum l T := by linarith
  have hDi : 0 < l - 1 + escape l (child T (i + 1)) := by linarith [hβ0 i]
  rw [Yt, Wt, div_le_div_iff₀ hDi hD]
  nlinarith [mul_nonneg (by linarith : 0 ≤ l - 1) (sub_nonneg.mpr hβle)]

theorem deltaChild_le_responseFactor {l : ℝ} (hl : 1 < l) (T : Tree)
    (i : Fin (degree T)) :
    deltaChild l T (i + 1) ≤ (1 - Wt l T) / (1 - Yt l (child T (i + 1))) := by
  have hβ0 : ∀ j : Fin (degree T), 0 ≤ escape l (child T (j + 1)) :=
    fun j => (escape_mem_Icc (by linarith) _).1
  have hβle : escape l (child T (i + 1)) ≤ childSum l T :=
    Finset.single_le_sum (fun j _ => hβ0 j) (Finset.mem_univ i)
  have hS : 0 ≤ childSum l T := Finset.sum_nonneg fun j _ => hβ0 j
  have hD : 0 < l - 1 + childSum l T := by linarith
  have hDi : 0 < l - 1 + escape l (child T (i + 1)) := by linarith [hβ0 i]
  have hDd : 0 < l - 1 + childSum l T - escape l (child T (i + 1)) := by linarith
  have hW : 1 - Wt l T = (l - 1) / (l - 1 + childSum l T) := by
    unfold Wt
    field_simp [hD.ne']
    ring
  have hY : 1 - Yt l (child T (i + 1)) =
      (l - 1) / (l - 1 + escape l (child T (i + 1))) := by
    unfold Yt
    field_simp [hDi.ne']
    ring
  rw [hW, hY, deltaChild]
  have hfactor : ((l - 1) / (l - 1 + childSum l T)) /
      ((l - 1) / (l - 1 + escape l (child T (i + 1)))) =
      (l - 1 + escape l (child T (i + 1))) / (l - 1 + childSum l T) := by
    field_simp [hD.ne', hDi.ne', (by linarith : l - 1 ≠ 0)]
  rw [hfactor, div_le_div_iff₀ hDd hD]
  have hprod : 0 ≤ escape l (child T (i + 1)) *
      (childSum l T - escape l (child T (i + 1))) :=
    mul_nonneg (hβ0 i) (sub_nonneg.mpr hβle)
  nlinarith

/-- The exact differentiation identity behind the child-response recursion. -/
theorem Bresp_eq_sum (h : OffspringHyp μ) {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    Bresp l T = ∑ i : Fin (degree T),
      ((1 - Wt l T) / (1 - Yt l (child T (i + 1)))) ^ 2 * Yresp l (child T (i + 1)) := by
  have ha : 0 < l - 1 := by linarith
  have hS : 0 ≤ childSum l T :=
    Finset.sum_nonneg fun i _ => (escape_mem_Icc (by linarith) _).1
  have hD : 0 < l - 1 + childSum l T := by linarith
  rw [Bresp, (hasDerivAt_Wt hT hl hlm).deriv]
  have hleft : -(l - 1) *
      ((childSumDeriv T l * (l - 1 + childSum l T) -
        childSum l T * (1 + childSumDeriv T l)) / (l - 1 + childSum l T) ^ 2) =
      ((l - 1) * childSum l T - (l - 1) ^ 2 * childSumDeriv T l) /
        (l - 1 + childSum l T) ^ 2 := by ring
  rw [hleft]
  have hsum : (l - 1) * childSum l T - (l - 1) ^ 2 * childSumDeriv T l =
      ∑ i : Fin (degree T), ((l - 1) * escape l (child T (i + 1)) -
        (l - 1) ^ 2 * deriv (fun x => escape x (child T (i + 1))) l) := by
    unfold childSum childSumDeriv
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hβ := (escape_mem_Icc (by linarith : 0 < l) (child T (i + 1))).1
  have hDi : 0 < l - 1 + escape l (child T (i + 1)) := by linarith
  rw [Yresp_eq_direct (regTree_child hT i) hl hlm]
  have hW : 1 - Wt l T = (l - 1) / (l - 1 + childSum l T) := by
    unfold Wt
    field_simp [hD.ne']
    ring
  have hY : 1 - Yt l (child T (i + 1)) =
      (l - 1) / (l - 1 + escape l (child T (i + 1))) := by
    unfold Yt
    field_simp [hDi.ne']
    ring
  rw [hW, hY]
  field_simp [hD.ne', hDi.ne', ha.ne']

/-- The child-response recursion before averaging: the parent moment dominates the sum
of the weighted child moments. -/
theorem Wt_pow_mul_Bresp_ge_sum (h : OffspringHyp μ) {T : Tree} (hT : RegTree μ T)
    {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2 * childTerm l n (child T (i + 1)) ≤
      Wt l T ^ (n - 1) * Bresp l T := by
  rw [Bresp_eq_sum h hT hl hlm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hδ0 := (deltaChild_mem_Icc' hl T i).1
  have hq := deltaChild_le_responseFactor hl T i
  have hq0 : 0 ≤ (1 - Wt l T) / (1 - Yt l (child T (i + 1))) := hδ0.trans hq
  have hYr := Yresp_nonneg (regTree_child hT i) hl hlm
  have hYW := Yt_le_Wt hl T i
  have hY0 : 0 ≤ Yt l (child T (i + 1)) := by
    exact div_nonneg (escape_mem_Icc (by linarith) _).1 (by
      have hβ := (escape_mem_Icc (by linarith : 0 < l) (child T (i + 1))).1
      positivity)
  have hW0 := (Wt_mem_Icc' hl T).1
  have hfirst : deltaChild l T (i + 1) ^ 2 * Yresp l (child T (i + 1)) ≤
      ((1 - Wt l T) / (1 - Yt l (child T (i + 1)))) ^ 2 * Yresp l (child T (i + 1)) := by
    apply mul_le_mul_of_nonneg_right _ hYr
    exact (sq_le_sq₀ hδ0 hq0).2 hq
  have hsecond : Yt l (child T (i + 1)) ^ (n - 1) ≤ Wt l T ^ (n - 1) :=
    pow_le_pow_left₀ hY0 hYW _
  unfold childTerm
  calc
    deltaChild l T (i + 1) ^ 2 *
        (Yt l (child T (i + 1)) ^ (n - 1) * Yresp l (child T (i + 1))) =
        Yt l (child T (i + 1)) ^ (n - 1) *
          (deltaChild l T (i + 1) ^ 2 * Yresp l (child T (i + 1))) := by ring
    _ ≤ Wt l T ^ (n - 1) *
        (((1 - Wt l T) / (1 - Yt l (child T (i + 1)))) ^ 2 * Yresp l (child T (i + 1))) := by
      exact mul_le_mul hsecond hfirst (mul_nonneg (sq_nonneg _) hYr) (pow_nonneg hW0 _)
    _ = _ := by ring

end LPPMonotonicityProof.Analytic
