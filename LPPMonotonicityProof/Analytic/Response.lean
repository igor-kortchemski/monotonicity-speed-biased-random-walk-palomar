module

public import LPPMonotonicityProof.Analytic.EscapeC1.Final
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Response recursion and integrability

For the response `u = -λ ∂λ β` on regular trees, this module proves the recursion
`u = β(1-β) + λ(λ+S)⁻² Σ uᵢ`, the lower bounds `u ≥ β(1-β)` and `2u ≥ 1-β` for
`λ ≤ 1`, domination by the response envelope, and integrability: the last clauses of
Proposition 2.5 (`prop:regularity`). It also proves `|∂β| ≤ 2` for `λ ≤ 1/2`, used in
the proof of Proposition 2.6 near zero bias.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem differentiableAt_escape {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) : DifferentiableAt ℝ (fun x => escape x T) l :=
  ((escape_contDiffOn hT).differentiableOn (by norm_num) l hl).differentiableAt
    (isOpen_Ioo.mem_nhds hl)

private theorem childSum_pos_response {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) : 0 < childSum l T := by
  let i0 : Fin (degree T) := ⟨0, by
    have hr := hT.1.1 [] (present_nil T)
    change 0 < degree T at hr
    omega⟩
  apply Finset.sum_pos _ ⟨i0, Finset.mem_univ _⟩
  intro i _
  rw [child_eq_subtree]
  exact hT.1.2 l hl [i.val + 1] ⟨Nat.succ_pos _, Nat.succ_le_of_lt i.isLt, present_nil _⟩

private theorem resp_nonneg {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) : 0 ≤ resp l T := by
  let a := l / 2
  let b := (l + mean μ) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hl.1]
  have hla : l ∈ Set.Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith [hl.1, hl.2]
  have hab : a ≤ b := hla.1.le.trans hla.2.le
  have hb : b < mean μ := by dsimp [b]; linarith [hl.2]
  have hn := (neg_deriv_escape_le hT ha hab hb (Set.mem_Icc.mpr ⟨hla.1.le, hla.2.le⟩)).2.1
  rw [resp]
  nlinarith [mul_nonneg hl.1.le hn]

/-- The response satisfies the same recursion as its finite-depth approximants. -/
theorem resp_eq {T : Tree} (hT : RegTree μ T) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    resp l T = escape l T * (1 - escape l T) +
      l / (l + childSum l T) ^ 2 * ∑ i : Fin (degree T), resp l (child T (i + 1)) := by
  have hSder : HasDerivAt (fun x => childSum x T)
      (∑ i : Fin (degree T), deriv (fun x => escape x (child T (i + 1))) l) l := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (differentiableAt_escape (regTree_child hT i) hl).hasDerivAt
  have hS := childSum_pos_response hT hl
  have hden : l + childSum l T ≠ 0 := (add_pos_of_pos_of_nonneg hl.1 hS.le).ne'
  have heq : (fun x => escape x T) =ᶠ[𝓝 l] fun x => childSum x T / (x + childSum x T) := by
    filter_upwards [isOpen_Ioi.mem_nhds hl.1] with x hx
    exact escape_eq hx T
  have hd : HasDerivAt (fun x => escape x T)
      (((∑ i : Fin (degree T), deriv (fun x => escape x (child T (i + 1))) l) *
        (l + childSum l T) - childSum l T *
        (1 + ∑ i : Fin (degree T), deriv (fun x => escape x (child T (i + 1))) l)) /
        (l + childSum l T) ^ 2) l := by
    exact (hSder.div ((hasDerivAt_id l).add hSder) hden).congr_of_eventuallyEq heq
  have hU : -l * ∑ i : Fin (degree T), deriv (fun x => escape x (child T (i + 1))) l =
      ∑ i : Fin (degree T), resp l (child T (i + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [resp, hd.deriv, escape_eq hl.1 T, ← hU]
  field_simp [hden]
  ring

/-- The root contributes a nonnegative lower bound to the response. -/
theorem resp_ge {T : Tree} (hT : RegTree μ T) {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    escape l T * (1 - escape l T) ≤ resp l T := by
  rw [resp_eq hT hl]
  apply le_add_of_nonneg_right
  apply mul_nonneg (div_nonneg hl.1.le (sq_nonneg _))
  exact Finset.sum_nonneg fun i _ => resp_nonneg (regTree_child hT i) hl

/-- The limiting finite-depth defect is nonnegative below bias one. -/
theorem two_resp_ge {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) (hl1 : l ≤ 1) : 1 - escape l T ≤ 2 * resp l T := by
  have hdef (N : ℕ) : 0 ≤ 2 * l * (-deriv (fun x => escapeN T.val x N []) l) -
      (1 - escapeN T.val l N []) := by
    rw [(hasDerivAt_escapeN_root hT hl.1 N).deriv]
    have hd := defectN_nonneg T.val hl.1 hl1 N []
      (leaflessBelow_tree hT.1.1 N [] (present_nil T))
    convert hd using 1 <;> field_simp [hl.1.ne'] <;> ring
  have ht : Tendsto (fun N => 2 * l * (-deriv (fun x => escapeN T.val x N []) l) -
      (1 - escapeN T.val l N [])) atTop
      (𝓝 (2 * l * (-deriv (fun x => escape x T) l) - (1 - escape l T))) :=
    ((tendsto_deriv_escapeN hT hl).neg.const_mul (2 * l)).sub
      (tendsto_const_nhds.sub (tendsto_escapeN_root hl.1))
  have hn := ge_of_tendsto ht (Filter.Eventually.of_forall hdef)
  rw [resp] at *
  nlinarith

/-- The response is dominated by the response envelope `envelope a b`. -/
theorem resp_le {T : Tree} (hT : RegTree μ T) {a b l : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) (hl : l ∈ Set.Icc a b) :
    resp l T ≤ l * (envelope a b T).toReal * escape l T := by
  have hn := (neg_deriv_escape_le hT ha hab hb hl).2.2
  rw [resp]
  calc
    -l * deriv (fun l' => escape l' T) l = l * (-deriv (fun l' => escape l' T) l) := by ring
    _ ≤ l * ((envelope a b T).toReal * escape l T) :=
      mul_le_mul_of_nonneg_left hn (ha.trans_le hl.1).le
    _ = l * (envelope a b T).toReal * escape l T := by ring
/-- On `(0,m)`, the response is an a.e. limit of measurable slope quotients. -/
theorem aemeasurable_resp_of_mem (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) : AEMeasurable (resp l) (GW μ) := by
  let t : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ))⁻¹
  have ht0 : Tendsto t atTop (𝓝 0) := by
    simpa only [t, Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht0, Filter.Eventually.of_forall fun n => ?_⟩
    change (((n + 1 : ℕ) : ℝ))⁻¹ ≠ 0
    exact inv_ne_zero (by positivity)
  let F : ℕ → Tree → ℝ := fun n T =>
    -l * slope (fun x => escape x T) l (l + t n)
  have hmeas (n : ℕ) : AEMeasurable (F n) (GW μ) := by
    apply AEMeasurable.const_mul
    simp only [F, slope_def_module, add_sub_cancel_left]
    exact ((measurable_escape (l + t n)).sub (measurable_escape l)).const_smul (t n)⁻¹ |>.aemeasurable
  apply aemeasurable_of_tendsto_metrizable_ae atTop hmeas
  filter_upwards [ae_regTree h] with T hT
  have hlim := (differentiableAt_escape hT hl).hasDerivAt.tendsto_slope_zero.comp ht
  have hmul := hlim.const_mul (-l)
  simpa only [F, resp, Function.comp_apply, slope_def_module, add_sub_cancel_left] using hmul

/-- The response is integrable at every bias in `(0,m)`. -/
theorem integrable_resp (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) : Integrable (resp l) (GW μ) := by
  let a := l / 2
  let b := (l + mean μ) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hl.1]
  have hla : l ∈ Set.Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith [hl.1, hl.2]
  have hab : a ≤ b := hla.1.le.trans hla.2.le
  have hb : b < mean μ := by dsimp [b]; linarith [hl.2]
  have hfin : ∫⁻ T, envelope a b T ∂GW μ ≠ ⊤ :=
    (lintegral_envelope_lt_top h ha hab hb).ne
  have henv : Integrable (fun T => l * (envelope a b T).toReal) (GW μ) :=
    (integrable_toReal_of_lintegral_ne_top (measurable_envelope a b).aemeasurable hfin).const_mul l
  apply Integrable.mono' henv (aemeasurable_resp_of_mem h hl).aestronglyMeasurable
  filter_upwards [ae_regTree h] with T hT
  rw [Real.norm_eq_abs, abs_of_nonneg (resp_nonneg hT hl)]
  calc
    resp l T ≤ l * (envelope a b T).toReal * escape l T :=
      resp_le hT ha hab hb (Set.mem_Icc.mpr ⟨hla.1.le, hla.2.le⟩)
    _ ≤ l * (envelope a b T).toReal * 1 :=
      mul_le_mul_of_nonneg_left (escape_mem_Icc hl.1 _).2
        (mul_nonneg hl.1.le ENNReal.toReal_nonneg)
    _ = l * (envelope a b T).toReal := mul_one _
/-- The low-bias derivative bound `|∂β| ≤ 2`, on `(0, m)`, where the escape of a regular
tree is differentiable. -/
theorem abs_deriv_escape_le_two_of_mem {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) (hl2 : l ≤ 1 / 2) :
    |deriv (fun l' => escape l' T) l| ≤ 2 := by
  have hl1 : l < 1 := hl2.trans_lt (by norm_num)
  have hn : -deriv (fun l' => escape l' T) l ≤ 1 / (1 - l) := by
    apply le_of_tendsto (tendsto_deriv_escapeN hT hl).neg
    filter_upwards with N
    rw [(hasDerivAt_escapeN_root hT hl.1 N).deriv]
    have hw := wN_le_geom hT.1.1 hl.1 hl1 N
    calc
      -(-(escapeN T.val l N [] * wN T.val l N []) / l) =
          escapeN T.val l N [] * wN T.val l N [] / l := by ring
      _ ≤ (1 * (l / (1 - l))) / l := by
        apply div_le_div_of_nonneg_right _ hl.1.le
        calc
          escapeN T.val l N [] * wN T.val l N [] ≤ 1 * wN T.val l N [] :=
            mul_le_mul_of_nonneg_right (escapeN_le_one _ hl.1 _ _)
              (wN_nonneg _ hl.1 _ _ (leaflessBelow_tree hT.1.1 N [] (present_nil T)))
          _ = wN T.val l N [] := one_mul _
          _ ≤ l / (1 - l) := hw
          _ = 1 * (l / (1 - l)) := (one_mul _).symm
      _ = 1 / (1 - l) := by field_simp [hl.1.ne', (sub_pos.mpr hl1).ne']
  have hn0 : 0 ≤ -deriv (fun l' => escape l' T) l := by
    let a := l / 2
    let b := (l + mean μ) / 2
    have ha : 0 < a := by dsimp [a]; linarith [hl.1]
    have hla : l ∈ Set.Ioo a b := by
      constructor <;> dsimp [a, b] <;> linarith [hl.1, hl.2]
    have hab : a ≤ b := hla.1.le.trans hla.2.le
    have hb : b < mean μ := by dsimp [b]; linarith [hl.2]
    exact (neg_deriv_escape_le hT ha hab hb (Set.mem_Icc.mpr ⟨hla.1.le, hla.2.le⟩)).2.1
  rw [abs_of_nonpos (neg_nonneg.mp hn0)]
  exact hn.trans ((div_le_iff₀ (sub_pos.mpr hl1)).2 (by linarith))

end LPPMonotonicityProof.Analytic
