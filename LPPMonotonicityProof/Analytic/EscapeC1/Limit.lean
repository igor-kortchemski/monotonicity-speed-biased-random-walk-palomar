module

public import LPPMonotonicityProof.Analytic.EscapeC1
public import LPPMonotonicityProof.Analytic.EscapeC1.Truncation
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Uniform limits for the `C¹` escape argument

This module proves, on the regular event `RegTree`, that the escape is continuous on
compact subintervals of `(0, m)`, that its logarithm has the Lipschitz bound given by
the response envelope, and that the finite-depth escapes converge uniformly to it
(Dini).  These are steps of the path expansion in the proof of Proposition 2.5
(`prop:regularity`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

theorem leaflessBelow_tree {T : Tree}
    (hT : ∀ v, Present T v → 1 ≤ T.val v) :
    ∀ (N : ℕ) (v : Address), Present T v → LeaflessBelow T.val N v := by
  intro N
  induction N with
  | zero => intro v _; trivial
  | succ N ih =>
      intro v hv
      exact ⟨hT v hv, fun i => ih _ ((present_append_singleton T v (i.val + 1) hv).2
        ⟨Nat.succ_pos _, i.isLt⟩)⟩

theorem child_eq_subtree (T : Tree) (j : ℕ) : child T j = subtree T [j] := by
  rw [subtree_cons, subtree_nil]

theorem regTree_child {T : Tree} (hT : RegTree μ T) (i : Fin (degree T)) :
    RegTree μ (child T (i + 1)) := by
  rw [child_eq_subtree]
  exact hT.subtree ⟨Nat.succ_pos _, i.isLt, present_nil _⟩

theorem leafless_child {T : Tree}
    (hT : ∀ v, Present T v → 1 ≤ T.val v) (i : Fin (degree T)) :
    ∀ v, Present (child T (i + 1)) v → 1 ≤ (child T (i + 1)).val v := by
  intro v hv
  exact hT ((i.val + 1) :: v) ⟨Nat.succ_pos _, Nat.succ_le_of_lt i.isLt, hv⟩

/-- RegTree supplies a finite canonical envelope on every real compact subinterval. -/
theorem RegTree.envelope_lt_top {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) : envelope a b T < ⊤ := by
  obtain ⟨qNeg, hq0, hqNeg⟩ := exists_rat_btwn ha
  obtain ⟨qPos, hbq, hqm⟩ := exists_rat_btwn hb
  have hq0Q : 0 < qNeg := by exact_mod_cast hq0
  have hqle : qNeg ≤ qPos := by exact_mod_cast (show (qNeg : ℝ) ≤ qPos from
    hqNeg.le.trans (hab.trans hbq.le))
  have hfin := hT.2 qNeg qPos hq0Q hqle hqm [] (present_nil T)
  rw [← envelope_eq_prov] at hfin
  exact (envelope_mono (lNeg := a) (lPos := b) (lNeg' := (qNeg : ℝ)) (lPos' := (qPos : ℝ)) hq0 (ha.trans_le hab)
    hqNeg.le hbq.le T).trans_lt hfin

private theorem pathSeries_ne_top {T : Tree} {a b : ℝ} (ha : 0 < a)
    (hfin : envelope a b T < ⊤) :
    (∑' k, (pathMax b (k + 1) T : ℝ≥0∞)) ≠ ⊤ := by
  apply ne_of_lt
  apply ENNReal.lt_top_of_mul_ne_top_right hfin.ne
  exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top

theorem summable_pathMax {T : Tree} {a b : ℝ} (ha : 0 < a)
    (hfin : envelope a b T < ⊤) : Summable (fun k => (pathMax b (k + 1) T : ℝ)) := by
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mp (pathSeries_ne_top ha hfin)

private theorem envelope_toReal {a : ℝ} (ha : 0 < a) (b T) :
    (envelope a b T).toReal = a⁻¹ * ∑' k, (pathMax b (k + 1) T : ℝ) := by
  rw [envelope, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal ha.le,
    ENNReal.tsum_toReal_eq (by simp)]
  simp only [ENNReal.coe_toReal]

private theorem sum_pathMax_le_envelope {T : Tree} {a b : ℝ} (ha : 0 < a)
    (hfin : envelope a b T < ⊤) (N : ℕ) :
    (∑ k ∈ Finset.range N, (pathMax b (k + 1) T : ℝ)) ≤ a * (envelope a b T).toReal := by
  have hs := ENNReal.sum_le_tsum (f := fun k => (pathMax b (k + 1) T : ℝ≥0∞)) (Finset.range N)
  have hreal := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top (pathSeries_ne_top ha hfin) hs)
    (pathSeries_ne_top ha hfin)).mpr hs
  rw [ENNReal.toReal_sum (by simp), ENNReal.tsum_toReal_eq (by simp)] at hreal
  simp only [ENNReal.coe_toReal] at hreal
  rw [envelope_toReal ha]
  calc
    (∑ k ∈ Finset.range N, (pathMax b (k + 1) T : ℝ)) ≤
        ∑' k, (pathMax b (k + 1) T : ℝ) := hreal
    _ = a * (a⁻¹ * ∑' k, (pathMax b (k + 1) T : ℝ)) := by field_simp

theorem wN_le_mul_envelope {T : Tree} (hT : RegTree μ T) {a b l : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) (hl : 0 < l) (hlb : l ≤ b) (N : ℕ) :
    wN T.val l N [] ≤ a * (envelope a b T).toReal := by
  exact (wN_le_pathMax (lNeg := a) hT.1.1 hl (ha.trans_le hab) hlb N).trans
    (sum_pathMax_le_envelope ha (hT.envelope_lt_top ha hab hb) N)

private theorem wN_div_le_envelope {T : Tree} (hT : RegTree μ T) {a b l : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) (hl : l ∈ Set.Icc a b) (N : ℕ) :
    wN T.val l N [] / l ≤ (envelope a b T).toReal := by
  have hl0 : 0 < l := ha.trans_le hl.1
  apply (div_le_iff₀ hl0).2
  calc
    wN T.val l N [] ≤ a * (envelope a b T).toReal :=
      wN_le_mul_envelope hT ha hab hb hl0 hl.2 N
    _ ≤ l * (envelope a b T).toReal :=
      mul_le_mul_of_nonneg_right hl.1 ENNReal.toReal_nonneg
    _ = (envelope a b T).toReal * l := mul_comm _ _

theorem hasDerivAt_escapeN_root {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 0 < l) (N : ℕ) :
    HasDerivAt (fun x => escapeN T.val x N [])
      (-(escapeN T.val l N [] * wN T.val l N []) / l) l :=
  hasDerivAt_escapeN T.val hl N [] (leaflessBelow_tree hT.1.1 N [] (present_nil T))

private theorem hasDerivAt_log_escapeN {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 0 < l) (N : ℕ) :
    HasDerivAt (fun x => Real.log (escapeN T.val x N []))
      (-wN T.val l N [] / l) l := by
  have hb : 0 < escapeN T.val l N [] :=
    escapeN_pos _ hl _ _ (leaflessBelow_tree hT.1.1 N [] (present_nil T))
  convert (hasDerivAt_escapeN_root hT hl N).log hb.ne' using 1
  field_simp

theorem log_escapeN_lipschitz {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) (N : ℕ) :
    LipschitzOnWith (Real.toNNReal (envelope a b T).toReal)
      (fun l => Real.log (escapeN T.val l N [])) (Set.Icc a b) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
  · intro l hl
    exact (hasDerivAt_log_escapeN hT (ha.trans_le hl.1) N).differentiableAt
  · intro l hl
    rw [((hasDerivAt_log_escapeN hT (ha.trans_le hl.1) N).deriv)]
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ ENNReal.toReal_nonneg]
    have hw0 : 0 ≤ wN T.val l N [] :=
      wN_nonneg _ (ha.trans_le hl.1) _ _ (leaflessBelow_tree hT.1.1 N [] (present_nil T))
    rw [abs_div, abs_of_pos (ha.trans_le hl.1), abs_neg, abs_of_nonneg hw0]
    exact wN_div_le_envelope hT ha hab hb hl N
  · exact convex_Icc a b

private theorem escapeN_antitone {T : Tree} {l : ℝ} (hl : 0 < l) :
    Antitone (fun N => escapeN T.val l N []) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (escapeN_anti_height T.val hl b []).trans ih

theorem tendsto_escapeN_root {T : Tree} {l : ℝ} (hl : 0 < l) :
    Tendsto (fun N => escapeN T.val l N []) atTop (𝓝 (escape l T)) := by
  apply tendsto_atTop_ciInf (escapeN_antitone (T := T) hl)
  exact ⟨0, by rintro x ⟨N, rfl⟩; exact escapeN_nonneg' T.val hl N []⟩

set_option maxHeartbeats 800000 in
/-- The limit logarithm has the same Lipschitz bound as every finite-depth logarithm. -/
theorem log_escape_lipschitzOn_Icc {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) :
    LipschitzOnWith (Real.toNNReal (envelope a b T).toReal)
      (fun l => Real.log (escape l T)) (Set.Icc a b) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hpy : 0 < escape y T :=
    hT.1.2 y ⟨ha.trans_le hy.1, hy.2.trans_lt hb⟩ [] (present_nil T)
  have hpx : 0 < escape x T :=
    hT.1.2 x ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩ [] (present_nil T)
  have hlim : Tendsto (fun N => dist (Real.log (escapeN T.val y N []))
      (Real.log (escapeN T.val x N []))) atTop
      (𝓝 (dist (Real.log (escape y T)) (Real.log (escape x T)))) :=
    ((Real.continuousAt_log hpy.ne').tendsto.comp
      (tendsto_escapeN_root (ha.trans_le hy.1))).dist
      ((Real.continuousAt_log hpx.ne').tendsto.comp
        (tendsto_escapeN_root (ha.trans_le hx.1)))
  have H : dist (Real.log (escape y T)) (Real.log (escape x T)) ≤
      (Real.toNNReal (envelope a b T).toReal : ℝ) * dist y x := by
    apply le_of_tendsto hlim
    filter_upwards with N
    exact (lipschitzOnWith_iff_dist_le_mul.mp (log_escapeN_lipschitz hT ha hab hb N)) y hy x hx
  simpa only [dist_comm] using H

/-- The infinite escape is continuous on each compact subinterval of `(0,m)`. -/
theorem continuousOn_escape_Icc {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) :
    ContinuousOn (fun l => escape l T) (Set.Icc a b) := by
  have hexp := Real.continuous_exp.comp_continuousOn
    (log_escape_lipschitzOn_Icc hT ha hab hb).continuousOn
  apply hexp.congr
  intro l hl
  simp only [Function.comp_apply, subtree_nil]
  exact (Real.exp_log (hT.1.2 l ⟨ha.trans_le hl.1, hl.2.trans_lt hb⟩ [] (present_nil T))).symm

/-- Dini convergence of finite-depth escapes on every compact subinterval. -/
theorem tendstoUniformlyOn_escapeN_Icc {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) :
    TendstoUniformlyOn (fun N l => escapeN T.val l N []) (fun l => escape l T)
      atTop (Set.Icc a b) := by
  apply Antitone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · intro N
    exact fun l hl => (hasDerivAt_escapeN_root hT (ha.trans_le hl.1) N).continuousAt.continuousWithinAt
  · intro l hl
    exact escapeN_antitone (ha.trans_le hl.1)
  · exact continuousOn_escape_Icc hT ha hab hb
  · intro l hl
    exact tendsto_escapeN_root (ha.trans_le hl.1)

end LPPMonotonicityProof.Analytic
