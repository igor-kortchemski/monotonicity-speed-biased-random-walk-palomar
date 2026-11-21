module

public import LPPMonotonicityProof.Analytic.EscapeC1.Limit
public import LPPMonotonicityProof.Analytic.EscapeC1.Uniform

/-!
# Uniform limits of the truncated logarithmic responses

This module shows that, for each fixed truncation depth `K`, the truncated
logarithmic responses converge uniformly on compact subintervals of `(0, m)` as the
depth of the finite tree grows, on the regular event `RegTree`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem escapeN_child' (T : Tree) (l : ℝ) (N : ℕ) (j : ℕ) (v : Address) :
    escapeN (child T j).val l N v = escapeN T.val l N (j :: v) := by
  have hst : subtree T [j] = child T j := by rw [subtree_cons, subtree_nil]
  simpa only [hst, List.singleton_append] using escapeN_subtree T l N [j] v

private theorem wN_child' (T : Tree) (l : ℝ) (N : ℕ) (j : ℕ) (v : Address) :
    wN (child T j).val l N v = wN T.val l N (j :: v) := by
  induction N generalizing j v with
  | zero => rfl
  | succ N ih =>
      simp only [wN, offChild, List.nil_append, List.cons_append]
      simp only [escapeN_child', ih]
      rfl

private theorem wTrunc_child' (T : Tree) (l : ℝ) (K N : ℕ) (j : ℕ) (v : Address) :
    wTrunc (child T j).val l K N v = wTrunc T.val l K N (j :: v) := by
  induction N generalizing K j v with
  | zero => rfl
  | succ N ih =>
      simp only [wTrunc, offChild, List.nil_append, List.cons_append]
      simp only [escapeN_child', ih]
      rfl

private theorem escape_le_escapeN' (T : Tree) {l : ℝ} (hl : 0 < l) (N : ℕ) :
    escape l T ≤ escapeN T.val l N [] := by
  apply ciInf_le
  exact ⟨0, by rintro x ⟨M, rfl⟩; exact escapeN_nonneg' T.val hl M []⟩

private theorem wTrunc_nonneg_le_wN {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 0 < l) (K N : ℕ) :
    0 ≤ wTrunc T.val l K N [] ∧ wTrunc T.val l K N [] ≤ wN T.val l N [] := by
  induction N generalizing K T with
  | zero => simp [wTrunc, wN]
  | succ N ih =>
      cases K with
      | zero =>
          constructor
          · simp [wTrunc]
          · simpa [wTrunc] using
              wN_nonneg _ hl _ _ (leaflessBelow_tree hT.1.1 (N + 1) [] (present_nil T))
      | succ K =>
          simp only [wTrunc, wN, Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false, offChild,
            List.nil_append]
          simp_rw [← escapeN_child', ← wTrunc_child', ← wN_child']
          have hS : 0 < ∑ j : Fin (degree T), escapeN (child T (j + 1)).val l N [] := by
            apply Finset.sum_pos
            · intro i _
              exact escapeN_pos _ hl _ _ (leaflessBelow_tree (leafless_child hT.1.1 i)
                N [] (present_nil _))
            · let i0 : Fin (degree T) := ⟨0, by
                have hroot := hT.1.1 [] (present_nil T)
                change 0 < degree T at hroot
                omega⟩
              exact ⟨i0, Finset.mem_univ _⟩
          have hw (i : Fin (degree T)) :
              0 ≤ escapeN (child T (i + 1)).val l N [] /
                (∑ j : Fin (degree T), escapeN (child T (j + 1)).val l N []) :=
            div_nonneg (escapeN_nonneg' _ hl _ _) hS.le
          have hfac : 0 ≤ 1 - escapeN T.val l (N + 1) [] :=
            sub_nonneg.mpr (escapeN_le_one _ hl _ _)
          constructor
          · exact mul_nonneg hfac (add_nonneg zero_le_one (Finset.sum_nonneg fun i _ =>
              mul_nonneg (hw i) (ih (regTree_child hT i) K).1))
          · apply mul_le_mul_of_nonneg_left _ hfac
            apply add_le_add le_rfl
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left (ih (regTree_child hT i) K).2 (hw i)

/-- The explicit pointwise limit of the depth-`K` truncation. -/
private noncomputable def wTruncLim (T : Tree) (l : ℝ) : ℕ → ℝ
  | 0 => 0
  | K + 1 => (1 - escape l T) *
      (1 + ∑ i : Fin (degree T), escape l (child T (i + 1)) / childSum l T *
        wTruncLim (child T (i + 1)) l K)

private theorem escape_pos_child {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) (i : Fin (degree T)) :
    0 < escape l (child T (i + 1)) := by
  rw [child_eq_subtree]
  exact hT.1.2 l hl [i.val + 1] ⟨Nat.succ_pos _, Nat.succ_le_of_lt i.isLt, present_nil _⟩

private theorem childSum_pos' {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) : 0 < childSum l T := by
  let i0 : Fin (degree T) := ⟨0, by
    have hroot := hT.1.1 [] (present_nil T)
    change 0 < degree T at hroot
    omega⟩
  exact Finset.sum_pos (fun i _ => escape_pos_child hT hl i)
    ⟨i0, Finset.mem_univ _⟩

private theorem sum_escapeN_pos {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 0 < l) (N : ℕ) :
    0 < ∑ j : Fin (degree T), escapeN T.val l N [j.val + 1] := by
  let i0 : Fin (degree T) := ⟨0, by
    have hroot := hT.1.1 [] (present_nil T)
    change 0 < degree T at hroot
    omega⟩
  apply Finset.sum_pos _ ⟨i0, Finset.mem_univ _⟩
  intro i _
  exact escapeN_pos _ hl _ _ (leaflessBelow_tree hT.1.1 N [i.val + 1]
    ⟨Nat.succ_pos _, Nat.succ_le_of_lt i.isLt, present_nil _⟩)

private theorem weightN_nonneg {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 0 < l) (N : ℕ) (i : Fin (degree T)) :
    0 ≤ escapeN T.val l N [i.val + 1] /
      (∑ j : Fin (degree T), escapeN T.val l N [j.val + 1]) :=
  div_nonneg (escapeN_nonneg' _ hl _ _) (sum_escapeN_pos hT hl N).le

private theorem weightN_le_one {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 0 < l) (N : ℕ) (i : Fin (degree T)) :
    escapeN T.val l N [i.val + 1] /
      (∑ j : Fin (degree T), escapeN T.val l N [j.val + 1]) ≤ 1 := by
  apply (div_le_one (sum_escapeN_pos hT hl N)).2
  exact Finset.single_le_sum (f := fun j : Fin (degree T) => escapeN T.val l N [j.val + 1])
    (fun j _ => escapeN_nonneg' _ hl _ _) (Finset.mem_univ i)

private theorem weight_nonneg {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) (i : Fin (degree T)) :
    0 ≤ escape l (child T (i + 1)) / childSum l T :=
  div_nonneg (escape_mem_Icc hl.1 _).1 (childSum_pos' hT hl).le

private theorem weight_le_one {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) (i : Fin (degree T)) :
    escape l (child T (i + 1)) / childSum l T ≤ 1 := by
  apply (div_le_one (childSum_pos' hT hl)).2
  exact Finset.single_le_sum (f := fun j : Fin (degree T) => escape l (child T (j + 1)))
    (fun j _ => (escape_mem_Icc hl.1 _).1) (Finset.mem_univ i)

private theorem tendstoUniformlyOn_wTruncLim {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) (K : ℕ) :
    TendstoUniformlyOn (fun N l => wTrunc T.val l K N []) (fun l => wTruncLim T l K)
      atTop (Set.Icc a b) ∧
      ∀ l ∈ Set.Icc a b, 0 ≤ wTruncLim T l K ∧
        wTruncLim T l K ≤ a * (envelope a b T).toReal := by
  induction K generalizing T with
  | zero =>
      constructor
      · have hz : (fun N l => wTrunc T.val l 0 N []) = (fun _ _ => (0 : ℝ)) := by
          funext N l
          cases N <;> rfl
        rw [hz]
        simpa only [wTruncLim] using
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
            (𝓝 0)).tendstoUniformlyOn_const (Set.Icc a b))
      · intro l hl
        simp only [wTruncLim, le_refl, true_and]
        positivity
  | succ K ih =>
      have hEsc := tendstoUniformlyOn_escapeN_Icc hT ha hab hb
      have hEscShift : TendstoUniformlyOn (fun N l => escapeN T.val l (N + 1) [])
          (fun l => escape l T) atTop (Set.Icc a b) :=
        tendstoUniformlyOn_nat_add_one_iff.mpr hEsc
      have hroot (l : ℝ) (hl : l ∈ Set.Icc a b) : l ∈ Set.Ioo 0 (mean μ) :=
        ⟨ha.trans_le hl.1, hl.2.trans_lt hb⟩
      have hδ : 0 < childSum b T := childSum_pos' hT ⟨ha.trans_le hab, hb⟩
      have hB (i : Fin (degree T)) : TendstoUniformlyOn
          (fun N l => escapeN T.val l N [i.val + 1])
          (fun l => escape l (child T (i + 1))) atTop (Set.Icc a b) := by
        simpa only [escapeN_child'] using
          (tendstoUniformlyOn_escapeN_Icc (regTree_child hT i) ha hab hb)
      have hS : TendstoUniformlyOn
          (fun N l => ∑ j : Fin (degree T), escapeN T.val l N [j.val + 1])
          (fun l => childSum l T) atTop (Set.Icc a b) := by
        simpa only [childSum] using tendstoUniformlyOn_sum Finset.univ (fun i _ => hB i)
      have hSlow (N : ℕ) (l : ℝ) (hl : l ∈ Set.Icc a b) :
          childSum b T ≤ ∑ j : Fin (degree T), escapeN T.val l N [j.val + 1] := by
        apply Finset.sum_le_sum
        intro i _
        calc
          escape b (child T (i + 1)) ≤ escape l (child T (i + 1)) :=
            escape_antitoneOn _ (hroot l hl).1 (ha.trans_le hab) hl.2
          _ ≤ escapeN (child T (i + 1)).val l N [] :=
            escape_le_escapeN' _ (hroot l hl).1 N
          _ = escapeN T.val l N [i.val + 1] := escapeN_child' _ _ _ _ _
      have hSlimLower (l : ℝ) (hl : l ∈ Set.Icc a b) : childSum b T ≤ childSum l T := by
        apply Finset.sum_le_sum
        intro i _
        exact escape_antitoneOn _ (hroot l hl).1 (ha.trans_le hab) hl.2
      have hSInv := tendstoUniformlyOn_inv hδ hS
        (fun N l hl => hSlow N l hl) (fun l hl => hSlimLower l hl)
      have hfrac (i : Fin (degree T)) : TendstoUniformlyOn
          (fun N l => escapeN T.val l N [i.val + 1] /
            (∑ j : Fin (degree T), escapeN T.val l N [j.val + 1]))
          (fun l => escape l (child T (i + 1)) / childSum l T) atTop (Set.Icc a b) := by
        simp only [div_eq_mul_inv]
        apply tendstoUniformlyOn_mul_of_compact
          (K := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc 0 (childSum b T)⁻¹) (hB i) hSInv
          (isCompact_Icc.prod isCompact_Icc)
        · intro N l hl
          have hpos := hδ.trans_le (hSlow N l hl)
          exact ⟨⟨escapeN_nonneg' _ (hroot l hl).1 _ _, escapeN_le_one _ (hroot l hl).1 _ _⟩,
            inv_nonneg.mpr hpos.le, (inv_le_inv₀ hpos hδ).2 (hSlow N l hl)⟩
        · intro l hl
          have hpos := childSum_pos' hT (hroot l hl)
          exact ⟨⟨(escape_mem_Icc (hroot l hl).1 _).1, (escape_mem_Icc (hroot l hl).1 _).2⟩,
            inv_nonneg.mpr hpos.le, (inv_le_inv₀ hpos hδ).2 (hSlimLower l hl)⟩
      have hW (i : Fin (degree T)) : TendstoUniformlyOn
          (fun N l => wTrunc T.val l K N [i.val + 1])
          (fun l => wTruncLim (child T (i + 1)) l K) atTop (Set.Icc a b) := by
        simpa only [wTrunc_child'] using (ih (regTree_child hT i)).1
      have hprod (i : Fin (degree T)) : TendstoUniformlyOn
          (fun N l => escapeN T.val l N [i.val + 1] /
            (∑ j : Fin (degree T), escapeN T.val l N [j.val + 1]) *
            wTrunc T.val l K N [i.val + 1])
          (fun l => escape l (child T (i + 1)) / childSum l T *
            wTruncLim (child T (i + 1)) l K) atTop (Set.Icc a b) := by
        apply tendstoUniformlyOn_mul_of_compact
          (K := Set.Icc (0 : ℝ) 1 ×ˢ
            Set.Icc 0 (a * (envelope a b (child T (i + 1))).toReal))
          (hfrac i) (hW i) (isCompact_Icc.prod isCompact_Icc)
        · intro N l hl
          have hbounds := wTrunc_nonneg_le_wN (regTree_child hT i) (hroot l hl).1 K N
          have hupper := hbounds.2.trans
            (wN_le_mul_envelope (regTree_child hT i) ha hab hb (hroot l hl).1 hl.2 N)
          refine ⟨⟨weightN_nonneg hT (hroot l hl).1 N i, weightN_le_one hT (hroot l hl).1 N i⟩,
            ?_, ?_⟩
          · simpa only [wTrunc_child'] using hbounds.1
          · simpa only [wTrunc_child'] using hupper
        · intro l hl
          exact ⟨⟨weight_nonneg hT (hroot l hl) i, weight_le_one hT (hroot l hl) i⟩,
            (ih (regTree_child hT i)).2 l hl⟩
      have hSum := tendstoUniformlyOn_sum Finset.univ (fun i _ => hprod i)
      have hInner : TendstoUniformlyOn
          (fun N l => 1 + ∑ i : Fin (degree T),
            escapeN T.val l N [i.val + 1] /
              (∑ j : Fin (degree T), escapeN T.val l N [j.val + 1]) *
              wTrunc T.val l K N [i.val + 1])
          (fun l => 1 + ∑ i : Fin (degree T), escape l (child T (i + 1)) / childSum l T *
            wTruncLim (child T (i + 1)) l K) atTop (Set.Icc a b) :=
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
          (𝓝 1)).tendstoUniformlyOn_const (Set.Icc a b)).add hSum
      have hOuterConv := tendstoUniformlyOn_mul_of_compact
        (K := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc 0
          (1 + ∑ i : Fin (degree T), a * (envelope a b (child T (i + 1))).toReal))
        (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
          (𝓝 1)).tendstoUniformlyOn_const (Set.Icc a b)).sub hEscShift)
        hInner (isCompact_Icc.prod isCompact_Icc)
        (by
          intro N l hl
          refine ⟨⟨sub_nonneg.mpr (escapeN_le_one _ (hroot l hl).1 _ _),
            sub_le_self 1 (escapeN_nonneg' T.val (hroot l hl).1 (N + 1) [])⟩, ⟨?_, ?_⟩⟩
          · apply add_nonneg zero_le_one
            exact Finset.sum_nonneg fun i _ => mul_nonneg (weightN_nonneg hT (hroot l hl).1 N i)
              (by simpa only [wTrunc_child'] using
                (wTrunc_nonneg_le_wN (regTree_child hT i) (hroot l hl).1 K N).1)
          · change 1 + (∑ i : Fin (degree T), escapeN T.val l N [i.val + 1] /
              (∑ j : Fin (degree T), escapeN T.val l N [j.val + 1]) *
              wTrunc T.val l K N [i.val + 1]) ≤ _
            apply add_le_add le_rfl
            apply Finset.sum_le_sum
            intro i _
            have hbounds := wTrunc_nonneg_le_wN (regTree_child hT i) (hroot l hl).1 K N
            have hupper := hbounds.2.trans
              (wN_le_mul_envelope (regTree_child hT i) ha hab hb (hroot l hl).1 hl.2 N)
            calc
              escapeN T.val l N [i.val + 1] /
                  (∑ j : Fin (degree T), escapeN T.val l N [j.val + 1]) *
                  wTrunc T.val l K N [i.val + 1] ≤
                  1 * (a * (envelope a b (child T (i + 1))).toReal) := by
                apply mul_le_mul (weightN_le_one hT (hroot l hl).1 N i)
                · simpa only [wTrunc_child'] using hupper
                · simpa only [wTrunc_child'] using hbounds.1
                · exact zero_le_one
              _ = a * (envelope a b (child T (i + 1))).toReal := one_mul _)
        (by
          intro l hl
          refine ⟨⟨sub_nonneg.mpr (escape_mem_Icc (hroot l hl).1 _).2,
            sub_le_self 1 (escape_mem_Icc (hroot l hl).1 T).1⟩, ⟨?_, ?_⟩⟩
          · apply add_nonneg zero_le_one
            exact Finset.sum_nonneg fun i _ => mul_nonneg (weight_nonneg hT (hroot l hl) i)
              ((ih (regTree_child hT i)).2 l hl).1
          · change 1 + (∑ i : Fin (degree T), escape l (child T (i + 1)) / childSum l T *
              wTruncLim (child T (i + 1)) l K) ≤ _
            apply add_le_add le_rfl
            apply Finset.sum_le_sum
            intro i _
            have hlim := (ih (regTree_child hT i)).2 l hl
            calc
              escape l (child T (i + 1)) / childSum l T * wTruncLim (child T (i + 1)) l K ≤
                  1 * (a * (envelope a b (child T (i + 1))).toReal) :=
                mul_le_mul (weight_le_one hT (hroot l hl) i) hlim.2 hlim.1 zero_le_one
              _ = a * (envelope a b (child T (i + 1))).toReal := one_mul _)
      have hshift : TendstoUniformlyOn (fun N l => wTrunc T.val l (K + 1) (N + 1) [])
          (fun l => wTruncLim T l (K + 1)) atTop (Set.Icc a b) := by
        apply hOuterConv.congr
        filter_upwards with N
        intro l hl
        simp only [Pi.sub_apply, Pi.one_apply, wTrunc, Nat.add_sub_cancel, Nat.succ_ne_zero,
          ite_false, offChild, List.nil_append, wTruncLim]
        rfl
      have hfull : TendstoUniformlyOn (fun N l => wTrunc T.val l (K + 1) N [])
          (fun l => wTruncLim T l (K + 1)) atTop (Set.Icc a b) :=
        tendstoUniformlyOn_nat_add_one_iff.mp hshift
      refine ⟨hfull, fun l hl => ⟨?_, ?_⟩⟩
      · apply ge_of_tendsto (hfull.tendsto_at hl)
        filter_upwards with N
        exact (wTrunc_nonneg_le_wN hT (hroot l hl).1 (K + 1) N).1
      · apply le_of_tendsto (hfull.tendsto_at hl)
        filter_upwards with N
        exact (wTrunc_nonneg_le_wN hT (hroot l hl).1 (K + 1) N).2.trans
          (wN_le_mul_envelope hT ha hab hb (hroot l hl).1 hl.2 N)

/-- Uniform Cauchyness of every fixed truncation on a compact subinterval. -/
theorem uniformCauchySeqOn_wTrunc_Icc {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) (K : ℕ) :
    UniformCauchySeqOn (fun N l => wTrunc T.val l K N []) atTop (Set.Icc a b) :=
  (tendstoUniformlyOn_wTruncLim hT ha hab hb K).1.uniformCauchySeqOn

end LPPMonotonicityProof.Analytic

