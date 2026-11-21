module

public import LPPMonotonicityProof.Analytic.EscapeC1.TruncationLimit

/-!
# Completion of the `C¹` escape argument

This module completes the `C¹` part of Proposition 2.5 (`prop:regularity`): on the
regular event `RegTree`, the escape is `C¹` on `(0, m)`, the finite-depth
derivatives converge to its derivative, and `0 ≤ -∂_λ β ≤ K_I β` on every compact
interval `I`, where `K_I` is the response envelope.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

noncomputable def wLim (T : Tree) (l : ℝ) : ℝ :=
  limUnder atTop (fun N => wN T.val l N [])

private theorem summable_pathTail_at {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) (K : ℕ) :
    Summable (fun j => (pathMax b (K + j + 1) T : ℝ)) := by
  have hs := (summable_nat_add_iff K).2 (summable_pathMax ha (hT.envelope_lt_top ha hab hb))
  simpa only [Nat.add_comm K, Nat.add_assoc] using hs

private theorem pathTail_le_tsum {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) (K N : ℕ) :
    pathTail b K N T ≤ ∑' j, (pathMax b (K + j + 1) T : ℝ) := by
  unfold pathTail
  exact Summable.sum_le_tsum _ (fun j _ => NNReal.coe_nonneg _)
    (summable_pathTail_at hT ha hab hb K)

private theorem tendsto_pathTail_tsum {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) :
    Tendsto (fun K => ∑' j, (pathMax b (K + j + 1) T : ℝ)) atTop (𝓝 0) := by
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (_root_.tendsto_sum_nat_add (fun j => (pathMax b (j + 1) T : ℝ)))

/-- The logarithmic responses are uniformly Cauchy on each compact subinterval. -/
theorem uniformCauchySeqOn_wN_Icc {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) :
    UniformCauchySeqOn (fun N l => wN T.val l N []) atTop (Set.Icc a b) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ K in atTop, (∑' j, (pathMax b (K + j + 1) T : ℝ)) < ε / 4 :=
    (tendsto_pathTail_tsum hT ha hab hb).eventually (Iio_mem_nhds (by positivity))
  obtain ⟨K, hK⟩ := hsmall.exists
  have htail (N : ℕ) : pathTail b K N T ≤ ∑' j, (pathMax b (K + j + 1) T : ℝ) :=
    pathTail_le_tsum hT ha hab hb K N
  have htrunc := (uniformCauchySeqOn_wTrunc_Icc hT ha hab hb K)
  obtain ⟨N₀, hN₀⟩ := Metric.uniformCauchySeqOn_iff.mp htrunc (ε / 2) (by positivity)
  refine ⟨N₀, fun M hM N hN l hl => ?_⟩
  have herr (J : ℕ) : |wN T.val l J [] - wTrunc T.val l K J []| ≤
      ∑' j, (pathMax b (K + j + 1) T : ℝ) :=
    (abs_wN_sub_wTrunc_le hT.1.1 (ha.trans_le hl.1) (ha.trans_le hab) hl.2 K J).trans (htail J)
  have hlast : |wTrunc T.val l K N [] - wN T.val l N []| ≤
      ∑' j, (pathMax b (K + j + 1) T : ℝ) := by
    rw [abs_sub_comm]
    exact herr N
  have hdist : dist (wTrunc T.val l K M []) (wTrunc T.val l K N []) < ε / 2 :=
    hN₀ M hM N hN l hl
  calc
    dist (wN T.val l M []) (wN T.val l N []) ≤
        dist (wN T.val l M []) (wTrunc T.val l K M []) +
        dist (wTrunc T.val l K M []) (wTrunc T.val l K N []) +
        dist (wTrunc T.val l K N []) (wN T.val l N []) := dist_triangle4 _ _ _ _
    _ ≤ (∑' j, (pathMax b (K + j + 1) T : ℝ)) +
        dist (wTrunc T.val l K M []) (wTrunc T.val l K N []) +
        (∑' j, (pathMax b (K + j + 1) T : ℝ)) := by
      apply add_le_add
      · apply add_le_add
        · simpa only [Real.dist_eq] using herr M
        · exact le_rfl
      · simpa only [Real.dist_eq] using hlast
    _ < ε / 4 + ε / 2 + ε / 4 := add_lt_add (add_lt_add hK hdist) hK
    _ = ε := by ring

private theorem tendsto_wN_lim {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) {l : ℝ} (hl : l ∈ Set.Icc a b) :
    Tendsto (fun N => wN T.val l N []) atTop (𝓝 (wLim T l)) := by
  apply CauchySeq.tendsto_limUnder
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.uniformCauchySeqOn_iff.mp
    (uniformCauchySeqOn_wN_Icc hT ha hab hb) ε hε
  exact ⟨N₀, fun M hM N hN => hN₀ M hM N hN l hl⟩

/-- Uniform convergence of the logarithmic responses to their pointwise limit. -/
theorem tendstoUniformlyOn_wN_Icc {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) :
    TendstoUniformlyOn (fun N l => wN T.val l N []) (fun l => wLim T l)
      atTop (Set.Icc a b) :=
  (uniformCauchySeqOn_wN_Icc hT ha hab hb).tendstoUniformlyOn_of_tendsto
    (fun l hl => tendsto_wN_lim hT ha hab hb hl)

private theorem escapeN_child_final (T : Tree) (l : ℝ) (N : ℕ) (j : ℕ) (v : Address) :
    escapeN (child T j).val l N v = escapeN T.val l N (j :: v) := by
  have hst : subtree T [j] = child T j := by rw [subtree_cons, subtree_nil]
  simpa only [hst, List.singleton_append] using escapeN_subtree T l N [j] v

private theorem wN_child_final (T : Tree) (l : ℝ) (N : ℕ) (j : ℕ) (v : Address) :
    wN (child T j).val l N v = wN T.val l N (j :: v) := by
  induction N generalizing j v with
  | zero => rfl
  | succ N ih =>
      simp only [wN, offChild, List.nil_append, List.cons_append]
      simp only [escapeN_child_final, ih]
      rfl

private theorem continuousAt_wN {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 0 < l) (N : ℕ) : ContinuousAt (fun x => wN T.val x N []) l := by
  induction N generalizing T with
  | zero => simpa only [wN] using continuousAt_const
  | succ N ih =>
      have he : ContinuousAt (fun x => escapeN T.val x (N + 1) []) l :=
        (hasDerivAt_escapeN_root hT hl (N + 1)).continuousAt
      have hsum : ContinuousAt
          (fun x => ∑ j : Fin (degree T), escapeN (child T (j + 1)).val x N []) l := by
        apply tendsto_finsetSum
        intro i _
        exact (hasDerivAt_escapeN_root (regTree_child hT i) hl N).continuousAt
      have hS : 0 < ∑ j : Fin (degree T), escapeN (child T (j + 1)).val l N [] := by
        let i0 : Fin (degree T) := ⟨0, by
          have hr := hT.1.1 [] (present_nil T)
          change 0 < degree T at hr
          omega⟩
        exact Finset.sum_pos (fun i _ => escapeN_pos _ hl _ _
          (leaflessBelow_tree (leafless_child hT.1.1 i) N [] (present_nil _)))
          ⟨i0, Finset.mem_univ _⟩
      simp only [wN, offChild, List.nil_append]
      simp_rw [← escapeN_child_final, ← wN_child_final]
      apply (continuousAt_const.sub he).mul
      apply continuousAt_const.add
      apply tendsto_finsetSum
      intro i _
      exact (((hasDerivAt_escapeN_root (regTree_child hT i) hl N).continuousAt.div hsum hS.ne').mul
        (ih (regTree_child hT i)))

/-- The uniform limit `wLim` is continuous on every compact subinterval. -/
theorem continuousOn_wLim_Icc {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) :
    ContinuousOn (fun l => wLim T l) (Set.Icc a b) := by
  apply (tendstoUniformlyOn_wN_Icc hT ha hab hb).continuousOn
  exact Filter.Frequently.of_forall fun N l hl =>
    (continuousAt_wN hT (ha.trans_le hl.1) N).continuousWithinAt

private theorem wLim_nonneg {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) {l : ℝ} (hl : l ∈ Set.Icc a b) :
    0 ≤ wLim T l := by
  apply ge_of_tendsto (tendsto_wN_lim hT ha hab hb hl)
  filter_upwards with N
  exact wN_nonneg _ (ha.trans_le hl.1) _ _ (leaflessBelow_tree hT.1.1 N [] (present_nil T))

private theorem wLim_le_mul_envelope {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) {l : ℝ} (hl : l ∈ Set.Icc a b) :
    wLim T l ≤ a * (envelope a b T).toReal := by
  apply le_of_tendsto (tendsto_wN_lim hT ha hab hb hl)
  filter_upwards with N
  exact wN_le_mul_envelope hT ha hab hb (ha.trans_le hl.1) hl.2 N
private theorem tendstoUniformlyOn_deriv_escapeN_Icc {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) :
    TendstoUniformlyOn (fun N l => -(escapeN T.val l N [] * wN T.val l N []) / l)
      (fun l => -(escape l T * wLim T l) / l) atTop (Set.Icc a b) := by
  have hEsc := tendstoUniformlyOn_escapeN_Icc hT ha hab hb
  have hW := tendstoUniformlyOn_wN_Icc hT ha hab hb
  have hprod := tendstoUniformlyOn_mul_of_compact
    (K := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc 0 (a * (envelope a b T).toReal))
    hEsc hW (isCompact_Icc.prod isCompact_Icc)
    (fun N l hl => ⟨⟨escapeN_nonneg' _ (ha.trans_le hl.1) _ _,
      escapeN_le_one _ (ha.trans_le hl.1) _ _⟩,
      wN_nonneg _ (ha.trans_le hl.1) _ _ (leaflessBelow_tree hT.1.1 N [] (present_nil T)),
      wN_le_mul_envelope hT ha hab hb (ha.trans_le hl.1) hl.2 N⟩)
    (fun l hl => ⟨⟨(escape_mem_Icc (ha.trans_le hl.1) _).1,
      (escape_mem_Icc (ha.trans_le hl.1) _).2⟩,
      wLim_nonneg hT ha hab hb hl, wLim_le_mul_envelope hT ha hab hb hl⟩)
  have hId : TendstoUniformlyOn (fun (_ : ℕ) (l : ℝ) => l) (fun l => l) atTop (Set.Icc a b) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Filter.Eventually.of_forall (fun N x hx => by simpa using hε)
  have hInv := tendstoUniformlyOn_inv ha hId (fun _ l hl => hl.1) (fun l hl => hl.1)
  simp only [div_eq_mul_inv, Pi.neg_apply]
  apply tendstoUniformlyOn_mul_of_compact
    (K := Set.Icc (-(a * (envelope a b T).toReal)) 0 ×ˢ Set.Icc 0 a⁻¹)
    hprod.neg hInv (isCompact_Icc.prod isCompact_Icc)
  · intro N l hl
    have hw0 := wN_nonneg T.val (ha.trans_le hl.1) N [] (leaflessBelow_tree hT.1.1 N [] (present_nil T))
    have hp0 : 0 ≤ escapeN T.val l N [] * wN T.val l N [] :=
      mul_nonneg (escapeN_nonneg' _ (ha.trans_le hl.1) _ _) hw0
    have hp1 : escapeN T.val l N [] * wN T.val l N [] ≤ a * (envelope a b T).toReal := by
      calc
        _ ≤ 1 * (a * (envelope a b T).toReal) :=
          mul_le_mul (escapeN_le_one _ (ha.trans_le hl.1) _ _)
            (wN_le_mul_envelope hT ha hab hb (ha.trans_le hl.1) hl.2 N) hw0 zero_le_one
        _ = _ := one_mul _
    have hli : 0 < l := ha.trans_le hl.1
    exact ⟨⟨neg_le_neg hp1, neg_nonpos.mpr hp0⟩,
      inv_nonneg.mpr hli.le, (inv_le_inv₀ hli ha).2 hl.1⟩
  · intro l hl
    have hp0 : 0 ≤ escape l T * wLim T l :=
      mul_nonneg (escape_mem_Icc (ha.trans_le hl.1) _).1 (wLim_nonneg hT ha hab hb hl)
    have hp1 : escape l T * wLim T l ≤ a * (envelope a b T).toReal := by
      calc
        _ ≤ 1 * (a * (envelope a b T).toReal) :=
          mul_le_mul (escape_mem_Icc (ha.trans_le hl.1) _).2
            (wLim_le_mul_envelope hT ha hab hb hl) (wLim_nonneg hT ha hab hb hl) zero_le_one
        _ = _ := one_mul _
    have hli : 0 < l := ha.trans_le hl.1
    exact ⟨⟨neg_le_neg hp1, neg_nonpos.mpr hp0⟩,
      inv_nonneg.mpr hli.le, (inv_le_inv₀ hli ha).2 hl.1⟩

private theorem hasDerivAt_escape_on_Ioo {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) {l : ℝ} (hl : l ∈ Set.Ioo a b) :
    HasDerivAt (fun x => escape x T) (-(escape l T * wLim T l) / l) l := by
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo
    ((tendstoUniformlyOn_deriv_escapeN_Icc hT ha hab hb).mono Set.Ioo_subset_Icc_self)
  · filter_upwards with N
    intro x hx
    exact hasDerivAt_escapeN_root hT (lt_trans ha hx.1) N
  · intro x hx
    exact tendsto_escapeN_root (lt_trans ha hx.1)
  · exact hl

private theorem hasDerivAt_escape_limit {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    HasDerivAt (fun x => escape x T) (-(escape l T * wLim T l) / l) l := by
  let a := l / 2
  let b := (l + mean μ) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hl.1]
  have hla : l ∈ Set.Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith [hl.1, hl.2]
  have hab : a ≤ b := hla.1.le.trans hla.2.le
  have hb : b < mean μ := by dsimp [b]; linarith [hl.2]
  exact hasDerivAt_escape_on_Ioo hT ha hab hb hla

private theorem continuousOn_derivLim_Icc {T : Tree} (hT : RegTree μ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) :
    ContinuousOn (fun l => -(escape l T * wLim T l) / l) (Set.Icc a b) := by
  apply (tendstoUniformlyOn_deriv_escapeN_Icc hT ha hab hb).continuousOn
  exact Filter.Frequently.of_forall fun N l hl =>
    (((hasDerivAt_escapeN_root hT (ha.trans_le hl.1) N).continuousAt.mul
      (continuousAt_wN hT (ha.trans_le hl.1) N)).neg.div continuousAt_id
        (ha.trans_le hl.1).ne').continuousWithinAt

private theorem continuousOn_deriv_escape {T : Tree} (hT : RegTree μ T) :
    ContinuousOn (deriv (fun l => escape l T)) (Set.Ioo 0 (mean μ)) := by
  apply continuousOn_of_locally_continuousOn
  intro l hl
  let a := l / 2
  let b := (l + mean μ) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hl.1]
  have hla : l ∈ Set.Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith [hl.1, hl.2]
  have hab : a ≤ b := hla.1.le.trans hla.2.le
  have hb : b < mean μ := by dsimp [b]; linarith [hl.2]
  refine ⟨Set.Ioo a b, isOpen_Ioo, hla, ?_⟩
  have hsub : Set.Ioo 0 (mean μ) ∩ Set.Ioo a b = Set.Ioo a b := by
    apply Set.inter_eq_right.mpr
    intro x hx
    exact ⟨lt_trans ha hx.1, hx.2.trans hb⟩
  rw [hsub]
  apply ((continuousOn_derivLim_Icc hT ha hab hb).mono Set.Ioo_subset_Icc_self).congr
  intro x hx
  exact (hasDerivAt_escape_on_Ioo hT ha hab hb hx).deriv

/-- Proposition 2.5: almost sure tree-wise escape probabilities are `C¹` on `(0,m)`. -/
theorem escape_contDiffOn {T : Tree} (hT : RegTree μ T) :
    ContDiffOn ℝ 1 (fun l => escape l T) (Set.Ioo 0 (mean μ)) := by
  apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).2
  constructor
  · intro l hl
    exact (hasDerivAt_escape_limit hT hl).differentiableAt.differentiableWithinAt
  · apply (continuousOn_deriv_escape hT).congr
    intro x hx
    exact derivWithin_of_isOpen isOpen_Ioo hx

/-- The finite-depth derivatives converge to the escape derivative. -/
theorem tendsto_deriv_escapeN {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Tendsto (fun N => deriv (fun l' => escapeN T.val l' N []) l) atTop
      (𝓝 (deriv (fun l' => escape l' T) l)) := by
  let a := l / 2
  let b := (l + mean μ) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hl.1]
  have hla : l ∈ Set.Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith [hl.1, hl.2]
  have hab : a ≤ b := hla.1.le.trans hla.2.le
  have hb : b < mean μ := by dsimp [b]; linarith [hl.2]
  have ht := (tendstoUniformlyOn_deriv_escapeN_Icc hT ha hab hb).tendsto_at
    (Set.mem_Icc.mpr ⟨hla.1.le, hla.2.le⟩)
  rw [(hasDerivAt_escape_limit hT hl).deriv]
  apply ht.congr'
  filter_upwards with N
  exact (hasDerivAt_escapeN_root hT hl.1 N).deriv.symm

/-- Proposition 2.5: the derivative has the canonical integrable-envelope bound. -/
theorem neg_deriv_escape_le {T : Tree} (hT : RegTree μ T) {a b l : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) (hl : l ∈ Set.Icc a b) :
    envelope a b T < ⊤ ∧ 0 ≤ -deriv (fun l' => escape l' T) l ∧
      -deriv (fun l' => escape l' T) l ≤ (envelope a b T).toReal * escape l T := by
  have hl0 : 0 < l := ha.trans_le hl.1
  have hlim : l ∈ Set.Ioo 0 (mean μ) := ⟨hl0, hl.2.trans_lt hb⟩
  have hd := (hasDerivAt_escape_limit hT hlim).deriv
  have hwdiv : wLim T l / l ≤ (envelope a b T).toReal := by
    apply (div_le_iff₀ hl0).2
    calc
      wLim T l ≤ a * (envelope a b T).toReal := wLim_le_mul_envelope hT ha hab hb hl
      _ ≤ l * (envelope a b T).toReal :=
        mul_le_mul_of_nonneg_right hl.1 ENNReal.toReal_nonneg
      _ = (envelope a b T).toReal * l := mul_comm _ _
  refine ⟨hT.envelope_lt_top ha hab hb, ?_, ?_⟩
  · rw [hd]
    simpa only [neg_div, neg_neg] using
      div_nonneg (mul_nonneg (escape_mem_Icc hl0 _).1 (wLim_nonneg hT ha hab hb hl)) hl0.le
  · rw [hd]
    calc
      -(-(escape l T * wLim T l) / l) = escape l T * (wLim T l / l) := by ring
      _ ≤ escape l T * (envelope a b T).toReal :=
        mul_le_mul_of_nonneg_left hwdiv (escape_mem_Icc hl0 _).1
      _ = (envelope a b T).toReal * escape l T := mul_comm _ _

end LPPMonotonicityProof.Analytic
