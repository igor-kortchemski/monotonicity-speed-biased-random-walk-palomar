module

public import LPPMonotonicityProof.Speed.Interface.Escape
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Deterministic properties of the infinite escape

This module proves the deterministic parts of Lemma 2.1 (`lem:escape`) for the
escape `escape l T`: the recursion, bounds, monotonicity in the bias and
measurability.  All assertions are deterministic: no walk law,
leaflessness almost surely, or physical finite-escape identification is used.
-/

@[expose] public section

open scoped BigOperators
open Filter Topology

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite

/-- The finite sum of the escapes of the existing children. -/
noncomputable def childSum (l : ℝ) (T : Tree) : ℝ :=
  ∑ i : Fin (degree T), escape l (child T (i.val + 1))

private theorem escapeN_nonneg' (ω : List ℕ → ℕ) {l : ℝ} (hl : 0 < l) :
    ∀ (N : ℕ) (v : List ℕ), 0 ≤ escapeN ω l N v := by
  intro N
  induction N with
  | zero => intro v; simp [escapeN]
  | succ N ih =>
      intro v
      rw [escapeN]
      have hS : 0 ≤ ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i) :=
        Finset.sum_nonneg fun i _ => ih _
      exact div_nonneg hS (by positivity)

/-- Shifting a raw field by one address component shifts every finite escape. -/
theorem escapeN_shift (ω : List ℕ → ℕ) (l : ℝ) (j : ℕ) :
    ∀ (k : ℕ) (v : List ℕ),
      escapeN (fun u => ω (j :: u)) l k v = escapeN ω l k (j :: v) := by
  intro k
  induction k with
  | zero => intro v; rfl
  | succ k ih =>
      intro v
      rw [escapeN, escapeN]
      have hsum :
          (∑ i : Fin ((fun u => ω (j :: u)) v),
            escapeN (fun u => ω (j :: u)) l k (offChild (fun u => ω (j :: u)) v i)) =
          ∑ i : Fin (ω (j :: v)), escapeN ω l k (offChild ω (j :: v) i) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [offChild, List.cons_append, List.append_assoc] using ih (v ++ [i.val + 1])
      rw [hsum]

private theorem escapeN_antitone_height' (ω : List ℕ → ℕ) {l : ℝ} (hl : 0 < l)
    (v : List ℕ) : Antitone fun N => escapeN ω l N v := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (escapeN_anti_height ω hl b v).trans ih

private theorem bddBelow_escapeN (ω : List ℕ → ℕ) {l : ℝ} (hl : 0 < l)
    (v : List ℕ) : BddBelow (Set.range fun N => escapeN ω l N v) :=
  ⟨0, by rintro _ ⟨N, rfl⟩; exact escapeN_nonneg' ω hl N v⟩

private theorem tendsto_escapeN (ω : List ℕ → ℕ) {l : ℝ} (hl : 0 < l)
    (v : List ℕ) : Tendsto (fun N => escapeN ω l N v) atTop (𝓝 (escapeRaw ω l v)) := by
  exact tendsto_atTop_ciInf (escapeN_antitone_height' ω hl v) (bddBelow_escapeN ω hl v)

private theorem escape_nonneg (l : ℝ) (T : Tree) (hl : 0 < l) : 0 ≤ escape l T := by
  exact le_ciInf fun N => escapeN_nonneg' T.val hl N []

private theorem childSum_nonneg {l : ℝ} (T : Tree) (hl : 0 < l) : 0 ≤ childSum l T := by
  exact Finset.sum_nonneg fun i _ => escape_nonneg l _ hl

private theorem tendsto_escape_child {l : ℝ} (hl : 0 < l) (T : Tree) (j : ℕ) :
    Tendsto (fun N => escapeN T.val l N [j]) atTop (𝓝 (escape l (child T j))) := by
  have hst : subtree T [j] = child T j := by rw [subtree_cons, subtree_nil]
  rw [← hst, escape_subtree]
  exact tendsto_escapeN T.val hl [j]

/-- The infinite escape satisfies the same local recursion as the finite
escapes, for every canonical tree, including trees with leaves. -/
theorem escape_eq {l : ℝ} (hl : 0 < l) (T : Tree) :
    escape l T = childSum l T / (l + childSum l T) := by
  have hroot : Tendsto (fun N => escapeN T.val l (N + 1) []) atTop (𝓝 (escape l T)) := by
    exact (tendsto_escapeN T.val hl []).comp (tendsto_add_atTop_nat 1)
  have hsum : Tendsto
      (fun N => ∑ i : Fin (degree T), escapeN T.val l N [i.val + 1]) atTop
      (𝓝 (childSum l T)) := by
    exact tendsto_finsetSum Finset.univ fun i _ => tendsto_escape_child hl T (i.val + 1)
  have hratio := hsum.div (tendsto_const_nhds.add hsum)
    (ne_of_gt (add_pos_of_pos_of_nonneg hl (childSum_nonneg T hl)))
  apply tendsto_nhds_unique hroot
  apply hratio.congr
  intro N
  rfl

/-- Escape lies in the closed unit interval at every positive bias. -/
theorem escape_mem_Icc {l : ℝ} (hl : 0 < l) (T : Tree) : escape l T ∈ Set.Icc 0 1 := by
  constructor
  · exact escape_nonneg l T hl
  · change escapeRaw T.val l [] ≤ 1
    calc
      escapeRaw T.val l [] ≤ escapeN T.val l 0 [] := ciInf_le (bddBelow_escapeN T.val hl []) 0
      _ = 1 := rfl

/-- Escape is strictly below one at every positive bias and for every tree. -/
theorem escape_lt_one {l : ℝ} (hl : 0 < l) (T : Tree) : escape l T < 1 := by
  change escapeRaw T.val l [] < 1
  exact (ciInf_le (bddBelow_escapeN T.val hl []) 1).trans_lt
    (by simpa using escapeN_succ_lt_one T.val hl 0 [])

/-- The infinite escape is nonincreasing in the positive bias. -/
theorem escape_antitoneOn (T : Tree) : AntitoneOn (fun l => escape l T) (Set.Ioi 0) := by
  intro a ha b hb hab
  change escapeRaw T.val b [] ≤ escapeRaw T.val a []
  apply le_ciInf
  intro N
  exact (ciInf_le (bddBelow_escapeN T.val hb []) N).trans
    (escapeN_antitoneOn T.val N [] ha hb hab)

private theorem leaflessBelow_of_positive (T : Tree)
    (hT : ∀ v, Present T v → 0 < T.val v) :
    ∀ (N : ℕ) (v : Address), Present T v → LeaflessBelow T.val N v := by
  intro N
  induction N with
  | zero => intro v _; trivial
  | succ N ih =>
      intro v hv
      refine ⟨hT v hv, fun i => ih _ ?_⟩
      apply (present_append_singleton T v (i.val + 1) hv).2
      exact ⟨Nat.succ_pos _, i.isLt⟩

/-- Below bias one, escape is at least `1 - l` on every globally leafless tree. -/
theorem escape_ge {l : ℝ} (hl : 0 < l) (hl1 : l < 1) (T : Tree)
    (hT : ∀ v, Present T v → 0 < T.val v) : 1 - l ≤ escape l T := by
  apply le_ciInf
  intro N
  exact escapeN_lower_bound T.val hl hl1 N [] (leaflessBelow_of_positive T hT N [] (present_nil T))

private theorem measurable_escapeN (l : ℝ) (N : ℕ) (v : Address) :
    Measurable (fun T : Tree => escapeN T.val l N v) := by
  induction N generalizing v with
  | zero => simp [escapeN]
  | succ N ih =>
      have hsum : Measurable (fun T : Tree =>
          ∑ j ∈ Finset.range (T.val v), escapeN T.val l N (v ++ [j + 1])) := by
        have h : Measurable (fun p : ℕ × Tree =>
            ∑ j ∈ Finset.range p.1, escapeN p.2.val l N (v ++ [j + 1])) :=
          measurable_from_prod_countable_right fun k =>
            (Finset.range k).measurable_sum fun j _ => ih (v ++ [j + 1])
        exact h.comp ((continuous_offspring v).measurable.prodMk measurable_id)
      have hsum' : Measurable (fun T : Tree =>
          ∑ i : Fin (T.val v), escapeN T.val l N (offChild T.val v i)) := by
        have heq : (fun T : Tree =>
            ∑ i : Fin (T.val v), escapeN T.val l N (offChild T.val v i)) =
            (fun T : Tree => ∑ j ∈ Finset.range (T.val v),
              escapeN T.val l N (v ++ [j + 1])) := by
          funext T
          simpa only [offChild] using Fin.sum_univ_eq_sum_range
            (fun j => escapeN T.val l N (v ++ [j + 1])) (T.val v)
        rw [heq]
        exact hsum
      change Measurable (fun T : Tree =>
        (∑ i : Fin (T.val v), escapeN T.val l N (offChild T.val v i)) /
          (l + ∑ i : Fin (T.val v), escapeN T.val l N (offChild T.val v i)))
      convert hsum'.div (measurable_const.add hsum') using 1

/-- Escape is measurable on the canonical-tree Borel space at every bias. -/
theorem measurable_escape (l : ℝ) : Measurable (escape l) := by
  exact Measurable.iInf fun N => measurable_escapeN l N []

private theorem measurable_sum_children (β : Tree → ℝ) (hβ : Measurable β) :
    Measurable (fun T : Tree => ∑ j ∈ Finset.range (degree T), β (child T (j + 1))) := by
  have h : Measurable (fun p : ℕ × Tree =>
      ∑ j ∈ Finset.range p.1, β (child p.2 (j + 1))) :=
    measurable_from_prod_countable_right fun k =>
      (Finset.range k).measurable_sum fun j _ => hβ.comp (continuous_child (j + 1)).measurable
  exact h.comp (continuous_degree.measurable.prodMk measurable_id)

/-- The finite child sum is measurable at every bias. -/
theorem measurable_childSum (l : ℝ) : Measurable (childSum l) := by
  have heq : childSum l = (fun T : Tree =>
      ∑ j ∈ Finset.range (degree T), escape l (child T (j + 1))) := by
    funext T
    exact Fin.sum_univ_eq_sum_range (fun j => escape l (child T (j + 1))) (degree T)
  rw [heq]
  exact measurable_sum_children (escape l) (measurable_escape l)

/-- Replacing one existing child changes the child sum by the corresponding
single summand. -/
theorem childSum_replaceChild {l : ℝ} {T : Tree} {i : ℕ}
    (hi : 1 ≤ i ∧ i ≤ degree T) (R : Tree) :
    childSum l (replaceChild T i R) =
      childSum l T - escape l (child T i) + escape l R := by
  let i₀ : Fin (degree T) := ⟨i - 1, by omega⟩
  have hi₀ : i₀.val + 1 = i := by dsimp [i₀]; omega
  unfold childSum
  rw [degree_replaceChild]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
  have herase : (∑ j ∈ Finset.univ.erase i₀,
      escape l (child (replaceChild T i R) (j.val + 1))) =
      ∑ j ∈ Finset.univ.erase i₀, escape l (child T (j.val + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [child_replaceChild_of_ne]
    intro hji
    apply (Finset.mem_erase.mp hj).1
    apply Fin.ext
    omega
  rw [herase, hi₀, child_replaceChild_same R hi]
  ring

end LPPMonotonicityProof.Speed
