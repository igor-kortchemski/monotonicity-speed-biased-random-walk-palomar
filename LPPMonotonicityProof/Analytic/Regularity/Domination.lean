module

public import LPPMonotonicityProof.Analytic.Regularity.Envelope
public import LPPMonotonicityProof.Analytic.RegularityFinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Finite-depth response domination

This module bounds the finite-depth logarithmic response by the path maxima of the
sibling factors, as in the path expansion of the proof of Proposition 2.5
(`prop:regularity`), and by `l / (1 - l)` below bias one.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

private theorem leaflessBelow_treeProv {T : Tree}
    (hT : ∀ v, Present T v → 1 ≤ T.val v) :
    ∀ (N : ℕ) (v : Address), Present T v → LeaflessBelow T.val N v := by
  intro N
  induction N with
  | zero => intro v _; trivial
  | succ N ih =>
      intro v hv
      refine ⟨hT v hv, fun i => ih _ ?_⟩
      exact (present_append_singleton T v (i.val + 1) hv).2 ⟨Nat.succ_pos _, i.isLt⟩

private theorem leafless_childProv {T : Tree}
    (hT : ∀ v, Present T v → 1 ≤ T.val v) (j : ℕ) (hj : j ≤ degree T) (hj0 : 1 ≤ j) :
    ∀ v, Present (child T j) v → 1 ≤ (child T j).val v := by
  intro v hv
  exact hT (j :: v) ⟨hj0, hj, hv⟩

private theorem escape_le_escapeNProv {l : ℝ} (hl : 0 < l) (T : Tree) (N : ℕ) :
    escape l T ≤ escapeN T.val l N [] := by
  have hnonneg : ∀ (M : ℕ) (v : Address), 0 ≤ escapeN T.val l M v := by
    intro M
    induction M with
    | zero => intro v; simp [escapeN]
    | succ M ih =>
        intro v
        simp only [escapeN]
        apply div_nonneg
        · exact Finset.sum_nonneg fun i _ => ih _
        · have hS : 0 ≤ ∑ i : Fin (T.val v), escapeN T.val l M (offChild T.val v i) :=
            Finset.sum_nonneg fun i _ => ih _
          positivity
  apply ciInf_le
  exact ⟨0, by rintro x ⟨M, rfl⟩; exact hnonneg M []⟩

private theorem escapeN_child_tree (T : Tree) (l : ℝ) (N : ℕ) (j : ℕ) (v : Address) :
    escapeN (child T j).val l N v = escapeN T.val l N (j :: v) := by
  have hst : subtree T [j] = child T j := by rw [subtree_cons, subtree_nil]
  simpa only [hst, List.singleton_append] using escapeN_subtree T l N [j] v

private theorem wN_child_tree (T : Tree) (l : ℝ) (N : ℕ) (j : ℕ) (v : Address) :
    wN (child T j).val l N v = wN T.val l N (j :: v) := by
  induction N generalizing j v with
  | zero => rfl
  | succ N ih =>
      simp only [wN, offChild, List.nil_append, List.cons_append]
      simp only [escapeN_child_tree, ih]
      rfl

private theorem wN_succ_tree (T : Tree) (l : ℝ) (N : ℕ) :
    wN T.val l (N + 1) [] = (1 - escapeN T.val l (N + 1) []) *
      (1 + ∑ i : Fin (degree T),
        escapeN (child T (i + 1)).val l N [] /
          (∑ j : Fin (degree T), escapeN (child T (j + 1)).val l N []) *
            wN (child T (i + 1)).val l N []) := by
  simp only [wN, degree, offChild, List.nil_append]
  simp_rw [← escapeN_child_tree, ← wN_child_tree]
  rfl

private theorem weighted_average_one {n : ℕ} (b : Fin n → ℝ) {S : ℝ}
    (hS : S ≠ 0) (hsum : (∑ i, b i) = S) :
    ∑ i, b i / S = 1 := by
  rw [← Finset.sum_div, hsum, div_self hS]

private theorem one_sub_escapeN_le_sib {l lPos : ℝ} (hl : 0 < l)
    (hlPos : 0 < lPos) (hll : l ≤ lPos) (T : Tree)
    (hT : ∀ v, Present T v → 1 ≤ T.val v) (N : ℕ) (i : Fin (degree T)) :
    1 - escapeN T.val l (N + 1) [] ≤ (sib lPos T i : ℝ) := by
  let b : Fin (degree T) → ℝ := fun j => escapeN (child T (j + 1)).val l N []
  let S : ℝ := ∑ j, b j
  let R : ℝ := ∑ j ∈ Finset.univ.erase i, escape lPos (child T (j + 1))
  have hb (j : Fin (degree T)) : 0 < b j := by
    exact escapeN_pos _ hl _ _ (leaflessBelow_treeProv (leafless_childProv hT (j + 1)
      (Nat.succ_le_of_lt j.isLt) (Nat.succ_le_succ (Nat.zero_le _)))
      N [] (present_nil _))
  have hS : 0 < S := Finset.sum_pos (fun j _ => hb j) ⟨i, Finset.mem_univ i⟩
  have hroot : 1 - escapeN T.val l (N + 1) [] = l / (l + S) := by
    have he : escapeN T.val l (N + 1) [] = S / (l + S) := by
      simp only [escapeN, degree, offChild, List.nil_append]
      simp only [b, S]
      simp_rw [← escapeN_child_tree]
      rfl
    rw [he]
    field_simp [hl.ne', (add_pos_of_pos_of_nonneg hl hS.le).ne']
    ring
  have hNinf (j : Fin (degree T)) : escape l (child T (j + 1)) ≤ b j := by
    simpa only [b] using escape_le_escapeNProv hl (child T (j + 1)) N
  have hlbias (j : Fin (degree T)) : escape lPos (child T (j + 1)) ≤ escape l (child T (j + 1)) :=
    escape_antitoneOn _ hl hlPos hll
  have hSR : R ≤ S := by
    calc
      R ≤ ∑ j ∈ Finset.univ.erase i, b j := by
        apply Finset.sum_le_sum
        intro j _
        exact (hlbias j).trans (hNinf j)
      _ ≤ S := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro j _ hj
        exact (hb j).le
  have hR : 0 ≤ R := Finset.sum_nonneg fun j _ => (escape_mem_Icc hlPos _).1
  rw [hroot, coe_sib hlPos]
  change l / (l + S) ≤ lPos / (lPos + R)
  calc
    l / (l + S) ≤ l / (l + R) := by
      apply div_le_div_of_nonneg_left hl.le (add_pos_of_pos_of_nonneg hl hR) (add_le_add (le_refl l) hSR)
    _ ≤ lPos / (lPos + R) := by
      apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg hl hR)
        (add_pos_of_pos_of_nonneg hlPos hR)).2
      nlinarith [mul_le_mul_of_nonneg_right hll hR]

/-- The finite logarithmic response is dominated by the path-maximum envelope. -/
theorem wN_le_pathMax {lNeg lPos l : ℝ} {T : Tree}
    (hT : ∀ v, Present T v → 1 ≤ T.val v) (hl : 0 < l)
    (hlPos : 0 < lPos) (hll : l ≤ lPos) (N : ℕ) :
    wN T.val l N [] ≤ ∑ k ∈ Finset.range N, (pathMax lPos (k + 1) T : ℝ) := by
  induction N generalizing T with
  | zero => simp [wN]
  | succ N ih =>
      let b : Fin (degree T) → ℝ := fun j => escapeN (child T (j + 1)).val l N []
      let w : Fin (degree T) → ℝ := fun j => wN (child T (j + 1)).val l N []
      let S : ℝ := ∑ j, b j
      let C : ℝ := (pathMax lPos 1 T : ℝ) +
        ∑ k ∈ Finset.range N, (pathMax lPos (k + 2) T : ℝ)
      have hb (j : Fin (degree T)) : 0 < b j := by
        exact escapeN_pos _ hl _ _ (leaflessBelow_treeProv (leafless_childProv hT (j + 1)
          (Nat.succ_le_of_lt j.isLt) (Nat.succ_le_succ (Nat.zero_le _))) N [] (present_nil _))
      have hS : 0 < S := by
        let i0 : Fin (degree T) := ⟨0, by have := hT [] (present_nil T); simp only [degree]; omega⟩
        exact Finset.sum_pos (fun j _ => hb j) ⟨i0, Finset.mem_univ i0⟩
      have hweights : ∑ j, b j / S = 1 := weighted_average_one b hS.ne' rfl
      have hweight_nonneg (j : Fin (degree T)) : 0 ≤ b j / S := div_nonneg (hb j).le hS.le
      have hCchild (i : Fin (degree T)) :
          (1 - escapeN T.val l (N + 1) []) * (1 + w i) ≤ C := by
        have hw : w i ≤ ∑ k ∈ Finset.range N,
            (pathMax lPos (k + 1) (child T (i + 1)) : ℝ) := by
          apply ih
          exact leafless_childProv hT (i + 1) (Nat.succ_le_of_lt i.isLt)
            (Nat.succ_le_succ (Nat.zero_le _))
        have hone : 1 - escapeN T.val l (N + 1) [] ≤ (sib lPos T i : ℝ) :=
          one_sub_escapeN_le_sib hl hlPos hll T hT N i
        have hone0 : 0 ≤ 1 - escapeN T.val l (N + 1) [] := sub_nonneg.mpr (escapeN_le_one _ hl _ _)
        have hw0 : 0 ≤ w i := wN_nonneg _ hl _ _ (leaflessBelow_treeProv
          (leafless_childProv hT (i + 1) (Nat.succ_le_of_lt i.isLt)
            (Nat.succ_le_succ (Nat.zero_le _))) N [] (present_nil _))
        calc
          (1 - escapeN T.val l (N + 1) []) * (1 + w i) ≤
              (sib lPos T i : ℝ) *
                (1 + ∑ k ∈ Finset.range N, (pathMax lPos (k + 1) (child T (i + 1)) : ℝ)) := by
            apply mul_le_mul hone (add_le_add (le_refl 1) hw) (add_nonneg zero_le_one hw0)
            exact (sib lPos T i).coe_nonneg
          _ = (sib lPos T i : ℝ) + ∑ k ∈ Finset.range N,
              ((sib lPos T i : ℝ) * (pathMax lPos (k + 1) (child T (i + 1)) : ℝ)) := by
            rw [mul_add, mul_one, Finset.mul_sum]
          _ ≤ C := by
            apply add_le_add
            · have hs : sib lPos T i * pathMax lPos 0 (child T (i + 1)) ≤ pathMax lPos 1 T := by
                change _ ≤ Finset.univ.sup (fun j : Fin (degree T) =>
                  sib lPos T j * pathMax lPos 0 (child T (j + 1)))
                exact Finset.le_sup (f := fun j : Fin (degree T) =>
                  sib lPos T j * pathMax lPos 0 (child T (j + 1))) (Finset.mem_univ i)
              have hs' : sib lPos T i ≤ pathMax lPos 1 T := by
                simpa only [pathMax, mul_one] using hs
              exact_mod_cast hs'
            · apply Finset.sum_le_sum
              intro k _
              have hs : sib lPos T i * pathMax lPos (k + 1) (child T (i + 1)) ≤
                  pathMax lPos (k + 2) T := by
                change _ ≤ Finset.univ.sup (fun j : Fin (degree T) =>
                  sib lPos T j * pathMax lPos (k + 1) (child T (j + 1)))
                exact Finset.le_sup (f := fun j : Fin (degree T) =>
                  sib lPos T j * pathMax lPos (k + 1) (child T (j + 1))) (Finset.mem_univ i)
              exact_mod_cast hs
      have hsum : wN T.val l (N + 1) [] =
          ∑ i, (b i / S) * ((1 - escapeN T.val l (N + 1) []) * (1 + w i)) := by
        rw [wN_succ_tree]
        change (1 - escapeN T.val l (N + 1) []) * (1 + ∑ i, b i / S * w i) = _
        calc
          _ = (1 - escapeN T.val l (N + 1) []) * ∑ i, (b i / S) * (1 + w i) := by
            congr 1
            calc
              1 + ∑ i, b i / S * w i = (∑ i, b i / S) + ∑ i, b i / S * w i := by rw [hweights]
              _ = _ := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro i _
                ring
          _ = _ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      rw [hsum]
      calc
        _ ≤ ∑ i, (b i / S) * C := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hCchild i) (hweight_nonneg i)
        _ = C := by rw [← Finset.sum_mul, hweights, one_mul]
        _ = _ := by
          simp only [C]
          rw [add_comm, Finset.sum_range_succ']

/-- **Below bias one.** The finite response is bounded by `l / (1-l)`. -/
theorem wN_le_geom {l : ℝ} {T : Tree}
    (hT : ∀ v, Present T v → 1 ≤ T.val v) (hl : 0 < l) (hl1 : l < 1) (N : ℕ) :
    wN T.val l N [] ≤ l / (1 - l) := by
  induction N generalizing T with
  | zero => simp [wN, div_nonneg hl.le (sub_nonneg.mpr hl1.le)]
  | succ N ih =>
      let b : Fin (degree T) → ℝ := fun j => escapeN (child T (j + 1)).val l N []
      let w : Fin (degree T) → ℝ := fun j => wN (child T (j + 1)).val l N []
      let S : ℝ := ∑ j, b j
      have hb (j : Fin (degree T)) : 0 < b j := by
        exact escapeN_pos _ hl _ _ (leaflessBelow_treeProv (leafless_childProv hT (j + 1)
          (Nat.succ_le_of_lt j.isLt) (Nat.succ_le_succ (Nat.zero_le _))) N [] (present_nil _))
      have hS : 0 < S := by
        let i0 : Fin (degree T) := ⟨0, by have := hT [] (present_nil T); simp only [degree]; omega⟩
        exact Finset.sum_pos (fun j _ => hb j) ⟨i0, Finset.mem_univ i0⟩
      have hweights : ∑ j, b j / S = 1 := weighted_average_one b hS.ne' rfl
      have hw : ∑ j, (b j / S) * w j ≤ l / (1 - l) := by
        calc
          _ ≤ ∑ j, (b j / S) * (l / (1 - l)) := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (div_nonneg (hb j).le hS.le)
            apply ih
            exact leafless_childProv hT (j + 1) (Nat.succ_le_of_lt j.isLt)
              (Nat.succ_le_succ (Nat.zero_le _))
          _ = _ := by rw [← Finset.sum_mul, hweights, one_mul]
      have hone : 1 - escapeN T.val l (N + 1) [] ≤ l := by
        have hj := escapeN_lower_bound T.val hl hl1 (N + 1) []
          (leaflessBelow_treeProv hT (N + 1) [] (present_nil T))
        linarith
      rw [wN_succ_tree]
      change (1 - escapeN T.val l (N + 1) []) * (1 + ∑ j, b j / S * w j) ≤ _
      have hfactor : 0 ≤ 1 - escapeN T.val l (N + 1) [] :=
        sub_nonneg.mpr (escapeN_le_one _ hl _ _)
      have havg : 0 ≤ ∑ j, b j / S * w j := by
        apply Finset.sum_nonneg
        intro j _
        exact mul_nonneg (div_nonneg (hb j).le hS.le) (wN_nonneg _ hl _ _
          (leaflessBelow_treeProv (leafless_childProv hT (j + 1) (Nat.succ_le_of_lt j.isLt)
            (Nat.succ_le_succ (Nat.zero_le _))) N [] (present_nil _)))
      calc
        _ ≤ l * (1 + l / (1 - l)) := mul_le_mul hone (add_le_add (le_refl 1) hw) (by positivity) hl.le
        _ = l / (1 - l) := by field_simp [(sub_pos.mpr hl1).ne']; ring

end LPPMonotonicityProof.Analytic
