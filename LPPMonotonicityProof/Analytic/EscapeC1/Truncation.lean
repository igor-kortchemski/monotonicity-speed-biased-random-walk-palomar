module

public import LPPMonotonicityProof.Analytic.EscapeC1

/-!
# Truncated response recursions

This module truncates the finite-depth logarithmic-response recursion after `K`
levels and bounds the truncation error by the tail of the path envelope, for the
path expansion in the proof of Proposition 2.5 (`prop:regularity`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- The finite-depth response with the recursion cut off (set to zero) after `K` levels. -/
noncomputable def wTrunc (ω : List ℕ → ℕ) (l : ℝ) : ℕ → ℕ → List ℕ → ℝ
  | _, 0, _ => 0
  | K, N + 1, v =>
      if K = 0 then 0 else
      (1 - escapeN ω l (N + 1) v) *
        (1 + ∑ i : Fin (ω v),
          escapeN ω l N (offChild ω v i) /
            (∑ j : Fin (ω v), escapeN ω l N (offChild ω v j)) *
            wTrunc ω l (K - 1) N (offChild ω v i))

/-- Terms in the path-envelope tail. -/
noncomputable def pathTail (lPos : ℝ) (K N : ℕ) (T : Tree) : ℝ :=
  ∑ j ∈ Finset.range (N - K), (pathMax lPos (K + j + 1) T : ℝ)

private theorem leaflessBelow_trunc {T : Tree}
    (hT : ∀ v, Present T v → 1 ≤ T.val v) :
    ∀ (N : ℕ) (v : Address), Present T v → LeaflessBelow T.val N v := by
  intro N
  induction N with
  | zero => intro v _; trivial
  | succ N ih =>
      intro v hv
      refine ⟨hT v hv, fun i => ih _ ?_⟩
      exact (present_append_singleton T v (i.val + 1) hv).2 ⟨Nat.succ_pos _, i.isLt⟩

private theorem leafless_child_trunc {T : Tree}
    (hT : ∀ v, Present T v → 1 ≤ T.val v) (j : ℕ) (hj : j ≤ degree T) (hj0 : 1 ≤ j) :
    ∀ v, Present (child T j) v → 1 ≤ (child T j).val v := by
  intro v hv
  exact hT (j :: v) ⟨hj0, hj, hv⟩

private theorem escapeN_child_trunc (T : Tree) (l : ℝ) (N : ℕ) (j : ℕ) (v : Address) :
    escapeN (child T j).val l N v = escapeN T.val l N (j :: v) := by
  have hst : subtree T [j] = child T j := by rw [subtree_cons, subtree_nil]
  simpa only [hst, List.singleton_append] using escapeN_subtree T l N [j] v

private theorem wN_child_trunc (T : Tree) (l : ℝ) (N : ℕ) (j : ℕ) (v : Address) :
    wN (child T j).val l N v = wN T.val l N (j :: v) := by
  induction N generalizing j v with
  | zero => rfl
  | succ N ih =>
      simp only [wN, offChild, List.nil_append, List.cons_append]
      simp only [escapeN_child_trunc, ih]
      rfl

private theorem wTrunc_child_trunc (T : Tree) (l : ℝ) (K N : ℕ) (j : ℕ) (v : Address) :
    wTrunc (child T j).val l K N v = wTrunc T.val l K N (j :: v) := by
  induction N generalizing K j v with
  | zero => rfl
  | succ N ih =>
      simp only [wTrunc, offChild, List.nil_append, List.cons_append]
      simp only [escapeN_child_trunc, ih]
      rfl

private theorem weights_sum_one {n : ℕ} (b : Fin n → ℝ) {S : ℝ}
    (hS : S ≠ 0) (hsum : (∑ i, b i) = S) :
    ∑ i, b i / S = 1 := by
  rw [← Finset.sum_div, hsum, div_self hS]

private theorem pathTail_zero (lPos : ℝ) (N : ℕ) (T : Tree) :
    pathTail lPos 0 N T = ∑ j ∈ Finset.range N, (pathMax lPos (j + 1) T : ℝ) := by
  simp only [pathTail, Nat.sub_zero, Nat.zero_add]

private theorem sib_mul_pathTail_le {l lPos : ℝ} (hl : 0 < l)
    (hlPos : 0 < lPos) (hll : l ≤ lPos) {T : Tree}
    (hT : ∀ v, Present T v → 1 ≤ T.val v) (K N : ℕ) (i : Fin (degree T)) :
    (1 - escapeN T.val l (N + 1) []) * pathTail lPos K N (child T (i + 1)) ≤
      pathTail lPos (K + 1) (N + 1) T := by
  let b : Fin (degree T) → ℝ := fun j => escapeN (child T (j + 1)).val l N []
  let S : ℝ := ∑ j, b j
  let R : ℝ := ∑ j ∈ Finset.univ.erase i, escape lPos (child T (j + 1))
  have hpos : 0 < escapeN (child T (i + 1)).val l N [] := by
    exact escapeN_pos _ hl _ _ (leaflessBelow_trunc (leafless_child_trunc hT (i + 1)
      (Nat.succ_le_of_lt i.isLt) (Nat.succ_le_succ (Nat.zero_le _))) N [] (present_nil _))
  have hS : 0 < S := by
    apply Finset.sum_pos (fun j _ => ?_) ⟨i, Finset.mem_univ i⟩
    exact escapeN_pos _ hl _ _ (leaflessBelow_trunc (leafless_child_trunc hT (j + 1)
      (Nat.succ_le_of_lt j.isLt) (Nat.succ_le_succ (Nat.zero_le _))) N [] (present_nil _))
  have hroot : 1 - escapeN T.val l (N + 1) [] = l / (l + S) := by
    have he : escapeN T.val l (N + 1) [] = S / (l + S) := by
      simp only [escapeN, degree, offChild, List.nil_append]
      simp only [b, S]
      simp_rw [← escapeN_child_trunc]
      rfl
    rw [he]
    field_simp [hl.ne', (add_pos_of_pos_of_nonneg hl hS.le).ne']
    ring
  have hle : 1 - escapeN T.val l (N + 1) [] ≤ (sib lPos T i : ℝ) := by
    have hSR : R ≤ S := by
      change (∑ j ∈ Finset.univ.erase i, escape lPos (child T (j + 1))) ≤ ∑ j, b j
      have hc : (∑ j ∈ Finset.univ.erase i, escape lPos (child T (j + 1))) ≤
          ∑ j ∈ Finset.univ.erase i, b j := Finset.sum_le_sum (N := ℝ) (s := Finset.univ.erase i)
        (f := fun j : Fin (degree T) => escape lPos (child T (j + 1)))
        (g := fun j : Fin (degree T) => b j) (fun j _ => by
          exact (escape_antitoneOn _ hl hlPos hll).trans
            (ciInf_le (⟨0, by rintro x ⟨M, rfl⟩; exact escapeN_nonneg' (child T (j + 1)).val hl M []⟩) N))
      exact hc.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun j _ _ => escapeN_nonneg' (child T (j + 1)).val hl N []))
    have hR0 : 0 ≤ R := by
      dsimp [R]
      exact Finset.sum_nonneg fun j _ => (escape_mem_Icc hlPos _).1
    rw [hroot, coe_sib hlPos]
    apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg hl hS.le)
      (add_pos_of_pos_of_nonneg hlPos hR0)).2
    nlinarith [mul_le_mul_of_nonneg_left hSR hl.le,
      mul_le_mul_of_nonneg_right hll hR0]
  unfold pathTail
  simp only [Nat.succ_sub_succ_eq_sub]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hp : sib lPos T i * pathMax lPos (K + j + 1) (child T (i + 1)) ≤
      pathMax lPos (K + j + 2) T := by
    change _ ≤ Finset.univ.sup (fun t : Fin (degree T) =>
      sib lPos T t * pathMax lPos (K + j + 1) (child T (t + 1)))
    exact Finset.le_sup (f := fun t : Fin (degree T) =>
      sib lPos T t * pathMax lPos (K + j + 1) (child T (t + 1))) (Finset.mem_univ i)
  calc
    (1 - escapeN T.val l (N + 1) []) * (pathMax lPos (K + j + 1) (child T (i + 1)) : ℝ) ≤
        (sib lPos T i : ℝ) * (pathMax lPos (K + j + 1) (child T (i + 1)) : ℝ) := by
      exact mul_le_mul_of_nonneg_right hle (NNReal.coe_nonneg _)
    _ = ((sib lPos T i * pathMax lPos (K + j + 1) (child T (i + 1)) : ℝ≥0) : ℝ) := by
      norm_cast
    _ ≤ (pathMax lPos (K + 1 + j + 1) T : ℝ) := by
      have hc : ((sib lPos T i * pathMax lPos (K + j + 1) (child T (i + 1)) : ℝ≥0) : ℝ) ≤
          (pathMax lPos (K + j + 2) T : ℝ) := by exact_mod_cast hp
      simpa only [show K + j + 2 = K + 1 + j + 1 by omega] using hc

/-- The truncation error is dominated by the tail of the path envelope. -/
theorem abs_wN_sub_wTrunc_le {l lPos : ℝ} {T : Tree}
    (hT : ∀ v, Present T v → 1 ≤ T.val v) (hl : 0 < l)
    (hlPos : 0 < lPos) (hll : l ≤ lPos) (K N : ℕ) :
    |wN T.val l N [] - wTrunc T.val l K N []| ≤ pathTail lPos K N T := by
  induction N generalizing T K with
  | zero => simp [wN, wTrunc, pathTail]
  | succ N ih =>
      by_cases hK : K = 0
      · subst K
        rw [wTrunc, if_pos rfl, sub_zero, abs_of_nonneg
          (wN_nonneg T.val hl (N + 1) [] (leaflessBelow_trunc hT (N + 1) [] (present_nil T)))]
        simpa only [pathTail_zero] using wN_le_pathMax (lNeg := 1) hT hl hlPos hll (N + 1)
      · obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK
        let b : Fin (degree T) → ℝ := fun j => escapeN (child T (j + 1)).val l N []
        let S : ℝ := ∑ j, b j
        let A : ℝ := 1 - escapeN T.val l (N + 1) []
        let i0 : Fin (degree T) := ⟨0, by
          have hroot := hT [] (present_nil T)
          change 0 < degree T at hroot
          omega⟩
        let x : Fin (degree T) → ℝ := fun i => b i / S *
          (wN (child T (i + 1)).val l N [] - wTrunc (child T (i + 1)).val l K N [])
        let C : Fin (degree T) → ℝ := fun i => pathTail lPos (K + 1) (N + 1) T
        have hb (i : Fin (degree T)) : 0 < b i := by
          exact escapeN_pos _ hl _ _ (leaflessBelow_trunc (leafless_child_trunc hT (i + 1)
            (Nat.succ_le_of_lt i.isLt) (Nat.succ_le_succ (Nat.zero_le _))) N [] (present_nil _))
        have hS : 0 < S := Finset.sum_pos (fun i _ => hb i)
          ⟨i0, Finset.mem_univ _⟩
        have hw : ∑ i, b i / S = 1 := weights_sum_one (b := b) (S := S) hS.ne' rfl
        have hw0 (i : Fin (degree T)) : 0 ≤ b i / S := div_nonneg (hb i).le hS.le
        have hA : 0 ≤ A := sub_nonneg.mpr (escapeN_le_one _ hl _ _)
        have hshift (i : Fin (degree T)) : A * pathTail lPos K N (child T (i + 1)) ≤ C i :=
          sib_mul_pathTail_le hl hlPos hll hT K N i
        have hdiff (i : Fin (degree T)) :
            |wN (child T (i + 1)).val l N [] - wTrunc (child T (i + 1)).val l K N []| ≤
              pathTail lPos K N (child T (i + 1)) :=
          ih (leafless_child_trunc hT (i + 1) (Nat.succ_le_of_lt i.isLt)
            (Nat.succ_le_succ (Nat.zero_le _))) K
        have hitem (i : Fin (degree T)) : |A * x i| ≤ b i / S * C i := by
          calc
            |A * x i| = A * (b i / S) *
                |wN (child T (i + 1)).val l N [] - wTrunc (child T (i + 1)).val l K N []| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hA, abs_of_nonneg (hw0 i)]
              ring
            _ ≤ (A * (b i / S)) * pathTail lPos K N (child T (i + 1)) :=
              mul_le_mul_of_nonneg_left (hdiff i) (mul_nonneg hA (hw0 i))
            _ = (b i / S) * (A * pathTail lPos K N (child T (i + 1))) := by ring
            _ ≤ b i / S * C i := mul_le_mul_of_nonneg_left (hshift i) (hw0 i)
        have hrec : wN T.val l (N + 1) [] - wTrunc T.val l (K + 1) (N + 1) [] =
            A * ∑ i, x i := by
          simp only [wN, wTrunc, Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.succ_ne_zero]
          simp only [A, x, b, S, offChild, List.nil_append]
          simp_rw [← escapeN_child_trunc, ← wN_child_trunc, ← wTrunc_child_trunc]
          simp only [ite_false]
          simp_rw [mul_sub, Finset.sum_sub_distrib]
          ring_nf
          rfl
        rw [hrec, Finset.mul_sum]
        calc
          |∑ i, A * x i| ≤ ∑ i, |A * x i| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, b i / S * C i := Finset.sum_le_sum fun i _ => hitem i
          _ = C i0 := by rw [← Finset.sum_mul, hw, one_mul]

end LPPMonotonicityProof.Analytic
