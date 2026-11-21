module

public import LPPMonotonicityProof.Escape.FiniteFlow
public import LPPMonotonicityProof.Speed.Interface.Subtrees

/-!
# Finite-flow escape on raw and pruned fields
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite

/-- A valid child of a present vertex is present in the pruned tree. -/
theorem present_offChild {ω : Offspring} {v : Address}
    (hv : Present (prune ω) v) (i : Fin (ω v)) :
    Present (prune ω) (offChild ω v i) := by
  rw [offChild, present_append_singleton _ _ _ hv]
  refine ⟨Nat.succ_pos _, ?_⟩
  rw [prune_val_of_present hv]
  exact i.isLt

/-- Pruning does not change finite escape below a present vertex. -/
theorem escapeN_prune (ω : Offspring) {v : Address}
    (hv : Present (prune ω) v) (l : ℝ) (N : ℕ) :
    escapeN (prune ω).val l N v = escapeN ω l N v := by
  induction N generalizing v with
  | zero => rfl
  | succ N ih =>
      have hsum :
          (∑ i : Fin ((prune ω).val v),
            escapeN (prune ω).val l N (offChild (prune ω).val v i)) =
          ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i) := by
        refine Fintype.sum_equiv (finCongr (prune_val_of_present hv)) _ _ (fun i => ?_)
        let i' : Fin (ω v) := ⟨i.val, by
          have hi := i.isLt
          rwa [← prune_val_of_present hv]⟩
        have hp : Present (prune ω) (offChild (prune ω).val v i) := by
          simpa only [offChild] using present_offChild hv i'
        simpa only [offChild, finCongr_apply, Fin.val_cast] using ih hp
      rw [escapeN, escapeN, hsum]

/-- The non-positive-escape limit on a raw field, with remaining height tending
monotonically downwards through `escapeN`. -/
noncomputable def escapeRaw (ω : List ℕ → ℕ) (l : ℝ) (v : List ℕ) : ℝ :=
  ⨅ N, escapeN ω l N v

/-- Escape from the root of an RTL tree. -/
noncomputable def escape (l : ℝ) (T : Tree) : ℝ := escapeRaw T.val l []

/-- Finite escape at an address is finite escape at the root of its subtree. -/
theorem escapeN_subtree (T : Tree) (l : ℝ) (N : ℕ) (v u : Address) :
    escapeN (subtree T v).val l N u = escapeN T.val l N (v ++ u) := by
  induction N generalizing v u with
  | zero => rfl
  | succ N ih =>
      have hsum :
          (∑ i : Fin ((subtree T v).val u),
            escapeN (subtree T v).val l N (offChild (subtree T v).val u i)) =
          ∑ i : Fin (T.val (v ++ u)),
            escapeN T.val l N (offChild T.val (v ++ u) i) := by
        refine Fintype.sum_equiv (finCongr (subtree_val T v u)) _ _ (fun i => ?_)
        simpa only [offChild, List.append_assoc, finCongr_apply, Fin.val_cast] using ih v (u ++ [i.val + 1])
      rw [escapeN, escapeN, hsum]

/-- Infinite escape commutes with taking a subtree. -/
theorem escape_subtree (l : ℝ) (T : Tree) (v : Address) :
    escape l (subtree T v) = escapeRaw T.val l v := by
  unfold escape escapeRaw
  congr 1
  funext N
  simpa using escapeN_subtree T l N v []

end LPPMonotonicityProof.Speed
