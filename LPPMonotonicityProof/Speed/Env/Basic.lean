module

public import LPPMonotonicityProof.RTL.LocallyFinite.Topology
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Lean.Elab.Tactic.Omega

/-!
# Ordered environments with a vacated slot

The environment for the stationary marked-walk argument (the occupation argument
of Lin in the proof of Theorem 2.2, `thm:speed-formula`).  Child
indices are one-based.  On an outward move through child `i`, slot `i` of the
new backward tree holds the old backward tree; on the inverse inward move,
slot `i` of the new forward tree holds the old forward tree.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory

private theorem measurableSet_le_nat {α : Type*} [MeasurableSpace α] {f g : α → ℕ}
    (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | f x ≤ g x} :=
  (MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | p.1 ≤ p.2}).preimage (hf.prodMk hg)

/-- The ordered tree with root degree `k` and child `j` equal to `ts j`.
Indices outside `1, …, k` represent absent children. -/
def node (k : ℕ) (ts : ℕ → Tree) : Tree :=
  ⟨fun
    | [] => k
    | j :: u => if 1 ≤ j ∧ j ≤ k then (ts j).val u else 0, by
      intro u j hj
      cases u with
      | nil => simp [hj]
      | cons i u =>
          by_cases hi : 1 ≤ i ∧ i ≤ k
          · change (if 1 ≤ i ∧ i ≤ k then (ts i).val (u ++ [j]) else 0) = 0
            rw [if_pos hi]
            apply (ts i).property u j
            simpa [hi, List.cons_append] using hj
          · simp [hi, List.cons_append]⟩

@[simp] theorem degree_node (k : ℕ) (ts : ℕ → Tree) : degree (node k ts) = k := rfl

theorem child_node_of_valid {k j : ℕ} (ts : ℕ → Tree) (hj : 1 ≤ j ∧ j ≤ k) :
    child (node k ts) j = ts j := by
  apply Subtype.ext
  funext u
  simp [node, hj]

theorem child_node_of_absent {k j : ℕ} (ts : ℕ → Tree) (hj : ¬(1 ≤ j ∧ j ≤ k)) :
    child (node k ts) j = leaf := by
  apply Subtype.ext
  funext u
  simp [node, hj]

/-- The root degree and existing ordered children determine a tree. -/
@[simp] theorem node_degree_child (T : Tree) : node (degree T) (child T) = T := by
  symm
  apply eq_of_degree_child_eq (by simp)
  intro j hj hjk
  exact (child_node_of_valid (child T) ⟨hj, hjk⟩).symm

/-- Replace one existing child, leaving the tree unchanged if the slot is absent. -/
def replaceChild (T : Tree) (i : ℕ) (R : Tree) : Tree :=
  if 1 ≤ i ∧ i ≤ degree T then
    node (degree T) (Function.update (child T) i R)
  else T

@[simp] theorem degree_replaceChild (T : Tree) (i : ℕ) (R : Tree) :
    degree (replaceChild T i R) = degree T := by
  simp only [replaceChild]
  split <;> simp

theorem child_replaceChild_same {T : Tree} {i : ℕ} (R : Tree)
    (hi : 1 ≤ i ∧ i ≤ degree T) : child (replaceChild T i R) i = R := by
  rw [replaceChild, if_pos hi]
  rw [child_node_of_valid (Function.update (child T) i R) (by simpa using hi)]
  exact Function.update_self i R (child T)

theorem child_replaceChild_original {T : Tree} {i : ℕ} (R : Tree)
    (hi : 1 ≤ i ∧ i ≤ degree T) : child (replaceChild T i R) i = R :=
  child_replaceChild_same R hi

theorem child_replaceChild_of_ne {T : Tree} {i j : ℕ} (R : Tree) (hji : j ≠ i) :
    child (replaceChild T i R) j = child T j := by
  by_cases hi : 1 ≤ i ∧ i ≤ degree T
  · by_cases hj : 1 ≤ j ∧ j ≤ degree T
    · rw [replaceChild, if_pos hi, child_node_of_valid _ (by simpa using hj)]
      exact Function.update_of_ne hji _ _
    · have hjn : ¬(1 ≤ j ∧ j ≤ degree (replaceChild T i R)) := by simpa using hj
      rw [child_eq_leaf_of_absent _ _ hjn, child_eq_leaf_of_absent _ _ hj]
  · simp [replaceChild, hi]

@[simp] theorem replaceChild_replaceChild_original {T : Tree} {i : ℕ} (R : Tree)
    (hi : 1 ≤ i ∧ i ≤ degree T) :
    replaceChild (replaceChild T i R) i (child T i) = T := by
  apply eq_of_degree_child_eq (by simp)
  intro j hj hjk
  by_cases hji : j = i
  · subst j
    rw [child_replaceChild_same _ (by simpa using hi)]
  · rw [child_replaceChild_of_ne _ hji, child_replaceChild_of_ne _ hji]

/-- A forward tree, a backward tree, and the outward child slots on the ray. -/
abbrev Env := Tree × Tree × (ℕ → ℕ)

def Env.fwd (e : Env) : Tree := e.1
def Env.bwd (e : Env) : Tree := e.2.1
def Env.ray (e : Env) : ℕ → ℕ := e.2.2

def seqCons (j : ℕ) (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => j
  | n + 1 => c n

def seqTail (c : ℕ → ℕ) : ℕ → ℕ := fun n => c (n + 1)

@[simp] theorem seqCons_zero (j : ℕ) (c : ℕ → ℕ) : seqCons j c 0 = j := rfl
@[simp] theorem seqCons_succ (j : ℕ) (c : ℕ → ℕ) (n : ℕ) :
    seqCons j c (n + 1) = c n := rfl
@[simp] theorem seqTail_cons (j : ℕ) (c : ℕ → ℕ) : seqTail (seqCons j c) = c := rfl
@[simp] theorem seqCons_head_tail (c : ℕ → ℕ) : seqCons (c 0) (seqTail c) = c := by
  funext n
  cases n <;> rfl

/-- Outward move with the old backward tree placed in the vacated slot. -/
def outward (e : Env) (i : ℕ) : Env :=
  (child e.fwd i, replaceChild e.fwd i e.bwd, seqCons i e.ray)

/-- Inward move through the first ray slot, restoring the old forward tree there. -/
def inward (e : Env) : Env :=
  (replaceChild e.bwd (e.ray 0) e.fwd, child e.bwd (e.ray 0), seqTail e.ray)

/-- Move zero is inward; a positive move goes outward through that child. -/
def move (e : Env) (j : ℕ) : Env := if j = 0 then inward e else outward e j

@[simp] theorem inward_outward {e : Env} {i : ℕ}
    (hi : 1 ≤ i ∧ i ≤ degree e.fwd) : inward (outward e i) = e := by
  apply Prod.ext
  · exact replaceChild_replaceChild_original e.bwd hi
  · apply Prod.ext
    · exact child_replaceChild_same e.bwd hi
    · exact seqTail_cons i e.ray

@[simp] theorem outward_inward {e : Env}
    (hi : 1 ≤ e.ray 0 ∧ e.ray 0 ≤ degree e.bwd) : outward (inward e) (e.ray 0) = e := by
  have hi' : 1 ≤ e.ray 0 ∧ e.ray 0 ≤ degree e.bwd := hi
  apply Prod.ext
  · exact child_replaceChild_same e.fwd hi
  · apply Prod.ext
    · exact replaceChild_replaceChild_original e.fwd hi'
    · exact seqCons_head_tail e.ray

/-- Joint measurability of the ordered-node constructor. -/
theorem measurable_node : Measurable (fun p : ℕ × (ℕ → Tree) => node p.1 p.2) := by
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro u
  cases u with
  | nil => exact measurable_fst
  | cons j u =>
      apply Measurable.ite
        ((measurableSet_le_nat measurable_const measurable_const).inter
          (measurableSet_le_nat measurable_const measurable_fst))
      · exact (continuous_offspring u).measurable.comp
          ((measurable_pi_apply j).comp measurable_snd)
      · exact measurable_const

/-- Child replacement is jointly measurable, including a variable child index. -/
theorem measurable_replaceChild :
    Measurable (fun p : ℕ × (Tree × Tree) => replaceChild p.2.1 p.1 p.2.2) := by
  apply measurable_from_prod_countable_right
  intro i
  apply Measurable.ite
    ((measurableSet_le_nat measurable_const measurable_const).inter
      (measurableSet_le_nat measurable_const ((continuous_degree.measurable).comp measurable_fst)))
  · exact measurable_node.comp
      (((continuous_degree.measurable).comp measurable_fst).prodMk
        (measurable_update'.comp
          (((Measurable.of_eval fun j => (continuous_child j).measurable).comp
            measurable_fst).prodMk measurable_snd)))
  · exact measurable_fst

theorem measurable_child : Measurable (fun p : ℕ × Tree => child p.2 p.1) := by
  apply measurable_from_prod_countable_right
  intro i
  exact (continuous_child i).measurable

theorem measurable_seqCons :
    Measurable (fun p : ℕ × (ℕ → ℕ) => seqCons p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

theorem measurable_seqTail : Measurable (fun c : (ℕ → ℕ) => seqTail c) := by
  apply measurable_pi_iff.mpr
  intro n
  exact measurable_pi_apply (n + 1)

@[simp] theorem measurable_outward (i : ℕ) : Measurable (fun e : Env => outward e i) := by
  refine ((continuous_child i).measurable.comp measurable_fst).prodMk ?_
  refine (measurable_replaceChild.comp
    (measurable_const.prodMk (measurable_fst.prodMk measurable_snd.fst))).prodMk ?_
  exact measurable_seqCons.comp (measurable_const.prodMk measurable_snd.snd)

theorem measurable_inward : Measurable (fun e : Env => inward e) := by
  have hslot : Measurable (fun e : Env => e.ray 0) :=
    (measurable_pi_apply 0).comp measurable_snd.snd
  refine (measurable_replaceChild.comp
    (hslot.prodMk (measurable_snd.fst.prodMk measurable_fst))).prodMk ?_
  refine (measurable_child.comp (hslot.prodMk measurable_snd.fst)).prodMk ?_
  exact measurable_seqTail.comp measurable_snd.snd

/-- Every fixed environment move is measurable. -/
theorem measurable_move (j : ℕ) : Measurable (fun e : Env => move e j) := by
  by_cases hj : j = 0
  · simpa [move, hj] using measurable_inward
  · simpa [move, hj] using measurable_outward j

end LPPMonotonicityProof.Speed
