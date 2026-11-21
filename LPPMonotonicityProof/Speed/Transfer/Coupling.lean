module

public import LPPMonotonicityProof.Speed.Transfer.Basic

import Lean.Elab.Tactic.Omega

/-!
# Ordered-environment/public-walk coupling before the first crossing

Positive probabilities of the labels already read are an
explicit hypothesis: they ensure that every outward move uses a present child,
so that the next inward move can cancel it by `inward_outward`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState
open LPPMonotonicityProof.RTL.LocallyFinite
open LPPMonotonicityProof.Speed.Markov

@[simp] lemma pubState_zero (ω : List ℕ → ℕ) (l : ℝ≥0) (c : ℕ → ℕ) :
    pubState ω l c 0 = .vtx [] := rfl

lemma pubState_succ (ω : List ℕ → ℕ) (l : ℝ≥0) (c : ℕ → ℕ) (n : ℕ) :
    pubState ω l c (n + 1) = publicNext (pubState ω l c n) (c n) := rfl

/-- The labels before `N` have positive public transition mass. -/
def PositiveBefore (ω : List ℕ → ℕ) (l : ℝ≥0) (c : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ n < N, publicWeight ω l (pubState ω l c n) (c n) ≠ 0

@[simp] lemma outward_fwd (e : Env) (j : ℕ) : (outward e j).fwd = child e.fwd j := rfl

@[simp] lemma foldl_outward_fwd (e : Env) (v : Address) :
    (v.foldl outward e).fwd = subtree e.fwd v := by
  induction v generalizing e with
  | nil => exact subtree_nil e.fwd
  | cons j v ih =>
      rw [List.foldl_cons, ih, outward_fwd, subtree_cons]

lemma present_of_append_left {T : Tree} {u v : Address} (h : Present T (u ++ v)) :
    Present T u := by
  induction u generalizing T with
  | nil => exact present_nil T
  | cons j u ih =>
      exact ⟨h.1, h.2.1, ih h.2.2⟩

/-- The stronger coupling invariant, including full ordered-environment equality and
presence of the current public vertex. -/
theorem coupling_invariant_strong (l : ℝ) (hl : 0 < l) (e : Env) (c : ℕ → ℕ)
    (n : ℕ) (hc : ∀ m ≤ n, pubState e.fwd.val l.toNNReal c m ≠ .rootParent)
    (hw : PositiveBefore e.fwd.val l.toNNReal c n) :
    ∃ v : Address,
      pubState e.fwd.val l.toNNReal c n = .vtx v ∧
      (walkSpec l hl).state e c n = v.foldl outward e ∧ Present e.fwd v := by
  induction n with
  | zero => exact ⟨[], rfl, rfl, present_nil e.fwd⟩
  | succ n ih =>
      have hn : n ≤ n + 1 := Nat.le_succ n
      rcases ih (fun m hm => hc m (hm.trans hn))
        (fun m hm => hw m (Nat.lt_succ_of_lt hm)) with ⟨v, hp, he, hpresent⟩
      cases hlabel : c n with
      | zero =>
          have hv : v ≠ [] := by
            intro hv
            apply hc (n + 1) le_rfl
            rw [pubState_succ, hp, hlabel]
            simp [publicNext, parentState, hv]
          have hlast : 1 ≤ v.getLast hv ∧ v.getLast hv ≤ e.fwd.val v.dropLast := by
            apply present_valid_of_append e.fwd v.dropLast (v.getLast hv) []
            rw [List.dropLast_append_getLast hv]
            exact hpresent
          have hvalid : 1 ≤ v.getLast hv ∧
              v.getLast hv ≤ degree (v.dropLast.foldl outward e).fwd := by
            simpa only [foldl_outward_fwd, degree_subtree] using hlast
          refine ⟨v.dropLast, ?_, ?_, ?_⟩
          · rw [pubState_succ, hp, hlabel]
            simp [publicNext, parentState, hv]
          · rw [Markov.LabelSpec.state, hlabel, he]
            calc
              inward (v.foldl outward e) =
                  inward (outward (v.dropLast.foldl outward e) (v.getLast hv)) := by
                congr 1
                conv_lhs => rw [← List.dropLast_append_getLast hv, List.foldl_append]
                rfl
              _ = v.dropLast.foldl outward e := inward_outward hvalid
          · apply present_of_append_left (u := v.dropLast) (v := [v.getLast hv])
            rw [List.dropLast_append_getLast hv]
            exact hpresent
      | succ j =>
          have hl0 : l.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hl)
          have hj : j < e.fwd.val v := by
            by_contra hj
            apply hw n (Nat.lt_succ_self n)
            rw [hp, hlabel]
            simp [publicWeight, hl0, hj]
          refine ⟨v ++ [j + 1], ?_, ?_, ?_⟩
          · rw [pubState_succ, hp, hlabel]
            rfl
          · rw [Markov.LabelSpec.state, hlabel, he]
            simp [walkSpec, move, List.foldl_append]
          · exact (present_append_singleton e.fwd v (j + 1) hpresent).2
              ⟨Nat.succ_pos j, hj⟩

/-- Before crossing, the forward tree is the subtree at the public address. -/
theorem coupling_invariant (l : ℝ) (hl : 0 < l) (e : Env) (c : ℕ → ℕ) (n : ℕ)
    (hc : ∀ m ≤ n, pubState e.fwd.val l.toNNReal c m ≠ .rootParent)
    (hw : PositiveBefore e.fwd.val l.toNNReal c n) :
    ∃ v : Address, pubState e.fwd.val l.toNNReal c n = .vtx v ∧
      ((walkSpec l hl).state e c n).fwd = subtree e.fwd v := by
  rcases coupling_invariant_strong l hl e c n hc hw with ⟨v, hp, he, _⟩
  exact ⟨v, hp, he ▸ foldl_outward_fwd e v⟩

/-- The ordered-environment and public label weights agree before crossing. -/
theorem weights_agree (l : ℝ) (hl : 0 < l) (e : Env) (c : ℕ → ℕ) (n : ℕ)
    (hc : ∀ m ≤ n, pubState e.fwd.val l.toNNReal c m ≠ .rootParent)
    (hw : PositiveBefore e.fwd.val l.toNNReal c n) (j : ℕ) :
    walkWeight l ((walkSpec l hl).state e c n) j =
      publicWeight e.fwd.val l.toNNReal (pubState e.fwd.val l.toNNReal c n) j := by
  rcases coupling_invariant_strong l hl e c n hc hw with ⟨v, hp, he, _⟩
  rw [hp, he]
  have hl0 : l.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hl)
  cases j with
  | zero =>
      simp only [walkWeight, publicWeight, hl0, false_and, ↓reduceIte,
        foldl_outward_fwd, degree_subtree]
      exact (coe_bias_div l hl (e.fwd.val v)).symm
  | succ j =>
      by_cases hj : j < e.fwd.val v
      · simp only [walkWeight, Nat.succ_ne_zero, ↓reduceIte, publicWeight, hl0,
          false_and, foldl_outward_fwd, degree_subtree, Nat.succ_le_iff, hj]
        exact (coe_one_div l hl (e.fwd.val v)).symm
      · simp [walkWeight, publicWeight, hl0, foldl_outward_fwd, degree_subtree,
          Nat.succ_le_iff, hj]

end LPPMonotonicityProof.Speed
