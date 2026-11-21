module

public import LPPMonotonicityProof.Speed.Transfer.Coupling
public import Mathlib.MeasureTheory.Measure.Continuity

import Lean.Elab.Tactic.Omega

/-!
# Equality of environment and public label laws on non-crossing paths

For a cylinder of length `n`, the finite approximants use
horizons `n + k`.  Their measures are finite sums of cylinder products, which
agree by the coupling of `Transfer/Coupling.lean` (`weights_agree`).  Continuity from
above gives the statement on `noHit`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState
open LPPMonotonicityProof.RTL.LocallyFinite
open LPPMonotonicityProof.Speed.Markov
open LPPMonotonicityProof.Speed.Markov.LabelSpec

/-- Cylinder products agree on words which avoid the joining edge long enough. -/
theorem cylinder_products_agree (l : ℝ) (hl : 0 < l) (e : Env) (c : ℕ → ℕ)
    (N : ℕ) (hc : c ∈ noHitBefore e.fwd.val l.toNNReal N) :
    ∀ n ≤ N,
      (∏ i ∈ Finset.range n,
        (walkSpec l hl).weight ((walkSpec l hl).state e c i) (c i)) =
      ∏ i ∈ Finset.range n,
        (publicSpec e.fwd.val l.toNNReal).weight
          ((publicSpec e.fwd.val l.toNNReal).state (.vtx []) c i) (c i) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro hn
      by_cases hw : PositiveBefore e.fwd.val l.toNNReal c n
      · have hwc : ∀ m ≤ n, pubState e.fwd.val l.toNNReal c m ≠ .rootParent := by
          intro m hm
          exact hc m (hm.trans_lt hn)
        rw [Finset.prod_range_succ, Finset.prod_range_succ,
          ih (Nat.le_trans (Nat.le_succ n) hn)]
        have hww := weights_agree l hl e c n hwc hw (c n)
        change (walkSpec l hl).weight ((walkSpec l hl).state e c n) (c n) =
          (publicSpec e.fwd.val l.toNNReal).weight
            ((publicSpec e.fwd.val l.toNNReal).state (.vtx []) c n) (c n) at hww
        rw [hww]
      · rw [PositiveBefore] at hw
        push_neg at hw
        rcases hw with ⟨m, hm, hzero⟩
        have hpub : (∏ i ∈ Finset.range n,
            (publicSpec e.fwd.val l.toNNReal).weight
              ((publicSpec e.fwd.val l.toNNReal).state (.vtx []) c i) (c i)) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_range.mpr hm)
          exact hzero
        rw [Finset.prod_range_succ, Finset.prod_range_succ,
          ih (Nat.le_trans (Nat.le_succ n) hn), hpub, zero_mul, zero_mul]

lemma noHitBefore_congr (ω : List ℕ → ℕ) (l : ℝ≥0) (N : ℕ) {c d : ℕ → ℕ}
    (h : ∀ i < N, c i = d i) : c ∈ noHitBefore ω l N ↔ d ∈ noHitBefore ω l N := by
  have hs (m : ℕ) (hm : m < N) : pubState ω l c m = pubState ω l d m := by
    exact (publicSpec ω l).state_eq_of_forall_lt (.vtx []) c d m
      (fun i hi => h i (hi.trans hm))
  constructor <;> intro hc m hm
  · rw [← hs m hm]
    exact hc m hm
  · rw [hs m hm]
    exact hc m hm

lemma extendPrefix_apply {N : ℕ} (q : Fin N → ℕ) {i : ℕ} (hi : i < N) :
    LabelSpec.extendPrefix q i = q ⟨i, hi⟩ := by
  simp [LabelSpec.extendPrefix, hi]

lemma disjoint_wordCylinder_extendPrefix {N : ℕ} {q q' : Fin N → ℕ} (h : q ≠ q') :
    Disjoint (wordCylinder (LabelSpec.extendPrefix q) N)
      (wordCylinder (LabelSpec.extendPrefix q') N) := by
  rw [Set.disjoint_left]
  intro c hc hc'
  apply h
  funext i
  have hi := hc i.1 i.2
  have hi' := hc' i.1 i.2
  rw [extendPrefix_apply q i.2] at hi
  rw [extendPrefix_apply q' i.2] at hi'
  exact hi.symm.trans hi'

/-- A no-hit cylinder of horizon at least its own length is a countable disjoint
union of full-length cylinders. -/
lemma cylinder_inter_noHitBefore_decompose (ω : List ℕ → ℕ) (l : ℝ≥0)
    (w : ℕ → ℕ) (n N : ℕ) (hn : n ≤ N) :
    ∃ Q : Set (Fin N → ℕ),
      wordCylinder w n ∩ noHitBefore ω l N =
        ⋃ q ∈ Q, wordCylinder (LabelSpec.extendPrefix q) N ∧
      ∀ q ∈ Q, LabelSpec.extendPrefix q ∈ noHitBefore ω l N := by
  classical
  let Q : Set (Fin N → ℕ) := {q |
    LabelSpec.extendPrefix q ∈ noHitBefore ω l N ∧
      ∀ i < n, LabelSpec.extendPrefix q i = w i}
  refine ⟨Q, ?_, ?_⟩
  · ext c
    constructor
    · intro hc
      let q : Fin N → ℕ := fun i => c i.1
      have heq : ∀ i < N, LabelSpec.extendPrefix q i = c i := by
        intro i hi
        exact extendPrefix_apply q hi
      have hq : q ∈ Q := by
        constructor
        · exact (noHitBefore_congr ω l N heq).2 hc.2
        · intro i hi
          rw [heq i (hi.trans_le hn)]
          exact hc.1 i hi
      apply Set.mem_iUnion₂.mpr
      refine ⟨q, hq, ?_⟩
      intro i hi
      exact (heq i hi).symm
    · intro hc
      rcases Set.mem_iUnion₂.mp hc with ⟨q, hq, hcq⟩
      have hq' : LabelSpec.extendPrefix q ∈ noHitBefore ω l N ∧
          ∀ i < n, LabelSpec.extendPrefix q i = w i := hq
      constructor
      · intro i hi
        rw [hcq i (hi.trans_le hn)]
        exact hq'.2 i hi
      · exact (noHitBefore_congr ω l N hcq).2 hq'.1
  · intro q hq
    exact hq.1

/-- Measure of a no-hit cylinder at a horizon at least the cylinder length. -/
theorem measure_cylinder_inter_noHitBefore (l : ℝ) (hl : 0 < l) (e : Env)
    (w : ℕ → ℕ) (n N : ℕ) (hn : n ≤ N) :
    (moveLaw l hl e) (wordCylinder w n ∩ noHitBefore e.fwd.val l.toNNReal N) =
      ((publicSpec e.fwd.val l.toNNReal).law (.vtx []))
        (wordCylinder w n ∩ noHitBefore e.fwd.val l.toNNReal N) := by
  classical
  rcases cylinder_inter_noHitBefore_decompose e.fwd.val l.toNNReal w n N hn with
    ⟨Q, hQ, hQhit⟩
  rw [hQ]
  have hd : Set.PairwiseDisjoint Q
      (fun q => wordCylinder (LabelSpec.extendPrefix q) N) := by
    intro q _ q' _ hqq'
    exact disjoint_wordCylinder_extendPrefix hqq'
  rw [MeasureTheory.measure_biUnion Q.to_countable hd
      (fun q _ => measurableSet_wordCylinder _ _),
    MeasureTheory.measure_biUnion Q.to_countable hd
      (fun q _ => measurableSet_wordCylinder _ _)]
  apply tsum_congr
  intro q
  change (walkSpec l hl).law e (wordCylinder (LabelSpec.extendPrefix q.1) N) = _
  rw [(walkSpec l hl).law_cylinder, (publicSpec e.fwd.val l.toNNReal).law_cylinder]
  exact cylinder_products_agree l hl e (LabelSpec.extendPrefix q.1) N (hQhit q.1 q.2) N le_rfl

/-- The environment walk and the public labelled walk have the same law on
paths which never cross the joining edge. -/
theorem moveLaw_restrict_noHit (l : ℝ) (hl : 0 < l) (e : Env) :
    (moveLaw l hl e).restrict (noHit e.fwd.val l.toNNReal) =
      ((publicSpec e.fwd.val l.toNNReal).law (.vtx [])).restrict
        (noHit e.fwd.val l.toNNReal) := by
  letI : IsMarkovKernel (moveLaw l hl) := by
    unfold moveLaw
    infer_instance
  have hCyl (w : ℕ → ℕ) (n : ℕ) :
      ((moveLaw l hl e).restrict (noHit e.fwd.val l.toNNReal)) (wordCylinder w n) =
        (((publicSpec e.fwd.val l.toNNReal).law (.vtx [])).restrict
          (noHit e.fwd.val l.toNNReal)) (wordCylinder w n) := by
    rw [Measure.restrict_apply (measurableSet_wordCylinder w n),
      Measure.restrict_apply (measurableSet_wordCylinder w n)]
    let A : ℕ → Set (ℕ → ℕ) := fun k =>
      wordCylinder w n ∩ noHitBefore e.fwd.val l.toNNReal (n + k)
    have hAmeas (k : ℕ) : MeasurableSet (A k) :=
      (measurableSet_wordCylinder w n).inter (measurableSet_noHitBefore _ _ _)
    have hAnti : Antitone A := by
      intro a b hab
      apply Set.inter_subset_inter_right
      intro c hc m hm
      exact hc m (by omega)
    have hInter : (⋂ k, A k) = wordCylinder w n ∩ noHit e.fwd.val l.toNNReal := by
      ext c
      constructor
      · intro hc
        have hc' := Set.mem_iInter.mp hc
        exact ⟨(hc' 0).1, fun m => (hc' (m + 1)).2 m (by omega)⟩
      · intro hc
        apply Set.mem_iInter.mpr
        intro k
        exact ⟨hc.1, fun m _ => hc.2 m⟩
    have hmove := MeasureTheory.tendsto_measure_iInter_atTop
      (μ := moveLaw l hl e) (s := A) (fun k => (hAmeas k).nullMeasurableSet)
      hAnti ⟨0, measure_ne_top _ _⟩
    have hpub := MeasureTheory.tendsto_measure_iInter_atTop
      (μ := (publicSpec e.fwd.val l.toNNReal).law (.vtx [])) (s := A)
      (fun k => (hAmeas k).nullMeasurableSet) hAnti ⟨0, measure_ne_top _ _⟩
    rw [hInter] at hmove hpub
    have heq : (moveLaw l hl e) ∘ A =
        ((publicSpec e.fwd.val l.toNNReal).law (.vtx [])) ∘ A := by
      funext k
      exact measure_cylinder_inter_noHitBefore l hl e w n (n + k) (Nat.le_add_right n k)
    rw [heq] at hmove
    exact tendsto_nhds_unique hmove hpub
  apply MeasureTheory.ext_of_generate_finite wordCylinderSystem
    generateFrom_wordCylinderSystem isPiSystem_wordCylinderSystem
  · intro t ht
    rcases ht with (rfl | ⟨⟨w, n⟩, rfl⟩)
    · simp
    · exact hCyl w n
  · have h0 := hCyl (fun _ => 0) 0
    simpa [wordCylinder] using h0

end LPPMonotonicityProof.Speed
