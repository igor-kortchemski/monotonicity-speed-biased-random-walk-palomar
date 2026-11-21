module

public import LPPMonotonicityProof.Speed.Env.Basic
public import LPPMonotonicityProof.RTL.LocallyFinite.GenerationLaw
public import Mathlib.MeasureTheory.Constructions.Pi
import Lean.Elab.Tactic.Omega

/-!
# The ordered Bienaymé child swap

The root decomposition uses finite ordered child tuples,
and the swap is later proved by transposing explicit coordinates of a product
measure, rather than by an unordered-tree symmetry argument.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- Rebuild a tree from a tuple indexed by `Fin k`. -/
def nodeFin (k : ℕ) (ts : Fin k → Tree) : Tree :=
  node k fun j => if h : 1 ≤ j ∧ j ≤ k then ts ⟨j - 1, by omega⟩ else leaf

theorem measurable_nodeFin (k : ℕ) : Measurable (nodeFin k) := by
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro u
  cases u with
  | nil => exact measurable_const
  | cons j u =>
      change Measurable (fun ts : Fin k → Tree => (nodeFin k ts).val (j :: u))
      by_cases hj : 1 ≤ j ∧ j ≤ k
      · simp only [nodeFin, node, hj, dite_true, ite_true]
        exact (continuous_offspring u).measurable.comp
          (measurable_pi_apply (⟨j - 1, by omega⟩ : Fin k))
      · simp only [nodeFin, node, hj, dite_false, ite_false]
        exact measurable_const

@[simp] theorem nodeFin_children {T : Tree} {k : ℕ} (hT : degree T = k) :
    nodeFin k (fun i => child T (i.val + 1)) = T := by
  apply eq_of_degree_child_eq (by simp [nodeFin, hT])
  intro j hj hjk
  have hj' : 1 ≤ j ∧ j ≤ k := by simpa [hT] using ⟨hj, hjk⟩
  rw [nodeFin, child_node_of_valid _ (by simpa [nodeFin, hT] using hj')]
  rw [dif_pos hj']
  congr 2
  change j - 1 + 1 = j
  omega

@[simp] theorem degree_nodeFin (k : ℕ) (ts : Fin k → Tree) : degree (nodeFin k ts) = k := rfl

/-- Exact root decomposition of the ordered Bienaymé law as a measure. -/
theorem bienaymeLaw_restrict_degree (k : ℕ) :
    (bienaymeLaw μ).restrict {T | degree T = k} =
      μ {k} • (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k) := by
  have hdeg : MeasurableSet {T : Tree | degree T = k} :=
    continuous_degree.measurable (measurableSet_singleton k)
  have hd : bienaymeLaw μ {T | degree T = k} = μ {k} := by
    have h := congrArg (fun ν : Measure ℕ => ν {k}) (bienaymeLaw_map_degree μ)
    rwa [Measure.map_apply continuous_degree.measurable (measurableSet_singleton k)] at h
  by_cases hk : μ {k} = 0
  · rw [Measure.restrict_eq_zero.mpr (hd.trans hk), hk, zero_smul]
  · have hr : (bienaymeLaw μ).restrict {T | degree T = k} =
        μ {k} • (bienaymeLaw μ)[|{T | degree T = k}] := by
      rw [ProbabilityTheory.cond, hd, smul_smul,
        ENNReal.mul_inv_cancel hk (measure_ne_top _ _), one_smul]
    rw [hr, ← (isBienayme_bienaymeLaw μ).2 k (by rwa [hd]),
      Measure.map_map (measurable_nodeFin k)
        (Measurable.of_eval fun i => (continuous_child (i.val + 1)).measurable)]
    congr 1
    rw [Measure.map_congr, Measure.map_id]
    filter_upwards [ae_cond_mem hdeg] with T hT
    exact nodeFin_children hT

/-- Exchange child `i` of an ordered tuple with the final independent tree. -/
def swapFin {k : ℕ} (i : Fin k) (p : (Fin k → Tree) × Tree) : (Fin k → Tree) × Tree :=
  (Function.update p.1 i p.2, p.1 i)

theorem measurable_swapFin {k : ℕ} (i : Fin k) : Measurable (swapFin i) := by
  exact (measurable_update'.comp (measurable_fst.prodMk measurable_snd)).prodMk
    ((measurable_pi_apply i).comp measurable_fst)

/-- On ordered finite tuples, exchanging a child with an independent copy is
measure-preserving by an explicit coordinate transposition. -/
theorem measurePreserving_swapFin {k : ℕ} (i : Fin k) :
    MeasurePreserving (swapFin (k := k) i)
      ((Measure.pi fun _ : Fin k => bienaymeLaw μ).prod (bienaymeLaw μ))
      ((Measure.pi fun _ : Fin k => bienaymeLaw μ).prod (bienaymeLaw μ)) := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin k) => Tree)
  let c := Equiv.swap (some i) none
  have he : MeasurePreserving e.symm
      ((Measure.pi fun _ : Fin k => bienaymeLaw μ).prod (bienaymeLaw μ))
      (Measure.pi fun _ : Option (Fin k) => bienaymeLaw μ) :=
    ⟨e.symm.measurable, Measure.pi_map_piOptionEquivProd
      (fun _ : Option (Fin k) => bienaymeLaw μ)⟩
  have hc : MeasurePreserving (MeasurableEquiv.piCongrLeft
      (fun _ : Option (Fin k) => Tree) c)
      (Measure.pi fun _ : Option (Fin k) => bienaymeLaw μ)
      (Measure.pi fun _ : Option (Fin k) => bienaymeLaw μ) :=
    measurePreserving_piCongrLeft (α := fun _ : Option (Fin k) => Tree)
      (fun _ : Option (Fin k) => bienaymeLaw μ) c
  have hcomp := he.symm.comp (hc.comp he)
  have e_apply (f : Option (Fin k) → Tree) :
      e f = ((fun j => f (some j)), f none) := by rfl
  have e_symm_some (p : (Fin k → Tree) × Tree) (j : Fin k) :
      e.symm p (some j) = p.1 j := by rfl
  have e_symm_none (p : (Fin k → Tree) × Tree) :
      e.symm p none = p.2 := by rfl
  have hfun : (fun p => e ((MeasurableEquiv.piCongrLeft
      (fun _ : Option (Fin k) => Tree) c) (e.symm p))) = swapFin (k := k) i := by
    funext p
    apply Prod.ext
    · rw [e_apply]
      simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
        Equiv.apply_symm_apply, eq_rec_constant]
      change (fun j => (e.symm p) (c.symm (some j))) = Function.update p.1 i p.2
      funext j
      by_cases hj : j = i
      · subst j
        simp [c, e_symm_none]
      · rw [show c.symm (some j) = some j by
          simp [c, Equiv.swap_apply_of_ne_of_ne, hj], e_symm_some,
        Function.update_of_ne hj]
    · rw [e_apply]
      simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
        Equiv.apply_symm_apply, eq_rec_constant]
      change (e.symm p) (c.symm none) = p.1 i
      simp [c, e_symm_some]
  rw [← hfun]
  exact hcomp

@[simp] theorem children_nodeFin (k : ℕ) (ts : Fin k → Tree) (i : Fin k) :
    child (nodeFin k ts) (i.val + 1) = ts i := by
  have hi : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ k := by omega
  rw [nodeFin, child_node_of_valid _ hi, dif_pos hi]
  congr 2

@[simp] theorem nodeFin_update_children {T : Tree} {k : ℕ} (hT : degree T = k)
    (i : Fin k) (R : Tree) :
    nodeFin k (Function.update (fun j => child T (j.val + 1)) i R) =
      replaceChild T (i.val + 1) R := by
  have hi : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ degree T := by omega
  rw [replaceChild, if_pos hi]
  apply eq_of_degree_child_eq (by simp [hT])
  intro j hj hjk
  have hj' : 1 ≤ j ∧ j ≤ k := by simpa [hT] using ⟨hj, hjk⟩
  rw [nodeFin, child_node_of_valid _ (by simpa [nodeFin, hT] using hj'),
    child_node_of_valid _ (by simpa [hT] using hj')]
  rw [dif_pos hj']
  by_cases hji : j = i.val + 1
  · subst j
    simp only [Function.update_self]
    have hfin : (⟨i.val + 1 - 1, by omega⟩ : Fin k) = i := by
      apply Fin.ext
      simp only
      omega
    rw [hfin, Function.update_self]
  · have hfin : (⟨j - 1, by omega⟩ : Fin k) ≠ i := by
      intro h
      apply hji
      have := congrArg Fin.val h
      dsimp at this
      omega
    simp only [Function.update_of_ne hfin, Function.update_of_ne hji]
    congr 2
    omega

/-- Exchange one ordered child subtree with an independent tree. -/
def swapChild (i : ℕ) (p : Tree × Tree) : Tree × Tree :=
  (replaceChild p.1 i p.2, child p.1 i)


/-- The ordered child swap in each exact-root-degree stratum. -/
theorem measurePreserving_swapChild_of_degree {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    MeasurePreserving (swapChild i)
      (((bienaymeLaw μ).restrict {T | degree T = k}).prod (bienaymeLaw μ))
      (((bienaymeLaw μ).restrict {T | degree T = k}).prod (bienaymeLaw μ)) := by
  let ix : Fin k := ⟨i - 1, by omega⟩
  let C : Tree × Tree → (Fin k → Tree) × Tree := fun p =>
    ((fun j => child p.1 (j.val + 1)), p.2)
  let N : (Fin k → Tree) × Tree → Tree × Tree := fun p => (nodeFin k p.1, p.2)
  have hCmeas : Measurable C :=
    (Measurable.of_eval fun (j : Fin k) => (continuous_child (j.val + 1)).measurable.comp
      measurable_fst).prodMk measurable_snd
  have hNmeas : Measurable N := (measurable_nodeFin k).comp measurable_fst |>.prodMk measurable_snd
  have hchildren : ((bienaymeLaw μ).restrict {T | degree T = k}).map
      (fun T (j : Fin k) => child T (j.val + 1)) =
        μ {k} • Measure.pi (fun _ : Fin k => bienaymeLaw μ) := by
    rw [bienaymeLaw_restrict_degree, Measure.map_smul _
      (Measurable.of_eval fun (j : Fin k) => (continuous_child (j.val + 1)).measurable).aemeasurable,
      Measure.map_map (Measurable.of_eval fun (j : Fin k) => (continuous_child (j.val + 1)).measurable)
        (measurable_nodeFin k)]
    congr 1
    rw [show (fun c (j : Fin k) => child c (j.val + 1)) ∘ nodeFin k = id by
      funext ts j
      exact children_nodeFin k ts j, Measure.map_id]
  have hC : (((bienaymeLaw μ).restrict {T | degree T = k}).prod (bienaymeLaw μ)).map C =
      μ {k} • ((Measure.pi fun _ : Fin k => bienaymeLaw μ).prod (bienaymeLaw μ)) := by
    change Measure.map (Prod.map (fun T (j : Fin k) => child T (j.val + 1)) id) _ = _
    rw [← Measure.map_prod_map _ _
      (Measurable.of_eval fun (j : Fin k) => (continuous_child (j.val + 1)).measurable)
      measurable_id, Measure.map_id, hchildren, Measure.prod_smul_left]
  have hN : (μ {k} • ((Measure.pi fun _ : Fin k => bienaymeLaw μ).prod
      (bienaymeLaw μ))).map N =
        ((bienaymeLaw μ).restrict {T | degree T = k}).prod (bienaymeLaw μ) := by
    rw [Measure.map_smul _ hNmeas.aemeasurable]
    change μ {k} • (((Measure.pi fun _ : Fin k => bienaymeLaw μ).prod
      (bienaymeLaw μ)).map (Prod.map (nodeFin k) id)) = _
    rw [← Measure.map_prod_map _ _ (measurable_nodeFin k) measurable_id,
      Measure.map_id, ← Measure.prod_smul_left, ← bienaymeLaw_restrict_degree]
  have hfun : swapChild i =ᵐ[((bienaymeLaw μ).restrict {T | degree T = k}).prod
      (bienaymeLaw μ)] N ∘ swapFin ix ∘ C := by
    have hdeg : MeasurableSet {T : Tree | degree T = k} :=
      continuous_degree.measurable (measurableSet_singleton k)
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem hdeg)] with p hp
    apply Prod.ext
    · change replaceChild p.1 i p.2 = nodeFin k
        (Function.update (fun j => child p.1 (j.val + 1)) ix p.2)
      rw [show i = ix.val + 1 by dsimp [ix]; omega]
      exact (nodeFin_update_children hp ix p.2).symm
    · change child p.1 i = child p.1 (ix.val + 1)
      congr 1
      dsimp [ix]
      omega
  refine ⟨?_, ?_⟩
  · exact (measurable_replaceChild.comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).prodMk
        ((measurable_child.comp (measurable_const.prodMk measurable_fst)))
  · rw [Measure.map_congr hfun, ← Measure.map_map hNmeas ((measurable_swapFin ix).comp hCmeas),
      ← Measure.map_map (measurable_swapFin ix) hCmeas, hC,
      Measure.map_smul _ (measurable_swapFin ix).aemeasurable,
      (measurePreserving_swapFin ix).map_eq]
    exact hN

/-- The measure-preserving exchange of an existing ordered child with an
independent Bienaymé tree. -/
theorem measurePreserving_swapChild {i : ℕ} (hi : 1 ≤ i) :
    MeasurePreserving (swapChild i)
      (((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ))
      (((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ)) := by
  have hswapMeas : Measurable (swapChild i) :=
    (measurable_replaceChild.comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).prodMk
        (measurable_child.comp (measurable_const.prodMk measurable_fst))
  have hdecomp :
      ((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ) =
        Measure.sum (fun k : {k : ℕ // i ≤ k} =>
          ((bienaymeLaw μ).restrict {T | degree T = k.val}).prod (bienaymeLaw μ)) := by
    have hU : {T : Tree | i ≤ degree T} =
        ⋃ k : {k : ℕ // i ≤ k}, {T : Tree | degree T = k.val} := by
      ext T
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h
        exact ⟨⟨degree T, h⟩, rfl⟩
      · rintro ⟨k, hk⟩
        rw [hk]
        exact k.property
    have hd : Pairwise (Disjoint on fun k : {k : ℕ // i ≤ k} =>
        {T : Tree | degree T = k.val}) := by
      intro a b hab
      apply Set.disjoint_left.mpr
      intro T ha hb
      apply hab
      apply Subtype.ext
      exact ha.symm.trans hb
    have hm : ∀ k : {k : ℕ // i ≤ k}, MeasurableSet {T : Tree | degree T = k.val} :=
      fun k => continuous_degree.measurable (measurableSet_singleton k.val)
    rw [hU, Measure.restrict_iUnion hd hm, Measure.prod_sum_left]
  refine ⟨hswapMeas, ?_⟩
  rw [hdecomp, Measure.map_sum hswapMeas.aemeasurable]
  congr 1
  funext k
  exact (measurePreserving_swapChild_of_degree hi k.property).map_eq

@[simp] theorem swapChild_swapChild {i : ℕ} (hi : 1 ≤ i) {p : Tree × Tree}
    (h : i ≤ degree p.1) : swapChild i (swapChild i p) = p := by
  apply Prod.ext
  · exact replaceChild_replaceChild_original p.2 ⟨hi, h⟩
  · exact child_replaceChild_same p.2 ⟨hi, h⟩

end LPPMonotonicityProof.Speed
