/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import LPPMonotonicityProof.RTL.LocallyFinite.Branching

/-!
# Leafless Bienaymé trees and the escape-recursion decomposition

This module checks that the copied `random-trees-lean` construction directly
supports leafless Bienaymé trees and the independent-child decomposition used by the
escape-probability recursion.
-/

@[expose] public section

namespace LPPMonotonicityProof.RTL.Leafless

open MeasureTheory ProbabilityTheory
open LPPMonotonicityProof.RTL.LocallyFinite

private theorem measurableSet_present (u : Address) :
    MeasurableSet {T : Tree | Present T u} := by
  induction u with
  | nil =>
      simpa only [present_nil, Set.ofPred_true] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set Tree))
  | cons j u ih =>
      have hj : MeasurableSet {T : Tree | 1 ≤ j ∧ j ≤ degree T} :=
        (MeasurableSet.of_discrete (s := {k : ℕ | 1 ≤ j ∧ j ≤ k})).preimage
          continuous_degree.measurable
      simpa only [Set.preimage_ofPred_eq, ← Set.ofPred_and, present_cons, and_assoc] using
        hj.inter (ih.preimage (continuous_child j).measurable)

/-- Under an offspring law with no atom at zero, every present vertex almost surely has a
positive offspring count. The countable intersection is over all finite addresses. -/
theorem ae_present_offspring_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : μ {0} = 0) :
    ∀ᵐ T ∂bienaymeLaw μ, ∀ u : Address, Present T u → 0 < T.val u := by
  have hfield : ∀ᵐ f ∂offspringFieldLaw μ, ∀ u : Address, f u ≠ 0 := by
    rw [ae_all_iff]
    intro u
    rw [ae_iff]
    calc
      offspringFieldLaw μ {f | ¬f u ≠ 0} =
          offspringFieldLaw μ ((fun f : Offspring => f u) ⁻¹' {0}) := by
            congr 1
            ext f
            simp
      _ = ((offspringFieldLaw μ).map (fun f : Offspring => f u)) {0} :=
        (Measure.map_apply (measurable_pi_apply u) (measurableSet_singleton 0)).symm
      _ = μ {0} := by
        change ((Measure.infinitePi (fun _ : Address => μ)).map
          (fun f : Offspring => f u)) {0} = μ {0}
        rw [(measurePreserving_eval_infinitePi (fun _ : Address => μ) u).map_eq]
      _ = 0 := hμ
  have hpruned : ∀ᵐ f ∂offspringFieldLaw μ,
      ∀ u : Address, Present (prune f) u → 0 < (prune f).val u := by
    filter_upwards [hfield] with f hf
    intro u hu
    exact Nat.pos_of_ne_zero (by rw [prune_val_of_present hu]; exact hf u)
  have hgood : MeasurableSet {T : Tree | ∀ u : Address, Present T u → 0 < T.val u} := by
    have he : {T : Tree | ∀ u : Address, Present T u → 0 < T.val u} =
        ⋂ u : Address, {T : Tree | Present T u}ᶜ ∪ {T : Tree | 0 < T.val u} := by
      ext T
      simp [imp_iff_not_or]
    rw [he]
    exact MeasurableSet.iInter fun u => (measurableSet_present u).compl.union
      ((MeasurableSet.of_discrete (s := {k : ℕ | 0 < k})).preimage
        (continuous_offspring u).measurable)
  change ∀ᵐ T ∂(offspringFieldLaw μ).map prune,
    ∀ u : Address, Present T u → 0 < T.val u
  exact (MeasureTheory.ae_map_iff measurable_prune.aemeasurable hgood).2 hpruned

private theorem present_append_one {T : Tree} {u : Address}
    (hu : Present T u) (hpos : 0 < T.val u) : Present T (u ++ [1]) := by
  induction u generalizing T with
  | nil => exact ⟨by omega, hpos, trivial⟩
  | cons j u ih =>
      exact ⟨hu.1, hu.2.1, ih hu.2.2 hpos⟩

/-- Geometric form of leaflessness: almost surely, every present vertex has a present child.
The proof chooses child number `1`; child addresses in this library start at one. -/
theorem ae_present_has_child (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : μ {0} = 0) :
    ∀ᵐ T ∂bienaymeLaw μ, ∀ u : Address, Present T u →
      ∃ j : ℕ, Present T (u ++ [j]) := by
  filter_upwards [ae_present_offspring_pos μ hμ] with T hT
  intro u hu
  exact ⟨1, present_append_one hu (hT u hu)⟩

/-- The escape-recursion interface: the root degree has law `μ` and, conditionally on every
non-null degree event `{degree = k}`, the ordered child subtrees are independent with common
law `bienaymeLaw μ`. Thus their conditional joint law does not depend on any further
information about the root offspring count. -/
theorem bienaymeLaw_escape_recursion (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (bienaymeLaw μ).map degree = μ ∧
      ∀ k : ℕ, bienaymeLaw μ {T | degree T = k} ≠ 0 →
        (ProbabilityTheory.cond (bienaymeLaw μ) {T | degree T = k}).map
          (fun T (i : Fin k) => child T (i.val + 1)) =
            Measure.pi (fun _ : Fin k => bienaymeLaw μ) :=
  isBienayme_bienaymeLaw μ

end LPPMonotonicityProof.RTL.Leafless

#print axioms LPPMonotonicityProof.RTL.Leafless.ae_present_offspring_pos
#print axioms LPPMonotonicityProof.RTL.Leafless.ae_present_has_child
#print axioms LPPMonotonicityProof.RTL.Leafless.bienaymeLaw_escape_recursion
