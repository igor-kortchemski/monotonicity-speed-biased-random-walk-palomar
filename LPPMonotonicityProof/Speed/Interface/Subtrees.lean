module

public import LPPMonotonicityProof.Speed.Env.Lin
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Subtrees and shifted offspring fields

`Speed.Env.Lin` already supplies the direct descendant-tree constructor
`subtree`.  This interface records the equivalent recursive address law and
its compatibility with pruning and the i.i.d. offspring law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite

@[simp] theorem subtree_val (T : Tree) (v u : Address) :
    (subtree T v).val u = T.val (v ++ u) := rfl

/-- Shifting all coordinates of an i.i.d. field by a fixed address preserves its law. -/
theorem map_shift_offspringFieldLaw (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (v : Address) :
    (offspringFieldLaw μ).map (fun ω u => ω (v ++ u)) = offspringFieldLaw μ := by
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Address => μ) (List.append_right_injective v)

/-- Pruning commutes with shifting to a present vertex. -/
theorem prune_shift {ω : Offspring} {v : Address} (hv : Present (prune ω) v) :
    prune (fun u => ω (v ++ u)) = subtree (prune ω) v := by
  induction v generalizing ω with
  | nil =>
      simp
  | cons j v ih =>
      have hj : 1 ≤ j ∧ j ≤ ω [] := ⟨hv.1, hv.2.1⟩
      have hc : child (prune ω) j = prune (fun u => ω (j :: u)) := by
        rw [child_prune, ite_eq_left hj]
      have hp : Present (prune (fun u => ω (j :: u))) v := hc ▸ hv.2.2
      rw [subtree_cons, hc]
      simpa only [List.cons_append] using ih hp

/-- The descendant-tree map at a fixed address is measurable. -/
theorem measurable_subtree (v : Address) : Measurable (fun T : Tree => subtree T v) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval
  intro u
  exact (continuous_offspring (v ++ u)).measurable

/-- Present membership at a fixed address is measurable. -/
theorem measurableSet_present (v : Address) :
    MeasurableSet {T : Tree | Present T v} := by
  induction v with
  | nil =>
      simpa only [present_nil, Set.ofPred_true] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set Tree))
  | cons j v ih =>
      have hj : MeasurableSet {T : Tree | 1 ≤ j ∧ j ≤ degree T} :=
        (MeasurableSet.of_discrete (s := {k : ℕ | 1 ≤ j ∧ j ≤ k})).preimage
          continuous_degree.measurable
      simpa only [Set.preimage_ofPred_eq, ← Set.ofPred_and, present_cons, and_assoc] using
        hj.inter (ih.preimage (continuous_child j).measurable)

/-- A measurable almost-sure tree property holds at every present subtree simultaneously. -/
theorem ae_all_subtrees (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {P : Tree → Prop} (hP : MeasurableSet {T | P T})
    (h : ∀ᵐ T ∂bienaymeLaw μ, P T) :
    ∀ᵐ T ∂bienaymeLaw μ, ∀ v, Present T v → P (subtree T v) := by
  rw [ae_all_iff]
  intro v
  have hp : ∀ᵐ ω ∂offspringFieldLaw μ, P (prune ω) := by
    have h' := h
    change ∀ᵐ T ∂(offspringFieldLaw μ).map prune, P T at h'
    exact (MeasureTheory.ae_map_iff measurable_prune.aemeasurable hP).mp h'
  have hsmap : ∀ᵐ ω ∂(offspringFieldLaw μ).map (fun ω u => ω (v ++ u)),
      P (prune ω) := by
    rw [map_shift_offspringFieldLaw]
    exact hp
  have hs : ∀ᵐ ω ∂offspringFieldLaw μ, P (prune (fun u => ω (v ++ u))) :=
    MeasureTheory.ae_of_ae_map
      (Measurable.of_eval fun u => measurable_pi_apply (v ++ u)).aemeasurable hsmap
  have hmeas : MeasurableSet {T : Tree | Present T v → P (subtree T v)} := by
    rw [show {T : Tree | Present T v → P (subtree T v)} =
        {T : Tree | Present T v}ᶜ ∪ (fun T : Tree => subtree T v) ⁻¹' {T | P T} by
      ext T
      simp [imp_iff_not_or]]
    exact (measurableSet_present v).compl.union (hP.preimage (measurable_subtree v))
  change ∀ᵐ T ∂(offspringFieldLaw μ).map prune, Present T v → P (subtree T v)
  rw [MeasureTheory.ae_map_iff measurable_prune.aemeasurable hmeas]
  filter_upwards [hs] with ω hω hv
  rw [← prune_shift hv]
  exact hω

end LPPMonotonicityProof.Speed
