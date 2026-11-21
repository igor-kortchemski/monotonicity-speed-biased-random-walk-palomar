module

public import LPPMonotonicityProof.Escape.FiniteFlow
public import LPPMonotonicityProof.RTL.LocallyFinite.Law

/-!
# Almost-sure leaflessness for raw offspring fields

The finite-flow names live in the global namespace; this module
uses only `escapeN`-free names and does not open RTL's `generation` namespace.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite

/-- Almost every raw field has positive offspring count at every address. -/
theorem ae_offspring_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : μ {0} = 0) :
    ∀ᵐ ω ∂offspringFieldLaw μ, ∀ v, 1 ≤ ω v := by
  have hfield : ∀ᵐ ω ∂offspringFieldLaw μ, ∀ v : Address, ω v ≠ 0 := by
    rw [ae_all_iff]
    intro v
    rw [ae_iff]
    calc
      offspringFieldLaw μ {ω | ¬ω v ≠ 0} =
          offspringFieldLaw μ ((fun ω : Offspring => ω v) ⁻¹' {0}) := by
            congr 1
            ext ω
            simp
      _ = ((offspringFieldLaw μ).map (fun ω : Offspring => ω v)) {0} :=
        (Measure.map_apply (measurable_pi_apply v) (measurableSet_singleton 0)).symm
      _ = μ {0} := by
        change ((Measure.infinitePi (fun _ : Address => μ)).map
          (fun ω : Offspring => ω v)) {0} = μ {0}
        rw [(measurePreserving_eval_infinitePi (fun _ : Address => μ) v).map_eq]
      _ = 0 := hμ
  filter_upwards [hfield] with ω hω
  exact fun v => Nat.one_le_iff_ne_zero.mpr (hω v)

/-- Global positivity gives leaflessness throughout every finite ball. -/
theorem leaflessBelow_of {ω : List ℕ → ℕ} (hω : ∀ v, 1 ≤ ω v) :
    ∀ N v, LeaflessBelow ω N v := by
  intro N
  induction N with
  | zero => intro v; trivial
  | succ N ih =>
      intro v
      exact ⟨hω v, fun i => ih (offChild ω v i)⟩

end LPPMonotonicityProof.Speed
