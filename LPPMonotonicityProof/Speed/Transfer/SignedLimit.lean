module

public import LPPMonotonicityProof.Speed.Transfer.Basic

/-!
# Transfer of the signed-step limit to the reference law

The ergodic limit of the signed step under the normalized path law is an explicit
hypothesis here, with an arbitrary limit `v`; the absolute-continuity transfer itself
is proved in full.  `Speed/Close/S4.lean` supplies that limit and applies the transfer
(`ref_ae_signed_limit`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

/-- Quenched signed-step limit under the reference law, given the limit under the
normalized path law as a hypothesis.  Absolute
continuity `ref ≪ muW` transfers the normalized path-law limit to the
reference law, and Fubini then gives the quenched statement. -/
theorem ref_ae_signed_limit (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    (v : ℝ)
    (hS4 : ∀ᵐ p ∂walkPathLaw μ l hl hμ hEscapePos,
      Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, sgn (p.2 j)) / n) atTop (𝓝 v)) :
    ∀ᵐ e ∂ref μ l hl, ∀ᵐ c ∂moveLaw l hl e,
      Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, sgn (c j)) / n) atTop (𝓝 v) := by
  let D := concreteEscapeData μ l hl hμ hEscapePos
  letI : IsProbabilityMeasure D.muW :=
    D.isProbabilityMeasure_muW (ne_of_gt D.wRef_univ_pos) (D.wRef_univ_lt_top hμ).ne
  letI : IsMarkovKernel (moveLaw l hl) := by
    unfold moveLaw
    infer_instance
  have hac : refPathLaw μ l hl ≪ walkPathLaw μ l hl hμ hEscapePos :=
    ((concreteEscapeData μ l hl hμ hEscapePos).ref_absolutelyContinuous_muW hμ).compProd_left
      (moveLaw l hl)
  exact MeasureTheory.Measure.ae_ae_of_ae_compProd (hac.ae_le hS4)

end LPPMonotonicityProof.Speed
