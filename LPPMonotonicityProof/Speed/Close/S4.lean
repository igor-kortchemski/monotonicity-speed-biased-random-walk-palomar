module

public import LPPMonotonicityProof.Speed.Ergodic.G4
public import LPPMonotonicityProof.Speed.Signed.TwoCopyProof
public import LPPMonotonicityProof.Ergodic.Birkhoff
public import LPPMonotonicityProof.Speed.Transfer.SignedLimit

/-!
# The ergodic limit of the signed step

The bounded ergodic theorem, applied to the ergodic environment walk, identifies the
limit of the signed steps with `N/Z` (Theorem 2.2, `thm:speed-formula`).  This closes
the explicit limit hypothesis used by `Transfer.SignedLimit`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

/-- The speed at positive bias is the two-copy quotient.  Zero bias is
handled separately by the deterministic outward walk. -/
noncomputable def speedValue (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) : ℝ :=
  if l = 0 then 1 else Nval μ l / Zval μ l

@[simp] theorem speedValue_zero (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    speedValue μ 0 = 1 := by
  simp [speedValue]

@[simp] theorem speedValue_of_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) : speedValue μ l = Nval μ l / Zval μ l := by
  simp [speedValue, ne_of_gt hl]

/-- **Ergodic limit.**  Bounded Birkhoff for the ergodic ordered walk identifies the
almost-sure limit of its signed spatial increments. -/
theorem walk_signed_limit (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) :
    ∀ᵐ x ∂walkPathLaw μ l hl hμ (escapePosOnSubtrees hμ hl hlm),
      Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, (if x.2 j = 0 then (-1 : ℝ) else 1)) / n)
        atTop (𝓝 (speedValue μ l)) := by
  let E := escapePosOnSubtrees hμ hl hlm
  let P := walkPathLaw μ l hl hμ E
  letI : IsProbabilityMeasure P := by
    dsimp [P, E]
    infer_instance
  have hsm : Measurable signedStep := by
    apply Measurable.ite
      (measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd) measurable_const)
    · exact measurable_const
    · exact measurable_const
  have hb : ∃ C : ℝ, ∀ x, ‖signedStep x‖ ≤ C := by
    refine ⟨1, fun x => ?_⟩
    unfold signedStep
    split_ifs <;> norm_num
  have hlim := tendsto_birkhoffAverage_of_ergodic
    (ergodic_walkShift μ l hl hμ E hlm) hsm hb
  rw [show ∫ x, signedStep x ∂P = speedValue μ l by
    dsimp [P, E]
    rw [integral_signedStep μ l hl hμ hlm, degreeQuotient_eq μ hl hμ hlm,
      speedValue_of_pos μ hl]] at hlim
  filter_upwards [hlim] with x hx
  convert hx using 1
  ext n
  rw [birkhoffAverage, birkhoffSum_signedStep hl]
  simp [div_eq_inv_mul]

/-- `ref_ae_signed_limit` with its limit hypothesis discharged by `walk_signed_limit`. -/
theorem ref_ae_walk_signed_limit (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) :
    ∀ᵐ e ∂ref μ l hl, ∀ᵐ c ∂moveLaw l hl e,
      Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, sgn (c j)) / n) atTop
        (𝓝 (speedValue μ l)) := by
  apply ref_ae_signed_limit μ l hl hμ (escapePosOnSubtrees hμ hl hlm)
  simpa only [sgn] using walk_signed_limit μ hl hμ hlm

end LPPMonotonicityProof.Speed
