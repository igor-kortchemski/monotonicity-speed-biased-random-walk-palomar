module

public import LPPMonotonicityProof.Analytic.FarCost
public import LPPMonotonicityProof.Analytic.RightEndpoint
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Regularity of the speed (Proposition 2.6, `prop:cost`)

The two-copy integrals and their quotient are C¹ on the open transient
interval. The right derivative and the derivative limit at zero extend this
regularity to the closed-left interval, which gives the `C¹` clause of
Theorem 1.1 (`thm:main`) for the speed `Speed.speedValue`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LPPMonotonicityProof.Speed

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem contDiffOn_one_of_hasDerivAt {s : Set ℝ} (hs : IsOpen s)
    {f f' : ℝ → ℝ} (hd : ∀ l ∈ s, HasDerivAt f (f' l) l)
    (hc : ContinuousOn f' s) : ContDiffOn ℝ 1 f s := by
  refine (contDiffOn_one_iff_derivWithin hs.uniqueDiffOn).mpr ⟨?_, ?_⟩
  · exact fun l hl => (hd l hl).differentiableAt.differentiableWithinAt
  · exact hc.congr fun l hl => (hd l hl).hasDerivWithinAt.derivWithin (hs.uniqueDiffOn l hl)

/-- The numerator, denominator and speed are continuously differentiable at positive
transient biases. -/
theorem contDiffOn_Nval_Zval_speed (h : OffspringHyp μ) :
    ContDiffOn ℝ 1 (Nval μ) (Set.Ioo 0 (mean μ)) ∧
    ContDiffOn ℝ 1 (Zval μ) (Set.Ioo 0 (mean μ)) ∧
    ContDiffOn ℝ 1 (speedValue μ) (Set.Ioo 0 (mean μ)) := by
  have hN : ContDiffOn ℝ 1 (Nval μ) (Set.Ioo 0 (mean μ)) :=
    contDiffOn_one_of_hasDerivAt isOpen_Ioo (fun _ hl => hasDerivAt_Nval h hl)
      (continuousOn_pairDeriv_N h)
  have hZ : ContDiffOn ℝ 1 (Zval μ) (Set.Ioo 0 (mean μ)) :=
    contDiffOn_one_of_hasDerivAt isOpen_Ioo (fun _ hl => hasDerivAt_Zval h hl)
      (continuousOn_pairDeriv_Z h)
  exact ⟨hN, hZ, (hN.div hZ fun _ hl => (Speed.Zval_pos μ hl.1 h hl.2).ne').congr
    fun _ hl => Speed.speedValue_of_pos μ hl.1⟩

/-- The ordinary derivative of the speed is continuous at positive transient biases. -/
theorem continuousOn_deriv_speedValue (h : OffspringHyp μ) :
    ContinuousOn (deriv (speedValue μ)) (Set.Ioo 0 (mean μ)) :=
  (contDiffOn_Nval_Zval_speed h).2.2.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl

/-- The speed is continuously differentiable on the transient interval including zero. -/
theorem contDiffOn_speedValue (h : OffspringHyp μ) :
    ContDiffOn ℝ 1 (speedValue μ) (Set.Ico 0 (mean μ)) := by
  let s := Set.Ico 0 (mean μ)
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_Ico 0 (mean μ)
  have hright : HasDerivWithinAt (speedValue μ) (-2 * invMean μ) s 0 :=
    (hasDerivWithinAt_speedValue_zero h).mono Set.Ico_subset_Ici_self
  have hderiv (l : ℝ) (hl : l ∈ Set.Ioo 0 (mean μ)) :
      derivWithin (speedValue μ) s l = deriv (speedValue μ) l :=
    derivWithin_of_mem_nhds
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hl) Set.Ioo_subset_Ico_self)
  refine (contDiffOn_one_iff_derivWithin hs).mpr ⟨?_, ?_⟩
  · intro l hl
    rcases hl.1.eq_or_lt with heq | hpos
    · subst l
      exact hright.differentiableWithinAt
    · exact (hasDerivAt_speedValue h ⟨hpos, hl.2⟩).differentiableAt.differentiableWithinAt
  · have hIoo := (continuousOn_deriv_speedValue h).congr hderiv
    intro l hl
    rcases hl.1.eq_or_lt with heq | hpos
    · subst l
      apply continuousWithinAt_sdiff_self.mp
      rw [show s \ {0} = Set.Ioo 0 (mean μ) from Set.Ico_sdiff_left]
      change Tendsto (derivWithin (speedValue μ) s) (𝓝[Set.Ioo 0 (mean μ)] 0)
        (𝓝 (derivWithin (speedValue μ) s 0))
      rw [hright.derivWithin (hs 0 hl)]
      refine ((tendsto_deriv_speedValue_zero h).mono_left
        (nhdsWithin_mono _ Set.Ioo_subset_Ioi_self)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hderiv t ht).symm
    · have hl' : l ∈ Set.Ioo 0 (mean μ) := ⟨hpos, hl.2⟩
      exact ((hIoo l hl').continuousAt (isOpen_Ioo.mem_nhds hl')).continuousWithinAt

/-- The speed is continuous on the transient interval including zero. -/
theorem continuousOn_speedValue (h : OffspringHyp μ) :
    ContinuousOn (speedValue μ) (Set.Ico 0 (mean μ)) :=
  (contDiffOn_speedValue h).continuousOn

/-- The `C¹` clause of Theorem 1.1 (`thm:main`) for the speed `Speed.speedValue`, for an
offspring law given as a PMF as in `speed_monotone_of_interval_certificates`. -/
theorem contDiffOn_speedValue_pmf (μ' : PMF ℕ) (hμ0 : μ' 0 = 0)
    (hm1 : 1 < LPPMonotonicity.offspringMean μ')
    (hmfin : LPPMonotonicity.offspringMean μ' < ∞) :
    ContDiffOn ℝ 1 (Speed.speedValue μ'.toMeasure)
      (Set.Ico 0 (LPPMonotonicity.offspringMean μ').toReal) := by
  rw [← mean_eq μ']
  exact contDiffOn_speedValue (offspringHyp_of μ' hμ0 hm1 hmfin)

end LPPMonotonicityProof.Analytic
