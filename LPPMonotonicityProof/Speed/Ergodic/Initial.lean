module

public import LPPMonotonicityProof.Speed.Ergodic.StateLaw
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Martingale.Convergence

/-!
# An invariant event depends only on the initial environment

The future-probability functions form a bounded
martingale.  Stationarity gives constant second moments, and the tower
property identifies its cross moments; hence every future probability agrees
with its time-zero value.  Lévy's upward theorem then identifies that common
value with the indicator of the invariant event.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

/-- The probability of an event from the next walk trajectory, viewed as a
function of the current environment. -/
noncomputable def hInv (l : ℝ) (hl : 0 < l) (A : Set PathSpace) (e : Env) : ℝ :=
  (moveLaw l hl e {c | (e, c) ∈ A}).toReal

instance moveLaw_isMarkov (l : ℝ) (hl : 0 < l) : IsMarkovKernel (moveLaw l hl) := by
  unfold moveLaw
  infer_instance

instance walkPathLaw_isProbability (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l) :
    IsProbabilityMeasure (walkPathLaw μ l hl hμ hEscapePos) := by
  unfold walkPathLaw
  infer_instance

lemma measurable_hInv (l : ℝ) (hl : 0 < l) {A : Set PathSpace}
    (hA : MeasurableSet A) : Measurable (hInv l hl A) := by
  have heq : hInv l hl A = fun e => ((walkSpec l hl).jointLaw e A).toReal := by
    funext e
    exact congrArg ENNReal.toReal ((walkSpec l hl).jointLaw_apply_set e hA).symm
  rw [heq]
  exact ((walkSpec l hl).jointLaw.measurable_coe hA).ennreal_toReal

lemma hInv_nonneg (l : ℝ) (hl : 0 < l) (A : Set PathSpace) (e : Env) :
    0 ≤ hInv l hl A e := ENNReal.toReal_nonneg

lemma hInv_le_one (l : ℝ) (hl : 0 < l) (A : Set PathSpace) (e : Env) :
    hInv l hl A e ≤ 1 := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
  exact prob_le_one

lemma measurable_hInv_state (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A) (n : ℕ) :
    Measurable (fun (x : PathSpace) => hInv l hl A ((walkSpec l hl).state x.1 x.2 n)) :=
  (measurable_hInv l hl hA).comp ((walkSpec l hl).measurable_state n)

lemma integrable_hInv_state (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A) (n : ℕ) :
    Integrable (fun (x : PathSpace) => hInv l hl A ((walkSpec l hl).state x.1 x.2 n))
      (walkPathLaw μ l hl hμ hEscapePos) := by
  apply Integrable.of_bound (measurable_hInv_state μ l hl hμ hEscapePos hA n).aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hInv_nonneg l hl A _)]
  exact hInv_le_one l hl A _

lemma integrable_hInv_state_mul (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A) (m n : ℕ) :
    Integrable (fun (x : PathSpace) => hInv l hl A ((walkSpec l hl).state x.1 x.2 m) *
      hInv l hl A ((walkSpec l hl).state x.1 x.2 n))
      (walkPathLaw μ l hl hμ hEscapePos) := by
  apply Integrable.of_bound
    ((measurable_hInv_state μ l hl hμ hEscapePos hA m).mul
      (measurable_hInv_state μ l hl hμ hEscapePos hA n)).aestronglyMeasurable 1
  filter_upwards [] with x
  change |hInv l hl A ((walkSpec l hl).state x.1 x.2 m) *
    hInv l hl A ((walkSpec l hl).state x.1 x.2 n)| ≤ 1
  rw [abs_mul, abs_of_nonneg (hInv_nonneg l hl A _),
    abs_of_nonneg (hInv_nonneg l hl A _)]
  exact mul_le_one₀ (hInv_le_one l hl A _) (hInv_nonneg l hl A _) (hInv_le_one l hl A _)

lemma integrable_hInv_state_sq (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A) (n : ℕ) :
    Integrable (fun x => (hInv l hl A ((walkSpec l hl).state x.1 x.2 n)) ^ 2)
      (walkPathLaw μ l hl hμ hEscapePos) := by
  simpa only [pow_two] using integrable_hInv_state_mul μ l hl hμ hEscapePos hA n n

lemma integral_hInv_state_comp (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    (f : Env → ℝ) (hf : Measurable f) (n : ℕ) :
    ∫ x, f ((walkSpec l hl).state x.1 x.2 n) ∂walkPathLaw μ l hl hμ hEscapePos =
      ∫ e, f e ∂muW μ l hl hμ hEscapePos := by
  calc
    _ = ∫ e, f e ∂(walkPathLaw μ l hl hμ hEscapePos).map
        (fun x => (walkSpec l hl).state x.1 x.2 n) :=
      (integral_map ((walkSpec l hl).measurable_state n).aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by rw [walkPathLaw_map_state μ l hl hμ hEscapePos n]

lemma condExp_hInv_state (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A)
    (hinv : walkShift l hl ⁻¹' A = A) (n : ℕ) :
    (walkPathLaw μ l hl hμ hEscapePos)[A.indicator 1 |
      Markov.LabelSpec.labelFiltration n] =ᵐ[walkPathLaw μ l hl hμ hEscapePos]
      fun (x : PathSpace) => hInv l hl A ((walkSpec l hl).state x.1 x.2 n) := by
  have hcond := (walkSpec l hl).condExp_shift (muW μ l hl hμ hEscapePos) n hA
  have hinv' : (walkSpec l hl).shift ⁻¹' A = A := hinv
  rw [Function.IsFixedPt.preimage_iterate hinv' n] at hcond
  simpa only [hInv, moveLaw, walkPathLaw] using hcond

lemma stronglyMeasurable_hInv_state (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A) (n : ℕ) :
    StronglyMeasurable[Markov.LabelSpec.labelFiltration n]
      (fun (x : PathSpace) => hInv l hl A ((walkSpec l hl).state x.1 x.2 n)) := by
  have heq : (fun (x : PathSpace) =>
      hInv l hl A ((walkSpec l hl).state x.1 x.2 n)) =
      fun x => ((walkSpec l hl).jointLaw ((walkSpec l hl).state x.1 x.2 n) A).toReal := by
    funext x
    exact congrArg ENNReal.toReal
      ((walkSpec l hl).jointLaw_apply_set ((walkSpec l hl).state x.1 x.2 n) hA).symm
  rw [heq]
  exact stronglyMeasurable_iff_measurable.mpr
    ((walkSpec l hl).measurable_futureProb_labelFiltration n hA)

/-- **Stationarity step.**  The future probability at any fixed time is
almost surely equal to the future probability at time zero. -/
theorem hInv_state_ae_eq (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A)
    (hinv : walkShift l hl ⁻¹' A = A) (n : ℕ) :
    (fun (x : PathSpace) => hInv l hl A ((walkSpec l hl).state x.1 x.2 n)) =ᵐ[walkPathLaw μ l hl hμ hEscapePos]
      fun x => hInv l hl A x.1 := by
  let P := walkPathLaw μ l hl hμ hEscapePos
  let F := Markov.LabelSpec.labelFiltration (S := Env)
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let M : ℕ → PathSpace → ℝ := fun n x => hInv l hl A ((walkSpec l hl).state x.1 x.2 n)
  have hcond (m : ℕ) : P[A.indicator 1 | F m] =ᵐ[P] M m :=
    condExp_hInv_state μ l hl hμ hEscapePos hA hinv m
  have htower : P[M n | F 0] =ᵐ[P] M 0 := by
    calc
      P[M n | F 0] =ᵐ[P] P[P[A.indicator 1 | F n] | F 0] :=
        condExp_congr_ae (hcond n).symm
      _ =ᵐ[P] P[A.indicator 1 | F 0] :=
        condExp_condExp_of_le (F.mono (Nat.zero_le n)) (F.le n)
      _ =ᵐ[P] M 0 := hcond 0
  have hpull : P[M n * M 0 | F 0] =ᵐ[P] P[M n | F 0] * M 0 := by
    apply condExp_mul_of_stronglyMeasurable_right
    · exact stronglyMeasurable_hInv_state μ l hl hμ hEscapePos hA 0
    · exact integrable_hInv_state_mul μ l hl hμ hEscapePos hA n 0
    · exact integrable_hInv_state μ l hl hμ hEscapePos hA n
  have hcross : ∫ x, M n x * M 0 x ∂P = ∫ x, M 0 x * M 0 x ∂P := by
    calc
      ∫ x, M n x * M 0 x ∂P = ∫ x, (P[M n * M 0 | F 0]) x ∂P :=
        (integral_condExp (F.le 0)).symm
      _ = ∫ x, (P[M n | F 0] * M 0) x ∂P := integral_congr_ae hpull
      _ = ∫ x, M 0 x * M 0 x ∂P := integral_congr_ae (htower.mul EventuallyEq.rfl)
  have hsq : ∫ x, (M n x) ^ 2 ∂P = ∫ x, (M 0 x) ^ 2 ∂P := by
    calc
      _ = ∫ e, (hInv l hl A e) ^ 2 ∂muW μ l hl hμ hEscapePos :=
        integral_hInv_state_comp μ l hl hμ hEscapePos _ ((measurable_hInv l hl hA).pow_const 2) n
      _ = ∫ x, (M 0 x) ^ 2 ∂P :=
        (integral_hInv_state_comp μ l hl hμ hEscapePos _
          ((measurable_hInv l hl hA).pow_const 2) 0).symm
  have hMnSq : Integrable (fun x => (M n x) ^ 2) P :=
    integrable_hInv_state_sq μ l hl hμ hEscapePos hA n
  have hM0Sq : Integrable (fun x => (M 0 x) ^ 2) P :=
    integrable_hInv_state_sq μ l hl hμ hEscapePos hA 0
  have hprod : Integrable (fun x => M n x * M 0 x) P :=
    integrable_hInv_state_mul μ l hl hμ hEscapePos hA n 0
  have hdiff : Integrable (fun x => (M n x - M 0 x) ^ 2) P := by
    apply ((hMnSq.sub (hprod.const_mul 2)).add hM0Sq).congr
    filter_upwards [] with x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hzero : ∫ x, (M n x - M 0 x) ^ 2 ∂P = 0 := by
    calc
      ∫ x, (M n x - M 0 x) ^ 2 ∂P =
          ∫ x, ((M n x) ^ 2 - 2 * (M n x * M 0 x) + (M 0 x) ^ 2) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (∫ x, (M n x) ^ 2 - 2 * (M n x * M 0 x) ∂P) +
          ∫ x, (M 0 x) ^ 2 ∂P := by
        have hadd := integral_add (hMnSq.sub (hprod.const_mul 2)) hM0Sq
        simpa only [Pi.add_apply, Pi.sub_apply] using hadd
      _ = (∫ x, (M n x) ^ 2 ∂P) - 2 * (∫ x, M n x * M 0 x ∂P) +
          ∫ x, (M 0 x) ^ 2 ∂P := by
        have hsub : (∫ x, (M n x) ^ 2 - 2 * (M n x * M 0 x) ∂P) =
            (∫ x, (M n x) ^ 2 ∂P) - ∫ x, 2 * (M n x * M 0 x) ∂P := by
          simpa only [Pi.sub_apply] using integral_sub hMnSq (hprod.const_mul 2)
        have hmul : (∫ x, 2 * (M n x * M 0 x) ∂P) =
            2 * ∫ x, M n x * M 0 x ∂P := integral_const_mul 2 _
        rw [hsub, hmul]
      _ = 0 := by rw [hsq, hcross]; ring
  have hae : (fun x => (M n x - M 0 x) ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (M n x - M 0 x)) hdiff).mp hzero
  filter_upwards [hae] with x hx
  change M n x = M 0 x
  apply sub_eq_zero.mp
  exact sq_eq_zero_iff.mp (by simpa using hx)

/-- **Dependence on the initial environment.**  The indicator of a shift-invariant
path event is almost surely the future probability evaluated at the initial
environment. -/
theorem indicator_ae_eq_hInv (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A)
    (hinv : walkShift l hl ⁻¹' A = A) :
    A.indicator 1 =ᵐ[walkPathLaw μ l hl hμ hEscapePos] fun x => hInv l hl A x.1 := by
  let P := walkPathLaw μ l hl hμ hEscapePos
  let F := Markov.LabelSpec.labelFiltration (S := Env)
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hfint : Integrable (A.indicator (fun _ => (1 : ℝ))) P := (integrable_const 1).indicator hA
  have hfmeas : StronglyMeasurable[⨆ n, F n] (A.indicator (fun _ => (1 : ℝ))) := by
    rw [Markov.LabelSpec.iSup_labelFiltration]
    exact stronglyMeasurable_iff_measurable.mpr (measurable_const.indicator hA)
  have hlim := hfint.tendsto_ae_condExp hfmeas
  have hall : ∀ᵐ x ∂P, ∀ n, (P[A.indicator 1 | F n]) x = hInv l hl A x.1 := by
    rw [ae_all_iff]
    intro n
    exact (condExp_hInv_state μ l hl hμ hEscapePos hA hinv n).trans
      (hInv_state_ae_eq μ l hl hμ hEscapePos hA hinv n)
  filter_upwards [hlim, hall] with x hxlim hx
  apply tendsto_nhds_unique hxlim
  change Tendsto (fun n => (P[A.indicator (fun _ => (1 : ℝ)) | F n]) x) atTop
    (𝓝 (hInv l hl A x.1))
  have heq : (fun n => (P[A.indicator (fun _ => (1 : ℝ)) | F n]) x) =
      (fun _ : ℕ => hInv l hl A x.1) := funext hx
  rw [heq]
  exact tendsto_const_nhds

end LPPMonotonicityProof.Speed
