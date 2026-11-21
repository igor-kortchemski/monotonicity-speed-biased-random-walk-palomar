module

public import LPPMonotonicityProof.Speed.Signed.Concrete
public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Mean signed step

The mean of the conditional drift `(j-λ)/(j+λ)` under the stationary law is the degree
quotient of equation (2.1) (`eq:aidekon`), as in the proof of Theorem 2.2. -/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The sign of the first recorded physical move. -/
def signedStep (x : PathSpace) : ℝ := if x.2 0 = 0 then -1 else 1

/-- Iterating the edge-recording shift merely advances the label sequence. -/
theorem birkhoffSum_signedStep {l : ℝ} (hl : 0 < l) (x : PathSpace) (n : ℕ) :
    birkhoffSum (walkShift l hl) signedStep n x =
      ∑ j ∈ Finset.range n, (if x.2 j = 0 then -1 else 1) := by
  simp [birkhoffSum, walkShift, Markov.LabelSpec.shift_iterate, signedStep]

/-- The degree quotient of equation (2.1), written with integrals against the
unnormalized reference law `ref`; it appears in `integral_signedStep`. -/
noncomputable def degreeQuotient (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) : ℝ :=
  (∫ e, (degree e.fwd - l) * (escape l e.bwd) / (l - 1 + escape l e.bwd + escapeSum (escape l) e.fwd) ∂ref μ l hl) /
  (∫ e, (degree e.fwd + l) * (escape l e.bwd) / (l - 1 + escape l e.bwd + escapeSum (escape l) e.fwd) ∂ref μ l hl)

/-- Bochner integration against the normalized walk environment law. -/
theorem integral_muW {μ : Measure ℕ} [IsProbabilityMeasure μ] {l : ℝ}
    (D : EscapeData μ l) (hμ : OffspringHyp μ) (f : Env → ℝ) :
    ∫ e, f e ∂D.muW =
      (∫ e, EscapeData.wDens D e * f e ∂D.ref) / ∫ e, EscapeData.wDens D e ∂D.ref := by
  have hW : Measurable (fun e => ENNReal.ofReal (EscapeData.wDens D e)) :=
    ENNReal.measurable_ofReal.comp D.measurable_wDens
  have hA : 0 ≤ ∫ e, EscapeData.wDens D e ∂D.ref := by
    apply integral_nonneg_of_ae
    filter_upwards [D.ae_good_ref] with e he
    exact EscapeData.wDens_nonneg he
  have hprod : (∫ e, (ENNReal.ofReal (EscapeData.wDens D e)).toReal • f e ∂D.ref) =
      ∫ e, EscapeData.wDens D e * f e ∂D.ref := by
    apply integral_congr_ae
    filter_upwards [D.ae_good_ref] with e he
    rw [ENNReal.toReal_ofReal (EscapeData.wDens_nonneg he)]
    rfl
  rw [EscapeData.muW, integral_smul_measure,
    D.wRef_univ_eq_ofReal_integral hμ, EscapeData.wRef,
    integral_withDensity_eq_integral_toReal_smul hW (Filter.Eventually.of_forall fun _ =>
      ENNReal.ofReal_lt_top) f,
    ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hA, hprod]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- First-step expectation of a bounded measurable function of the first label. -/
theorem integral_firstLabel {S : Type*} [MeasurableSpace S] (G : Markov.LabelSpec S)
    (s : S) (f : ℕ → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ j, ‖f j‖ ≤ C) :
    ∫ c, f (c 0) ∂G.law s = ∑' j, (G.weight s j).toReal * f j := by
  have hmeas : Measurable (fun c : ℕ → ℕ => f (c 0)) := hf.comp (measurable_pi_apply 0)
  have hint : Integrable (fun c : ℕ → ℕ => f (c 0)) (G.law s) := by
    have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
    apply (integrable_const C).mono hmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun c => by simpa [Real.norm_eq_abs, abs_of_nonneg hC0] using hC (c 0)
  rw [G.law_firstStep]
  rw [integral_sum_measure (G.law_firstStep s ▸ hint)]
  apply tsum_congr
  intro j
  rw [integral_smul_measure, integral_map (Markov.LabelSpec.measurable_seqCons j).aemeasurable
    hmeas.aestronglyMeasurable]
  simp [Markov.LabelSpec.seqCons, smul_eq_mul]


set_option maxHeartbeats 800000 in
/-- The conditional mean of the first signed physical move. -/
theorem integral_moveLaw_signed {l : ℝ} (hl : 0 < l) (e : Env) :
    ∫ c, (if c 0 = 0 then (-1 : ℝ) else 1) ∂moveLaw l hl e =
      (degree e.fwd - l) / (degree e.fwd + l) := by
  have hlk : (0 : ℝ) < l + degree e.fwd :=
    add_pos_of_pos_of_nonneg hl (Nat.cast_nonneg _)
  have hp : 0 ≤ l / (l + degree e.fwd) := div_nonneg hl.le hlk.le
  have hq : 0 ≤ 1 / (l + degree e.fwd) := div_nonneg zero_le_one hlk.le
  rw [moveLaw, integral_firstLabel (walkSpec l hl) e (fun j => if j = 0 then (-1 : ℝ) else 1)
    (measurable_of_countable _) 1 (fun j => by split_ifs <;> norm_num)]
  change (∑' j : ℕ, (walkWeight l e j).toReal * (if j = 0 then (-1 : ℝ) else 1)) = _
  have htail : (∑' j : ℕ, if j = 0 then (0 : ℝ) else
      (walkWeight l e j).toReal * (if j = 0 then -1 else 1)) =
      ∑ _i : Fin (degree e.fwd), 1 / (l + degree e.fwd) := by
    calc
      _ = ∑' j : ℕ, if 1 ≤ j ∧ j ≤ degree e.fwd then
          1 / (l + degree e.fwd) else 0 := by
        apply tsum_congr
        intro j
        by_cases hj : j = 0
        · simp [hj]
        · by_cases hjk : 1 ≤ j ∧ j ≤ degree e.fwd
          · simp [hj, hjk, walkWeight, ENNReal.toReal_ofReal, hlk.le]
          · have hjk' : ¬j ≤ degree e.fwd := fun hle => hjk ⟨by omega, hle⟩
            simp [hj, hjk', walkWeight]
      _ = _ := slots_degree e.fwd (fun _ => 1 / (l + degree e.fwd))
  have hsum : Summable (fun j => (walkWeight l e j).toReal *
      (if j = 0 then (-1 : ℝ) else 1)) := by
    apply summable_of_ne_finset_zero (s := Finset.range (degree e.fwd + 1))
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    by_cases hj0 : j = 0
    · simp [hj0] at hj
    · have hjk : ¬j ≤ degree e.fwd := by omega
      simp [walkWeight, hj0, hjk]
  rw [hsum.tsum_eq_add_tsum_ite 0]
  rw [htail]
  simp only [walkWeight, ↓reduceIte, mul_neg, mul_one]
  rw [ENNReal.toReal_ofReal hp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (l + (degree e.fwd : ℝ)) = (degree e.fwd : ℝ) + l by ring]
  field_simp [ne_of_gt hlk]
  ring

/-- **Mean signed step:** the mean signed step is the normalized degree quotient. -/
theorem integral_signedStep (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) :
    ∫ x, signedStep x ∂walkPathLaw μ l hl hμ (escapePosOnSubtrees hμ hl hlm) =
      degreeQuotient μ l hl := by
  let D := concreteEscapeData' μ l hl hμ hlm
  letI : IsMarkovKernel (moveLaw l hl) := by
    unfold moveLaw
    infer_instance
  letI : IsProbabilityMeasure
      (walkPathLaw μ l hl hμ (escapePosOnSubtrees hμ hl hlm)) := by
    constructor
    rw [walkPathLaw, Measure.compProd_apply MeasurableSet.univ]
    simp
  have hsm : Measurable signedStep := by
    apply Measurable.ite
      (measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd) measurable_const)
    · exact measurable_const
    · exact measurable_const
  have hint : Integrable signedStep
      (walkPathLaw μ l hl hμ (escapePosOnSubtrees hμ hl hlm)) := by
    apply (integrable_const (1 : ℝ)).mono hsm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by unfold signedStep; split_ifs <;> norm_num
  rw [walkPathLaw, Measure.integral_compProd hint]
  simp_rw [show ∀ e, (∫ c, signedStep (e, c) ∂moveLaw l hl e) =
      (degree e.fwd - l) / (degree e.fwd + l) from fun e => integral_moveLaw_signed hl e]
  change (∫ e, (degree e.fwd - l) / (degree e.fwd + l) ∂D.muW) = _
  rw [integral_muW D hμ]
  unfold degreeQuotient
  congr 1
  apply integral_congr_ae
  filter_upwards [D.ae_good_ref] with e he
  have hkl : (0 : ℝ) < degree e.fwd + l :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hl
  have hH : 0 < EscapeData.Hden D e := EscapeData.Hden_pos he.1 he.2
  change (degree e.fwd + l) * D.β e.bwd / EscapeData.Hden D e *
      ((degree e.fwd - l) / (degree e.fwd + l)) =
    (degree e.fwd - l) * D.β e.bwd /
      (l - 1 + D.β e.bwd + escapeSum D.β e.fwd)
  calc
    _ = ((degree e.fwd - l) * D.β e.bwd / EscapeData.Hden D e) *
        ((degree e.fwd + l) / (degree e.fwd + l)) := by ring
    _ = _ := by rw [div_self (ne_of_gt hkl), mul_one]; rfl

end LPPMonotonicityProof.Speed
