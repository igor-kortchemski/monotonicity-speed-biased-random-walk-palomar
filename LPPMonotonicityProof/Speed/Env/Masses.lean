module

public import LPPMonotonicityProof.Speed.Env.Invariance
public import LPPMonotonicityProof.Speed.Hyp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Masses, equivalence, and harmonic-ray validity

This module promotes the unnormalised Lin reference
measures to finite positive measures, identifies the corresponding normalised
laws up to equivalence, and proves that the harmonic ray uses valid child
slots at every level.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace EscapeData

variable {μ : Measure ℕ} [IsProbabilityMeasure μ] {l : ℝ}

instance ref_isProbabilityMeasure (D : EscapeData μ l) : IsProbabilityMeasure D.ref := by
  unfold ref
  infer_instance

/-- The physical environment-walk kernel is Markov for every offspring law. -/
instance walkKernel_isMarkov (D : EscapeData μ l) : IsMarkovKernel D.walkKernel := by
  refine ⟨fun e => ⟨?_⟩⟩
  rw [← lintegral_one, walkKernel,
    lintegral_weightedMoves move measurable_move (walkWeight D)
      (measurable_walkWeight D) e measurable_const]
  simp only [mul_one]
  have hm := D.walk_moveSum e (f := fun _ => 1)
  simp only [mul_one] at hm
  rw [hm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hlk : (0 : ℝ) < l + degree e.fwd :=
    add_pos_of_pos_of_nonneg D.hl (Nat.cast_nonneg _)
  have h0 : 0 ≤ l / (l + degree e.fwd) := div_nonneg D.hl.le hlk.le
  rw [← ENNReal.ofReal_add h0 (mul_nonneg (Nat.cast_nonneg _) (by positivity))]
  field_simp [ne_of_gt hlk]
  simp

/-- On a tree of positive escape sum, the harmonic weights sum to one. -/
theorem summable_escapeWeight (D : EscapeData μ l) (T : Tree) :
    Summable (escapeWeight D.β T) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 (degree T))
  intro i hi
  simp only [Finset.mem_Icc, not_and, not_le] at hi
  simp only [escapeWeight, ite_eq_right_iff]
  intro hvalid
  exfalso
  omega

theorem qWeight_tsum (D : EscapeData μ l) (e : Env) :
    ∑' j, qWeight D e j = 1 := by
  by_cases hS : 0 < escapeSum D.β e.fwd
  · simp only [qWeight, hS, ↓reduceIte]
    have hs : Summable (fun j => escapeWeight D.β e.fwd j / escapeSum D.β e.fwd) :=
      (D.summable_escapeWeight e.fwd).div_const _
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun j => div_nonneg (escapeWeight_nonneg D.β_nonneg _ _) hS.le) hs]
    rw [tsum_div_const]
    change ENNReal.ofReal (escapeSum D.β e.fwd / escapeSum D.β e.fwd) = 1
    rw [div_self (ne_of_gt hS), ENNReal.ofReal_one]
  · have hS0 : escapeSum D.β e.fwd = 0 :=
      le_antisymm (not_lt.mp hS) (escapeSum_nonneg D.β_nonneg _)
    simp [qWeight, hS0]

/-- The harmonic outward kernel is Markov, including the off-good-set fallback. -/
instance qKernel_isMarkov (D : EscapeData μ l) : IsMarkovKernel D.qKernel := by
  refine ⟨fun e => ⟨?_⟩⟩
  rw [← lintegral_one, qKernel,
    lintegral_weightedMoves outward measurable_outward (qWeight D)
      (measurable_qWeight D) e measurable_const]
  simpa only [Pi.one_apply, mul_one] using D.qWeight_tsum e

theorem measurable_wDens (D : EscapeData μ l) : Measurable (wDens D) := by
  exact (((Nat.cast_continuous.measurable.comp
    (continuous_degree.measurable.comp measurable_fst)).add measurable_const).mul
      D.measurable_beta0).div D.measurable_Hden

theorem measurable_uDens (D : EscapeData μ l) : Measurable (uDens D) :=
  (D.measurable_beta0.mul D.measurable_fwdSum).div D.measurable_Hden


theorem wDens_nonneg {D : EscapeData μ l} {e : Env}
    (he : GoodTree D.β l e.fwd ∧ GoodTree D.β l e.bwd) : 0 ≤ wDens D e := by
  exact div_nonneg (mul_nonneg (add_nonneg (Nat.cast_nonneg _) D.hl.le)
    (D.β_nonneg _)) (Hden_pos he.1 he.2).le

theorem wDens_pos {D : EscapeData μ l} {e : Env}
    (he : GoodTree D.β l e.fwd ∧ GoodTree D.β l e.bwd) : 0 < wDens D e := by
  have hkl : (0 : ℝ) < degree e.fwd + l :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) D.hl
  exact div_pos (mul_pos hkl he.2.escape_pos) (Hden_pos he.1 he.2)

/-- Lin's walk density is bounded by `degree + l` on the good set. -/
theorem wDens_le {D : EscapeData μ l} {e : Env}
    (he : GoodTree D.β l e.fwd ∧ GoodTree D.β l e.bwd) :
    wDens D e ≤ degree e.fwd + l := by
  have hH : 0 < Hden D e := Hden_pos he.1 he.2
  have hkl : (0 : ℝ) ≤ degree e.fwd + l :=
    add_nonneg (Nat.cast_nonneg _) D.hl.le
  rw [wDens, div_le_iff₀ hH]
  calc
    (degree e.fwd + l) * beta0 D e ≤ (degree e.fwd + l) * Hden D e :=
      mul_le_mul_of_nonneg_left (Hden_ge_beta he.1 he.2) hkl
    _ = (degree e.fwd + l) * Hden D e := rfl

theorem uDens_pos {D : EscapeData μ l} {e : Env}
    (he : GoodTree D.β l e.fwd ∧ GoodTree D.β l e.bwd) : 0 < uDens D e := by
  exact div_pos (mul_pos he.2.escape_pos he.1.escapeSum_pos) (Hden_pos he.1 he.2)

theorem uDens_nonneg {D : EscapeData μ l} {e : Env}
    (he : GoodTree D.β l e.fwd ∧ GoodTree D.β l e.bwd) : 0 ≤ uDens D e :=
  (uDens_pos he).le

/-- The denominator also dominates the forward escape sum. -/
theorem Hden_ge_fwdSum {D : EscapeData μ l} {e : Env}
    (he : GoodTree D.β l e.fwd ∧ GoodTree D.β l e.bwd) :
    fwdSum D e ≤ Hden D e := by
  unfold Hden beta0 fwdSum
  by_cases hl : l < 1
  · have hβ := he.2.escape_lower hl
    linarith
  · have hβ := D.β_nonneg e.bwd
    linarith

/-- The `Q` density is at most one on the good set, without any moment assumption. -/
theorem uDens_le_one {D : EscapeData μ l} {e : Env}
    (he : GoodTree D.β l e.fwd ∧ GoodTree D.β l e.bwd) : uDens D e ≤ 1 := by
  have hH : 0 < Hden D e := Hden_pos he.1 he.2
  calc
    uDens D e ≤ beta0 D e := by
      rw [uDens, div_le_iff₀ hH]
      calc
        beta0 D e * fwdSum D e ≤ beta0 D e * Hden D e :=
          mul_le_mul_of_nonneg_left (Hden_ge_fwdSum he) (D.β_nonneg _)
        _ = beta0 D e * Hden D e := rfl
    _ ≤ 1 := D.β_le_one _

theorem ae_wDens_pos (D : EscapeData μ l) : ∀ᵐ e ∂D.ref, 0 < wDens D e :=
  D.ae_good_ref.mono fun _ he => wDens_pos he

theorem ae_uDens_pos (D : EscapeData μ l) : ∀ᵐ e ∂D.ref, 0 < uDens D e :=
  D.ae_good_ref.mono fun _ he => uDens_pos he

/-- The total unnormalised walk mass is positive. -/
theorem wRef_univ_pos (D : EscapeData μ l) : 0 < D.wRef Set.univ := by
  rw [wRef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, pos_iff_ne_zero]
  intro hzero
  have h := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp D.measurable_wDens)).mp hzero
  have hfalse : ∀ᵐ _e : Env ∂D.ref, False := by
    filter_upwards [D.ae_wDens_pos, h] with e hpos heq
    exact (ENNReal.ofReal_pos.mpr hpos).ne' (by simpa using heq)
  obtain ⟨_e, he⟩ := hfalse.exists
  exact he.elim

/-- The total unnormalised `Q` mass is positive. -/
theorem uRef_univ_pos (D : EscapeData μ l) : 0 < D.uRef Set.univ := by
  rw [uRef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, pos_iff_ne_zero]
  intro hzero
  have h := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp D.measurable_uDens)).mp hzero
  have hfalse : ∀ᵐ _e : Env ∂D.ref, False := by
    filter_upwards [D.ae_uDens_pos, h] with e hpos heq
    exact (ENNReal.ofReal_pos.mpr hpos).ne' (by simpa using heq)
  obtain ⟨_e, he⟩ := hfalse.exists
  exact he.elim

/-- The `Q` mass is finite because its density is at most one almost surely. -/
theorem uRef_univ_lt_top (D : EscapeData μ l) : D.uRef Set.univ < ∞ := by
  rw [uRef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    (∫⁻ e, ENNReal.ofReal (uDens D e) ∂D.ref) ≤ ∫⁻ _e : Env, 1 ∂D.ref := by
      apply lintegral_mono_ae
      filter_upwards [D.ae_good_ref] with e he
      exact ENNReal.ofReal_le_one.mpr (uDens_le_one he)
    _ = 1 := by simp
    _ < ∞ := ENNReal.one_lt_top

/-- Integrating the forward root degree under `ref` gives the offspring mean. -/
theorem lintegral_degree_fwd (D : EscapeData μ l) :
    (∫⁻ e, (degree e.fwd : ℝ≥0∞) ∂D.ref) = ∫⁻ k, (k : ℝ≥0∞) ∂μ := by
  have hfwd : @MeasurePreserving Env Tree _ _ Env.fwd D.ref (bienaymeLaw μ) := by
    exact ⟨measurable_fst, (measurePreserving_fst (μ := bienaymeLaw μ)
      (ν := (bienaymeLaw μ) ⊗ₘ D.harm)).map_eq⟩
  calc
    _ = ∫⁻ T, (degree T : ℝ≥0∞) ∂bienaymeLaw μ :=
      hfwd.lintegral_comp ((measurable_of_countable _).comp continuous_degree.measurable)
    _ = ∫⁻ k, (k : ℝ≥0∞) ∂(bienaymeLaw μ).map degree := by
      rw [lintegral_map (measurable_of_countable _) continuous_degree.measurable]
    _ = _ := by rw [bienaymeLaw_map_degree]

/-- The forward root degree is integrable under a finite-first-moment hypothesis. -/
theorem integrable_degree_fwd (D : EscapeData μ l) (hμ : OffspringHyp μ) :
    Integrable (fun e => (degree e.fwd : ℝ)) D.ref := by
  have hm : Measurable (fun e : Env => (degree e.fwd : ℝ)) :=
    Nat.cast_continuous.measurable.comp (continuous_degree.measurable.comp measurable_fst)
  rw [← lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun e => Nat.cast_nonneg (degree e.fwd))]
  simp only [ENNReal.ofReal_natCast, D.lintegral_degree_fwd]
  exact hμ.mean_lt_top.ne

/-- Under finite first moment, Lin's walk density is integrable. -/
theorem integrable_wDens (D : EscapeData μ l) (hμ : OffspringHyp μ) :
    Integrable (wDens D) D.ref := by
  have hdom : Integrable (fun e : Env => (degree e.fwd : ℝ) + l) D.ref :=
    (D.integrable_degree_fwd hμ).add (integrable_const l)
  apply hdom.mono_nonneg D.measurable_wDens.aestronglyMeasurable
  · filter_upwards [D.ae_good_ref] with e he
    exact wDens_nonneg he
  · filter_upwards [D.ae_good_ref] with e he
    exact wDens_le he

/-- The walk mass is the extended-real form of the real integral. -/
theorem wRef_univ_eq_ofReal_integral (D : EscapeData μ l) (hμ : OffspringHyp μ) :
    D.wRef Set.univ = ENNReal.ofReal (∫ e, wDens D e ∂D.ref) := by
  rw [wRef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ofReal_integral_eq_lintegral_ofReal (D.integrable_wDens hμ)
      (D.ae_good_ref.mono fun _ he => wDens_nonneg he)]

/-- The walk mass is finite under the offspring's finite-first-moment hypothesis. -/
theorem wRef_univ_lt_top (D : EscapeData μ l) (hμ : OffspringHyp μ) :
    D.wRef Set.univ < ∞ := by
  rw [D.wRef_univ_eq_ofReal_integral hμ]
  exact ENNReal.ofReal_lt_top

/-- The reference law is absolutely continuous with respect to the normalised walk law. -/
theorem ref_absolutelyContinuous_muW (D : EscapeData μ l) (hμ : OffspringHyp μ) :
    D.ref ≪ D.muW := by
  have hd : D.ref ≪ D.wRef := by
    rw [wRef]
    apply withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp D.measurable_wDens).aemeasurable
    filter_upwards [D.ae_wDens_pos] with e he
    exact (ENNReal.ofReal_pos.mpr he).ne'
  exact hd.smul_right (ENNReal.inv_ne_zero.mpr (D.wRef_univ_lt_top hμ).ne)

/-- The normalised walk law is absolutely continuous with respect to `ref`. -/
theorem muW_absolutelyContinuous_ref (D : EscapeData μ l) : D.muW ≪ D.ref := by
  rw [muW, wRef]
  exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

/-- The reference law is absolutely continuous with respect to the normalised `Q` law. -/
theorem ref_absolutelyContinuous_muU (D : EscapeData μ l) : D.ref ≪ D.muU := by
  have hd : D.ref ≪ D.uRef := by
    rw [uRef]
    apply withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp D.measurable_uDens).aemeasurable
    filter_upwards [D.ae_uDens_pos] with e he
    exact (ENNReal.ofReal_pos.mpr he).ne'
  exact hd.smul_right (ENNReal.inv_ne_zero.mpr (D.uRef_univ_lt_top).ne)

/-- The normalised `Q` law is absolutely continuous with respect to `ref`. -/
theorem muU_absolutelyContinuous_ref (D : EscapeData μ l) : D.muU ≪ D.ref := by
  rw [muU, uRef]
  exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

end EscapeData

/-- The tree reached after the first `n` harmonic-ray slots. -/
def rayTree (T : Tree) (r : ℕ → ℕ) : ℕ → Tree
  | 0 => T
  | n + 1 => child (rayTree T r n) (r n)

/-- Validity of the `n`th ray slot at its level. -/
def raySlotValid (T : Tree) (r : ℕ → ℕ) (n : ℕ) : Prop :=
  1 ≤ r n ∧ r n ≤ degree (rayTree T r n)

/-- Every harmonic-ray coordinate is a valid child slot at its level. -/
def rayValid (T : Tree) (r : ℕ → ℕ) : Prop := ∀ n, raySlotValid T r n

@[simp] theorem raySlotValid_cons_zero (T : Tree) (i : ℕ) (r : ℕ → ℕ) :
    raySlotValid T (seqCons i r) 0 ↔ 1 ≤ i ∧ i ≤ degree T := by
  simp [raySlotValid, rayTree]

theorem rayTree_cons (T : Tree) (i : ℕ) (r : ℕ → ℕ) (n : ℕ) :
    rayTree T (seqCons i r) (n + 1) = rayTree (child T i) r n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change child (rayTree T (seqCons i r) (n + 1)) (r n) =
        child (rayTree (child T i) r n) (r n)
      rw [ih]

@[simp] theorem raySlotValid_cons_succ (T : Tree) (i : ℕ) (r : ℕ → ℕ) (n : ℕ) :
    raySlotValid T (seqCons i r) (n + 1) ↔ raySlotValid (child T i) r n := by
  simp [raySlotValid, rayTree_cons]

theorem measurable_rayTree (T : Tree) (n : ℕ) : Measurable (fun r => rayTree T r n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact measurable_child.comp ((measurable_pi_apply n).prodMk ih)

theorem measurable_rayTree_uncurry (n : ℕ) :
    Measurable (fun p : Tree × (ℕ → ℕ) => rayTree p.1 p.2 n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      exact measurable_child.comp (((measurable_pi_apply n).comp measurable_snd).prodMk ih)

theorem measurableSet_raySlotValid (n : ℕ) :
    MeasurableSet {p : Tree × (ℕ → ℕ) | raySlotValid p.1 p.2 n} := by
  exact (MeasurableSet.of_discrete : MeasurableSet {q : ℕ × ℕ | 1 ≤ q.1 ∧ q.1 ≤ q.2}).preimage
    (((measurable_pi_apply n).comp measurable_snd).prodMk
      (continuous_degree.measurable.comp (measurable_rayTree_uncurry n)))

theorem measurableSet_rayValid :
    MeasurableSet {p : Tree × (ℕ → ℕ) | rayValid p.1 p.2} := by
  have heq : {p : Tree × (ℕ → ℕ) | rayValid p.1 p.2} =
      ⋂ n, {p : Tree × (ℕ → ℕ) | raySlotValid p.1 p.2 n} := by
    ext p
    simp [rayValid]
  rw [heq]
  exact MeasurableSet.iInter measurableSet_raySlotValid

namespace EscapeData

variable {μ : Measure ℕ} [IsProbabilityMeasure μ] {l : ℝ}

/-- Each fixed slot of the harmonic ray is valid almost surely on a good tree. -/
theorem ae_raySlotValid_harm (D : EscapeData μ l) (n : ℕ) (T : Tree)
    (hT : GoodTree D.β l T) : ∀ᵐ r ∂D.harm T, raySlotValid T r n := by
  classical
  induction n generalizing T with
  | zero =>
      have hs : MeasurableSet {r : ℕ → ℕ | ¬raySlotValid T r 0} := by
        have hmap : Measurable (fun r : ℕ → ℕ => (T, r)) :=
          measurable_const.prodMk measurable_id
        exact ((measurableSet_raySlotValid 0).preimage hmap).compl
      have hnull : D.harm T {r : ℕ → ℕ | ¬raySlotValid T r 0} = 0 := by
        rw [← lintegral_indicator_one hs,
          show (1 : (ℕ → ℕ) → ℝ≥0∞) = (fun _ => 1) from rfl,
          D.harm_firstStep_normalized T hT
          (g := {r : ℕ → ℕ | ¬raySlotValid T r 0}.indicator (fun _ => (1 : ℝ≥0∞)))
          (measurable_const.indicator hs)]
        rw [ENNReal.tsum_eq_zero]
        intro i
        by_cases hi : 1 ≤ i ∧ i ≤ degree T
        · simp [Set.indicator, hi]
        · simp [escapeWeight, hi]
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with r hr
      exact not_not.mp hr
  | succ n ih =>
      have hs : MeasurableSet {r : ℕ → ℕ | ¬raySlotValid T r (n + 1)} := by
        have hmap : Measurable (fun r : ℕ → ℕ => (T, r)) :=
          measurable_const.prodMk measurable_id
        exact ((measurableSet_raySlotValid (n + 1)).preimage hmap).compl
      have hnull : D.harm T {r : ℕ → ℕ | ¬raySlotValid T r (n + 1)} = 0 := by
        rw [← lintegral_indicator_one hs,
          show (1 : (ℕ → ℕ) → ℝ≥0∞) = (fun _ => 1) from rfl,
          D.harm_firstStep_normalized T hT
          (g := {r : ℕ → ℕ | ¬raySlotValid T r (n + 1)}.indicator (fun _ => (1 : ℝ≥0∞)))
          (measurable_const.indicator hs)]
        rw [ENNReal.tsum_eq_zero]
        intro i
        by_cases hi : 1 ≤ i ∧ i ≤ degree T
        · have hs' : MeasurableSet {r : ℕ → ℕ | ¬raySlotValid (child T i) r n} := by
            have hmap : Measurable (fun r : ℕ → ℕ => (child T i, r)) :=
              measurable_const.prodMk measurable_id
            exact ((measurableSet_raySlotValid n).preimage hmap).compl
          have hnot : ∀ᵐ r ∂D.harm (child T i),
              r ∉ {r : ℕ → ℕ | ¬raySlotValid (child T i) r n} := by
            filter_upwards [ih (child T i) (hT.goodChild hi)] with r hr
            exact not_not.mpr hr
          have hnull' : D.harm (child T i) {r : ℕ → ℕ | ¬raySlotValid (child T i) r n} = 0 :=
            measure_eq_zero_iff_ae_notMem.mpr hnot
          have hfun : (fun r : ℕ → ℕ =>
              {r : ℕ → ℕ | ¬raySlotValid T r (n + 1)}.indicator (fun _ => (1 : ℝ≥0∞))
                (seqCons i r)) =
              {r : ℕ → ℕ | ¬raySlotValid (child T i) r n}.indicator (fun _ => (1 : ℝ≥0∞)) := by
            funext r
            simp only [Set.indicator_apply, Set.mem_ofPred_eq, raySlotValid_cons_succ]
          rw [hfun, show (fun _ : ℕ → ℕ => (1 : ℝ≥0∞)) =
            (1 : (ℕ → ℕ) → ℝ≥0∞) from rfl, lintegral_indicator_one hs', hnull']
          simp
        · simp [escapeWeight, hi]
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with r hr
      exact not_not.mp hr

/-- The full harmonic ray is valid almost surely on every good tree. -/
theorem ae_rayValid_harm (D : EscapeData μ l) (T : Tree) (hT : GoodTree D.β l T) :
    ∀ᵐ r ∂D.harm T, rayValid T r := by
  unfold rayValid
  rw [ae_all_iff]
  exact fun n => D.ae_raySlotValid_harm n T hT

/-- Under the reference environment law, every backward-ray slot is valid at its level. -/
theorem ae_rayValid_ref (D : EscapeData μ l) :
    ∀ᵐ e ∂D.ref, rayValid e.bwd e.ray := by
  have hp : ∀ᵐ p : Tree × (ℕ → ℕ) ∂(bienaymeLaw μ) ⊗ₘ D.harm, rayValid p.1 p.2 := by
    apply Measure.ae_compProd_of_ae_ae measurableSet_rayValid
    filter_upwards [D.ae_good] with T hT
    exact D.ae_rayValid_harm T hT
  exact (measurePreserving_snd (μ := bienaymeLaw μ)
    (ν := (bienaymeLaw μ) ⊗ₘ D.harm)).quasiMeasurePreserving.ae hp

end EscapeData


end LPPMonotonicityProof.Speed
