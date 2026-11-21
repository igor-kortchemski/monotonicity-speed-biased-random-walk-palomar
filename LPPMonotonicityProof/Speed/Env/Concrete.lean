module

public import LPPMonotonicityProof.Speed.Env.Harmonic
public import LPPMonotonicityProof.Speed.Env.Masses
public import LPPMonotonicityProof.Speed.Markov.LabelFiltration
public import LPPMonotonicityProof.Speed.Hyp
public import LPPMonotonicityProof.RTL.Leafless
public import LPPMonotonicityProof.Speed.Interface.Labels

/-!
# Concrete ordered-environment chain and escape interface

This module constructs the concrete `EscapeData` from `escape l` and the harmonic
label law `harm` of `Harmonic.lean`, together with the reference law, the walk and
`Q` systems on environments and their normalized laws.  Almost-sure positivity on
present subtrees (Lemma 2.1(iv), `lem:escape`) is the explicit named hypothesis
`EscapePosOnSubtrees` here, discharged in `Speed/Signed/Concrete.lean`; every other
field is proved here.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The concrete reference environment law: two independent Bienaymé trees, and a
harmonic ray in the backward tree. -/
noncomputable def ref (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) (hl : 0 < l) :
    Measure Env := (bienaymeLaw μ).prod ((bienaymeLaw μ) ⊗ₘ harm l hl)

instance (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) (hl : 0 < l) :
    IsProbabilityMeasure (ref μ l hl) := by
  unfold ref
  infer_instance

/-- The weighted walk moves as an inward term plus the finite outward sum. -/
theorem walkWeight_moveSum (l : ℝ) (e : Env) {f : Env → ℝ≥0∞} :
    ∑' j, walkWeight l e j * f (move e j) =
      ENNReal.ofReal (l / (l + degree e.fwd)) * f (inward e) +
        ∑ i : Fin (degree e.fwd),
          ENNReal.ofReal (1 / (l + degree e.fwd)) * f (outward e (i.val + 1)) := by
  classical
  rw [ENNReal.tsum_eq_add_tsum_ite 0]
  simp only [walkWeight, ↓reduceIte, move]
  congr 1
  calc
    _ = ∑' j : ℕ, if 1 ≤ j ∧ j ≤ degree e.fwd then
        ENNReal.ofReal (1 / (l + degree e.fwd)) * f (outward e j) else 0 := by
      apply tsum_congr
      intro j
      by_cases hj : j = 0
      · simp [hj]
      · have hj1 : 1 ≤ j := by omega
        simp [hj, hj1]
    _ = _ := slots_degree e.fwd
      (fun j => ENNReal.ofReal (1 / (l + degree e.fwd)) * f (outward e j))

/-- Physical walk weights have total mass one at every positive bias. -/
theorem tsum_walkWeight {l : ℝ} (hl : 0 < l) (e : Env) :
    ∑' j, walkWeight l e j = 1 := by
  have hm := walkWeight_moveSum l e (f := fun _ => 1)
  simp only [mul_one] at hm
  rw [hm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hlk : (0 : ℝ) < l + degree e.fwd :=
    add_pos_of_pos_of_nonneg hl (Nat.cast_nonneg _)
  have h0 : 0 ≤ l / (l + degree e.fwd) := div_nonneg hl.le hlk.le
  rw [← ENNReal.ofReal_add h0 (mul_nonneg (Nat.cast_nonneg _) (by positivity))]
  field_simp [ne_of_gt hlk]
  simp

/-- The edge-recording physical walk as a labelled Markov system. -/
noncomputable def walkSpec (l : ℝ) (hl : 0 < l) : Markov.LabelSpec Env where
  next := move
  weight := walkWeight l
  measurable_next := measurable_move
  measurable_weight j := by
    apply Measurable.ite (measurableSet_eq_fun measurable_const measurable_const)
    · exact ENNReal.measurable_ofReal.comp
        (measurable_const.div (measurable_const.add
          (Nat.cast_continuous.measurable.comp
            (continuous_degree.measurable.comp measurable_fst))))
    · apply Measurable.ite
        ((MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | p.1 ≤ p.2}).preimage
          (measurable_const.prodMk (continuous_degree.measurable.comp measurable_fst)))
      · exact ENNReal.measurable_ofReal.comp
          (measurable_const.div (measurable_const.add
            (Nat.cast_continuous.measurable.comp
              (continuous_degree.measurable.comp measurable_fst))))
      · exact measurable_const
  tsum_weight := tsum_walkWeight hl

/-- The law of the recorded physical moves. -/
noncomputable def moveLaw (l : ℝ) (hl : 0 < l) : Kernel Env (ℕ → ℕ) :=
  (walkSpec l hl).law

/-- The harmonic outward (`Q`) system on environments. -/
noncomputable def qSpec (l : ℝ) (hl : 0 < l) : Markov.LabelSpec Env where
  next := outward
  weight e i := harmWeight l e.fwd i
  measurable_next := measurable_outward
  measurable_weight j := (measurable_harmWeight l j).comp measurable_fst
  tsum_weight e := tsum_harmWeight hl e.fwd

/-- The forward component after `n` Q-moves is the `n`th harmonic-ray tree. -/
theorem qSpec_state_fwd (l : ℝ) (hl : 0 < l) (e : Env) (w : ℕ → ℕ) (n : ℕ) :
    ((qSpec l hl).state e w n).fwd = (harmSpec l hl).state e.fwd w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Markov.LabelSpec.state]
      change child (((qSpec l hl).state e w n).fwd) (w n) =
        child ((harmSpec l hl).state e.fwd w n) (w n)
      rw [ih]

/-- The Q label law is exactly the harmonic law `harm` on the forward tree. -/
theorem qSpec_law (l : ℝ) (hl : 0 < l) (e : Env) :
    (qSpec l hl).law e = harm l hl e.fwd := by
  apply Markov.LabelSpec.law_ext (harmSpec l hl) e.fwd
  intro w n
  rw [(qSpec l hl).law_cylinder, (harmSpec l hl).law_cylinder]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← qSpec_state_fwd l hl e w i]
  rfl

/-- An initial environment together with its recorded move sequence. -/
abbrev PathSpace := Env × (ℕ → ℕ)

/-- The edge-recording walk shift. -/
noncomputable def walkShift (l : ℝ) (hl : 0 < l) : PathSpace → PathSpace :=
  (walkSpec l hl).shift

/-- The edge-recording Q shift. -/
noncomputable def qShift (l : ℝ) (hl : 0 < l) : PathSpace → PathSpace :=
  (qSpec l hl).shift

/-- The unnormalised concrete reference path law. -/
noncomputable def refPathLaw (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) : Measure PathSpace := ref μ l hl ⊗ₘ moveLaw l hl

/-- **Positivity input** (Lemma 2.1(iv)): almost-sure positivity of escape on every
present subtree. -/
def EscapePosOnSubtrees (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) : Prop :=
  ∀ᵐ T ∂bienaymeLaw μ, ∀ v, Present T v → 0 < escape l (subtree T v)

/-- Concrete leaflessness, positivity, and the `escape_ge` lower bound give
`GoodTree` almost surely. -/
theorem ae_good_escape (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) (hl : 0 < l)
    (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l) :
    ∀ᵐ T ∂bienaymeLaw μ, GoodTree (escape l) l T := by
  filter_upwards [RTL.Leafless.ae_present_offspring_pos μ hμ.zero, hEscapePos] with T hleaf hpos
  constructor
  · exact hleaf [] (present_nil T)
  · intro v hv
    refine ⟨hleaf v hv, hpos v hv, fun hl1 => ?_⟩
    apply escape_ge hl hl1
    intro u hu
    rw [subtree_offspring]
    exact hleaf (v ++ u) ((present_subtree T v u hv).mp hu)

/-- **The concrete escape instance.**  Positivity of escape is isolated as
`hEscapePos`; all other `EscapeData` obligations are discharged from the deterministic
escape properties (`Speed/Walk/Escape.lean`), the harmonic ray, and leaflessness. -/
noncomputable def concreteEscapeData (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l) :
    EscapeData μ l where
  hl := hl
  β := escape l
  harm := harm l hl
  measurable_β := measurable_escape l
  β_nonneg T := (escape_mem_Icc hl T).1
  β_le_one T := (escape_mem_Icc hl T).2
  escape_rec T := by
    rw [escape_eq hl, escapeSum_escape_eq_childSum]
  harm_probability T := inferInstance
  harm_firstStep := LPPMonotonicityProof.Speed.harm_firstStep hl
  ae_good := ae_good_escape μ l hl hμ hEscapePos

/-- The abstract reference law of the concrete instance is `ref` by `rfl`. -/
theorem concreteEscapeData_ref (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l) :
    (concreteEscapeData μ l hl hμ hEscapePos).ref = ref μ l hl := rfl

/-- The concrete normalized walk law, inherited from the abstract `EscapeData` package. -/
noncomputable def muW (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l) :
    Measure Env := (concreteEscapeData μ l hl hμ hEscapePos).muW

/-- The concrete normalized Q law, inherited from the abstract `EscapeData` package. -/
noncomputable def muU (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l) :
    Measure Env := (concreteEscapeData μ l hl hμ hEscapePos).muU

instance (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l) :
    IsProbabilityMeasure (muW μ l hl hμ hEscapePos) := by
  let D := concreteEscapeData μ l hl hμ hEscapePos
  exact D.isProbabilityMeasure_muW (ne_of_gt D.wRef_univ_pos) (D.wRef_univ_lt_top hμ).ne

instance (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l) :
    IsProbabilityMeasure (muU μ l hl hμ hEscapePos) := by
  let D := concreteEscapeData μ l hl hμ hEscapePos
  exact D.isProbabilityMeasure_muU (ne_of_gt D.uRef_univ_pos) D.uRef_univ_lt_top.ne

/-- The normalized edge-recording walk path law. -/
noncomputable def walkPathLaw (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l) :
    Measure PathSpace := muW μ l hl hμ hEscapePos ⊗ₘ moveLaw l hl

/-- The normalized edge-recording Q path law. -/
noncomputable def qPathLaw (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l) :
    Measure PathSpace := muU μ l hl hμ hEscapePos ⊗ₘ (qSpec l hl).law

/-- The walk state kernel is definitionally the abstract `weightedMoves` kernel. -/
theorem walkSpec_stateKernel (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l) :
    (walkSpec l hl).stateKernel = (concreteEscapeData μ l hl hμ hEscapePos).walkKernel := rfl

/-- The Q state kernel is definitionally the abstract `weightedMoves` kernel. -/
theorem qSpec_stateKernel (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l) :
    (qSpec l hl).stateKernel = (concreteEscapeData μ l hl hμ hEscapePos).qKernel := rfl

end LPPMonotonicityProof.Speed
