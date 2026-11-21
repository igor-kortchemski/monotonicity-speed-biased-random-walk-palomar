module

public import LPPMonotonicityProof.Speed.Env.Invariance
public import LPPMonotonicityProof.Speed.Markov.Label
public import LPPMonotonicityProof.Speed.Walk.Escape
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The concrete harmonic ray

The harmonic label law chooses child `i` with weight
`escapeWeight (escape l) T i / escapeSum (escape l) T`, with the prescribed
`δ₁` fallback when the escape sum vanishes.  Using `escapeWeight` makes the
one-based, absent-child convention explicit and gives a definitional bridge to
the abstract `EscapeData.qWeight`.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The finite harmonic child sum in the abstract `EscapeData` normal form. -/
theorem escapeSum_escape_eq_childSum (l : ℝ) :
    escapeSum (escape l) = childSum l := by
  funext T
  exact escapeSum_eq_sum_fin (escape l) T

/-- Harmonic child weights, including the `δ₁` fallback off the good set. -/
noncomputable def harmWeight (l : ℝ) (T : Tree) (i : ℕ) : ℝ≥0∞ :=
  if 0 < escapeSum (escape l) T then
    ENNReal.ofReal (escapeWeight (escape l) T i / escapeSum (escape l) T)
  else if i = 1 then 1 else 0

private theorem summable_escapeWeight_escape (l : ℝ) (T : Tree) :
    Summable (escapeWeight (escape l) T) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 (degree T))
  intro i hi
  simp only [Finset.mem_Icc, not_and, not_le] at hi
  simp only [escapeWeight, ite_eq_right_iff]
  intro hvalid
  omega

private theorem escapeWeight_escape_eq_zero_of_sum_eq_zero {l : ℝ} (hl : 0 < l) {T : Tree}
    (hS : escapeSum (escape l) T = 0) (i : ℕ) : escapeWeight (escape l) T i = 0 := by
  have hβ : ∀ R, 0 ≤ escape l R := fun R => (escape_mem_Icc hl R).1
  by_cases hi : 1 ≤ i ∧ i ≤ degree T
  · have hle : escapeWeight (escape l) T i ≤ escapeSum (escape l) T := by
      rw [escapeSum_eq_sum_Icc, escapeWeight, ite_eq_left hi]
      exact Finset.single_le_sum
        (f := fun j => escape l (child T j)) (fun j _ => hβ _) (by simpa [Finset.mem_Icc] using hi)
    rw [hS] at hle
    exact le_antisymm hle (escapeWeight_nonneg hβ T i)
  · simp [escapeWeight, hi]

/-- The harmonic weights are measurable in their tree. -/
theorem measurable_harmWeight (l : ℝ) (i : ℕ) :
    Measurable (fun T => harmWeight l T i) := by
  have hS : Measurable (fun T : Tree => escapeSum (escape l) T) := by
    rw [escapeSum_escape_eq_childSum]
    exact measurable_childSum l
  have hβ : Measurable (escape l) := measurable_escape l
  have hw : Measurable (fun T : Tree => escapeWeight (escape l) T i) := by
    apply Measurable.ite
    · exact (MeasurableSet.of_discrete :
        MeasurableSet {p : ℕ × ℕ | 1 ≤ p.1 ∧ p.1 ≤ p.2}).preimage
        (measurable_const.prodMk continuous_degree.measurable)
    · exact hβ.comp (continuous_child i).measurable
    · exact measurable_const
  apply Measurable.ite (measurableSet_lt measurable_const hS)
  · exact ENNReal.measurable_ofReal.comp (hw.div hS)
  · exact measurable_const

/-- The harmonic weights have total mass one at every tree. -/
theorem tsum_harmWeight {l : ℝ} (hl : 0 < l) (T : Tree) :
    ∑' i, harmWeight l T i = 1 := by
  have hβ : ∀ R, 0 ≤ escape l R := fun R => (escape_mem_Icc hl R).1
  by_cases hS : 0 < escapeSum (escape l) T
  · simp only [harmWeight, hS, ↓reduceIte]
    have hs : Summable (fun j => escapeWeight (escape l) T j / escapeSum (escape l) T) :=
      (summable_escapeWeight_escape l T).div_const _
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun j => div_nonneg (escapeWeight_nonneg hβ _ _) hS.le) hs]
    rw [tsum_div_const]
    change ENNReal.ofReal (escapeSum (escape l) T / escapeSum (escape l) T) = 1
    rw [div_self (ne_of_gt hS), ENNReal.ofReal_one]
  · have hS0 : escapeSum (escape l) T = 0 :=
      le_antisymm (not_lt.mp hS) (escapeSum_nonneg hβ T)
    simp [harmWeight, hS]

/-- The harmonic ray as a labelled Markov system on arbitrary trees. -/
noncomputable def harmSpec (l : ℝ) (hl : 0 < l) : Markov.LabelSpec Tree where
  next := child
  weight := harmWeight l
  measurable_next j := (continuous_child j).measurable
  measurable_weight := measurable_harmWeight l
  tsum_weight := tsum_harmWeight hl

/-- The law of the harmonic ray. -/
noncomputable def harm (l : ℝ) (hl : 0 < l) : Kernel Tree (ℕ → ℕ) :=
  (harmSpec l hl).law

instance (l : ℝ) (hl : 0 < l) : IsMarkovKernel (harm l hl) := by
  unfold harm
  infer_instance

/-- First-step integration for any labelled system. -/
theorem lintegral_label_law_firstStep {S : Type*} [MeasurableSpace S]
    (G : Markov.LabelSpec S) (s : S) {g : (ℕ → ℕ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ r, g r ∂G.law s = ∑' j, G.weight s j *
      ∫⁻ r, g (Markov.LabelSpec.seqCons j r) ∂G.law (G.next s j) := by
  rw [G.law_firstStep]
  simp only [lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul]
  apply tsum_congr
  intro j
  exact congrArg (fun x => G.weight s j * x)
    (lintegral_map hg (Markov.LabelSpec.measurable_seqCons j))

/-- The normalized form of the concrete harmonic first-step identity. -/
theorem lintegral_harmSpec_firstStep (l : ℝ) (hl : 0 < l) (T : Tree)
    {g : (ℕ → ℕ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ r, g r ∂harm l hl T = ∑' i, harmWeight l T i *
      ∫⁻ r, g (seqCons i r) ∂harm l hl (child T i) := by
  exact lintegral_label_law_firstStep (harmSpec l hl) T hg

/-- **The harmonic first-step identity**, in the exact `EscapeData.harm_firstStep`
form, for every tree. -/
theorem harm_firstStep {l : ℝ} (hl : 0 < l) (T : Tree)
    {g : (ℕ → ℕ) → ℝ≥0∞} (hg : Measurable g) :
    ENNReal.ofReal (escapeSum (escape l) T) * ∫⁻ r, g r ∂harm l hl T =
      ∑' i : ℕ, ENNReal.ofReal (escapeWeight (escape l) T i) *
        ∫⁻ r, g (seqCons i r) ∂harm l hl (child T i) := by
  have hβ : ∀ R, 0 ≤ escape l R := fun R => (escape_mem_Icc hl R).1
  rw [lintegral_harmSpec_firstStep l hl T hg, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro i
  by_cases hS : 0 < escapeSum (escape l) T
  · simp only [harmWeight, hS, ↓reduceIte]
    have hcancel : ENNReal.ofReal (escapeSum (escape l) T) *
        ENNReal.ofReal (escapeWeight (escape l) T i / escapeSum (escape l) T) =
          ENNReal.ofReal (escapeWeight (escape l) T i) := by
      rw [← ENNReal.ofReal_mul hS.le]
      congr 1
      field_simp [ne_of_gt hS]
    rw [← mul_assoc, hcancel]
  · have hS0 : escapeSum (escape l) T = 0 :=
      le_antisymm (not_lt.mp hS) (escapeSum_nonneg hβ T)
    rw [hS0, escapeWeight_escape_eq_zero_of_sum_eq_zero hl hS0 i]
    simp

end LPPMonotonicityProof.Speed
