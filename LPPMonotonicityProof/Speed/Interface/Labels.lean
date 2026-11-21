module

public import LPPMonotonicityProof.Speed.Interface.Bias
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Sum

/-!
# The public walk as a labelled countable chain

Only the labelled-state interface needed to match the public walk weights with the
environment weights is included here.  The path law, cylinder formula and labelled
Markov property are in `Speed/Markov/Label.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState
open LPPMonotonicityProof.RTL.LocallyFinite

/-- Minimal labelled-chain specification used by the public-walk interface. -/
structure LabelSpec (S : Type*) [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] where
  next : S → ℕ → S
  weight : S → ℕ → ℝ≥0∞
  measurable_next : ∀ j, Measurable fun s => next s j
  measurable_weight : ∀ j, Measurable fun s => weight s j
  tsum_weight : ∀ s, ∑' j, weight s j = 1

namespace LabelSpec

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The state kernel obtained by forgetting the selected label. -/
noncomputable def stateKernel (G : LabelSpec S) : Kernel S S :=
  Kernel.ofFunOfCountable fun s => Measure.sum fun j => G.weight s j • Measure.dirac (G.next s j)

end LabelSpec

/-- The label of a parent step is zero; child labels are one-based. -/
def pubNext : WalkState → ℕ → WalkState
  | .rootParent, _ => .vtx []
  | .vtx v, 0 => parentState v
  | .vtx v, j + 1 => .vtx (v ++ [j + 1])

/-- Mass of each public-walk label.  The zero-bias leaf fallback is put on
label zero; it is the only case where `pubNext` would otherwise lose mass. -/
noncomputable def pubWeight (ω : List ℕ → ℕ) (l : ℝ≥0) : WalkState → ℕ → ℝ≥0∞
  | .rootParent, j => if j = 0 then 1 else 0
  | .vtx v, j =>
      if l = 0 ∧ ω v = 0 then if j = 0 then 1 else 0
      else match j with
        | 0 => ((l / (l + ω v) : ℝ≥0) : ℝ≥0∞)
        | j + 1 => if j < ω v then ((1 / (l + ω v) : ℝ≥0) : ℝ≥0∞) else 0

private noncomputable def pubStateMeasure (ω : List ℕ → ℕ) (l : ℝ≥0) (x : WalkState) :
    Measure WalkState :=
  Measure.sum fun j => pubWeight ω l x j • Measure.dirac (pubNext x j)

private theorem pubStateMeasure_eq_stepMeasure (ω : List ℕ → ℕ) (l : ℝ≥0)
    (x : WalkState) : pubStateMeasure ω l x = stepMeasure l ω x := by
  cases x with
  | rootParent =>
      ext A hA
      rw [pubStateMeasure, Measure.sum_apply _ hA]
      simp only [pubWeight, pubNext, stepMeasure, Measure.smul_apply, Measure.dirac_apply]
      rw [tsum_eq_single 0]
      · simp
      · intro j hj
        simp [hj]
  | vtx v =>
      by_cases h : l = 0 ∧ ω v = 0
      · ext A hA
        rw [pubStateMeasure, Measure.sum_apply _ hA]
        simp only [pubWeight, pubNext, stepMeasure, h, Measure.smul_apply, Measure.dirac_apply]
        rw [tsum_eq_single 0]
        · simp
        · intro j hj
          simp [hj]
      · ext A hA
        rw [stepMeasure, ite_eq_right h]
        rw [pubStateMeasure, Measure.sum_apply _ hA]
        simp only [Measure.coe_add, Measure.coe_finsetSum, Measure.coe_smul, Pi.add_apply,
          Finset.sum_apply, Pi.smul_apply, Measure.smul_apply, Measure.dirac_apply,
          smul_eq_mul]
        rw [tsum_eq_sum (s := Finset.range (ω v + 1)) (by
          intro j hj
          rw [Finset.mem_range] at hj
          cases j with
          | zero => omega
          | succ j =>
              have hjk : ¬j < ω v := by omega
              simp [pubWeight, hjk])]
        rw [Finset.sum_range_succ', ← Fin.sum_univ_eq_sum_range]
        simp [pubWeight, pubNext, h, add_comm]

/-- The total public label mass is one. -/
theorem tsum_pubWeight (ω : List ℕ → ℕ) (l : ℝ≥0) (x : WalkState) :
    ∑' j, pubWeight ω l x j = 1 := by
  have hm := congrArg (fun m : Measure WalkState => m Set.univ)
    (pubStateMeasure_eq_stepMeasure ω l x)
  rw [pubStateMeasure, Measure.sum_apply _ MeasurableSet.univ] at hm
  have hp : stepMeasure l ω x Set.univ = 1 := by
    change stepKernel l ω x Set.univ = 1
    exact measure_univ
  simpa [Measure.smul_apply, hp] using hm

/-- The public walk as a labelled specification. -/
noncomputable def pubSpec (ω : List ℕ → ℕ) (l : ℝ≥0) : LabelSpec WalkState where
  next := pubNext
  weight := pubWeight ω l
  measurable_next _ := measurable_of_countable _
  measurable_weight _ := measurable_of_countable _
  tsum_weight := tsum_pubWeight ω l

/-- Forgetting labels in the public specification gives the public transition kernel. -/
theorem stepKernel_eq_pubSpec_stateKernel (ω : List ℕ → ℕ) (l : ℝ≥0) :
    stepKernel l ω = (pubSpec ω l).stateKernel := by
  unfold stepKernel LabelSpec.stateKernel
  congr 1
  funext x
  exact (pubStateMeasure_eq_stepMeasure ω l x).symm

/-- RTL weights on an environment, with zero the inward label. -/
noncomputable def walkWeight (l : ℝ) (e : Env) (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then ENNReal.ofReal (l / (l + degree e.fwd))
  else if j ≤ degree e.fwd then ENNReal.ofReal (1 / (l + degree e.fwd)) else 0

/-- The RTL and public weights agree at a vertex, after converting the bias. -/
theorem walkWeight_eq_pubWeight (l : ℝ) (hl : 0 < l) (e : Env) (j : ℕ) :
    walkWeight l e j = pubWeight e.fwd.val l.toNNReal (.vtx []) j := by
  have hl0 : l.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hl)
  cases j with
  | zero =>
      simp only [walkWeight, pubWeight, hl0, false_and, ↓reduceIte, degree]
      exact (coe_bias_div l hl (degree e.fwd)).symm
  | succ j =>
      by_cases hj : j < degree e.fwd
      · change j < e.fwd.val [] at hj
        simp only [walkWeight, Nat.succ_ne_zero, ↓reduceIte, pubWeight, hl0, false_and,
          degree, Nat.succ_le_iff, hj]
        exact (coe_one_div l hl (degree e.fwd)).symm
      · change ¬j < e.fwd.val [] at hj
        simp only [walkWeight, Nat.succ_ne_zero, ↓reduceIte, pubWeight, hl0, false_and,
          degree, Nat.succ_le_iff, hj]

end LPPMonotonicityProof.Speed
