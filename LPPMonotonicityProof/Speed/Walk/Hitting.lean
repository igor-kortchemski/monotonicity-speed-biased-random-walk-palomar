module

public import LPPMonotonicityProof.Speed.Interface.ZeroBias
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Point-started walks and hitting events

This module gives the raw-field walk interface: walks started at any state, and
hitting events.  It uses the homogeneous path kernel and the adapters to the
public model of `LPPMonotonicity/Model/Defs.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState

/-- The quenched path law started at an arbitrary walk state. -/
noncomputable def walkFrom (ω : List ℕ → ℕ) (l : ℝ≥0) (x : WalkState) :
    Measure (ℕ → WalkState) := path (stepKernel l ω) x

instance isProbabilityMeasure_walkFrom (ω : List ℕ → ℕ) (l : ℝ≥0) (x : WalkState) :
    IsProbabilityMeasure (walkFrom ω l x) := by
  unfold walkFrom
  infer_instance

/-- The public root-started law is the point-started homogeneous path law. -/
theorem walkLaw_eq_walkFrom (ω : List ℕ → ℕ) (l : ℝ≥0) :
    walkLaw ω l = walkFrom ω l (.vtx []) := by
  rw [walkLaw_eq_path]
  rfl

/-- Reach generation `|v| + N` no later than the first visit to the parent of
`v` (in particular, the parent has not been visited at the hitting time). -/
def reachLevelBefore (v : List ℕ) (N : ℕ) : Set (ℕ → WalkState) :=
  {X | ∃ t, height (X t) = v.length + N ∧ ∀ s ≤ t, X s ≠ parentState v}

/-- Paths which never visit `y`. -/
def neverHits (y : WalkState) : Set (ℕ → WalkState) := {X | ∀ t, X t ≠ y}

/-- The hitting events are measurable in the product path space. -/
theorem measurableSet_reachLevelBefore (v : List ℕ) (N : ℕ) :
    MeasurableSet (reachLevelBefore v N) := by
  rw [reachLevelBefore]
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro t
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      ((measurable_of_countable height).comp (measurable_pi_apply t)) measurable_const
  · change MeasurableSet {X : ℕ → WalkState | ∀ s ≤ t, X s ≠ parentState v}
    rw [show {X : ℕ → WalkState | ∀ s ≤ t, X s ≠ parentState v} =
        ⋂ s, {X : ℕ → WalkState | s ≤ t → X s ≠ parentState v} by
      ext X
      simp]
    apply MeasurableSet.iInter
    intro s
    by_cases hs : s ≤ t
    · simp only [hs, forall_true_left]
      convert (measurableSet_eq_fun (measurable_pi_apply s)
          (measurable_const : Measurable (fun _ : ℕ → WalkState => parentState v))).compl using 1
      ext X
      simp
    · simp [hs]

/-- The never-hit event is measurable. -/
theorem measurableSet_neverHits (y : WalkState) : MeasurableSet (neverHits y) := by
  rw [neverHits]
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro t
  convert (measurableSet_eq_fun (measurable_pi_apply t)
    (measurable_const : Measurable (fun _ : ℕ → WalkState => y))).compl using 1
  ext X
  simp

end LPPMonotonicityProof.Speed
