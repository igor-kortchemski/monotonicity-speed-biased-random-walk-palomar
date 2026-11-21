module

public import LPPMonotonicityProof.Speed.Env.Concrete
public import LPPMonotonicityProof.Speed.Interface.Bias
public import LPPMonotonicityProof.Speed.Walk.Hitting

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Set.Lattice.Indexed

/-!
# Transfer from ordered environments to the public rooted walk

This module starts the comparison of the environment walk with the public rooted walk
up to the first crossing of the edge to the artificial parent.  The
`Interface.Labels` specification cannot be combined with `Env.Concrete`, since both
declare `Speed.walkWeight`.  This module therefore gives the public chain a separate
`Markov.LabelSpec` adapter, using the same labels and masses as the public
`stepMeasure`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState
open LPPMonotonicityProof.RTL.LocallyFinite
open LPPMonotonicityProof.Speed.Markov

/-- Zero is the parent label and positive labels are the one-based children. -/
def publicNext : WalkState → ℕ → WalkState
  | .rootParent, _ => .vtx []
  | .vtx v, 0 => parentState v
  | .vtx v, j + 1 => .vtx (v ++ [j + 1])

/-- The label masses of the public walk. -/
noncomputable def publicWeight (ω : List ℕ → ℕ) (l : ℝ≥0) :
    WalkState → ℕ → ℝ≥0∞
  | .rootParent, j => if j = 0 then 1 else 0
  | .vtx v, j =>
      if l = 0 ∧ ω v = 0 then if j = 0 then 1 else 0
      else match j with
        | 0 => ((l / (l + ω v) : ℝ≥0) : ℝ≥0∞)
        | j + 1 => if j < ω v then ((1 / (l + ω v) : ℝ≥0) : ℝ≥0∞) else 0

private noncomputable def publicStateMeasure (ω : List ℕ → ℕ) (l : ℝ≥0)
    (x : WalkState) : Measure WalkState :=
  Measure.sum fun j => publicWeight ω l x j • Measure.dirac (publicNext x j)

private theorem publicStateMeasure_eq_stepMeasure (ω : List ℕ → ℕ) (l : ℝ≥0)
    (x : WalkState) : publicStateMeasure ω l x = stepMeasure l ω x := by
  cases x with
  | rootParent =>
      ext A hA
      rw [publicStateMeasure, Measure.sum_apply _ hA]
      simp only [publicWeight, publicNext, stepMeasure, Measure.smul_apply,
        Measure.dirac_apply]
      rw [tsum_eq_single 0]
      · simp
      · intro j hj
        simp [hj]
  | vtx v =>
      by_cases h : l = 0 ∧ ω v = 0
      · ext A hA
        rw [publicStateMeasure, Measure.sum_apply _ hA]
        simp only [publicWeight, publicNext, stepMeasure, h, Measure.smul_apply,
          Measure.dirac_apply]
        rw [tsum_eq_single 0]
        · simp
        · intro j hj
          simp [hj]
      · ext A hA
        rw [stepMeasure, ite_eq_right h]
        rw [publicStateMeasure, Measure.sum_apply _ hA]
        simp only [Measure.coe_add, Measure.coe_finsetSum, Measure.coe_smul,
          Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Measure.smul_apply,
          Measure.dirac_apply, smul_eq_mul]
        rw [tsum_eq_sum (s := Finset.range (ω v + 1)) (by
          intro j hj
          rw [Finset.mem_range] at hj
          cases j with
          | zero => omega
          | succ j =>
              have hjk : ¬j < ω v := by omega
              simp [publicWeight, hjk])]
        rw [Finset.sum_range_succ', ← Fin.sum_univ_eq_sum_range]
        simp [publicWeight, publicNext, h, add_comm]

/-- Total public label mass is one. -/
theorem tsum_publicWeight (ω : List ℕ → ℕ) (l : ℝ≥0) (x : WalkState) :
    ∑' j, publicWeight ω l x j = 1 := by
  have hm := congrArg (fun m : Measure WalkState => m Set.univ)
    (publicStateMeasure_eq_stepMeasure ω l x)
  rw [publicStateMeasure, Measure.sum_apply _ MeasurableSet.univ] at hm
  have hp : stepMeasure l ω x Set.univ = 1 := by
    change stepKernel l ω x Set.univ = 1
    exact measure_univ
  simpa [Measure.smul_apply, hp] using hm

/-- The public walk as a labelled Markov system. -/
noncomputable def publicSpec (ω : List ℕ → ℕ) (l : ℝ≥0) :
    Markov.LabelSpec WalkState where
  next := publicNext
  weight := publicWeight ω l
  measurable_next _ := measurable_of_countable _
  measurable_weight _ := measurable_of_countable _
  tsum_weight := tsum_publicWeight ω l

/-- Forgetting public labels gives exactly the public step kernel `stepKernel`. -/
theorem stepKernel_eq_publicSpec_stateKernel (ω : List ℕ → ℕ) (l : ℝ≥0) :
    stepKernel l ω = (publicSpec ω l).stateKernel := by
  apply Kernel.ext
  intro x
  rw [Markov.LabelSpec.stateKernel_apply]
  exact (publicStateMeasure_eq_stepMeasure ω l x).symm

/-- The point-started public walk is the state path of its labelled chain. -/
theorem walkFrom_eq_publicLabel (ω : List ℕ → ℕ) (l : ℝ≥0) (x : WalkState) :
    walkFrom ω l x = ((publicSpec ω l).law x).map ((publicSpec ω l).state x) := by
  simpa only [walkFrom, stepKernel_eq_publicSpec_stateKernel] using
    (Markov.LabelSpec.path_stateKernel (publicSpec ω l) x)

/-- The public state after reading `n` labels. -/
noncomputable def pubState (ω : List ℕ → ℕ) (l : ℝ≥0) (c : ℕ → ℕ) (n : ℕ) :
    WalkState := (publicSpec ω l).state (.vtx []) c n

/-- The event that the rooted walk has not crossed the joining edge before `N`. -/
def noHitBefore (ω : List ℕ → ℕ) (l : ℝ≥0) (N : ℕ) : Set (ℕ → ℕ) :=
  {c | ∀ n < N, pubState ω l c n ≠ .rootParent}

/-- The event that the rooted walk never crosses the joining edge. -/
def noHit (ω : List ℕ → ℕ) (l : ℝ≥0) : Set (ℕ → ℕ) :=
  {c | ∀ n, pubState ω l c n ≠ .rootParent}

lemma measurableSet_noHitBefore (ω : List ℕ → ℕ) (l : ℝ≥0) (N : ℕ) :
    MeasurableSet (noHitBefore ω l N) := by
  have h (n : ℕ) : MeasurableSet {c : ℕ → ℕ | pubState ω l c n ≠ .rootParent} := by
    exact (measurableSet_eq_fun ((measurable_pi_apply n).comp
      ((publicSpec ω l).measurable_state_apply (.vtx [])))
      (measurable_const : Measurable (fun _ : ℕ → ℕ => (WalkState.rootParent)))).compl
  rw [show noHitBefore ω l N = ⋂ n ∈ Finset.range N,
      {c : ℕ → ℕ | pubState ω l c n ≠ .rootParent} by
    ext c
    simp [noHitBefore]]
  exact Finset.measurableSet_biInter _ fun n _ => h n

lemma measurableSet_noHit (ω : List ℕ → ℕ) (l : ℝ≥0) : MeasurableSet (noHit ω l) := by
  rw [noHit]
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  exact (measurableSet_eq_fun ((measurable_pi_apply n).comp
    ((publicSpec ω l).measurable_state_apply (.vtx []))) measurable_const).compl

/-- Signed displacement recorded by a label. -/
def sgn (j : ℕ) : ℝ := if j = 0 then -1 else 1

/-- Before crossing the joining edge, height is the sum of signed moves. -/
theorem height_eq_signed {ω : List ℕ → ℕ} {l : ℝ≥0} {c : ℕ → ℕ}
    (hc : c ∈ noHit ω l) (n : ℕ) :
    (height (pubState ω l c n) : ℝ) = ∑ j ∈ Finset.range n, sgn (c j) := by
  induction n with
  | zero => simp [pubState, publicSpec, Markov.LabelSpec.state, height]
  | succ n ih =>
      have hc' : ∀ m, pubState ω l c m ≠ .rootParent := hc
      have hn : pubState ω l c n ≠ .rootParent := hc' n
      have hs : pubState ω l c (n + 1) ≠ .rootParent := hc' (n + 1)
      cases hstate : pubState ω l c n with
      | rootParent => exact (hn hstate).elim
      | vtx v =>
          cases hlabel : c n with
          | zero =>
              have hv : v ≠ [] := by
                intro hv
                apply hs
                change publicNext (pubState ω l c n) (c n) = .rootParent
                rw [hstate, hlabel]
                simp [publicNext, hv, parentState]
              have hparent : pubState ω l c (n + 1) = .vtx v.dropLast := by
                change publicNext (pubState ω l c n) (c n) = .vtx v.dropLast
                rw [hstate, hlabel]
                simp [publicNext, parentState, hv]
              rw [hparent, Finset.sum_range_succ, ← ih, hstate]
              have hlen : 1 ≤ v.length := List.length_pos_of_ne_nil hv
              simp [height, sgn, hlabel, List.length_dropLast, Nat.cast_sub hlen]
              ring
          | succ j =>
              have hchild : pubState ω l c (n + 1) = .vtx (v ++ [j + 1]) := by
                change publicNext (pubState ω l c n) (c n) = .vtx (v ++ [j + 1])
                rw [hstate, hlabel]
                rfl
              rw [hchild, Finset.sum_range_succ, ← ih, hstate]
              simp [height, sgn, hlabel]

end LPPMonotonicityProof.Speed
