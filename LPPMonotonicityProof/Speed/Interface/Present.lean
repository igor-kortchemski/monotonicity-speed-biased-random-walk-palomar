module

public import LPPMonotonicityProof.Speed.Walk.Hitting
public import LPPMonotonicityProof.Speed.Markov.Label
public import LPPMonotonicityProof.Speed.Interface.Labels

/-!
# Walks read only the present vertices

The public walk is expressed through the general labelled
chain interface.  Positive-weight steps preserve the vertices of `prune ω`,
and finite-word cylinder probabilities depend on the field only at those
vertices.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState
open LPPMonotonicityProof.RTL.LocallyFinite

/-- A walk state allowed by the pruned tree: the artificial root parent or a
present vertex. -/
def PresentState (ω : Offspring) : WalkState → Prop
  | .rootParent => True
  | .vtx v => Present (prune ω) v

/-- The public specification in the general labelled-chain interface. -/
noncomputable def pubMarkovSpec (ω : Offspring) (l : ℝ≥0) :
    Markov.LabelSpec WalkState where
  next := pubNext
  weight := pubWeight ω l
  measurable_next _ := measurable_of_countable _
  measurable_weight _ := measurable_of_countable _
  tsum_weight := tsum_pubWeight ω l

@[simp] theorem pubMarkovSpec_next (ω : Offspring) (l : ℝ≥0) :
    (pubMarkovSpec ω l).next = pubNext := rfl

@[simp] theorem pubMarkovSpec_weight (ω : Offspring) (l : ℝ≥0) :
    (pubMarkovSpec ω l).weight = pubWeight ω l := rfl

/-- The general labelled specification has the public state kernel `stepKernel`. -/
theorem stepKernel_eq_pubMarkovSpec_stateKernel (ω : Offspring) (l : ℝ≥0) :
    stepKernel l ω = (pubMarkovSpec ω l).stateKernel := by
  rw [stepKernel_eq_pubSpec_stateKernel]
  ext x A hA
  rw [Markov.LabelSpec.stateKernel_apply, Measure.sum_apply _ hA]
  change (Measure.sum fun j => pubWeight ω l x j • Measure.dirac (pubNext x j)) A = _
  rw [Measure.sum_apply _ hA]
  rfl

private theorem path_congr_of_eq {K K' : Kernel WalkState WalkState}
    [IsMarkovKernel K] [IsMarkovKernel K'] (h : K = K') (x : WalkState) :
    path K x = path K' x := by
  subst K'
  rfl

/-- The point-started public path is the state projection of its label law. -/
theorem walkFrom_eq_label (ω : Offspring) (l : ℝ≥0) (x : WalkState) :
    walkFrom ω l x = ((pubMarkovSpec ω l).law x).map ((pubMarkovSpec ω l).state x) := by
  unfold walkFrom
  exact (path_congr_of_eq (stepKernel_eq_pubMarkovSpec_stateKernel ω l) x).trans
    (Markov.LabelSpec.path_stateKernel (pubMarkovSpec ω l) x)

private theorem present_dropLast {T : Tree} :
    ∀ (v : Address), Present T v → Present T v.dropLast := by
  intro v
  induction v generalizing T with
  | nil => exact fun _ => trivial
  | cons j u ih =>
      intro hv
      cases u with
      | nil => exact trivial
      | cons k u =>
          exact ⟨hv.1, hv.2.1, ih hv.2.2⟩

/-- A positive-weight public step from an allowed state stays in the allowed
states of the same pruned tree. -/
theorem presentState_pubNext {ω : Offspring} {l : ℝ≥0} {x : WalkState}
    (hx : PresentState ω x) {j : ℕ} (hj : pubWeight ω l x j ≠ 0) :
    PresentState ω (pubNext x j) := by
  cases x with
  | rootParent => exact trivial
  | vtx v =>
      cases j with
      | zero =>
          cases v with
          | nil => exact trivial
          | cons k u =>
              exact present_dropLast (k :: u) hx
      | succ j =>
          have hf : ¬(l = 0 ∧ ω v = 0) := by
            intro hf
            simp [pubWeight, hf] at hj
          have hjv : j < ω v := by
            by_contra hjv
            simp [pubWeight, hf, hjv] at hj
          apply (present_append_singleton (prune ω) v (j + 1) hx).2
          refine ⟨Nat.succ_pos j, ?_⟩
          rw [prune_val_of_present hx]
          omega

private def AgreeState (ω η : Offspring) (x : WalkState) : Prop :=
  PresentState ω x ∧ PresentState η x

/-- Fields agreeing on present vertices of `prune ω` have the same present
vertices. -/
theorem present_prune_of_agree {ω η : Offspring}
    (h : ∀ u, Present (prune ω) u → ω u = η u) :
    ∀ v, Present (prune ω) v → Present (prune η) v := by
  intro v
  induction v generalizing ω η with
  | nil => exact fun _ => trivial
  | cons j u ih =>
      intro hv
      have hj : 1 ≤ j ∧ j ≤ ω [] := ⟨hv.1, hv.2.1⟩
      have hroot : ω [] = η [] := h [] trivial
      have hjη : 1 ≤ j ∧ j ≤ η [] := hroot ▸ hj
      refine ⟨hjη.1, hjη.2, ?_⟩
      have hcω : child (prune ω) j = prune (fun u => ω (j :: u)) := by
        rw [child_prune, ite_eq_left hj]
      have hcη : child (prune η) j = prune (fun u => η (j :: u)) := by
        rw [child_prune, ite_eq_left hjη]
      rw [hcη]
      apply ih (ω := fun u => ω (j :: u)) (η := fun u => η (j :: u))
      · intro w hw
        apply h (j :: w)
        exact ⟨hj.1, hj.2, by rw [hcω]; exact hw⟩
      · have hv' := hv.2.2
        rw [hcω] at hv'
        exact hv'

private theorem pubWeight_eq_of_agree {ω η : Offspring} (l : ℝ≥0)
    (h : ∀ u, Present (prune ω) u → ω u = η u) {x : WalkState}
    (hx : AgreeState ω η x) (j : ℕ) :
    pubWeight ω l x j = pubWeight η l x j := by
  cases x with
  | rootParent => rfl
  | vtx v => simp only [pubWeight, h v hx.1]

private theorem agreeState_pubNext {ω η : Offspring} {l : ℝ≥0} {x : WalkState}
    (h : ∀ u, Present (prune ω) u → ω u = η u) (hx : AgreeState ω η x)
    {j : ℕ} (hj : pubWeight ω l x j ≠ 0) :
    AgreeState ω η (pubNext x j) := by
  exact ⟨presentState_pubNext hx.1 hj,
    presentState_pubNext hx.2 ((pubWeight_eq_of_agree l h hx j) ▸ hj)⟩

private theorem pubLaw_cylinder_eq_of_agree {ω η : Offspring} (l : ℝ≥0)
    (h : ∀ u, Present (prune ω) u → ω u = η u) {x : WalkState}
    (hx : AgreeState ω η x) (w : ℕ → ℕ) (n : ℕ) :
    (pubMarkovSpec ω l).law x (Markov.LabelSpec.wordCylinder w n) =
      (pubMarkovSpec η l).law x (Markov.LabelSpec.wordCylinder w n) := by
  rw [Markov.LabelSpec.law_cylinder, Markov.LabelSpec.law_cylinder]
  induction n generalizing x w with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ', Finset.prod_range_succ']
      simp only [pubMarkovSpec_weight]
      have hw := pubWeight_eq_of_agree l h hx (w 0)
      have hw' : pubWeight ω l ((pubMarkovSpec ω l).state x w 0) (w 0) =
          pubWeight η l ((pubMarkovSpec η l).state x w 0) (w 0) := by
        exact hw
      rw [hw']
      change (∏ k ∈ Finset.range n, pubWeight ω l
          ((pubMarkovSpec ω l).state x w (k + 1)) (w (k + 1))) *
          pubWeight η l x (w 0) = _
      by_cases hw0 : pubWeight η l x (w 0) = 0
      · have hw0' : pubWeight η l ((pubMarkovSpec η l).state x w 0) (w 0) = 0 := by
          exact hw0
        simp [hw0, hw0']
      · have hw0ω : pubWeight ω l x (w 0) ≠ 0 := by
          intro hzero
          apply hw0
          rw [← hw]
          exact hzero
        simp only [← Markov.LabelSpec.state_succ]
        exact congrArg (· * pubWeight η l x (w 0))
          (ih (agreeState_pubNext h hx hw0ω) (Markov.LabelSpec.seqTail w))

/-- The label laws of fields agreeing on present vertices are equal. -/
theorem pubLaw_eq_of_agree {ω η : Offspring} (l : ℝ≥0)
    (h : ∀ u, Present (prune ω) u → ω u = η u) {v : Address}
    (hv : Present (prune ω) v) :
    (pubMarkovSpec ω l).law (.vtx v) = (pubMarkovSpec η l).law (.vtx v) := by
  apply Markov.LabelSpec.law_ext (pubMarkovSpec η l) (.vtx v)
  intro w n
  exact pubLaw_cylinder_eq_of_agree l h (x := .vtx v)
    (show Present (prune ω) v ∧ Present (prune η) v from
      ⟨hv, present_prune_of_agree h v hv⟩) w n

private theorem pubMarkovSpec_state_eq (ω η : Offspring) (l : ℝ≥0) (x : WalkState) :
    (pubMarkovSpec ω l).state x = (pubMarkovSpec η l).state x := by
  funext c n
  induction n with
  | zero => rfl
  | succ n ih =>
      change pubNext ((pubMarkovSpec ω l).state x c n) (c n) =
        pubNext ((pubMarkovSpec η l).state x c n) (c n)
      rw [ih]

/-- Point-started public walks depend only on the field at present vertices. -/
theorem walkFrom_eq_of_agree {ω η : Offspring} (l : ℝ≥0)
    (h : ∀ u, Present (prune ω) u → ω u = η u) {v : Address}
    (hv : Present (prune ω) v) :
    walkFrom ω l (.vtx v) = walkFrom η l (.vtx v) := by
  calc
    walkFrom ω l (.vtx v) =
        ((pubMarkovSpec ω l).law (.vtx v)).map ((pubMarkovSpec ω l).state (.vtx v)) :=
      walkFrom_eq_label ω l (.vtx v)
    _ = ((pubMarkovSpec η l).law (.vtx v)).map ((pubMarkovSpec ω l).state (.vtx v)) := by
      rw [pubLaw_eq_of_agree l h hv]
    _ = ((pubMarkovSpec η l).law (.vtx v)).map ((pubMarkovSpec η l).state (.vtx v)) := by
      rw [pubMarkovSpec_state_eq]
    _ = walkFrom η l (.vtx v) := (walkFrom_eq_label η l (.vtx v)).symm

/-- Root-started public walks depend only on the field at present vertices. -/
theorem walkLaw_eq_of_agree {ω η : Offspring} (l : ℝ≥0)
    (h : ∀ u, Present (prune ω) u → ω u = η u) :
    walkLaw ω l = walkLaw η l := by
  rw [walkLaw_eq_walkFrom, walkLaw_eq_walkFrom]
  exact walkFrom_eq_of_agree l h trivial

/-- From a present vertex, pruning does not change the public walk law. -/
theorem walkFrom_prune (ω : Offspring) (l : ℝ≥0) {v : Address}
    (hv : Present (prune ω) v) :
    walkFrom ω l (.vtx v) = walkFrom (prune ω).val l (.vtx v) := by
  apply walkFrom_eq_of_agree l _ hv
  intro u hu
  exact (prune_val_of_present hu).symm

/-- Pruning does not change the root-started public walk law `walkLaw`. -/
theorem walkLaw_prune (ω : Offspring) (l : ℝ≥0) :
    walkLaw ω l = walkLaw (prune ω).val l := by
  apply walkLaw_eq_of_agree l
  intro u hu
  exact (prune_val_of_present hu).symm

private theorem ae_presentState_label (ω : Offspring) (l : ℝ≥0) {x : WalkState}
    (hx : PresentState ω x) (n : ℕ) :
    ∀ᵐ c ∂(pubMarkovSpec ω l).law x, PresentState ω ((pubMarkovSpec ω l).state x c n) := by
  induction n generalizing x with
  | zero => exact ae_of_all _ fun _ => hx
  | succ n ih =>
      rw [(pubMarkovSpec ω l).law_firstStep, Measure.ae_sum_iff]
      intro j
      by_cases hj : pubWeight ω l x j = 0
      · simp [hj]
      · apply Measure.ae_smul_measure _ _
        have hm : MeasurableSet {c : ℕ → ℕ |
            PresentState ω ((pubMarkovSpec ω l).state x c (n + 1))} :=
          (Set.to_countable {y : WalkState | PresentState ω y}).measurableSet.preimage
            ((measurable_pi_apply (n + 1)).comp
              ((pubMarkovSpec ω l).measurable_state_apply x))
        refine (MeasureTheory.ae_map_iff
          (Markov.LabelSpec.measurable_seqCons j).aemeasurable hm).2 ?_
        filter_upwards [ih (presentState_pubNext hx hj)] with c hc
        simpa [Markov.LabelSpec.state_seqCons, pcons] using hc

/-- A public walk started at a present vertex almost surely stays in the
present vertices and the artificial root parent at every time. -/
theorem ae_walkFrom_present (ω : Offspring) (l : ℝ≥0) {v : Address}
    (hv : Present (prune ω) v) :
    ∀ᵐ X ∂walkFrom ω l (.vtx v), ∀ n, PresentState ω (X n) := by
  have hm : MeasurableSet {X : ℕ → WalkState | ∀ n, PresentState ω (X n)} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      (Set.to_countable {y : WalkState | PresentState ω y}).measurableSet.preimage
        (measurable_pi_apply n)
  rw [walkFrom_eq_label, MeasureTheory.ae_map_iff
    ((pubMarkovSpec ω l).measurable_state_apply (.vtx v)).aemeasurable hm]
  exact ae_all_iff.2 fun n => ae_presentState_label ω l (x := .vtx v) hv n

/-- The root-started public walk `walkLaw` almost surely stays in the present
vertices of `prune ω` plus `rootParent`. -/
theorem ae_walkLaw_present (ω : Offspring) (l : ℝ≥0) :
    ∀ᵐ X ∂walkLaw ω l, ∀ n, PresentState ω (X n) := by
  rw [walkLaw_eq_walkFrom]
  exact ae_walkFrom_present ω l trivial

end LPPMonotonicityProof.Speed
