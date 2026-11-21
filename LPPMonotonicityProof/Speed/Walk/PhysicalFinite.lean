module

public import LPPMonotonicityProof.Speed.Walk.Ball
public import LPPMonotonicityProof.Speed.Markov.Stopping

/-!
# Physical finite escape probabilities

The probability of reaching generation `|v| + N` from `v` before visiting the
parent of `v` is the finite escape `escapeN` (Lemma 2.1(i), `lem:escape`, for the
walk stopped at a fixed generation).  The proof sums the fixed-time Markov property over the
first return to the base vertex which occurs before the boundary is reached.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Preorder Filtration
open scoped NNReal ENNReal BigOperators Function

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState

@[simp] lemma parentState_offChild (ω : List ℕ → ℕ) (v : List ℕ) (i : Fin (ω v)) :
    parentState (offChild ω v i) = .vtx v := by
  simp [parentState, offChild]

/-- A transition allowed by the raw offspring field. -/
def StepRel (ω : List ℕ → ℕ) : WalkState → WalkState → Prop
  | .rootParent, y => y = .vtx []
  | .vtx v, y => y = parentState v ∨ ∃ i : Fin (ω v), y = .vtx (offChild ω v i)

lemma stepRel_height {ω : List ℕ → ℕ} {x y : WalkState} (h : StepRel ω x y) :
    height y = height x + 1 ∨ height y = height x - 1 := by
  cases x with
  | rootParent =>
      cases y with
      | rootParent => simp [StepRel] at h
      | vtx v =>
          cases v with
          | nil => left; rfl
          | cons a v => simp [StepRel] at h
  | vtx v =>
      rcases h with h | ⟨i, rfl⟩
      · subst y
        right
        by_cases hv : v = []
        · simp [hv, parentState, height]
        · simp only [parentState, hv, ↓reduceIte, height, List.length_dropLast]
          have hlen : 0 < v.length := List.length_pos_of_ne_nil hv
          rw [Nat.cast_sub hlen]
          simp
      · left
        simp [height, offChild]

lemma measurableSet_stepRel (ω : List ℕ → ℕ) (x : WalkState) :
    MeasurableSet {y | StepRel ω x y} := by
  cases x with
  | rootParent =>
      have heq : {y | StepRel ω .rootParent y} = {.vtx []} := by
        ext y
        cases y <;> simp [StepRel]
      rw [heq]
      exact MeasurableSet.singleton _
  | vtx v =>
      have heq : {y | StepRel ω (.vtx v) y} =
          {parentState v} ∪ ⋃ i : Fin (ω v), {.vtx (offChild ω v i)} := by
        ext y
        simp only [Set.mem_setOf_eq, StepRel, Set.mem_union, Set.mem_singleton_iff,
          Set.mem_iUnion]
      rw [heq]
      exact (MeasurableSet.singleton _).union
        (MeasurableSet.iUnion fun _ => MeasurableSet.singleton _)

lemma stepKernel_stepRel (l : ℝ≥0) (ω : List ℕ → ℕ) (x : WalkState) :
    stepKernel l ω x {y | StepRel ω x y} = 1 := by
  cases x with
  | rootParent =>
      simp [stepKernel, Kernel.ofFunOfCountable, stepMeasure, StepRel]
  | vtx v =>
      by_cases h : l = 0 ∧ ω v = 0
      · simp [stepKernel, Kernel.ofFunOfCountable, stepMeasure, h, StepRel]
      · apply (prob_compl_eq_zero_iff (measurableSet_stepRel ω (.vtx v))).mp
        simp [stepKernel, Kernel.ofFunOfCountable, stepMeasure, h, StepRel, offChild]

lemma measurableSet_stepRel_path (ω : List ℕ → ℕ) :
    MeasurableSet {X : ℕ → WalkState | StepRel ω (X 0) (X 1)} := by
  rw [show {X : ℕ → WalkState | StepRel ω (X 0) (X 1)} =
      ⋃ x, {X | X 0 = x} ∩ {X | StepRel ω x (X 1)} by ext X; simp]
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.inter
  · exact (MeasurableSet.singleton x).preimage (measurable_pi_apply 0)
  · rw [show {X : ℕ → WalkState | StepRel ω x (X 1)} =
        ⋃ y, ⋃ (_ : StepRel ω x y), {X : ℕ → WalkState | X 1 = y} by ext X; simp]
    exact MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _ =>
      (MeasurableSet.singleton y).preimage (measurable_pi_apply 1)

lemma path_one_step (K : Kernel WalkState WalkState) [IsMarkovKernel K]
    (ω : List ℕ → ℕ) (hK : ∀ x, K x {y | StepRel ω x y} = 1) (x : WalkState) :
    path K x {X | StepRel ω (X 0) (X 1)} = 1 := by
  let A : Set (ℕ → WalkState) := {X | StepRel ω (X 0) (X 1)}
  have hA : MeasurableSet A := measurableSet_stepRel_path ω
  classical
  have hz (z : WalkState) : path K z (pcons x ⁻¹' A) =
      if StepRel ω x z then 1 else 0 := by
    split_ifs with h
    · apply (mem_ae_iff_prob_eq_one ((measurableSet_stepRel ω x).preimage
        (measurable_pi_apply 0))).mp
      filter_upwards [path_zero K z] with X hX
      change StepRel ω x (X 0)
      rwa [hX]
    · apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [path_zero K z] with X hX
      change ¬ StepRel ω x (X 0)
      rwa [hX]
  rw [path_apply_firstStep K x hA]
  simp_rw [hz]
  -- The integrand is the indicator of a set of full transition measure.
  have hi : (fun z => if StepRel ω x z then (1 : ℝ≥0∞) else 0) =
      {y | StepRel ω x y}.indicator 1 := by
    funext z
    simp [Set.indicator]
  rw [hi, lintegral_indicator_one (measurableSet_stepRel ω x), hK]

/-- Almost every trajectory follows transitions allowed by the raw field. -/
theorem walkFrom_ae_stepRel (l : ℝ≥0) (ω : List ℕ → ℕ) (x : WalkState) :
    ∀ᵐ X ∂walkFrom ω l x, ∀ t, StepRel ω (X t) (X (t + 1)) := by
  let A : Set (ℕ → WalkState) := {X | StepRel ω (X 0) (X 1)}
  have hA : MeasurableSet A := measurableSet_stepRel_path ω
  have hone (t : ℕ) : walkFrom ω l x (shiftN t ⁻¹' A) = 1 := by
    have hm := path_markov (stepKernel l ω) t x
      (MeasurableSet.univ : MeasurableSet[piLE t] (Set.univ : Set (ℕ → WalkState))) hA
    simp only [Set.univ_inter] at hm
    rw [walkFrom, hm]
    have hconst : (fun X : ℕ → WalkState => path (stepKernel l ω) (X t) A) =
        fun _ => 1 := by
      funext X
      exact path_one_step (stepKernel l ω) ω (stepKernel_stepRel l ω) (X t)
    rw [hconst]
    simp
  rw [ae_all_iff]
  intro t
  have ht : shiftN t ⁻¹' A ∈ MeasureTheory.ae (walkFrom ω l x) :=
    (mem_ae_iff_prob_eq_one (hA.preimage (measurable_shiftN t))).2 (hone t)
  filter_upwards [ht] with X hX
  simpa [A, shiftN, Nat.add_comm] using hX


private lemma physical_generation_length (ω : List ℕ → ℕ) :
    ∀ (j : ℕ) (v w : List ℕ), w ∈ generation ω v j → w.length = v.length + j := by
  intro j
  induction j with
  | zero =>
      intro v w hw
      simp only [generation, Finset.mem_singleton] at hw
      simp [hw]
  | succ j ih =>
      intro v w hw
      rw [generation] at hw
      rcases Finset.mem_biUnion.mp hw with ⟨i, _, hw⟩
      rw [ih _ _ hw]
      simp [offChild]
      omega

private lemma physical_child_generation (ω : List ℕ → ℕ) :
    ∀ (j : ℕ) (v w : List ℕ), w ∈ generation ω v j →
      ∀ i : Fin (ω w), offChild ω w i ∈ generation ω v (j + 1) := by
  intro j
  induction j with
  | zero =>
      intro v w hw i
      simp only [generation, Finset.mem_singleton] at hw
      subst w
      rw [generation]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [generation]⟩
  | succ j ih =>
      intro v w hw i
      rw [generation] at hw ⊢
      rcases Finset.mem_biUnion.mp hw with ⟨a, _, hw⟩
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, ih _ _ hw i⟩

private lemma physical_parent_generation (ω : List ℕ → ℕ) :
    ∀ (j : ℕ) (v w : List ℕ), w ∈ generation ω v (j + 1) →
      ∃ u ∈ generation ω v j, parentState w = .vtx u := by
  intro j
  induction j with
  | zero =>
      intro v w hw
      rw [generation] at hw
      rcases Finset.mem_biUnion.mp hw with ⟨i, _, hw⟩
      simp only [generation, Finset.mem_singleton] at hw
      subst w
      refine ⟨v, by simp [generation], ?_⟩
      simp [parentState, offChild]
  | succ j ih =>
      intro v w hw
      rw [generation] at hw
      rcases Finset.mem_biUnion.mp hw with ⟨i, _, hw⟩
      rcases ih _ _ hw with ⟨u, hu, hp⟩
      refine ⟨u, ?_, hp⟩
      rw [generation]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hu⟩

private lemma physical_mem_ball {ω : List ℕ → ℕ} {v w : List ℕ}
    {j N : ℕ} (hj : j < N) (hw : w ∈ generation ω v j) :
    .vtx w ∈ ball ω v N := by
  classical
  simp only [ball, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  exact ⟨j, hj, w, hw, rfl⟩

private lemma physical_of_mem_ball {ω : List ℕ → ℕ} {v w : List ℕ} {N : ℕ}
    (hw : .vtx w ∈ ball ω v N) : ∃ j < N, w ∈ generation ω v j := by
  classical
  simp only [ball, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at hw
  rcases hw with ⟨j, hj, w', hw', heq⟩
  cases heq
  exact ⟨j, hj, hw'⟩

private lemma physical_step_mem_ball {ω : List ℕ → ℕ} {v w : List ℕ} {N : ℕ}
    (hw : .vtx w ∈ ball ω v N) {y : WalkState} (hstep : StepRel ω (.vtx w) y)
    (hp : y ≠ parentState v) (hlevel : height y ≠ v.length + N) :
    y ∈ ball ω v N := by
  rcases physical_of_mem_ball hw with ⟨j, hj, hw⟩
  rcases hstep with hparent | ⟨i, hi⟩
  · subst y
    cases j with
    | zero =>
        simp only [generation, Finset.mem_singleton] at hw
        subst w
        exact False.elim (hp rfl)
    | succ j =>
        rcases physical_parent_generation ω j v w hw with ⟨u, hu, heq⟩
        rw [heq]
        exact physical_mem_ball (by omega) hu
  · subst y
    have hgen : offChild ω w i ∈ generation ω v (j + 1) :=
      physical_child_generation ω j v w hw i
    have hlen : (offChild ω w i).length = v.length + (j + 1) :=
      physical_generation_length ω (j + 1) v _ hgen
    have hj' : j + 1 < N := by
      by_contra hn
      apply hlevel
      simp only [height]
      rw [hlen]
      norm_cast
      omega
    exact physical_mem_ball hj' hgen

/-- A valid path which never visits the base parent and never records the
`reachLevelBefore` event remains in the corresponding finite ball. -/
lemma physical_mem_ball_of_not_reach {ω : List ℕ → ℕ} {v : List ℕ} {N : ℕ}
    {X : ℕ → WalkState} (h0 : X 0 = .vtx v)
    (hstep : ∀ t, StepRel ω (X t) (X (t + 1)))
    (hp : ∀ t, X t ≠ parentState v) (hr : X ∉ reachLevelBefore v N) :
    ∀ t, X t ∈ ball ω v N := by
  have hlevel (t : ℕ) : height (X t) ≠ v.length + N := by
    intro ht
    exact hr ⟨t, ht, fun s _ => hp s⟩
  intro t
  induction t with
  | zero =>
      rw [h0]
      apply physical_mem_ball (j := 0) (by
        by_contra hN
        have : N = 0 := Nat.eq_zero_of_not_pos hN
        apply hlevel 0
        simp [h0, height, this])
      simp [generation]
  | succ t ih =>
      rcases ih with ih
      cases hXt : X t with
      | rootParent =>
          rw [hXt] at ih
          simp [ball] at ih
      | vtx w =>
          rw [hXt] at ih
          exact physical_step_mem_ball ih (by simpa [hXt] using hstep t)
            (hp (t + 1)) (hlevel (t + 1))


/-- First hit of `v` which occurs before height `L`, with no earlier hit of `v`. -/
noncomputable def returnTime (v : List ℕ) (L : ℤ) (X : ℕ → WalkState) : ℕ∞ := by
  classical
  exact if h : ∃ t, X t = .vtx v ∧ ∀ s < t, X s ≠ .vtx v ∧ height (X s) ≠ L then
    Nat.find h else ⊤

private lemma returnTime_eq_nat (v : List ℕ) (L : ℤ) (X : ℕ → WalkState) (t : ℕ) :
    returnTime v L X = t ↔
      X t = .vtx v ∧ ∀ s < t, X s ≠ .vtx v ∧ height (X s) ≠ L := by
  classical
  constructor
  · intro ht
    by_cases h : ∃ t, X t = .vtx v ∧ ∀ s < t, X s ≠ .vtx v ∧ height (X s) ≠ L
    · rw [returnTime, dif_pos h] at ht
      have heq : Nat.find h = t := by exact_mod_cast ht
      simpa only [heq] using Nat.find_spec h
    · simp [returnTime, h] at ht
  · intro ht
    have h : ∃ t, X t = .vtx v ∧ ∀ s < t, X s ≠ .vtx v ∧ height (X s) ≠ L := ⟨t, ht⟩
    rw [returnTime, dif_pos h]
    have hspec := Nat.find_spec h
    have hle : Nat.find h ≤ t := Nat.find_le ht
    have hge : t ≤ Nat.find h := by
      by_contra hn
      exact (ht.2 (Nat.find h) (by omega)).1 hspec.1
    exact_mod_cast Nat.le_antisymm hle hge

private lemma measurableSet_returnTime (v : List ℕ) (L : ℤ) (t : ℕ) :
    MeasurableSet[piLE t] {X | returnTime v L X = t} := by
  rw [piLE_eq_comap_frestrictLe]
  let zt : (Π _ : Finset.Iic t, WalkState) → WalkState := fun z => z ⟨t, Finset.mem_Iic.mpr le_rfl⟩
  let zs : ℕ → (Π _ : Finset.Iic t, WalkState) → WalkState := fun s z =>
    z ⟨min s t, Finset.mem_Iic.mpr (min_le_right _ _)⟩
  let C : Set (Π _ : Finset.Iic t, WalkState) :=
    {z | zt z = .vtx v} ∩ ⋂ s, {z | s < t → zs s z ≠ .vtx v ∧ height (zs s z) ≠ L}
  refine ⟨C, ?_, ?_⟩
  · apply MeasurableSet.inter
    · exact (MeasurableSet.singleton _).preimage (measurable_pi_apply _)
    · apply MeasurableSet.iInter
      intro s
      by_cases hs : s < t
      · simp only [hs, forall_true_left]
        exact (((MeasurableSet.singleton _).preimage (measurable_pi_apply _)).compl).inter
          (measurableSet_eq_fun ((measurable_of_countable height).comp
            (measurable_pi_apply _ : Measurable (zs s))) measurable_const).compl
      · simp [hs]
  · ext X
    change Preorder.frestrictLe t X ∈ C ↔ returnTime v L X = t
    rw [returnTime_eq_nat]
    simp only [C, zt, zs, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨ht, hbefore⟩
      refine ⟨ht, fun s => ?_⟩
      intro hs
      have hmin : min s t = s := Nat.min_eq_left (Nat.le_of_lt hs)
      simpa [hmin] using hbefore s hs
    · rintro ⟨ht, hbefore⟩
      refine ⟨ht, fun s hs => ?_⟩
      have hmin : min s t = s := Nat.min_eq_left (Nat.le_of_lt hs)
      simpa [hmin] using hbefore s hs

private lemma physical_mem_ball_until {ω : List ℕ → ℕ} {v : List ℕ} {N : ℕ}
    {X : ℕ → WalkState} (h0 : X 0 ∈ ball ω v N)
    (hstep : ∀ t, StepRel ω (X t) (X (t + 1))) (T : ℕ)
    (hp : ∀ t ≤ T, X t ≠ parentState v)
    (hlevel : ∀ t ≤ T, height (X t) ≠ v.length + N) :
    ∀ t ≤ T, X t ∈ ball ω v N := by
  intro t ht
  induction t with
  | zero => exact h0
  | succ t ih =>
      have ht' : t ≤ T := by omega
      have hmem := ih ht'
      cases hXt : X t with
      | rootParent =>
          rw [hXt] at hmem
          simp [ball] at hmem
      | vtx w =>
          rw [hXt] at hmem
          exact physical_step_mem_ball hmem (by simpa [hXt] using hstep t)
            (hp (t + 1) ht) (hlevel (t + 1) ht)

private lemma physical_parent_not_mem_ball (ω : List ℕ → ℕ) (v : List ℕ) (N : ℕ) :
    parentState v ∉ ball ω v N := by
  classical
  by_cases hv : v = []
  · subst v
    simp [ball, parentState]
  · intro hp
    simp only [parentState, hv, ↓reduceIte] at hp
    rcases physical_of_mem_ball hp with ⟨j, hj, hw⟩
    have hlen := physical_generation_length ω j v v.dropLast hw
    have hpos : 0 < v.length := List.length_pos_of_ne_nil hv
    simp only [List.length_dropLast] at hlen
    omega

private lemma physical_base_of_step_to_parent {ω : List ℕ → ℕ} {v w : List ℕ}
    {N : ℕ} (hw : .vtx w ∈ ball ω v N) {y : WalkState}
    (hstep : StepRel ω (.vtx w) y) (hlevel : height y ≠ v.length + N)
    (hy : y = parentState v) : w = v := by
  rcases physical_of_mem_ball hw with ⟨j, hj, hw⟩
  rcases hstep with hparent | ⟨i, hi⟩
  · cases j with
    | zero =>
        simpa only [generation, Finset.mem_singleton] using hw
    | succ j =>
        exfalso
        rcases physical_parent_generation ω j v w hw with ⟨u, hu, heq⟩
        have hmem : y ∈ ball ω v N := by
          rw [hparent, heq]
          exact physical_mem_ball (by omega) hu
        rw [hy] at hmem
        exact physical_parent_not_mem_ball ω v N hmem
  · exfalso
    have hgen : offChild ω w i ∈ generation ω v (j + 1) :=
      physical_child_generation ω j v w hw i
    have hlen : (offChild ω w i).length = v.length + (j + 1) :=
      physical_generation_length ω (j + 1) v _ hgen
    have hj' : j + 1 < N := by
      by_contra hn
      apply hlevel
      simp only [hi, height]
      rw [hlen]
      norm_cast
      omega
    have hmem : y ∈ ball ω v N := by
      rw [hi]
      exact physical_mem_ball hj' hgen
    rw [hy] at hmem
    exact physical_parent_not_mem_ball ω v N hmem

private lemma no_parent_of_descendant {ω : List ℕ → ℕ} {v : List ℕ} {N : ℕ}
    {X : ℕ → WalkState} (i : Fin (ω v)) (hN : 0 < N)
    (h0 : X 0 = .vtx (offChild ω v i))
    (hstep : ∀ t, StepRel ω (X t) (X (t + 1))) (T : ℕ)
    (hnoV : ∀ s < T, X s ≠ .vtx v)
    (hnoLevel : ∀ s < T, height (X s) ≠ (offChild ω v i).length + N) :
    ∀ s < T, X s ≠ parentState v := by
  classical
  have h0mem : X 0 ∈ ball ω v (N + 1) := by
    rw [h0]
    apply physical_mem_ball (j := 1) (by omega)
    rw [generation]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [generation]⟩
  intro s hs
  suffices hall : ∀ q ≤ s, X q ≠ parentState v by exact hall s le_rfl
  induction s with
  | zero =>
      intro q hq
      have hq0 : q = 0 := by omega
      subst q
      intro hp
      have hmem := h0mem
      have hp' : .vtx (offChild ω v i) = parentState v := h0.symm.trans hp
      rw [h0] at hmem
      rw [hp'] at hmem
      exact physical_parent_not_mem_ball ω v (N + 1) hmem
  | succ s ih =>
      intro q hq
      by_cases hqs : q = s + 1
      · subst q
        have hsprev : ∀ q ≤ s, X q ≠ parentState v := ih (by omega)
        have hlevel : ∀ q ≤ s, height (X q) ≠ v.length + (N + 1) := by
          intro q hq
          have hne := hnoLevel q (by omega)
          simpa [offChild, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hne
        have hmem := physical_mem_ball_until h0mem hstep s hsprev hlevel s le_rfl
        intro hp
        cases hXt : X s with
        | rootParent =>
            rw [hXt] at hmem
            simp [ball] at hmem
        | vtx w =>
            rw [hXt] at hmem
            have hw : w = v := physical_base_of_step_to_parent hmem
              (by simpa [hXt] using hstep s) (by
                intro heq
                have hne := hnoLevel (s + 1) hs
                apply hne
                simpa [offChild, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc,
                  hXt] using heq) (by simpa [hXt] using hp)
            apply hnoV s (by omega)
            rw [hXt, hw]
      · exact ih (by omega) q (by omega)

private lemma no_parent_before_return {ω : List ℕ → ℕ} {v : List ℕ} {N : ℕ}
    {X : ℕ → WalkState} (i : Fin (ω v)) (hN : 0 < N)
    (h0 : X 0 = .vtx (offChild ω v i))
    (hstep : ∀ t, StepRel ω (X t) (X (t + 1)))
    {r : ℕ} (hr : returnTime v ((offChild ω v i).length + N) X = r) :
    ∀ s < r, X s ≠ parentState v := by
  have hret := (returnTime_eq_nat v ((offChild ω v i).length + N) X r).mp hr
  exact no_parent_of_descendant i hN h0 hstep r (fun s hs => (hret.2 s hs).1)
    (fun s hs => (hret.2 s hs).2)

private lemma height_parentState (v : List ℕ) : height (parentState v) = v.length - 1 := by
  by_cases hv : v = []
  · simp [hv, parentState, height]
  · simp only [parentState, hv, ↓reduceIte, height, List.length_dropLast]
    have hlen : 0 < v.length := List.length_pos_of_ne_nil hv
    rw [Nat.cast_sub hlen]
    simp

/-- Restart after a return which precedes the boundary. -/
def returnRestart (v : List ℕ) (L : ℤ) (A : Set (ℕ → WalkState)) :
    Set (ℕ → WalkState) :=
  {X | ∃ t : ℕ, returnTime v L X = t ∧ shiftN t X ∈ A}

private lemma measurableSet_returnRestart (v : List ℕ) (L : ℤ)
    {A : Set (ℕ → WalkState)} (hA : MeasurableSet A) :
    MeasurableSet (returnRestart v L A) := by
  rw [returnRestart]
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro t
  exact ((Filtration.piLE.le t) _ (measurableSet_returnTime v L t)).inter
    (hA.preimage (measurable_shiftN t))

private lemma reach_eq_direct_union_restart {ω : List ℕ → ℕ} {v : List ℕ} {N : ℕ}
    (i : Fin (ω v)) (hN : 0 < N) {X : ℕ → WalkState}
    (h0 : X 0 = .vtx (offChild ω v i))
    (hstep : ∀ t, StepRel ω (X t) (X (t + 1))) :
    X ∈ reachLevelBefore v (N + 1) ↔
      X ∈ reachLevelBefore (offChild ω v i) N ∪
        returnRestart v ((offChild ω v i).length + N) (reachLevelBefore v (N + 1)) := by
  classical
  let c := offChild ω v i
  have hcheight : (c.length : ℤ) + N = v.length + (N + 1) := by
    simp [c, offChild]
    ring
  constructor
  · rintro ⟨T, hT, hp⟩
    by_cases hd : X ∈ reachLevelBefore c N
    · exact Or.inl hd
    · right
      have hex : ∃ t ≤ T, X t = .vtx v := by
        by_contra hn
        apply hd
        refine ⟨T, ?_, ?_⟩
        · rwa [hcheight]
        · intro s hs
          by_contra hsv
          exact hn ⟨s, hs, by simpa [c] using hsv⟩
      let r := Nat.find hex
      have hr := Nat.find_spec hex
      have hmin (s : ℕ) (hs : s < r) : X s ≠ .vtx v := by
        intro hsv
        exact Nat.find_min hex hs ⟨Nat.le_trans (Nat.le_of_lt hs) hr.1, hsv⟩
      have hrret : returnTime v (c.length + N) X = r := by
        apply (returnTime_eq_nat v (c.length + N) X r).2
        refine ⟨hr.2, fun s hs => ⟨hmin s hs, ?_⟩⟩
        intro hlevel
        apply hd
        refine ⟨s, hlevel, fun q hq => by simpa [c] using hmin q (by omega)⟩
      refine ⟨r, hrret, T - r, ?_, ?_⟩
      · change height (X (T - r + r)) = v.length + (N + 1)
        rw [Nat.sub_add_cancel hr.1]
        exact hT
      · intro s hs
        change X (s + r) ≠ parentState v
        exact hp (s + r) (by omega)
  · intro h
    rcases h with hd | ⟨r, hr, u, hu, hp⟩
    · let hex : ∃ t, height (X t) = c.length + N ∧ ∀ s ≤ t, X s ≠ .vtx v := by
        simpa only [reachLevelBefore, c, parentState_offChild, Set.mem_setOf_eq] using hd
      let t := Nat.find hex
      have ht := Nat.find_spec hex
      have hmin (s : ℕ) (hs : s < t) : height (X s) ≠ c.length + N := by
        intro hlevel
        exact Nat.find_min hex hs ⟨hlevel, fun q _ => ht.2 q (by omega)⟩
      have hnp := no_parent_of_descendant i hN h0 hstep t
        (fun s hs => ht.2 s (by omega)) hmin
      refine ⟨t, ?_, ?_⟩
      · rw [Nat.cast_add, Nat.cast_one]
        exact ht.1.trans hcheight
      · intro s hs
        by_cases hst : s = t
        · subst s
          intro hparent
          have h1 := ht.1
          rw [hparent, height_parentState] at h1
          have hc : c.length = v.length + 1 := by simp [c, offChild]
          rw [hc] at h1
          simp only [Nat.cast_add, Nat.cast_one] at h1
          omega
        · exact hnp s (by omega)
    · have hret := (returnTime_eq_nat v (c.length + N) X r).mp hr
      have hnp := no_parent_before_return i hN h0 hstep hr
      refine ⟨u + r, ?_, ?_⟩
      · change height (X (u + r)) = v.length + (N + 1)
        exact hu
      · intro s hs
        by_cases hsr : s < r
        · exact hnp s hsr
        · have htail := hp (s - r) (by omega)
          change X (s - r + r) ≠ parentState v at htail
          rwa [Nat.sub_add_cancel (by omega : r ≤ s)] at htail

private lemma returnTime_finite_ae {l : ℝ≥0} (hl : 0 < l) (ω : List ℕ → ℕ)
    (c : List ℕ) (N : ℕ) (v : List ℕ) (hc : parentState c = .vtx v) :
    ∀ᵐ X ∂walkFrom ω l (.vtx c),
      X ∉ reachLevelBefore c N → returnTime v (c.length + N) X ≠ ⊤ := by
  classical
  have hnull := measure_eq_zero_iff_ae_notMem.mp
    (walkFrom_stays_in_ball hl ω c N (.vtx c))
  filter_upwards [walkFrom_ae_stepRel l ω (.vtx c), path_zero (stepKernel l ω) (.vtx c),
    hnull] with X hstep h0 hball hr
  intro htop
  apply hball
  apply physical_mem_ball_of_not_reach h0 hstep _ hr
  intro t
  by_contra ht
  have hex : ∃ t, X t = .vtx v := ⟨t, by simpa [hc] using ht⟩
  have hrspec := Nat.find_spec hex
  have hmin (s : ℕ) (hs : s < Nat.find hex) : X s ≠ .vtx v := fun h =>
    Nat.find_min hex hs h
  have hrret : returnTime v (c.length + N) X = Nat.find hex := by
    apply (returnTime_eq_nat v (c.length + N) X (Nat.find hex)).2
    refine ⟨hrspec, fun s hs => ⟨hmin s hs, ?_⟩⟩
    intro hlevel
    exact hr ⟨s, hlevel, fun q hq => by simpa [hc] using hmin q (by omega)⟩
  rw [htop] at hrret
  contradiction


private lemma measurableSet_returnTime_ne_top (v : List ℕ) (L : ℤ) :
    MeasurableSet {X | returnTime v L X ≠ ⊤} := by
  rw [show {X | returnTime v L X ≠ ⊤} = ⋃ t : ℕ, {X | returnTime v L X = t} by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ENat.ne_top_iff_exists.trans (by constructor <;> rintro ⟨t, ht⟩ <;> exact ⟨t, ht.symm⟩)]
  exact MeasurableSet.iUnion fun t => (Filtration.piLE.le t) _ (measurableSet_returnTime v L t)

private lemma measure_returnRestart {l : ℝ≥0} (ω : List ℕ → ℕ) (c v : List ℕ) (N : ℕ) :
    walkFrom ω l (.vtx c)
        (returnRestart v (c.length + N) (reachLevelBefore v (N + 1))) =
      walkFrom ω l (.vtx v) (reachLevelBefore v (N + 1)) *
        walkFrom ω l (.vtx c) {X | returnTime v (c.length + N) X ≠ ⊤} := by
  rw [returnRestart]
  change path (stepKernel l ω) (.vtx c)
    {X | ∃ t : ℕ, returnTime v (c.length + N) X = t ∧
      shiftN t X ∈ reachLevelBefore v (N + 1)} = _
  rw [path_markov_stopping (stepKernel l ω) (.vtx c)
    (measurableSet_returnTime v (c.length + N)) (measurableSet_reachLevelBefore v (N + 1))]
  have hmeas : MeasurableSet {X : ℕ → WalkState | returnTime v (c.length + N) X ≠ ⊤} :=
    measurableSet_returnTime_ne_top v (c.length + N)
  calc
    (∫⁻ X in {X | returnTime v (c.length + N) X ≠ ⊤},
        path (stepKernel l ω) (X (returnTime v (c.length + N) X).toNat)
          (reachLevelBefore v (N + 1)) ∂path (stepKernel l ω) (.vtx c)) =
        ∫⁻ _X in {X | returnTime v (c.length + N) X ≠ ⊤},
          path (stepKernel l ω) (.vtx v) (reachLevelBefore v (N + 1))
          ∂path (stepKernel l ω) (.vtx c) := by
      apply setLIntegral_congr_fun hmeas
      intro X hX
      obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hX
      have hspec := (returnTime_eq_nat v (c.length + N) X t).mp ht.symm
      dsimp only
      rw [ht.symm, ENat.toNat_natCast, hspec.1]
    _ = path (stepKernel l ω) (.vtx v) (reachLevelBefore v (N + 1)) *
        path (stepKernel l ω) (.vtx c) {X | returnTime v (c.length + N) X ≠ ⊤} := by
      rw [setLIntegral_const]

private lemma measure_returnTime_ne_top {l : ℝ≥0} (hl : 0 < l) (ω : List ℕ → ℕ)
    (v : List ℕ) (N : ℕ) (i : Fin (ω v)) :
    walkFrom ω l (.vtx (offChild ω v i))
        {X | returnTime v ((offChild ω v i).length + N) X ≠ ⊤} =
      1 - walkFrom ω l (.vtx (offChild ω v i)) (reachLevelBefore (offChild ω v i) N) := by
  let c := offChild ω v i
  have heq : {X : ℕ → WalkState | returnTime v (c.length + N) X ≠ ⊤} =ᵐ[walkFrom ω l (.vtx c)]
      (reachLevelBefore c N)ᶜ := by
    filter_upwards [returnTime_finite_ae hl ω c N v (by simp [c])] with X hX
    apply propext
    constructor
    · intro hfinite hd
      obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfinite
      have hret := (returnTime_eq_nat v (c.length + N) X t).mp ht.symm
      rcases hd with ⟨u, hu, hp⟩
      by_cases hur : u < t
      · exact (hret.2 u hur).2 hu
      · exact hp t (by omega) (by simpa [c] using hret.1)
    · intro hd
      exact hX hd
  rw [measure_congr heq, prob_compl_eq_one_sub (measurableSet_reachLevelBefore c N)]

private lemma direct_disjoint_restart {ω : List ℕ → ℕ} (v : List ℕ) (N : ℕ) (i : Fin (ω v)) :
    Disjoint (reachLevelBefore (offChild ω v i) N)
      (returnRestart v ((offChild ω v i).length + N) (reachLevelBefore v (N + 1))) := by
  rw [Set.disjoint_left]
  intro X hd ⟨r, hr, htail⟩
  have hret := (returnTime_eq_nat v ((offChild ω v i).length + N) X r).mp hr
  rcases hd with ⟨t, ht, hp⟩
  by_cases htr : t < r
  · exact (hret.2 t htr).2 ht
  · exact hp r (by omega) (by simpa using hret.1)

private lemma walkFrom_child_reach {l : ℝ≥0} (hl : 0 < l) (ω : List ℕ → ℕ)
    (v : List ℕ) {N : ℕ} (hN : 0 < N) (i : Fin (ω v)) :
    walkFrom ω l (.vtx (offChild ω v i)) (reachLevelBefore v (N + 1)) =
      walkFrom ω l (.vtx (offChild ω v i)) (reachLevelBefore (offChild ω v i) N) +
        (1 - walkFrom ω l (.vtx (offChild ω v i))
          (reachLevelBefore (offChild ω v i) N)) *
        walkFrom ω l (.vtx v) (reachLevelBefore v (N + 1)) := by
  let c := offChild ω v i
  have heq : reachLevelBefore v (N + 1) =ᵐ[walkFrom ω l (.vtx c)]
      reachLevelBefore c N ∪ returnRestart v (c.length + N) (reachLevelBefore v (N + 1)) := by
    filter_upwards [walkFrom_ae_stepRel l ω (.vtx c), path_zero (stepKernel l ω) (.vtx c)] with X hstep h0
    apply propext
    simpa only [c] using reach_eq_direct_union_restart i hN h0 hstep
  rw [measure_congr heq, measure_union (direct_disjoint_restart v N i)
    (measurableSet_returnRestart v (c.length + N) (measurableSet_reachLevelBefore v (N + 1)))]
  rw [measure_returnRestart, measure_returnTime_ne_top hl]
  ac_rfl

private lemma walkFrom_child_reach_zero (l : ℝ≥0) (ω : List ℕ → ℕ)
    (v : List ℕ) (i : Fin (ω v)) :
    walkFrom ω l (.vtx (offChild ω v i)) (reachLevelBefore v (0 + 1)) = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_reachLevelBefore v (0 + 1))).mp
  filter_upwards [path_zero (stepKernel l ω) (.vtx (offChild ω v i))] with X h0
  refine ⟨0, ?_, ?_⟩
  · rw [h0]
    simp [height, offChild]
  · intro s hs
    have hs0 : s = 0 := by omega
    subst s
    rw [h0]
    intro hp
    have hh := congrArg height hp
    rw [height_parentState] at hh
    simp only [height, offChild, List.length_append, List.length_singleton,
      Nat.cast_add, Nat.cast_one] at hh
    omega


private lemma vtx_ne_parentState (v : List ℕ) : (.vtx v : WalkState) ≠ parentState v := by
  intro hp
  have hh := congrArg height hp
  rw [height_parentState] at hh
  simp only [height] at hh
  by_cases hv : v.length = 0
  · rw [hv] at hh
    norm_num at hh
  · have hvpos : 0 < v.length := by omega
    omega

private lemma pcons_reach_preimage (v : List ℕ) (N : ℕ) (X : ℕ → WalkState) :
    pcons (.vtx v) X ∈ reachLevelBefore v (N + 1) ↔ X ∈ reachLevelBefore v (N + 1) := by
  constructor
  · rintro ⟨t, ht, hp⟩
    cases t with
    | zero =>
        simp [pcons, height] at ht
        omega
    | succ t =>
        refine ⟨t, by simpa [pcons] using ht, ?_⟩
        intro s hs
        have h := hp (s + 1) (by omega)
        simpa [pcons] using h
  · rintro ⟨t, ht, hp⟩
    refine ⟨t + 1, by simpa [pcons] using ht, ?_⟩
    intro s hs
    cases s with
    | zero => exact vtx_ne_parentState v
    | succ s =>
        have h := hp s (by omega)
        simpa [pcons] using h

private lemma walkFrom_parent_reach_zero (l : ℝ≥0) (ω : List ℕ → ℕ)
    (v : List ℕ) (N : ℕ) :
    walkFrom ω l (parentState v) (reachLevelBefore v (N + 1)) = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [path_zero (stepKernel l ω) (parentState v)] with X h0
  rintro ⟨t, ht, hp⟩
  exact hp 0 (Nat.zero_le t) h0

private lemma walkFrom_firstStep_succ (l : ℝ≥0) (ω : List ℕ → ℕ)
    (v : List ℕ) (N : ℕ) :
    walkFrom ω l (.vtx v) (reachLevelBefore v (N + 1)) =
      ∑ i : Fin (ω v), ((1 / (l + ω v) : ℝ≥0) : ℝ≥0∞) *
        walkFrom ω l (.vtx (offChild ω v i)) (reachLevelBefore v (N + 1)) := by
  have hpre : pcons (.vtx v) ⁻¹' reachLevelBefore v (N + 1) =
        reachLevelBefore v (N + 1) := by
    ext X
    exact pcons_reach_preimage v N X
  rw [walkFrom, path_apply_firstStep (stepKernel l ω) (.vtx v)
    (measurableSet_reachLevelBefore v (N + 1))]
  simp_rw [hpre]
  change (∫⁻ y, walkFrom ω l y (reachLevelBefore v (N + 1))
    ∂stepMeasure l ω (.vtx v)) = _
  by_cases h : l = 0 ∧ ω v = 0
  · simp [stepMeasure, h, walkFrom_parent_reach_zero]
  · simp only [stepMeasure, h, ↓reduceIte]
    rw [lintegral_add_measure]
    have hpzero : ∫⁻ y, walkFrom ω l y (reachLevelBefore v (N + 1))
        ∂(((l / (l + ω v) : ℝ≥0) : ℝ≥0∞) • Measure.dirac (parentState v)) = 0 := by
      rw [lintegral_smul_measure, lintegral_dirac, walkFrom_parent_reach_zero]
      simp
    rw [hpzero, zero_add]
    simp_rw [lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac]
    · simp only [smul_eq_mul, walkFrom, offChild]


lemma physical_escapeN_nonneg (ω : List ℕ → ℕ) {l : ℝ} (hl : 0 < l) :
    ∀ (N : ℕ) (v : List ℕ), 0 ≤ escapeN ω l N v := by
  intro N
  induction N with
  | zero => intro v; simp [escapeN]
  | succ N ih =>
      intro v
      rw [escapeN]
      have hS : 0 ≤ ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i) :=
        Finset.sum_nonneg fun i _ => ih _
      exact div_nonneg hS (by positivity)

/-- Physical finite escape, `lem:escape` (i), for every raw field. -/
theorem walkFrom_reachLevelBefore {l : ℝ≥0} (hl : 0 < (l : ℝ))
    (ω : List ℕ → ℕ) (N : ℕ) (v : List ℕ) :
    walkFrom ω l (.vtx v) (reachLevelBefore v N) = ENNReal.ofReal (escapeN ω l N v) := by
  have hlNN : 0 < l := by exact_mod_cast hl
  induction N generalizing v with
  | zero =>
      rw [show ENNReal.ofReal (escapeN ω l 0 v) = 1 by simp [escapeN]]
      apply (mem_ae_iff_prob_eq_one (measurableSet_reachLevelBefore v 0)).mp
      filter_upwards [path_zero (stepKernel l ω) (.vtx v)] with X h0
      refine ⟨0, by simp [h0, height], ?_⟩
      intro s hs
      have hs0 : s = 0 := by omega
      subst s
      simpa [h0] using vtx_ne_parentState v
  | succ N ih =>
      let p : ℝ≥0∞ := walkFrom ω l (.vtx v) (reachLevelBefore v (N + 1))
      let β : Fin (ω v) → ℝ := fun i => escapeN ω l N (offChild ω v i)
      let b : Fin (ω v) → ℝ≥0∞ := fun i => ENNReal.ofReal (β i)
      let a : ℝ≥0∞ := ((1 / (l + ω v) : ℝ≥0) : ℝ≥0∞)
      have hp1 : p ≤ 1 := prob_le_one
      have hb (i : Fin (ω v)) : b i = walkFrom ω l (.vtx (offChild ω v i))
          (reachLevelBefore (offChild ω v i) N) := (ih (offChild ω v i)).symm
      have hb1 (i : Fin (ω v)) : b i ≤ 1 := by rw [hb i]; exact prob_le_one
      have hchild (i : Fin (ω v)) :
          walkFrom ω l (.vtx (offChild ω v i)) (reachLevelBefore v (N + 1)) =
            b i + (1 - b i) * p := by
        cases N with
        | zero =>
            rw [walkFrom_child_reach_zero]
            simp [b, β, escapeN]
        | succ N =>
            rw [walkFrom_child_reach hlNN ω v (Nat.succ_pos N) i, ← hb i]
      have hfirst : p = ∑ i : Fin (ω v), a *
          (b i + (1 - b i) * p) := by
        change walkFrom ω l (.vtx v) (reachLevelBefore v (N + 1)) = _
        rw [walkFrom_firstStep_succ]
        apply Finset.sum_congr rfl
        intro i _
        rw [hchild i]
      have hreal : p.toReal = ∑ i : Fin (ω v), a.toReal *
          (β i + (1 - β i) * p.toReal) := by
        conv_lhs => rw [hfirst]
        rw [ENNReal.toReal_sum (by finiteness)]
        apply Finset.sum_congr rfl
        intro i _
        rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
          ENNReal.toReal_mul, ENNReal.toReal_sub_of_le (hb1 i) ENNReal.one_ne_top,
          ENNReal.toReal_one]
        rw [show (b i).toReal = β i from
          (ENNReal.toReal_ofReal (physical_escapeN_nonneg ω hl N _))]
      let S : ℝ := ∑ i : Fin (ω v), β i
      let L : ℝ := l
      let k : ℝ := ω v
      have hweight : a.toReal = 1 / (L + k) := by simp [a, L, k]
      have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => physical_escapeN_nonneg ω hl N _
      have hlinear : p.toReal = (1 / (L + k)) * (S + (k - S) * p.toReal) := by
        calc
          p.toReal = ∑ i : Fin (ω v), a.toReal * (β i + (1 - β i) * p.toReal) := hreal
          _ = a.toReal * ∑ i : Fin (ω v), (β i + (1 - β i) * p.toReal) := by
            rw [Finset.mul_sum]
          _ = (1 / (L + k)) * (S + (k - S) * p.toReal) := by
            rw [hweight]
            congr 1
            dsimp [S, k]
            simp only [one_mul, sub_mul, Finset.sum_add_distrib,
              Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hLk : 0 < L + k := by
        dsimp [L, k]
        positivity
      have hLS : 0 < L + S := add_pos_of_pos_of_nonneg (by exact hl) hS
      have hsolution : p.toReal = S / (L + S) := by
        apply (eq_div_iff hLS.ne').2
        field_simp [hLk.ne'] at hlinear
        linear_combination hlinear
      change p = ENNReal.ofReal (escapeN ω l (N + 1) v)
      rw [escapeN]
      change p = ENNReal.ofReal (S / (L + S))
      rw [← hsolution]
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

end LPPMonotonicityProof.Speed
