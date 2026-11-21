module

public import LPPMonotonicityProof.Speed.Walk.Hitting
public import LPPMonotonicityProof.Escape.FiniteFlow
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Uniform exit from a finite ball

A walk confined to finitely many generations has a uniformly positive chance to
hit the parent within a bounded number of steps (proof of Lemma 2.1(ii),
`lem:escape`), so it leaves every finite ball almost surely.
The only probabilistic input is the fixed-time Markov
property.  No finite or infinite physical escape formula is assumed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState

section GenericExit

variable {S : Type*} [MeasurableSpace S]

/-- In a measurable singleton class, every set is measurable here only when
that fact is supplied separately; these events depend on finitely/countably
many coordinates of the path. -/
private def stayUntil (F : Set S) (t : ℕ) : Set (ℕ → S) := {X | ∀ s ≤ t, X s ∈ F}

private def hitWithin (z : S) (t : ℕ) : Set (ℕ → S) := {X | ∃ s ≤ t, X s = z}

private lemma measurableSet_stayUntil {F : Set S} (hF : MeasurableSet F) (t : ℕ) :
    MeasurableSet (stayUntil F t) := by
  rw [stayUntil]
  rw [show {X : ℕ → S | ∀ s ≤ t, X s ∈ F} =
      ⋂ s, {X : ℕ → S | s ≤ t → X s ∈ F} by ext X; simp]
  apply MeasurableSet.iInter
  intro s
  by_cases hs : s ≤ t
  · simp only [hs, forall_true_left]
    have hm : Measurable (fun X : ℕ → S => X s) := measurable_pi_apply s
    convert hF.preimage hm using 1
    ext X
    rfl
  · simp [hs]

private def prefixStay (F : Set S) (t : ℕ) : Set (Π _ : Finset.Iic t, S) :=
  {z | ∀ i, z i ∈ F}

private lemma measurableSet_prefixStay {F : Set S} (hF : MeasurableSet F) (t : ℕ) :
    MeasurableSet (prefixStay F t) := by
  rw [prefixStay]
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => hF.preimage (measurable_pi_apply i)

private lemma measurableSet_stayUntil_piLE {F : Set S} (hF : MeasurableSet F) (t : ℕ) :
    MeasurableSet[Filtration.piLE t] (stayUntil F t) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  refine ⟨prefixStay F t, measurableSet_prefixStay hF t, ?_⟩
  ext X
  change (∀ i : Finset.Iic t, X i.1 ∈ F) ↔ ∀ s ≤ t, X s ∈ F
  constructor
  · intro h s hs
    exact h ⟨s, Finset.mem_Iic.mpr hs⟩
  · intro h i
    exact h i.1 (Finset.mem_Iic.mp i.2)

private lemma measurableSet_hitWithin [MeasurableSingletonClass S] (z : S) (t : ℕ) :
    MeasurableSet (hitWithin z t) := by
  rw [hitWithin]
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro s
  rw [show {X : ℕ → S | s ≤ t ∧ X s = z} =
      if s ≤ t then {X : ℕ → S | X s = z} else Set.univᶜ by ext X; split_ifs <;> simp_all]
  split_ifs with hs
  · have hm : Measurable (fun X : ℕ → S => X s) := measurable_pi_apply s
    convert (MeasurableSet.singleton z).preimage hm using 1
    ext X
    simp
  · exact MeasurableSet.univ.compl

omit [MeasurableSpace S] in
private lemma stayUntil_add (F : Set S) (t d : ℕ) :
    stayUntil F (t + d) = stayUntil F t ∩ shiftN t ⁻¹' stayUntil F d := by
  ext X
  constructor
  · intro h
    constructor
    · intro s hs
      exact h s (hs.trans (Nat.le_add_right t d))
    · intro s hs
      exact h (s + t) (by omega)
  · rintro ⟨ht, hd⟩ s hs
    by_cases hst : s ≤ t
    · exact ht s hst
    · let k := s - t
      have hks : k + t = s := by dsimp [k]; omega
      have hkd : k ≤ d := by dsimp [k]; omega
      have h := hd k hkd
      change X (k + t) ∈ F at h
      rwa [hks] at h

private theorem path_stayUntil_le (K : Kernel S S) [IsMarkovKernel K]
    {F : Set S} (hF : MeasurableSet F) (d : ℕ) (q : ℝ≥0∞)
    (hq : ∀ y ∈ F, path K y (stayUntil F d) ≤ q) :
    ∀ (n : ℕ) (x : S), path K x (stayUntil F (n * d)) ≤ q ^ n := by
  intro n
  induction n with
  | zero =>
      intro x
      calc
        path K x (stayUntil F (0 * d)) ≤ path K x Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ = q ^ 0 := (pow_zero q).symm
  | succ n ih =>
      intro x
      rw [Nat.succ_mul, stayUntil_add,
        path_markov K (n * d) x (measurableSet_stayUntil_piLE hF (n * d))
          (measurableSet_stayUntil hF d)]
      calc
        (∫⁻ X in stayUntil F (n * d), path K (X (n * d)) (stayUntil F d) ∂path K x) ≤
            ∫⁻ _X in stayUntil F (n * d), q ∂path K x := by
          apply setLIntegral_mono' (measurableSet_stayUntil hF (n * d))
          intro X hX
          exact hq (X (n * d)) (hX (n * d) le_rfl)
        _ = q * path K x (stayUntil F (n * d)) := setLIntegral_const _ _
        _ ≤ q * q ^ n := by gcongr; exact ih x
        _ = q ^ (n + 1) := by rw [pow_succ]; ac_rfl

omit [MeasurableSpace S] in
private lemma pcons_hitWithin_subset (x z : S) (d : ℕ) :
    hitWithin z d ⊆ pcons x ⁻¹' hitWithin z (d + 1) := by
  rintro X ⟨s, hs, hXs⟩
  refine ⟨s + 1, Nat.succ_le_succ hs, ?_⟩
  simpa [pcons] using hXs

private lemma le_path_of_firstStep (K : Kernel S S) [IsMarkovKernel K]
    [MeasurableSingletonClass S] (x y : S) {A B : Set (ℕ → S)}
    (hA : MeasurableSet A) (hsub : B ⊆ pcons x ⁻¹' A) {q : ℝ≥0∞}
    (hq : q ≤ path K y B) : K x {y} * q ≤ path K x A := by
  rw [path_apply_firstStep K x hA]
  calc
    K x {y} * q = ∫⁻ _z in {y}, q ∂K x := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ z in {y}, path K z B ∂K x := by
      apply setLIntegral_mono' (MeasurableSet.singleton y)
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact hq
    _ ≤ ∫⁻ z, path K z B ∂K x := setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ z, path K z (pcons x ⁻¹' A) ∂K x := by
      apply lintegral_mono
      intro z
      exact measure_mono hsub

private lemma hitWithin_zero_mem_ae (K : Kernel S S) [IsMarkovKernel K]
    [MeasurableSingletonClass S] [MeasurableEq S] (z : S) :
    hitWithin z 0 ∈ MeasureTheory.ae (path K z) := by
  filter_upwards [path_zero K z] with X hX
  exact ⟨0, le_rfl, hX⟩

private theorem path_stays_eq_zero (K : Kernel S S) [IsMarkovKernel K]
    {F : Set S} (hF : MeasurableSet F) (d : ℕ) {q : ℝ≥0∞} (hq0 : q < 1)
    (hq : ∀ y ∈ F, path K y (stayUntil F d) ≤ q) (x : S) :
    path K x {X | ∀ t, X t ∈ F} = 0 := by
  apply ENNReal.eq_zero_of_le_mul_pow (ε := 1) hq0
  intro n
  simp only [ENNReal.coe_one, one_mul]
  exact (measure_mono (fun X h s hs => h s) :
    path K x {X | ∀ t, X t ∈ F} ≤ path K x (stayUntil F (n * d))).trans
      (path_stayUntil_le K hF d q hq n x)

end GenericExit

/-- The finite raw-field ball of descendants of `v` at relative depth strictly
below `N`. -/
noncomputable def ball (ω : List ℕ → ℕ) (v : List ℕ) (N : ℕ) : Finset WalkState := by
  classical
  exact (Finset.range N).biUnion fun j => (generation ω v j).image .vtx


section WalkExit

/-- The offspring count read at a walk state. -/
def degreeAt (ω : List ℕ → ℕ) : WalkState → ℕ
  | .rootParent => 0
  | .vtx w => ω w

/-- A common upper bound for all offspring counts in the finite ball. -/
noncomputable def ballDegree (ω : List ℕ → ℕ) (v : List ℕ) (N : ℕ) : ℕ := by
  classical
  exact ∑ x ∈ ball ω v N, degreeAt ω x

/-- The parent probability corresponding to bias `l` and offspring bound `K`. -/
noncomputable def parentRatio (l : ℝ≥0) (K : ℕ) : ℝ≥0∞ :=
  ((l / (l + K) : ℝ≥0) : ℝ≥0∞)

/-- The transition mass assigned to the parent from a vertex. -/
noncomputable def parentProb (l : ℝ≥0) (ω : List ℕ → ℕ) (w : List ℕ) : ℝ≥0∞ :=
  parentRatio l (ω w)

private lemma generation_length (ω : List ℕ → ℕ) :
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

private lemma mem_ball_of_mem_generation {ω : List ℕ → ℕ} {v w : List ℕ}
    {j N : ℕ} (hj : j < N) (hw : w ∈ generation ω v j) :
    .vtx w ∈ ball ω v N := by
  classical
  simp only [ball, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  exact ⟨j, hj, w, hw, rfl⟩

private lemma mem_generation_of_mem_ball {ω : List ℕ → ℕ} {v w : List ℕ} {N : ℕ}
    (hw : .vtx w ∈ ball ω v N) : ∃ j < N, w ∈ generation ω v j := by
  classical
  simp only [ball, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at hw
  rcases hw with ⟨j, hj, w', hw', heq⟩
  cases heq
  exact ⟨j, hj, hw'⟩

private lemma parentState_not_mem_ball (ω : List ℕ → ℕ) (v : List ℕ) (N : ℕ) :
    parentState v ∉ ball ω v N := by
  classical
  by_cases hv : v = []
  · subst v
    simp [ball, parentState]
  · intro hp
    simp only [parentState, hv, ↓reduceIte] at hp
    rcases mem_generation_of_mem_ball hp with ⟨j, hj, hw⟩
    have hlen := generation_length ω j v v.dropLast hw
    have hpos : 0 < v.length := List.length_pos_of_ne_nil hv
    simp only [List.length_dropLast] at hlen
    omega

private lemma degreeAt_le_ballDegree {ω : List ℕ → ℕ} {v w : List ℕ}
    {j N : ℕ} (hj : j < N) (hw : w ∈ generation ω v j) : ω w ≤ ballDegree ω v N := by
  classical
  exact Finset.single_le_sum (fun x _ => Nat.zero_le (degreeAt ω x))
    (mem_ball_of_mem_generation hj hw)

private lemma stepKernel_parent (l : ℝ≥0) (ω : List ℕ → ℕ) (w : List ℕ)
    (hl : 0 < l) : stepKernel l ω (.vtx w) {parentState w} = parentProb l ω w := by
  have hl0 : l ≠ 0 := ne_of_gt hl
  have hchild (i : Fin (ω w)) : vtx (w ++ [i.val + 1]) ∉ ({parentState w} : Set WalkState) := by
    intro hi
    rw [Set.mem_singleton_iff] at hi
    have hw : w ++ [i.val + 1] ∈ generation ω w 1 := by
      simp [generation, offChild]
    have hb := mem_ball_of_mem_generation (j := 1) (N := 2) (show 1 < 2 by omega) hw
    rw [hi] at hb
    exact parentState_not_mem_ball ω w 2 hb
  simp [stepKernel, Kernel.ofFunOfCountable, stepMeasure, hl0, parentProb, parentRatio, hchild]


private lemma generation_parent (ω : List ℕ → ℕ) :
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

private lemma parentRatio_le_parentProb {l : ℝ≥0} (hl : 0 < l) {K : ℕ}
    (ω : List ℕ → ℕ) (w : List ℕ) (hk : ω w ≤ K) :
    parentRatio l K ≤ parentProb l ω w := by
  unfold parentRatio parentProb
  apply ENNReal.coe_le_coe.2
  have hk' : (ω w : ℝ≥0) ≤ (K : ℝ≥0) := by exact_mod_cast hk
  exact div_le_div_of_nonneg_left zero_le (by positivity) (add_le_add_right hk' l)

private lemma parentRatio_pos {l : ℝ≥0} (hl : 0 < l) (K : ℕ) : 0 < parentRatio l K := by
  unfold parentRatio
  exact ENNReal.coe_pos.2 (div_pos hl (by positivity))

private lemma parentRatio_le_one {l : ℝ≥0} (hl : 0 < l) (K : ℕ) : parentRatio l K ≤ 1 := by
  unfold parentRatio
  rw [← ENNReal.coe_one, ENNReal.coe_le_coe]
  exact (div_le_one (by positivity)).2 (by simp)

private theorem hit_parent_generation {l : ℝ≥0} (hl : 0 < l) (ω : List ℕ → ℕ)
    (v : List ℕ) (N : ℕ) : ∀ (j : ℕ), j < N → ∀ (w : List ℕ),
      w ∈ generation ω v j →
      parentRatio l (ballDegree ω v N) ^ (j + 1) ≤
        walkFrom ω l (.vtx w) (hitWithin (parentState v) (j + 1)) := by
  intro j
  induction j with
  | zero =>
      intro _ w hw
      simp only [generation, Finset.mem_singleton] at hw
      subst w
      have hk : ω v ≤ ballDegree ω v N := by
        exact degreeAt_le_ballDegree (by assumption) (by simp [generation])
      have hstep : parentRatio l (ballDegree ω v N) ≤
          stepKernel l ω (.vtx v) {parentState v} := by
        rw [stepKernel_parent l ω v hl]
        exact parentRatio_le_parentProb hl ω v hk
      have hzero : path (stepKernel l ω) (parentState v)
          (hitWithin (parentState v) 0) = 1 :=
        (mem_ae_iff_prob_eq_one (measurableSet_hitWithin _ _)).mp
          (hitWithin_zero_mem_ae _ _)
      have hstart : (1 : ℝ≥0∞) ≤ walkFrom ω l (parentState v)
          (hitWithin (parentState v) 0) := by
        rw [walkFrom, hzero]
      have hlow := le_path_of_firstStep (stepKernel l ω) (.vtx v) (parentState v)
        (measurableSet_hitWithin _ _) (pcons_hitWithin_subset _ _ _) hstart
      calc
        parentRatio l (ballDegree ω v N) ^ (0 + 1) =
            parentRatio l (ballDegree ω v N) * 1 := by simp
        _ ≤ stepKernel l ω (.vtx v) {parentState v} * 1 :=
          mul_le_mul_left hstep 1
        _ ≤ walkFrom ω l (.vtx v) (hitWithin (parentState v) (0 + 1)) := hlow
  | succ j ih =>
      intro hj w hw
      rcases generation_parent ω j v w hw with ⟨u, hu, hp⟩
      have hstep : parentRatio l (ballDegree ω v N) ≤
          stepKernel l ω (.vtx w) {parentState w} := by
        rw [stepKernel_parent l ω w hl]
        exact parentRatio_le_parentProb hl ω w (degreeAt_le_ballDegree hj hw)
      have hrec : parentRatio l (ballDegree ω v N) ^ (j + 1) ≤
          walkFrom ω l (parentState w) (hitWithin (parentState v) (j + 1)) := by
        rw [hp]
        exact ih (by omega) u hu
      have hlow := le_path_of_firstStep (stepKernel l ω) (.vtx w) (parentState w)
        (measurableSet_hitWithin _ _) (pcons_hitWithin_subset _ _ _) hrec
      calc
        parentRatio l (ballDegree ω v N) ^ (j + 1 + 1) =
            parentRatio l (ballDegree ω v N) *
              parentRatio l (ballDegree ω v N) ^ (j + 1) := by rw [pow_succ]; ac_rfl
        _ ≤ stepKernel l ω (.vtx w) {parentState w} *
              parentRatio l (ballDegree ω v N) ^ (j + 1) :=
          mul_le_mul_left hstep _
        _ ≤ walkFrom ω l (.vtx w) (hitWithin (parentState v) (j + 1 + 1)) := hlow

private lemma stayUntil_ball_le_compl_hit {l : ℝ≥0} {ω : List ℕ → ℕ} {v : List ℕ} {N : ℕ}
    (x : WalkState) : walkFrom ω l x (stayUntil (↑(ball ω v N) : Set WalkState) N) ≤
      walkFrom ω l x (hitWithin (parentState v) N)ᶜ := by
  apply measure_mono
  intro X hX
  rintro ⟨s, hs, hXs⟩
  exact parentState_not_mem_ball ω v N (hXs ▸ hX s hs)

private lemma one_block_stayUntil {l : ℝ≥0} (hl : 0 < l) (ω : List ℕ → ℕ)
    (v : List ℕ) (N : ℕ) (x : WalkState) (hx : x ∈ ball ω v N) :
    walkFrom ω l x (stayUntil (↑(ball ω v N) : Set WalkState) N) ≤
      1 - parentRatio l (ballDegree ω v N) ^ N := by
  cases x with
  | rootParent => simp [ball] at hx
  | vtx w =>
      rcases mem_generation_of_mem_ball hx with ⟨j, hj, hw⟩
      have hhit : parentRatio l (ballDegree ω v N) ^ N ≤
          walkFrom ω l (.vtx w) (hitWithin (parentState v) N) := by
        calc
          parentRatio l (ballDegree ω v N) ^ N ≤
              parentRatio l (ballDegree ω v N) ^ (j + 1) :=
            pow_le_pow_of_le_one zero_le (parentRatio_le_one hl _) (by omega)
          _ ≤ walkFrom ω l (.vtx w) (hitWithin (parentState v) (j + 1)) :=
            hit_parent_generation hl ω v N j hj w hw
          _ ≤ walkFrom ω l (.vtx w) (hitWithin (parentState v) N) := by
            apply measure_mono
            rintro X ⟨s, hs, hXs⟩
            exact ⟨s, by omega, hXs⟩
      calc
        walkFrom ω l (.vtx w) (stayUntil (↑(ball ω v N) : Set WalkState) N) ≤
            walkFrom ω l (.vtx w) (hitWithin (parentState v) N)ᶜ :=
          stayUntil_ball_le_compl_hit _
        _ = 1 - walkFrom ω l (.vtx w) (hitWithin (parentState v) N) := by
          rw [measure_compl (measurableSet_hitWithin _ _) (measure_ne_top _ _), measure_univ]
        _ ≤ 1 - parentRatio l (ballDegree ω v N) ^ N := tsub_le_tsub_left hhit 1

/-- From every initial state, the walk remains in a finite raw-field ball
forever with probability zero. -/
theorem walkFrom_stays_in_ball {l : ℝ≥0} (hl : 0 < l) (ω : List ℕ → ℕ)
    (v : List ℕ) (N : ℕ) (x : WalkState) :
    walkFrom ω l x {X | ∀ t, X t ∈ ball ω v N} = 0 := by
  have hr : parentRatio l (ballDegree ω v N) ^ N ≠ 0 :=
    ne_of_gt (ENNReal.pow_pos (parentRatio_pos hl _) N)
  apply path_stays_eq_zero (stepKernel l ω)
    (by exact (ball ω v N).measurableSet) N
    (ENNReal.sub_lt_self (by simp) (by simp) hr)
  intro y hy
  exact one_block_stayUntil hl ω v N y hy

end WalkExit

end LPPMonotonicityProof.Speed
