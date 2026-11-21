module

public import LPPMonotonicityProof.Speed.Walk.PhysicalLimit

/-!
# Restart at visits to the artificial parent

This is the step "the artificial parent is visited only finitely often" in the
proof of Theorem 2.2 (`thm:speed-formula`).  The first visit to a fixed state,
followed by one further step, is a stopping time.  Summing the Markov property
over its finite values shows that infinitely many visits to the artificial parent have probability
zero when the escape probability is positive.  Tail-null sets then split into
paths which never return, paths with a last return, and this null event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Preorder Filtration
open scoped NNReal ENNReal BigOperators Function

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState

private def hitAt (y : WalkState) (t : ℕ) : Set (ℕ → WalkState) :=
  {X | X t = y}

private def firstHitAt (y : WalkState) (t : ℕ) : Set (ℕ → WalkState) :=
  {X | X t = y ∧ ∀ s < t, X s ≠ y}

/-- The first visit to `y`, followed by one more step. -/
private noncomputable def restartTime (y : WalkState) (X : ℕ → WalkState) : ℕ∞ := by
  classical
  exact if h : ∃ t, X t = y then Nat.find h + 1 else ⊤

/-- Visits to `y` at arbitrarily late times. -/
private def infinitelyOften (y : WalkState) : Set (ℕ → WalkState) :=
  {X | ∀ n, ∃ t, n ≤ t ∧ X t = y}

private lemma measurableSet_hitAt_piLE (y : WalkState) (t : ℕ) :
    MeasurableSet[piLE t] (hitAt y t) := by
  rw [piLE_eq_comap_frestrictLe]
  let zt : (Π _ : Finset.Iic t, WalkState) → WalkState :=
    fun z => z ⟨t, Finset.mem_Iic.mpr le_rfl⟩
  refine ⟨{z | zt z = y}, (MeasurableSet.singleton y).preimage (measurable_pi_apply _), ?_⟩
  rfl

private lemma measurableSet_firstHitAt_piLE (y : WalkState) (t : ℕ) :
    MeasurableSet[piLE t] (firstHitAt y t) := by
  rw [piLE_eq_comap_frestrictLe]
  let zt : (Π _ : Finset.Iic t, WalkState) → WalkState :=
    fun z => z ⟨t, Finset.mem_Iic.mpr le_rfl⟩
  let zs : ℕ → (Π _ : Finset.Iic t, WalkState) → WalkState := fun s z =>
    z ⟨min s t, Finset.mem_Iic.mpr (min_le_right _ _)⟩
  let C : Set (Π _ : Finset.Iic t, WalkState) :=
    {z | zt z = y} ∩ ⋂ s, {z | s < t → zs s z ≠ y}
  refine ⟨C, ?_, ?_⟩
  · apply MeasurableSet.inter
    · exact (MeasurableSet.singleton _).preimage (measurable_pi_apply _)
    · apply MeasurableSet.iInter
      intro s
      by_cases hs : s < t
      · simp only [hs, forall_true_left]
        exact ((MeasurableSet.singleton _).preimage (measurable_pi_apply _)).compl
      · simp [hs]
  · ext X
    change Preorder.frestrictLe t X ∈ C ↔ X ∈ firstHitAt y t
    simp only [C, zt, zs, firstHitAt, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨ht, hbefore⟩
      refine ⟨ht, fun s hs => ?_⟩
      have hmin : min s t = s := Nat.min_eq_left (Nat.le_of_lt hs)
      simpa [hmin] using hbefore s hs
    · rintro ⟨ht, hbefore⟩
      refine ⟨ht, fun s hs => ?_⟩
      have hmin : min s t = s := Nat.min_eq_left (Nat.le_of_lt hs)
      simpa [hmin] using hbefore s hs

private lemma restartTime_eq_nat_succ (y : WalkState) (X : ℕ → WalkState) (t : ℕ) :
    restartTime y X = ((t + 1 : ℕ) : ℕ∞) ↔ X ∈ firstHitAt y t := by
  classical
  constructor
  · intro ht
    by_cases h : ∃ t, X t = y
    · rw [restartTime, dif_pos h] at ht
      have heq' : Nat.find h + 1 = t + 1 := by exact_mod_cast ht
      have heq : Nat.find h = t := by omega
      have hspec := Nat.find_spec h
      exact ⟨by simpa only [heq] using hspec, by
        simpa only [firstHitAt, Set.mem_setOf_eq, heq] using
          (show ∀ s < Nat.find h, X s ≠ y from fun s hs => Nat.find_min h hs)⟩
    · exfalso
      apply ENat.natCast_ne_top (t + 1)
      simpa [restartTime, h] using ht.symm
  · intro ht
    have h : ∃ t, X t = y := ⟨t, ht.1⟩
    rw [restartTime, dif_pos h]
    have hspec := Nat.find_spec h
    have hle : Nat.find h ≤ t := Nat.find_le ht.1
    have hge : t ≤ Nat.find h := by
      by_contra hn
      exact ht.2 (Nat.find h) (by omega) hspec
    have heq : Nat.find h = t := Nat.le_antisymm hle hge
    rw [heq]
    simp

private lemma restartTime_ne_zero (y : WalkState) (X : ℕ → WalkState) :
    restartTime y X ≠ 0 := by
  classical
  rw [restartTime]
  split_ifs <;> simp

private lemma measurableSet_restartTime (y : WalkState) (u : ℕ) :
    MeasurableSet[piLE u] {X | restartTime y X = u} := by
  cases u with
  | zero =>
      have heq : {X | restartTime y X = ((0 : ℕ) : ℕ∞)} = (∅ : Set (ℕ → WalkState)) := by
        ext X
        simp [restartTime_ne_zero]
      rw [heq]
      exact @MeasurableSet.empty _ (piLE 0)
  | succ t =>
      have heq : {X | restartTime y X = ((t + 1 : ℕ) : ℕ∞)} = firstHitAt y t := by
        ext X
        exact restartTime_eq_nat_succ y X t
      rw [heq]
      exact Filtration.piLE.mono (Nat.le_succ t) _ (measurableSet_firstHitAt_piLE y t)

private lemma measurableSet_infinitelyOften (y : WalkState) :
    MeasurableSet (infinitelyOften y) := by
  rw [infinitelyOften]
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iUnion
  intro t
  by_cases hnt : n ≤ t
  · simp only [hnt, true_and]
    exact (MeasurableSet.singleton y).preimage (measurable_pi_apply t)
  · simp [hnt]

private lemma restartTime_ne_top_iff (y : WalkState) (X : ℕ → WalkState) :
    restartTime y X ≠ ⊤ ↔ X ∉ neverHits y := by
  classical
  by_cases h : ∃ t, X t = y
  · simp [restartTime, h, neverHits]
  · simp [restartTime, h, neverHits]

private lemma infinitelyOften_eq_restart (y : WalkState) :
    infinitelyOften y = {X | ∃ u : ℕ, restartTime y X = u ∧ shiftN u X ∈ infinitelyOften y} := by
  classical
  ext X
  constructor
  · intro hX
    have h : ∃ t, X t = y := by
      obtain ⟨t, _, ht⟩ := hX 0
      exact ⟨t, ht⟩
    let u := Nat.find h + 1
    have hu : restartTime y X = u := by simp [restartTime, h, u]
    refine ⟨u, hu, ?_⟩
    intro n
    obtain ⟨s, hs, hXs⟩ := hX (n + u)
    refine ⟨s - u, by omega, ?_⟩
    change X (s - u + u) = y
    have hsu : s - u + u = s := by omega
    rw [hsu]
    exact hXs
  · rintro ⟨u, _, hu⟩ n
    obtain ⟨s, hs, hXs⟩ := hu n
    refine ⟨s + u, by omega, ?_⟩
    exact hXs

private lemma restart_integral_eq (l : ℝ≥0) (ω : List ℕ → ℕ)
    {A : Set (ℕ → WalkState)} (hA : MeasurableSet A) :
    (∫⁻ X in {X | restartTime .rootParent X ≠ ⊤},
      walkFrom ω l (X (restartTime .rootParent X).toNat) A ∂walkLaw ω l) =
      walkLaw ω l A * walkLaw ω l {X | restartTime .rootParent X ≠ ⊤} := by
  have hfinite : MeasurableSet {X : ℕ → WalkState | restartTime .rootParent X ≠ ⊤} := by
    have hcompl : MeasurableSet {X : ℕ → WalkState | restartTime .rootParent X = ⊤} := by
      rw [show {X : ℕ → WalkState | restartTime .rootParent X = ⊤} =
          (⋃ u : ℕ, {X | restartTime .rootParent X = u})ᶜ by
        ext X
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion]
        constructor
        · intro h ⟨u, hu⟩
          rw [hu] at h
          exact ENat.natCast_ne_top u h
        · intro h
          by_contra hn
          obtain ⟨u, hu⟩ := ENat.ne_top_iff_exists.mp hn
          exact h ⟨u, hu.symm⟩]
      exact MeasurableSet.compl (MeasurableSet.iUnion fun u =>
        (Filtration.piLE.le u) _ (measurableSet_restartTime .rootParent u))
    convert hcompl.compl using 1 <;> ext X <;> simp
  rw [← setLIntegral_const]
  apply setLIntegral_congr_fun_ae hfinite
  rw [walkLaw_eq_walkFrom]
  filter_upwards [walkFrom_ae_stepRel l ω (.vtx [])] with X hstep
  intro hX
  obtain ⟨u, hu⟩ := ENat.ne_top_iff_exists.mp hX
  cases u with
  | zero => exact (restartTime_ne_zero .rootParent X hu.symm).elim
  | succ t =>
      have ht : restartTime .rootParent X = ((t + 1 : ℕ) : ℕ∞) := hu.symm
      have hhit := (restartTime_eq_nat_succ .rootParent X t).mp ht
      have hnext : X (t + 1) = .vtx [] := by
        have hs := hstep t
        change StepRel ω (X t) (X (t + 1)) at hs
        rw [hhit.1] at hs
        exact hs
      rw [ht, ENat.toNat_natCast, hnext]

private lemma walkLaw_infinitelyOften_rootParent_null {l : ℝ≥0} (hl : 0 < (l : ℝ))
    (ω : List ℕ → ℕ) (hβ : 0 < escapeRaw ω l []) :
    walkLaw ω l (infinitelyOften .rootParent) = 0 := by
  letI : IsProbabilityMeasure (walkLaw ω l) := by
    rw [walkLaw_eq_walkFrom]
    infer_instance
  have hnever : walkLaw ω l (neverHits .rootParent) = ENNReal.ofReal (escapeRaw ω l []) := by
    rw [walkLaw_eq_walkFrom]
    simpa [parentState] using walkFrom_neverHits_parent hl ω []
  have hfiniteSet : {X : ℕ → WalkState | restartTime .rootParent X ≠ ⊤} =
      (neverHits .rootParent)ᶜ := by
    ext X
    exact restartTime_ne_top_iff .rootParent X
  have hfiniteProb : walkLaw ω l {X | restartTime .rootParent X ≠ ⊤} =
      1 - ENNReal.ofReal (escapeRaw ω l []) := by
    rw [hfiniteSet, measure_compl (measurableSet_neverHits _) (measure_ne_top _ _),
      measure_univ, hnever]
  have hrec : walkLaw ω l (infinitelyOften .rootParent) =
      walkLaw ω l (infinitelyOften .rootParent) *
        walkLaw ω l {X | restartTime .rootParent X ≠ ⊤} := by
    calc
      walkLaw ω l (infinitelyOften .rootParent) =
          walkLaw ω l {X | ∃ u : ℕ, restartTime .rootParent X = u ∧
            shiftN u X ∈ infinitelyOften .rootParent} := by rw [← infinitelyOften_eq_restart]
      _ = ∫⁻ X in {X | restartTime .rootParent X ≠ ⊤},
          walkFrom ω l (X (restartTime .rootParent X).toNat)
            (infinitelyOften .rootParent) ∂walkLaw ω l := by
        rw [walkLaw_eq_walkFrom]
        exact path_markov_stopping (stepKernel l ω) (.vtx [])
          (measurableSet_restartTime .rootParent) (measurableSet_infinitelyOften .rootParent)
      _ = _ := restart_integral_eq l ω (measurableSet_infinitelyOften .rootParent)
  rw [hfiniteProb] at hrec
  have hβ0 : ENNReal.ofReal (escapeRaw ω l []) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hβ).ne'
  have hq : 1 - ENNReal.ofReal (escapeRaw ω l []) < 1 :=
    ENNReal.sub_lt_self (by simp) (by simp) hβ0
  by_contra hp
  have hp0 : walkLaw ω l (infinitelyOften .rootParent) ≠ 0 := hp
  have hlt : (1 - ENNReal.ofReal (escapeRaw ω l [])) *
      walkLaw ω l (infinitelyOften .rootParent) <
      1 * walkLaw ω l (infinitelyOften .rootParent) :=
    ENNReal.mul_lt_mul_left hp0 (measure_ne_top _ _) hq
  rw [one_mul, mul_comm (1 - ENNReal.ofReal (escapeRaw ω l [])), ← hrec] at hlt
  exact (lt_irrefl _ hlt)

private lemma walkLaw_hit_shift_null (l : ℝ≥0) (ω : List ℕ → ℕ)
    {A : Set (ℕ → WalkState)} (hA : MeasurableSet A) (hA0 : walkLaw ω l A = 0) (t : ℕ) :
    walkLaw ω l (hitAt .rootParent t ∩ shiftN (t + 1) ⁻¹' A) = 0 := by
  have hhit : MeasurableSet[piLE (t + 1)] (hitAt .rootParent t) :=
    Filtration.piLE.mono (Nat.le_succ t) _ (measurableSet_hitAt_piLE .rootParent t)
  rw [walkLaw_eq_walkFrom]
  change path (stepKernel l ω) (.vtx []) (hitAt .rootParent t ∩ shiftN (t + 1) ⁻¹' A) = 0
  rw [path_markov (stepKernel l ω) (t + 1) (.vtx []) hhit hA]
  have hhitAmb : MeasurableSet (hitAt .rootParent t) :=
    (Filtration.piLE.le (t + 1)) _ hhit
  calc
    (∫⁻ X in hitAt .rootParent t, path (stepKernel l ω) (X (t + 1)) A
        ∂path (stepKernel l ω) (.vtx [])) =
        ∫⁻ _ in hitAt .rootParent t, walkLaw ω l A ∂walkLaw ω l := by
      rw [walkLaw_eq_walkFrom]
      apply setLIntegral_congr_fun_ae hhitAmb
      filter_upwards [walkFrom_ae_stepRel l ω (.vtx [])] with X hstep
      intro hX
      have hnext : X (t + 1) = .vtx [] := by
        have hs := hstep t
        change StepRel ω (X t) (X (t + 1)) at hs
        rw [hX] at hs
        exact hs
      rw [hnext]
      rfl
    _ = 0 := by rw [setLIntegral_const, hA0, zero_mul]

/-- A tail-invariant measurable set which is null on non-returning paths is
null whenever the escape probability from the root is positive. -/
theorem walkLaw_null_of_null_on_neverHits {l : ℝ≥0} (hl : 0 < (l : ℝ)) (ω : List ℕ → ℕ)
    (hβ : 0 < escapeRaw ω l []) {B : Set (ℕ → WalkState)} (hB : MeasurableSet B)
    (htail : ∀ t X, X ∈ B ↔ shiftN t X ∈ B)
    (h0 : walkLaw ω l (B ∩ neverHits .rootParent) = 0) :
    walkLaw ω l B = 0 := by
  classical
  have hA : MeasurableSet (B ∩ neverHits .rootParent) :=
    hB.inter (measurableSet_neverHits _)
  have hshift : walkLaw ω l (⋃ t : ℕ,
      hitAt .rootParent t ∩ shiftN (t + 1) ⁻¹' (B ∩ neverHits .rootParent)) = 0 :=
    measure_iUnion_null fun t => walkLaw_hit_shift_null l ω hA h0 t
  have hInf : walkLaw ω l (infinitelyOften .rootParent) = 0 :=
    walkLaw_infinitelyOften_rootParent_null hl ω hβ
  apply measure_mono_null (show B ⊆ (B ∩ neverHits .rootParent) ∪
      (⋃ t : ℕ, hitAt .rootParent t ∩ shiftN (t + 1) ⁻¹' (B ∩ neverHits .rootParent)) ∪
        infinitelyOften .rootParent from ?_)
    (measure_union_null (measure_union_null h0 hshift) hInf)
  intro X hXB
  by_cases hnever : X ∈ neverHits .rootParent
  · exact Or.inl (Or.inl ⟨hXB, hnever⟩)
  by_cases hXI : X ∈ infinitelyOften .rootParent
  · exact Or.inr hXI
  · apply Or.inl
    right
    have hex : ∃ t, X t = .rootParent := by simpa [neverHits] using hnever
    change ¬ ∀ n, ∃ t, n ≤ t ∧ X t = .rootParent at hXI
    push_neg at hXI
    obtain ⟨n, hn⟩ := hXI
    obtain ⟨s, hs⟩ := hex
    have hsn : s ≤ n := by
      by_contra h
      exact hn s (by omega) hs
    let t := Nat.findGreatest (fun t => X t = .rootParent) n
    have ht : X t = .rootParent := by
      dsimp [t]
      exact Nat.findGreatest_spec (P := fun t => X t = .rootParent) hsn hs
    have htlast : ∀ u, X (u + (t + 1)) ≠ .rootParent := by
      intro u hu
      have hts : t < u + (t + 1) := by omega
      by_cases hle : u + (t + 1) ≤ n
      · exact (Nat.findGreatest_is_greatest (P := fun t => X t = .rootParent)
          (n := n) hts hle) hu
      · exact hn (u + (t + 1)) (by omega) hu
    apply Set.mem_iUnion.mpr
    refine ⟨t, ht, (htail (t + 1) X).mp hXB, ?_⟩
    exact htlast

end LPPMonotonicityProof.Speed
