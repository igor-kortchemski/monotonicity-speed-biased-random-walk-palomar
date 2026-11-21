module

public import LPPMonotonicityProof.Speed.Walk.PhysicalFinite
public import LPPMonotonicityProof.Speed.Interface.Escape
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Physical infinite escape probabilities

The probability of never visiting the parent is the limit of the finite escapes
(Lemma 2.1(ii), `lem:escape`).  The finite-level events are nested almost surely, and
Mathlib's almost-everywhere form of continuity from above applies directly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Preorder Filtration
open scoped NNReal ENNReal BigOperators Function

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState

private lemma exists_height_pred {ω : List ℕ → ℕ} {v : List ℕ}
    {X : ℕ → WalkState} (_h0 : X 0 = .vtx v)
    (hstep : ∀ t, StepRel ω (X t) (X (t + 1))) {L : ℤ}
    (hstart : height (X 0) < L) {t : ℕ} (ht : height (X t) = L)
    (hmin : ∀ s < t, height (X s) ≠ L) :
    ∃ s < t, height (X s) = L - 1 := by
  have hbefore : ∀ s < t, height (X s) < L := by
    intro s hs
    induction s with
    | zero => exact hstart
    | succ s ih =>
        have hprev := ih (by omega)
        have hnext := hmin (s + 1) hs
        rcases stepRel_height (hstep s) with h | h <;> omega
  cases t with
  | zero =>
      exfalso
      exact hstart.ne ht
  | succ t =>
      refine ⟨t, by omega, ?_⟩
      have hprev := hbefore t (by omega)
      have hnext := ht
      rcases stepRel_height (hstep t) with h | h <;> omega

private lemma reach_succ_subset {ω : List ℕ → ℕ} {v : List ℕ}
    {X : ℕ → WalkState} (h0 : X 0 = .vtx v)
    (hstep : ∀ t, StepRel ω (X t) (X (t + 1))) (N : ℕ) :
    X ∈ reachLevelBefore v (N + 1) → X ∈ reachLevelBefore v N := by
  classical
  intro h
  let hex : ∃ t, height (X t) = v.length + (N + 1) ∧
      ∀ s ≤ t, X s ≠ parentState v := h
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  have hmin (s : ℕ) (hs : s < t) : height (X s) ≠ v.length + (N + 1) := by
    intro hlevel
    exact Nat.find_min hex hs ⟨hlevel, fun q _ => ht.2 q (by omega)⟩
  have hstart : height (X 0) < v.length + (N + 1) := by
    rw [h0]
    simp only [height]
    norm_cast
    omega
  rcases exists_height_pred h0 hstep hstart ht.1 hmin with ⟨s, hs, hlevel⟩
  refine ⟨s, ?_, fun q hq => ht.2 q (by omega)⟩
  rw [hlevel]
  ring

private lemma reach_antitone_ae (l : ℝ≥0) (ω : List ℕ → ℕ) (v : List ℕ) :
    ∀ᵐ X ∂walkFrom ω l (.vtx v), Antitone (fun N => X ∈ reachLevelBefore v N) := by
  filter_upwards [walkFrom_ae_stepRel l ω (.vtx v), path_zero (stepKernel l ω) (.vtx v)] with X hstep h0
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact id
  | succ b hab ih => exact fun hb => ih (reach_succ_subset h0 hstep b hb)

private lemma height_le_initial_add {ω : List ℕ → ℕ} {v : List ℕ}
    {X : ℕ → WalkState} (h0 : X 0 = .vtx v)
    (hstep : ∀ t, StepRel ω (X t) (X (t + 1))) (t : ℕ) :
    height (X t) ≤ v.length + t := by
  induction t with
  | zero => simp [h0, height]
  | succ t ih =>
      rcases stepRel_height (hstep t) with h | h <;>
        simp only [Nat.cast_add, Nat.cast_one] at * <;> omega

private lemma neverHits_eq_iInter_ae {l : ℝ≥0} (hl : 0 < l) (ω : List ℕ → ℕ) (v : List ℕ) :
    neverHits (parentState v) =ᵐ[walkFrom ω l (.vtx v)] ⋂ N, reachLevelBefore v N := by
  have hnull : ∀ N, {X : ℕ → WalkState | ∀ t, X t ∈ ball ω v N}ᶜ ∈
      MeasureTheory.ae (walkFrom ω l (.vtx v)) := by
    intro N
    exact measure_eq_zero_iff_ae_notMem.mp
      (walkFrom_stays_in_ball hl ω v N (.vtx v))
  have hnull' := (ae_all_iff).2 hnull
  filter_upwards [walkFrom_ae_stepRel l ω (.vtx v), path_zero (stepKernel l ω) (.vtx v),
    hnull'] with X hstep h0 hball
  apply propext
  constructor
  · intro hn
    simp only [Set.mem_iInter]
    intro N
    by_contra hr
    have hmem := physical_mem_ball_of_not_reach h0 hstep hn hr
    exact hball N hmem
  · intro hall t hp
    have hR := Set.mem_iInter.mp hall (t + 1)
    rcases hR with ⟨s, hs, hbefore⟩
    have hst : s < t := by
      by_contra hn
      exact hbefore t (by omega) hp
    have hbound := height_le_initial_add h0 hstep s
    rw [hs] at hbound
    simp only [Nat.cast_add, Nat.cast_one] at hbound
    omega

private lemma tendsto_escapeRaw (ω : List ℕ → ℕ) {l : ℝ} (hl : 0 < l) (v : List ℕ) :
    Tendsto (fun N => escapeN ω l N v) atTop (𝓝 (escapeRaw ω l v)) := by
  apply tendsto_atTop_ciInf
  · intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (escapeN_anti_height ω hl b v).trans ih
  · exact ⟨0, by rintro _ ⟨N, rfl⟩; exact physical_escapeN_nonneg ω hl N v⟩

/-- `lem:escape` (ii): finite physical escapes decrease to non-return. -/
theorem walkFrom_neverHits_parent {l : ℝ≥0} (hl : 0 < (l : ℝ))
    (ω : List ℕ → ℕ) (v : List ℕ) :
    walkFrom ω l (.vtx v) (neverHits (parentState v)) = ENNReal.ofReal (escapeRaw ω l v) := by
  have hlNN : 0 < l := by exact_mod_cast hl
  have hlimReal := (ENNReal.tendsto_ofReal (tendsto_escapeRaw ω hl v)).congr
    (fun N => (walkFrom_reachLevelBefore hl ω N v).symm)
  have hanti : Antitone (fun N => walkFrom ω l (.vtx v) (reachLevelBefore v N)) := by
    intro a b hab
    apply measure_mono_ae
    filter_upwards [reach_antitone_ae l ω v] with X hX
    exact hX hab
  have hlimMeasure : Tendsto (fun N => walkFrom ω l (.vtx v) (reachLevelBefore v N)) atTop
      (𝓝 (⨅ N, walkFrom ω l (.vtx v) (reachLevelBefore v N))) := by
    exact tendsto_atTop_iInf hanti
  have hiInf : (⨅ N, walkFrom ω l (.vtx v) (reachLevelBefore v N)) =
      ENNReal.ofReal (escapeRaw ω l v) := tendsto_nhds_unique hlimMeasure hlimReal
  rw [← hiInf]
  rw [measure_congr (neverHits_eq_iInter_ae hlNN ω v)]
  exact measure_iInter_of_ae_antitone (reach_antitone_ae l ω v)
    (fun N => (measurableSet_reachLevelBefore v N).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩

end LPPMonotonicityProof.Speed
