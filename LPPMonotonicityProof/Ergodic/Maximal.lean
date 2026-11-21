module

public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Order.Lattice

/-!
# The maximal inequality for Birkhoff sums

This is a project-independent development of the maximal inequality.
-/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped BigOperators Topology

variable {α : Type*} [MeasurableSpace α]
variable {T : α → α} {μ : Measure α} {g : α → ℝ}

/-- The maximum of `0, S₁ g, …, S_N g`, expressed through its shift recurrence. -/
noncomputable def maxBirkhoffSum (T : α → α) (g : α → ℝ) : ℕ → α → ℝ
  | 0 => 0
  | N + 1 => fun x => max 0 (g x + maxBirkhoffSum T g N (T x))

omit [MeasurableSpace α] in
@[simp] theorem maxBirkhoffSum_zero (T : α → α) (g : α → ℝ) (x : α) :
    maxBirkhoffSum T g 0 x = 0 := rfl

omit [MeasurableSpace α] in
@[simp] theorem maxBirkhoffSum_succ (T : α → α) (g : α → ℝ) (N : ℕ) (x : α) :
    maxBirkhoffSum T g (N + 1) x = max 0 (g x + maxBirkhoffSum T g N (T x)) := rfl

omit [MeasurableSpace α] in
theorem maxBirkhoffSum_nonneg (T : α → α) (g : α → ℝ) (N : ℕ) (x : α) :
    0 ≤ maxBirkhoffSum T g N x := by
  cases N <;> simp

omit [MeasurableSpace α] in
theorem birkhoffSum_le_maxBirkhoffSum (T : α → α) (g : α → ℝ)
    {n N : ℕ} (hn : n ≤ N) (x : α) : birkhoffSum T g n x ≤ maxBirkhoffSum T g N x := by
  induction N generalizing n x with
  | zero =>
      have : n = 0 := Nat.eq_zero_of_le_zero hn
      subst n
      simp
  | succ N ih =>
      cases n with
      | zero => simpa only [birkhoffSum_zero_apply] using
          maxBirkhoffSum_nonneg T g (N + 1) x
      | succ n =>
          have hn' : n ≤ N := Nat.succ_le_succ_iff.mp hn
          calc
            birkhoffSum T g (n + 1) x = g x + birkhoffSum T g n (T x) :=
              birkhoffSum_succ_apply' T g n x
            _ ≤ g x + maxBirkhoffSum T g N (T x) := add_le_add le_rfl (ih hn' (T x))
            _ ≤ max 0 (g x + maxBirkhoffSum T g N (T x)) := le_max_right _ _
            _ = maxBirkhoffSum T g (N + 1) x := (maxBirkhoffSum_succ T g N x).symm

theorem integrable_maxBirkhoffSum (hT : MeasurePreserving T μ μ)
    (hg : Integrable g μ) (N : ℕ) : Integrable (maxBirkhoffSum T g N) μ := by
  induction N with
  | zero => simpa only [maxBirkhoffSum] using integrable_zero α ℝ μ
  | succ N ih =>
      have hcomp : Integrable (fun x => maxBirkhoffSum T g N (T x)) μ := by
        change Integrable (maxBirkhoffSum T g N ∘ T) μ
        exact hT.integrable_comp_of_integrable ih
      have hadd : Integrable (fun x => g x + maxBirkhoffSum T g N (T x)) μ := hg.add hcomp
      change Integrable ((0 : α → ℝ) ⊔ fun x => g x + maxBirkhoffSum T g N (T x)) μ
      exact (integrable_zero α ℝ μ).sup hadd

theorem measurable_maxBirkhoffSum (hT : Measurable T) (hg : Measurable g) (N : ℕ) :
    Measurable (maxBirkhoffSum T g N) := by
  induction N with
  | zero =>
      change Measurable (fun _ : α => (0 : ℝ))
      exact measurable_const
  | succ N ih =>
      change Measurable (fun x => max 0 (g x + maxBirkhoffSum T g N (T x)))
      exact measurable_const.max (hg.add (ih.comp hT))

omit [MeasurableSpace α] in
theorem maxBirkhoffSum_mono_succ (T : α → α) (g : α → ℝ) (N : ℕ) (x : α) :
    maxBirkhoffSum T g N x ≤ maxBirkhoffSum T g (N + 1) x := by
  induction N generalizing x with
  | zero => simp
  | succ N ih =>
      rw [maxBirkhoffSum_succ, maxBirkhoffSum_succ]
      exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

omit [MeasurableSpace α] in
theorem maxBirkhoffSum_sub_comp_le_indicator (N : ℕ) (x : α) :
    maxBirkhoffSum T g (N + 1) x - maxBirkhoffSum T g N (T x) ≤
      {y | 0 < maxBirkhoffSum T g (N + 1) y}.indicator g x := by
  by_cases hx : 0 < maxBirkhoffSum T g (N + 1) x
  · rw [Set.indicator_of_mem (s := {y | 0 < maxBirkhoffSum T g (N + 1) y}) hx g]
    have hx' : 0 < max 0 (g x + maxBirkhoffSum T g N (T x)) := by
      simpa only [maxBirkhoffSum_succ] using hx
    have hpos : 0 ≤ g x + maxBirkhoffSum T g N (T x) := by
      by_contra h
      rw [max_eq_left (le_of_not_ge h)] at hx'
      exact lt_irrefl 0 hx'
    rw [maxBirkhoffSum_succ, max_eq_right hpos]
    simp
  · rw [Set.indicator_of_notMem (s := {y | 0 < maxBirkhoffSum T g (N + 1) y}) hx g]
    have hzero : maxBirkhoffSum T g (N + 1) x = 0 :=
      le_antisymm (le_of_not_gt hx) (maxBirkhoffSum_nonneg T g (N + 1) x)
    rw [hzero, zero_sub, neg_nonpos]
    exact maxBirkhoffSum_nonneg T g N (T x)

/-- **Maximal inequality** for an integrable observable and a measure-preserving map. -/
theorem integral_nonneg_on_maxBirkhoffSum_pos
    (hT : MeasurePreserving T μ μ) (hg : Integrable g μ) (N : ℕ) :
    0 ≤ ∫ x in {x | 0 < maxBirkhoffSum T g N x}, g x ∂μ := by
  cases N with
  | zero => simp
  | succ N =>
      let A := {x | 0 < maxBirkhoffSum T g (N + 1) x}
      have hMi := integrable_maxBirkhoffSum hT hg (N + 1)
      have hNi := integrable_maxBirkhoffSum hT hg N
      have hNTi : Integrable (fun x => maxBirkhoffSum T g N (T x)) μ := by
        change Integrable (maxBirkhoffSum T g N ∘ T) μ
        exact hT.integrable_comp_of_integrable hNi
      have hA : NullMeasurableSet A μ :=
        nullMeasurableSet_lt aemeasurable_const hMi.aestronglyMeasurable.aemeasurable
      have hdiff : Integrable
          (fun x => maxBirkhoffSum T g (N + 1) x - maxBirkhoffSum T g N (T x)) μ :=
        hMi.sub hNTi
      have hcomp : (∫ x, maxBirkhoffSum T g N (T x) ∂μ) =
          ∫ x, maxBirkhoffSum T g N x ∂μ := by
        calc
          (∫ x, maxBirkhoffSum T g N (T x) ∂μ) =
              ∫ x, maxBirkhoffSum T g N x ∂(μ.map T) :=
            (integral_map hT.aemeasurable (by
              rw [hT.map_eq]
              exact hNi.aestronglyMeasurable)).symm
          _ = ∫ x, maxBirkhoffSum T g N x ∂μ := by rw [hT.map_eq]
      have hnonneg : 0 ≤ ∫ x, (maxBirkhoffSum T g (N + 1) x -
          maxBirkhoffSum T g N (T x)) ∂μ := by
        rw [integral_sub hMi hNTi, hcomp, sub_nonneg]
        exact integral_mono hNi hMi (maxBirkhoffSum_mono_succ T g N)
      have hle := integral_mono_ae hdiff (hg.indicator₀ hA)
        (Eventually.of_forall (maxBirkhoffSum_sub_comp_le_indicator (T := T) (g := g) N))
      rw [integral_indicator₀ hA] at hle
      exact hnonneg.trans hle

end
