module

public import LPPMonotonicityProof.Speed.Close.NonReturning
public import LPPMonotonicityProof.Speed.Walk.Restart
public import LPPMonotonicityProof.Speed.Escape.Positive
public import LPPMonotonicityProof.Speed.Interface.Present

/-!
# Restarts: the speed on all paths

Since the artificial parent is visited only finitely often, the speed on paths which
never return (`NonReturning.lean`) extends to almost every path.  The exported
quenched speed clause is in `Export.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState
open LPPMonotonicityProof.RTL.LocallyFinite

private lemma tendsto_nat_add_div_self (t : ℕ) :
    Tendsto (fun n : ℕ => (((n + t : ℕ) : ℝ) / (n : ℝ))) atTop (𝓝 1) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (t : ℝ)).const_add 1
  have heq : (fun n : ℕ => (((n + t : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => 1 + (t : ℝ) / n) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    push_cast
    field_simp
  simpa only [add_zero] using h.congr' heq.symm

private lemma tendsto_nat_sub_div_self (t : ℕ) :
    Tendsto (fun n : ℕ => (((n - t : ℕ) : ℝ) / (n : ℝ))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - (t : ℝ) / n) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (t : ℝ))
  have heq : (fun n : ℕ => (((n - t : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => 1 - (t : ℝ) / n) := by
    filter_upwards [eventually_ge_atTop t, eventually_gt_atTop 0] with n htn hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    rw [Nat.cast_sub htn]
    field_simp
  simpa using h.congr' heq.symm

private lemma tendsto_shift_div_of_tendsto_div {a : ℕ → ℝ} {v : ℝ} (t : ℕ)
    (h : Tendsto (fun n : ℕ => a n / n) atTop (𝓝 v)) :
    Tendsto (fun n : ℕ => a (n + t) / n) atTop (𝓝 v) := by
  have hc := h.comp (tendsto_add_atTop_nat t)
  have hp := hc.mul (tendsto_nat_add_div_self t)
  have heq : (fun n : ℕ => a (n + t) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => (a (n + t) / (((n + t : ℕ) : ℝ))) *
        (((n + t : ℕ) : ℝ) / (n : ℝ))) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hnt0 : ((n + t : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  simpa using hp.congr' heq.symm

private lemma tendsto_div_of_tendsto_shift_div {a : ℕ → ℝ} {v : ℝ} (t : ℕ)
    (h : Tendsto (fun n : ℕ => a (n + t) / n) atTop (𝓝 v)) :
    Tendsto (fun n : ℕ => a n / n) atTop (𝓝 v) := by
  have hc := h.comp (tendsto_sub_atTop_nat t)
  have hp := hc.mul (tendsto_nat_sub_div_self t)
  have heq : (fun n : ℕ => a n / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => (a ((n - t) + t) / (((n - t : ℕ) : ℝ))) *
        (((n - t : ℕ) : ℝ) / (n : ℝ))) := by
    filter_upwards [eventually_gt_atTop t] with n hn
    have htn : t ≤ n := Nat.le_of_lt hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hst0 : (((n - t : ℕ) : ℝ)) ≠ 0 := by
      rw [Ne, Nat.cast_eq_zero]
      omega
    rw [Nat.sub_add_cancel htn]
    field_simp
  simpa using hp.congr' heq.symm

private lemma bad_tail (v : ℝ) (t : ℕ) (X : ℕ → WalkState) :
    X ∈ Bad v ↔ shiftN t X ∈ Bad v := by
  change (¬ Tendsto (fun n : ℕ => (height (X n) : ℝ) / n) atTop (𝓝 v)) ↔
    ¬ Tendsto (fun n : ℕ => (height (X (n + t)) : ℝ) / n) atTop (𝓝 v)
  apply not_congr
  exact ⟨tendsto_shift_div_of_tendsto_div
      (a := fun n : ℕ => (height (X n) : ℝ)) (v := v) t,
    tendsto_div_of_tendsto_shift_div
      (a := fun n : ℕ => (height (X n) : ℝ)) (v := v) t⟩

/-- **Restart.**  The last-return restart removes the non-returning intersection
from `ae_bad_neverHits`. -/
theorem ae_bad_null (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) :
    ∀ᵐ T ∂bienaymeLaw μ, walkLaw T.val l.toNNReal (Bad (speedValue μ l)) = 0 := by
  filter_upwards [ae_bad_neverHits μ hl hμ hlm, ae_escape_pos hμ hl hlm] with T hT hβ
  apply walkLaw_null_of_null_on_neverHits (Real.toNNReal_pos.mpr hl) T.val
    (l := l.toNNReal)
  · change 0 < escapeRaw T.val ((l.toNNReal : ℝ≥0) : ℝ) []
    change 0 < escapeRaw T.val l [] at hβ
    rwa [Real.coe_toNNReal l hl.le]
  · exact measurableSet_bad _
  · exact bad_tail (speedValue μ l)
  · exact hT

end LPPMonotonicityProof.Speed
