module

public import LPPMonotonicityProof.Speed.Ergodic.Initial

/-!
# Invariance across every neighbour

Every allowed physical move has positive label weight.
Consequently an almost-sure property of the one-step state holds at each
allowed move of almost every initial environment.  The two main statements are
applications to the time-zero future probability and to null sets.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Every allowed physical move, inward or outward, has positive weight. -/
theorem walkWeight_pos {l : ℝ} (hl : 0 < l) (e : Env) {j : ℕ}
    (hj : j ≤ degree e.fwd) : 0 < walkWeight l e j := by
  have hden : (0 : ℝ) < l + degree e.fwd :=
    add_pos_of_pos_of_nonneg hl (Nat.cast_nonneg _)
  by_cases hj0 : j = 0
  · subst j
    simpa [walkWeight] using ENNReal.ofReal_pos.mpr (div_pos hl hden)
  · simp only [walkWeight, if_neg hj0, if_pos hj]
    exact ENNReal.ofReal_pos.mpr (div_pos zero_lt_one hden)

namespace Markov.LabelSpec

variable {S : Type*} [MeasurableSpace S]

/-- Restrict an almost-sure label property to the label-zero fibre of a
positively weighted first step. -/
theorem ae_firstStep (G : LabelSpec S) (s : S) (j : ℕ)
    (hj : G.weight s j ≠ 0) {p : (ℕ → ℕ) → Prop}
    (h : ∀ᵐ c ∂G.law s, p c) :
    ∀ᵐ c ∂G.law (G.next s j), p (seqCons j c) := by
  have hsum : ∀ᵐ c ∂Measure.sum (fun j =>
      G.weight s j • (G.law (G.next s j)).map (seqCons j)), p c := by
    rw [← G.law_firstStep]
    exact h
  have hscaled := (Measure.ae_sum_iff.mp hsum) j
  have hmap := (Measure.ae_ennreal_smul_measure_iff hj).mp hscaled
  exact MeasureTheory.ae_of_ae_map (measurable_seqCons j).aemeasurable hmap

end Markov.LabelSpec

/-- Lift an almost-sure property of the one-step physical state to every
allowed move of almost every initial environment. -/
theorem ae_all_walkMoves (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {p : Env → Env → Prop}
    (h : ∀ᵐ x ∂walkPathLaw μ l hl hμ hEscapePos, p x.1 (move x.1 (x.2 0))) :
    ∀ᵐ e ∂muW μ l hl hμ hEscapePos, ∀ j ≤ degree e.fwd, p e (move e j) := by
  have hsections : ∀ᵐ e ∂muW μ l hl hμ hEscapePos,
      ∀ᵐ c ∂moveLaw l hl e, p e (move e (c 0)) := by
    change ∀ᵐ x ∂(muW μ l hl hμ hEscapePos ⊗ₘ moveLaw l hl),
      p x.1 (move x.1 (x.2 0)) at h
    exact Measure.ae_ae_of_ae_compProd h
  rw [ae_all_iff]
  intro j
  filter_upwards [hsections] with e he
  intro hj
  have hc := (walkSpec l hl).ae_firstStep e j (walkWeight_pos hl e hj).ne'
    (p := fun c => p e (move e (c 0))) he
  have hc' : ∀ᵐ _c ∂moveLaw l hl (move e j), p e (move e j) := by
    filter_upwards [hc] with c hc
    simpa only [Markov.LabelSpec.seqCons] using hc
  exact Filter.eventually_const.mp hc'

/-- **Neighbour invariance.**  The future probability is unchanged by every allowed neighbour
move, almost surely for the initial environment. -/
theorem hInv_move (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A)
    (hinv : walkShift l hl ⁻¹' A = A) :
    ∀ᵐ e ∂muW μ l hl hμ hEscapePos, ∀ j ≤ degree e.fwd,
      hInv l hl A (move e j) = hInv l hl A e := by
  refine ae_all_walkMoves μ l hl hμ hEscapePos
    (p := fun e e' => hInv l hl A e' = hInv l hl A e) ?_
  have h := hInv_state_ae_eq μ l hl hμ hEscapePos hA hinv 1
  change (fun (x : PathSpace) => hInv l hl A (move x.1 (x.2 0))) =ᵐ[walkPathLaw μ l hl hμ hEscapePos]
    fun x => hInv l hl A x.1 at h
  exact h

/-- **Null sets.**  Almost surely, no allowed neighbour belongs to a prescribed
`muW`-null set. -/
theorem ae_move_avoids_null (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {N : Set Env} (hN : muW μ l hl hμ hEscapePos N = 0) :
    ∀ᵐ e ∂muW μ l hl hμ hEscapePos, ∀ j ≤ degree e.fwd, move e j ∉ N := by
  obtain ⟨M, hNM, hM, hM0⟩ := exists_measurable_superset_of_null hN
  have hnull : (walkPathLaw μ l hl hμ hEscapePos)
      ((fun x => (walkSpec l hl).state x.1 x.2 1) ⁻¹' M) = 0 := by
    rw [← Measure.map_apply ((walkSpec l hl).measurable_state 1) hM,
      walkPathLaw_map_state μ l hl hμ hEscapePos 1, hM0]
  have hpath : ∀ᵐ x ∂walkPathLaw μ l hl hμ hEscapePos, move x.1 (x.2 0) ∉ M := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    exact hx
  have hall := ae_all_walkMoves μ l hl hμ hEscapePos (p := fun _ e => e ∉ M) hpath
  filter_upwards [hall] with e he
  intro j hj hn
  exact he j hj (hNM hn)

end LPPMonotonicityProof.Speed
