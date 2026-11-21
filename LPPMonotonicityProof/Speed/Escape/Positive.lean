module

public import LPPMonotonicityProof.Speed.Escape.EnergyEscape
public import LPPMonotonicityProof.Speed.Walk.Escape
public import LPPMonotonicityProof.RTL.LocallyFinite.Extinction
public import Mathlib.Algebra.Order.Archimedean.Basic
import Lean.Elab.Tactic.Omega

/-!
# Almost-sure positivity of escape

This module proves Lemma 2.1(iv) (`lem:escape`): for `0 < λ < m`, the escape
is almost surely in `(0, 1)`, at a fixed bias and simultaneously for all biases.
On the pruned Bienaymé tree, the zero-escape
event is the event that all root children have zero escape.  Its probability
is therefore a fixed point of the offspring generating function.  Positivity
of the mean raw escape (`integral_escapeRaw_pos`) rules out probability one, and a
supercritical offspring law has some mass at degree at least two, ruling out a fixed
point strictly between zero and one.  Rational upper biases and monotonicity give
the simultaneous statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL LPPMonotonicityProof.RTL.LocallyFinite

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- A supercritical offspring law gives positive mass to some degree at least two. -/
theorem exists_degree_ge_two (hμ : OffspringHyp μ) : ∃ k ≥ 2, μ {k} ≠ 0 := by
  by_contra h
  push Not at h
  have hmean : (∫⁻ k, (k : ℝ≥0∞) ∂μ) = ∑' k : ℕ, (k : ℝ≥0∞) * μ {k} :=
    lintegral_countable' _
  have hle : (∑' k : ℕ, (k : ℝ≥0∞) * μ {k}) ≤ ∑' k : ℕ, μ {k} := by
    apply ENNReal.tsum_le_tsum
    intro k
    rcases k with _ | _ | k
    · simp
    · simp
    · rw [h (k + 2) (by omega), mul_zero]
  have hm : 1 < ∑' k : ℕ, (k : ℝ≥0∞) * μ {k} := by
    simpa only [← hmean] using hμ.one_lt_mean
  exact (not_le_of_gt hm) (hle.trans_eq (tsum_measure_singleton μ))

/-- There is no offspring-generating-function fixed point strictly between zero
and one when the law is leafless and supercritical. -/
private theorem offspringGF_lt_self (hμ : OffspringHyp μ) {q : ℝ≥0∞}
    (hq0 : 0 < q) (hq1 : q < 1) : offspringGF μ q < q := by
  obtain ⟨j, hj2, hμj⟩ := exists_degree_ge_two hμ
  have hle : ∀ k : ℕ, μ {k} * q ^ k ≤ μ {k} * q := by
    intro k
    rcases k with _ | _ | k
    · simp [hμ.zero]
    · simp
    · gcongr
      simpa only [pow_one] using
        pow_le_pow_of_le_one zero_le hq1.le (show 1 ≤ k + 2 by omega)
  have hsum_lt : (∑' k : ℕ, μ {k} * q ^ k) < ∑' k : ℕ, μ {k} * q := by
    apply ENNReal.tsum_lt_tsum (i := j)
    · apply ne_top_of_le_ne_top (b := q) hq1.ne_top
      calc
        (∑' k : ℕ, μ {k} * q ^ k) ≤ ∑' k : ℕ, μ {k} * q :=
          ENNReal.tsum_le_tsum hle
        _ = q := by rw [ENNReal.tsum_mul_right, tsum_measure_singleton, one_mul]
    · exact hle
    · apply (ENNReal.mul_lt_mul_iff_right hμj (measure_ne_top μ {j})).2
      apply (ENNReal.toReal_lt_toReal (ENNReal.pow_ne_top hq1.ne_top) hq1.ne_top).mp
      have hqreal0 : 0 < q.toReal := ENNReal.toReal_pos hq0.ne' hq1.ne_top
      have hqreal1 : q.toReal < 1 := by
        simpa using (ENNReal.toReal_lt_toReal hq1.ne_top ENNReal.one_ne_top).2 hq1
      simpa only [ENNReal.toReal_pow, pow_one] using
        pow_lt_pow_right_of_lt_one₀ hqreal0 hqreal1 (show 1 < j by omega)
  simpa only [offspringGF, ENNReal.tsum_mul_right, tsum_measure_singleton, one_mul] using hsum_lt

private theorem escapeRaw_prune {ω : Offspring} {v : Address}
    (hv : Present (prune ω) v) (l : ℝ) :
    escapeRaw (prune ω).val l v = escapeRaw ω l v := by
  unfold escapeRaw
  congr 1
  funext N
  exact escapeN_prune ω hv l N

private theorem escape_prune (ω : Offspring) (l : ℝ) :
    escape l (prune ω) = escapeRaw ω l [] := by
  exact escapeRaw_prune (present_nil (prune ω)) l

private theorem measurableSet_escape_zero (l : ℝ) :
    MeasurableSet {T : Tree | escape l T = 0} :=
  measurableSet_eq_fun (measurable_escape l) measurable_const

private theorem measurableSet_escape_Ioo (l : ℝ) :
    MeasurableSet {T : Tree | 0 < escape l T ∧ escape l T < 1} :=
  (measurableSet_lt measurable_const (measurable_escape l)).inter
    (measurableSet_lt (measurable_escape l) measurable_const)

/-- At positive bias, escape vanishes exactly when every existing child escape vanishes. -/
private theorem escape_eq_zero_iff_children {l : ℝ} (hl : 0 < l) (T : Tree) :
    escape l T = 0 ↔ ∀ i : Fin (degree T), escape l (child T (i.val + 1)) = 0 := by
  have hsum_nonneg : 0 ≤ childSum l T := by
    apply Finset.sum_nonneg
    intro i _
    exact (escape_mem_Icc hl _).1
  have hden : l + childSum l T ≠ 0 := (add_pos_of_pos_of_nonneg hl hsum_nonneg).ne'
  rw [escape_eq hl T, div_eq_zero_iff, or_iff_left hden]
  change (∑ i : Fin (degree T), escape l (child T (i.val + 1))) = 0 ↔ _
  simpa using (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (fun (i : Fin (degree T)) _ => (escape_mem_Icc hl (child T (i.val + 1))).1))

private theorem escape_zero_eq_iUnion_childrenEvent {l : ℝ} (hl : 0 < l) :
    {T : Tree | escape l T = 0} =
      ⋃ k : ℕ, childrenEvent k fun _ => {T : Tree | escape l T = 0} := by
  ext T
  rw [Set.mem_ofPred_eq, Set.mem_iUnion, escape_eq_zero_iff_children hl T]
  constructor
  · intro h
    exact ⟨degree T, rfl, h⟩
  · rintro ⟨k, hk, hc⟩
    change degree T = k at hk
    subst k
    intro i
    exact hc i

private theorem offspringGF_measure_escape_zero {l : ℝ} (hl : 0 < l) :
    offspringGF μ (bienaymeLaw μ {T : Tree | escape l T = 0}) =
      bienaymeLaw μ {T : Tree | escape l T = 0} := by
  rw [← bienaymeLaw_iUnion_childrenEvent μ (measurableSet_escape_zero l),
    ← escape_zero_eq_iUnion_childrenEvent hl]

private theorem measure_escape_zero_lt_one (hμ : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    bienaymeLaw μ {T : Tree | escape l T = 0} < 1 := by
  apply lt_of_le_of_ne prob_le_one
  intro hq
  have hcompl : (bienaymeLaw μ) {T : Tree | escape l T = 0}ᶜ = 0 := by
    rw [measure_compl (measurableSet_escape_zero l) (measure_ne_top _ _), hq,
      measure_univ]
    simp
  have htree : ∀ᵐ T ∂bienaymeLaw μ, escape l T = 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hcompl] with T hT
    simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using hT
  change ∀ᵐ T ∂(offspringFieldLaw μ).map prune, escape l T = 0 at htree
  rw [MeasureTheory.ae_map_iff measurable_prune.aemeasurable
    (measurableSet_escape_zero l)] at htree
  have hraw : ∀ᵐ ω ∂offspringFieldLaw μ, escapeRaw ω l [] = 0 := by
    simpa only [escape_prune] using htree
  have hzero : (∫ ω, escapeRaw ω l [] ∂offspringFieldLaw μ) = 0 := by
    calc
      _ = ∫ _ω, (0 : ℝ) ∂offspringFieldLaw μ :=
        integral_congr_ae (hraw.mono fun _ h => by simp [h])
      _ = 0 := integral_zero _ _
  have hpos := integral_escapeRaw_pos hμ hl hlm
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

private theorem measure_escape_zero_eq_zero (hμ : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    bienaymeLaw μ {T : Tree | escape l T = 0} = 0 := by
  by_contra hq0
  have hqpos : 0 < bienaymeLaw μ {T : Tree | escape l T = 0} := pos_iff_ne_zero.mpr hq0
  have hlt := offspringGF_lt_self hμ hqpos (measure_escape_zero_lt_one hμ hl hlm)
  rw [offspringGF_measure_escape_zero hl] at hlt
  exact lt_irrefl _ hlt

/-- **Fixed-bias root positivity** on the pruned Bienaymé tree. -/
theorem ae_escape_pos (hμ : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ) :
    ∀ᵐ T ∂bienaymeLaw μ, 0 < escape l T := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_escape_zero_eq_zero hμ hl hlm)] with T hT
  exact lt_of_le_of_ne (escape_mem_Icc hl T).1 (Ne.symm hT)

/-- Fixed-bias root escape is almost surely strictly between zero and one. -/
theorem ae_escape_mem_Ioo (hμ : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ) :
    ∀ᵐ T ∂bienaymeLaw μ, 0 < escape l T ∧ escape l T < 1 := by
  filter_upwards [ae_escape_pos hμ hl hlm] with T hT
  exact ⟨hT, escape_lt_one hl T⟩

/-- **Fixed-bias positivity at every present vertex.** -/
theorem ae_escape_pos_subtrees (hμ : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) :
    ∀ᵐ T ∂bienaymeLaw μ, ∀ v, Present T v → 0 < escape l (subtree T v) := by
  exact ae_all_subtrees μ (measurableSet_lt measurable_const (measurable_escape l))
    (ae_escape_pos hμ hl hlm)

/-- At a fixed bias, every present subtree has escape strictly between zero and one. -/
theorem ae_escape_mem_Ioo_subtrees (hμ : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) :
    ∀ᵐ T ∂bienaymeLaw μ, ∀ v, Present T v →
      0 < escape l (subtree T v) ∧ escape l (subtree T v) < 1 := by
  exact ae_all_subtrees μ (measurableSet_escape_Ioo l) (ae_escape_mem_Ioo hμ hl hlm)

/-- Raw-field form of `ae_escape_pos` at the root, obtained through `prune`. -/
theorem ae_escapeRaw_pos (hμ : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ) :
    ∀ᵐ ω ∂offspringFieldLaw μ, 0 < escapeRaw ω l [] := by
  have h := ae_escape_pos hμ hl hlm
  change ∀ᵐ T ∂(offspringFieldLaw μ).map prune, 0 < escape l T at h
  simpa only [escape_prune] using
    (MeasureTheory.ae_of_ae_map measurable_prune.aemeasurable h)

/-- Raw-field fixed-bias root bounds, obtained through `prune`. -/
theorem ae_escapeRaw_mem_Ioo (hμ : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) :
    ∀ᵐ ω ∂offspringFieldLaw μ, 0 < escapeRaw ω l [] ∧ escapeRaw ω l [] < 1 := by
  have h := ae_escape_mem_Ioo hμ hl hlm
  change ∀ᵐ T ∂(offspringFieldLaw μ).map prune,
    0 < escape l T ∧ escape l T < 1 at h
  simpa only [escape_prune] using
    (MeasureTheory.ae_of_ae_map measurable_prune.aemeasurable h)

/-- Raw-field fixed-bias positivity at every address present after pruning. -/
theorem ae_escapeRaw_pos_subtrees (hμ : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) :
    ∀ᵐ ω ∂offspringFieldLaw μ, ∀ v, Present (prune ω) v → 0 < escapeRaw ω l v := by
  have h := ae_escape_pos_subtrees hμ hl hlm
  change ∀ᵐ T ∂(offspringFieldLaw μ).map prune,
    ∀ v, Present T v → 0 < escape l (subtree T v) at h
  filter_upwards [MeasureTheory.ae_of_ae_map measurable_prune.aemeasurable h] with ω hω v hv
  have hpos := hω v hv
  rwa [escape_subtree, escapeRaw_prune hv] at hpos

/-- **Simultaneous positivity and strict subunitarity.**  A rational bias
strictly above `l` and strictly below the mean gives a positive lower bound;
antitonicity transfers it to `l`. -/
theorem ae_escape_pos_all (hμ : OffspringHyp μ) :
    ∀ᵐ T ∂bienaymeLaw μ, ∀ l ∈ Set.Ioo 0 (mean μ), ∀ v, Present T v →
      0 < escape l (subtree T v) ∧ escape l (subtree T v) < 1 := by
  have hr : ∀ q : ℚ, ∀ᵐ T ∂bienaymeLaw μ,
      (0 < (q : ℝ) ∧ (q : ℝ) < mean μ) → ∀ v, Present T v →
        0 < escape (q : ℝ) (subtree T v) ∧ escape (q : ℝ) (subtree T v) < 1 := by
    intro q
    by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) < mean μ
    · filter_upwards [ae_escape_mem_Ioo_subtrees hμ hq.1 hq.2] with T hT
      exact fun _ => hT
    · exact ae_of_all _ fun _ h => (hq h).elim
  rw [← ae_all_iff] at hr
  filter_upwards [hr] with T hT l hl v hv
  obtain ⟨q, hlq, hqm⟩ := exists_rat_btwn hl.2
  have hq0 : 0 < (q : ℝ) := hl.1.trans hlq
  have hpos := (hT q ⟨hq0, hqm⟩ v hv).1
  exact ⟨hpos.trans_le (escape_antitoneOn (subtree T v) hl.1 hq0 hlq.le),
    escape_lt_one hl.1 (subtree T v)⟩

end LPPMonotonicityProof.Speed
