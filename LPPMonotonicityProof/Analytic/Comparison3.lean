module

public import LPPMonotonicityProof.Analytic.Comparison2
public import LPPMonotonicityProof.Analytic.Interface2
public import LPPMonotonicityProof.Analytic.Tools
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Moment comparison (Lemma 3.2, `lem:convex-order`)

This module completes the fixed-mean moment comparison of Lemma 3.2: every moment
`E Yⁿ`, `n ≥ 1`, is at most the matching moment `b / (λⁿ - 1 + b)` of the geometric
law with parameter `b = p_eff`.  The fixed root-degree fibers are split with the
root decomposition of `LPPMonotonicityProof.Analytic.Interface2` and the i.i.d.
splitting lemmas of `LPPMonotonicityProof.Analytic.Tools`; no dependent product of
tree laws is used.
-/

@[expose] public section

namespace LPPMonotonicityProof.Analytic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

private lemma integrable_bounded_ae {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ} (C : ℝ)
    (hf : AEMeasurable f ν) (hb : ∀ᵐ x ∂ν, ‖f x‖ ≤ C) : Integrable f ν := by
  exact Integrable.of_bound hf.aestronglyMeasurable C hb

private lemma Yt_bounds {l : ℝ} (hl : 1 < l) (T : Tree) :
    Yt l T ∈ Set.Icc 0 (1 / l) := by
  have hl0 : 0 < l := by linarith
  have hβ0 : 0 ≤ escape l T := (escape_mem_Icc hl0 T).1
  have hβ1 : escape l T < 1 := escape_lt_one hl0 T
  have hd : 0 < l - 1 + escape l T := by positivity
  constructor
  · exact div_nonneg hβ0 (by positivity)
  · rw [Yt, div_le_div_iff₀ hd hl0]
    nlinarith

private lemma Yt_lt_inv_own {l : ℝ} (hl : 1 < l) (T : Tree) : Yt l T < 1 / l := by
  have hl0 : 0 < l := by linarith
  have hd : 0 < l - 1 + escape l T := by
    have := (escape_mem_Icc hl0 T).1
    positivity
  rw [Yt, div_lt_div_iff₀ hd hl0]
  have hβ1 := escape_lt_one hl0 T
  have hβ0 := (escape_mem_Icc hl0 T).1
  nlinarith [mul_nonneg hβ0 (by linarith : 0 ≤ l - 1)]

private lemma ae_Yt_Icc (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : ∀ᵐ T ∂GW μ, Yt l T ∈ Set.Icc 0 1 := by
  filter_upwards [ae_escape_pos h (by linarith) hlm] with T hT
  have hy := Yt_mem hl hT
  exact ⟨hy.1.le, hy.2.le.trans ((div_le_one (by linarith)).2 (by linarith))⟩

private lemma ae_Yt_pi_Icc (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (k : ℕ) : ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => GW μ),
      ∀ i, Yt l (ts i) ∈ Set.Icc 0 1 := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (μ := fun _ : Fin k => GW μ) i).quasiMeasurePreserving.ae
    (ae_Yt_Icc μ h hl hlm)

private lemma integrable_Yt_pow (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : Integrable (fun T => Yt l T ^ n) (GW μ) := by
  apply integrable_bounded_ae 1 ((measurable_Yt l).pow_const n).aemeasurable
  filter_upwards [ae_Yt_Icc μ h hl hlm] with T hT
  rw [Real.norm_of_nonneg (pow_nonneg hT.1 _)]
  exact pow_le_one₀ hT.1 hT.2

private noncomputable def restOdds (l : ℝ) {k : ℕ} (ts : Fin k → Tree) : ℝ :=
  ∑ i, Yt l (ts i) / (1 - Yt l (ts i))

private noncomputable def resetFactor (l : ℝ) (y : ℝ) {k : ℕ} (ts : Fin k → Tree) : ℝ :=
  (1 + restOdds l ts * (1 - y))⁻¹

private noncomputable def resetMean (l : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  ∫ ts, resetFactor l y ts ∂Measure.pi (fun _ : Fin k => GW μ)

private noncomputable def tailWeight (μ : Measure ℕ) (k : ℕ) : ℝ := (μ {k + 1}).toReal

private noncomputable def meanReset (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (y : ℝ) : ℝ :=
  ∑' k : ℕ, tailWeight μ k * resetMean (μ := μ) l k y

private noncomputable def powSum (n : ℕ) (y : ℝ) : ℝ := ∑ j ∈ Finset.range n, y ^ j

private lemma summable_mass (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Summable fun k : ℕ => (μ {k}).toReal := by
  exact summable_measure_toReal (fun k => measurableSet_singleton k)
    (by
      intro i j hij
      exact Set.disjoint_left.mpr fun x hi hj => hij ((Set.mem_singleton_iff.mp hi).symm.trans
        (Set.mem_singleton_iff.mp hj)))

private lemma mass_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    ∑' k : ℕ, (μ {k}).toReal = 1 := by
  have hi := integral_countable (μ := μ) (f := fun _ : ℕ => (1 : ℝ)) (integrable_const 1)
  simpa [Measure.real] using hi.symm

private lemma summable_tailWeight (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Summable (tailWeight μ) := by
  exact (summable_nat_add_iff (f := fun k : ℕ => (μ {k}).toReal) 1).mpr (summable_mass μ)

private lemma tailWeight_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h : OffspringHyp μ) : ∑' k, tailWeight μ k = 1 := by
  calc
    ∑' k, tailWeight μ k = ∑' k : ℕ, (μ {k + 1}).toReal := rfl
    _ = (μ {0}).toReal + ∑' k : ℕ, (μ {k + 1}).toReal := by rw [h.zero]; simp
    _ = ∑' k : ℕ, (μ {k}).toReal := (summable_mass μ).tsum_eq_zero_add.symm
    _ = 1 := mass_tsum μ

private lemma restOdds_nonneg_of_mem {l : ℝ} {k : ℕ} (ts : Fin k → Tree)
    (hts : ∀ i, Yt l (ts i) ∈ Set.Icc 0 1) : 0 ≤ restOdds l ts := by
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (hts i).1 (sub_nonneg.mpr (hts i).2)

private lemma resetFactor_mem_of_mem {l : ℝ} {y : ℝ} (hy : y ∈ Set.Icc 0 1)
    {k : ℕ} (ts : Fin k → Tree) (hts : ∀ i, Yt l (ts i) ∈ Set.Icc 0 1) :
    resetFactor l y ts ∈ Set.Icc 0 1 := by
  have hr := restOdds_nonneg_of_mem ts hts
  have hd : 1 ≤ 1 + restOdds l ts * (1 - y) := by
    have := mul_nonneg hr (sub_nonneg.mpr hy.2)
    linarith
  exact ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ hd⟩

private lemma integrable_resetFactor (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {y : ℝ} (hy : y ∈ Set.Icc 0 1) (k : ℕ) :
    Integrable (resetFactor l y (k := k)) (Measure.pi (fun _ : Fin k => GW μ)) := by
  apply integrable_bounded_ae 1 (by
    apply Measurable.aemeasurable
    apply Measurable.inv
    apply Measurable.add measurable_const
    apply Measurable.mul _ measurable_const
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_Yt l).comp (measurable_pi_apply i)).div
      (measurable_const.sub ((measurable_Yt l).comp (measurable_pi_apply i))))
  filter_upwards [ae_Yt_pi_Icc μ h hl hlm k] with ts hts
  have hm := resetFactor_mem_of_mem hy ts hts
  rw [Real.norm_of_nonneg hm.1]
  exact hm.2

private lemma resetMean_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {y : ℝ} (hy : y ∈ Set.Icc 0 1) (k : ℕ) :
    resetMean (μ := μ) l k y ∈ Set.Icc 0 1 := by
  have hi := integrable_resetFactor μ h hl hlm hy k
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_Yt_pi_Icc μ h hl hlm k] with ts hts
    exact (resetFactor_mem_of_mem hy ts hts).1
  · calc
      resetMean (μ := μ) l k y ≤ ∫ _ts : Fin k → Tree, (1 : ℝ)
          ∂Measure.pi (fun _ : Fin k => GW μ) := by
        apply integral_mono_ae hi (integrable_const 1)
        filter_upwards [ae_Yt_pi_Icc μ h hl hlm k] with ts hts
        exact (resetFactor_mem_of_mem hy ts hts).2
      _ = 1 := by simp [Measure.real]

private lemma resetFactor_monotone {l : ℝ} {k : ℕ} (ts : Fin k → Tree)
    (hts : ∀ i, Yt l (ts i) ∈ Set.Icc 0 1) :
    MonotoneOn (fun y => resetFactor l y ts) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hr := restOdds_nonneg_of_mem ts hts
  have hdenx : 0 < 1 + restOdds l ts * (1 - x) := by
    have := mul_nonneg hr (sub_nonneg.mpr hx.2)
    linarith
  have hdeny : 0 < 1 + restOdds l ts * (1 - y) := by
    have := mul_nonneg hr (sub_nonneg.mpr hy.2)
    linarith
  dsimp [resetFactor]
  apply (inv_le_inv₀ hdenx hdeny).2
  have := mul_le_mul_of_nonneg_left hxy hr
  nlinarith

private lemma resetMean_monotone (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (k : ℕ) : MonotoneOn (resetMean (μ := μ) l k) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  apply integral_mono_ae (integrable_resetFactor μ h hl hlm hx k)
    (integrable_resetFactor μ h hl hlm hy k)
  filter_upwards [ae_Yt_pi_Icc μ h hl hlm k] with ts hts
  exact resetFactor_monotone ts hts hx hy hxy

private lemma meanReset_summable (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {y : ℝ} (hy : y ∈ Set.Icc 0 1) :
    Summable fun k => tailWeight μ k * resetMean (μ := μ) l k y := by
  apply (summable_tailWeight μ).of_nonneg_of_le
  · intro k
    exact mul_nonneg (ENNReal.toReal_nonneg) (resetMean_mem μ h hl hlm hy k).1
  · intro k
    change tailWeight μ k * resetMean (μ := μ) l k y ≤ tailWeight μ k
    simpa only [tailWeight, mul_one] using mul_le_mul_of_nonneg_left
      (resetMean_mem μ h hl hlm hy k).2 (ENNReal.toReal_nonneg)

private lemma meanReset_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {y : ℝ} (hy : y ∈ Set.Icc 0 1) :
    meanReset μ l y ∈ Set.Icc 0 1 := by
  have hs := meanReset_summable μ h hl hlm hy
  constructor
  · exact tsum_nonneg fun k => mul_nonneg ENNReal.toReal_nonneg
      (resetMean_mem μ h hl hlm hy k).1
  · calc
      meanReset μ l y ≤ ∑' k, tailWeight μ k * 1 :=
        hs.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left
          (resetMean_mem μ h hl hlm hy k).2 ENNReal.toReal_nonneg) (by simpa using summable_tailWeight μ)
      _ = 1 := by simpa using tailWeight_tsum μ h

private lemma meanReset_monotone (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : MonotoneOn (meanReset μ l) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  exact (meanReset_summable μ h hl hlm hx).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (resetMean_monotone μ h hl hlm k hx hy hxy)
      ENNReal.toReal_nonneg) (meanReset_summable μ h hl hlm hy)

private lemma measurable_resetMean (l : ℝ) (k : ℕ) : Measurable (resetMean (μ := μ) l k) := by
  apply StronglyMeasurable.measurable
  change StronglyMeasurable (fun y : ℝ => ∫ ts : Fin k → Tree,
    resetFactor l y ts ∂Measure.pi (fun _ : Fin k => GW μ))
  refine StronglyMeasurable.integral_prod_right'
    (ν := Measure.pi (fun _ : Fin k => GW μ))
    (f := fun p : ℝ × (Fin k → Tree) => resetFactor l p.1 p.2) ?_
  apply Measurable.stronglyMeasurable
  apply Measurable.inv
  apply Measurable.add measurable_const
  apply Measurable.mul _ (measurable_const.sub measurable_fst)
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_Yt l).comp ((measurable_pi_apply i).comp measurable_snd)).div
    (measurable_const.sub ((measurable_Yt l).comp ((measurable_pi_apply i).comp measurable_snd)))

private lemma measurable_meanReset (l : ℝ) : Measurable (meanReset μ l) := by
  unfold meanReset
  apply Measurable.tsum
  intro k
  exact measurable_const.mul (measurable_resetMean μ l k)


private lemma ae_Yt_range (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : ∀ᵐ T ∂GW μ, Yt l T ∈ Set.Ioo 0 (1 / l) := by
  filter_upwards [ae_escape_pos h (by linarith) hlm] with T hT
  exact Yt_mem hl hT

private lemma ae_Yt_pi_range (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (k : ℕ) : ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => GW μ),
      ∀ i, Yt l (ts i) ∈ Set.Ioo 0 (1 / l) := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (μ := fun _ : Fin k => GW μ) i).quasiMeasurePreserving.ae
    (ae_Yt_range μ h hl hlm)

private noncomputable def rootResidual (l : ℝ) (n : ℕ) (T : Tree) : ℝ :=
  1 - (l * Yt l T) ^ n

private noncomputable def fiberResidual (l : ℝ) (n : ℕ) {k : ℕ}
    (head : Tree) (tail : Fin k → Tree) : ℝ :=
  (1 - Yt l head) * resetFactor l (Yt l head) tail * powSum n (Yt l head)

private lemma split_odds {l : ℝ} (hl : 1 < l) (k : ℕ) (ts : Fin (k + 1) → Tree) :
    (∑ i : Fin (k + 1), Yt l (child (nodeFin (k + 1) ts) (i.val + 1)) /
      (1 - Yt l (child (nodeFin (k + 1) ts) (i.val + 1)))) =
      Yt l (ts 0) / (1 - Yt l (ts 0)) + restOdds l (Fin.tail ts) := by
  rw [Fin.sum_univ_succ]
  have h0 : Yt l (child (nodeFin (k + 1) ts) (0 + 1)) /
      (1 - Yt l (child (nodeFin (k + 1) ts) (0 + 1))) =
      Yt l (ts 0) / (1 - Yt l (ts 0)) := by
    simpa using congrArg (fun T : Tree => Yt l T / (1 - Yt l T))
      (children_nodeFin (k + 1) ts 0)
  have hs : (∑ i : Fin k, Yt l (child (nodeFin (k + 1) ts) (i.val + 1 + 1)) /
      (1 - Yt l (child (nodeFin (k + 1) ts) (i.val + 1 + 1)))) =
      restOdds l (Fin.tail ts) := by
    unfold restOdds
    apply Finset.sum_congr rfl
    intro i _
    simpa [Fin.tail] using congrArg (fun T : Tree =>
      Yt l T / (1 - Yt l T)) (children_nodeFin (k + 1) ts i.succ)
  simpa [Fin.val_succ] using congrArg₂ (· + ·) h0 hs

private lemma residual_split_identity (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {k : ℕ} (ts : Fin (k + 1) → Tree)
    (hts : ∀ i, Yt l (ts i) ∈ Set.Ioo 0 (1 / l)) :
    1 - l * Yt l (nodeFin (k + 1) ts) =
      (1 - Yt l (ts 0)) * resetFactor l (Yt l (ts 0)) (Fin.tail ts) := by
  have ha : 0 < l - 1 := by linarith
  have hl0 : 0 < l := by linarith
  have hy0 := hts 0
  have hy01 : Yt l (ts 0) < 1 := hy0.2.trans ((div_lt_one hl0).2 (by linarith))
  have hroot := additive_odds hl (nodeFin (k + 1) ts)
  have hroot' : l * Yt l (nodeFin (k + 1) ts) /
      (1 - l * Yt l (nodeFin (k + 1) ts)) =
      Yt l (ts 0) / (1 - Yt l (ts 0)) + restOdds l (Fin.tail ts) :=
    hroot.trans (split_odds hl k ts)
  have hyr := Yt_bounds hl (nodeFin (k + 1) ts)
  have hlyr : l * Yt l (nodeFin (k + 1) ts) < 1 := by
    have := mul_lt_mul_of_pos_left (Yt_lt_inv_own (l := l) hl (nodeFin (k + 1) ts)) hl0
    rwa [mul_one_div, div_self hl0.ne'] at this
  have hrest : 0 ≤ restOdds l (Fin.tail ts) := by
    apply restOdds_nonneg_of_mem
    intro i
    exact ⟨(hts i.succ).1.le, (hts i.succ).2.le.trans
      ((div_le_one hl0).2 (by linarith))⟩
  have hden : 0 < 1 + restOdds l (Fin.tail ts) * (1 - Yt l (ts 0)) := by
    have := mul_nonneg hrest (sub_nonneg.mpr hy01.le)
    linarith
  have hd0 : 1 - Yt l (ts 0) ≠ 0 := by linarith
  have hdr : 1 - l * Yt l (nodeFin (k + 1) ts) ≠ 0 := by linarith
  dsimp [resetFactor]
  field_simp [hd0, hdr, hden.ne'] at hroot' ⊢
  nlinarith [hroot']

private lemma residual_split_inequality (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {k : ℕ} (ts : Fin (k + 1) → Tree)
    (hts : ∀ i, Yt l (ts i) ∈ Set.Ioo 0 (1 / l)) (n : ℕ) :
    (1 - Yt l (ts 0)) * resetFactor l (Yt l (ts 0)) (Fin.tail ts) *
        powSum n (Yt l (ts 0)) ≤ rootResidual l n (nodeFin (k + 1) ts) := by
  have hl0 : 0 < l := by linarith
  have hid := residual_split_identity μ h hl hlm ts hts
  have hr : resetFactor l (Yt l (ts 0)) (Fin.tail ts) ∈ Set.Icc 0 1 := by
    apply resetFactor_mem_of_mem
    · exact ⟨(hts 0).1.le, (hts 0).2.le.trans ((div_le_one hl0).2 (by linarith))⟩
    · intro i
      exact ⟨(hts i.succ).1.le, (hts i.succ).2.le.trans ((div_le_one hl0).2 (by linarith))⟩
  have hy0l : Yt l (ts 0) ≤ l * Yt l (nodeFin (k + 1) ts) := by
    have hp : (1 - Yt l (ts 0)) * resetFactor l (Yt l (ts 0)) (Fin.tail ts) ≤
        1 - Yt l (ts 0) := by
      calc
        _ ≤ (1 - Yt l (ts 0)) * 1 := mul_le_mul_of_nonneg_left hr.2
          (sub_nonneg.mpr ((hts 0).2.le.trans ((div_le_one hl0).2 (by linarith))))
        _ = _ := mul_one _
    nlinarith [hid]
  have hly0 : 0 ≤ l * Yt l (nodeFin (k + 1) ts) :=
    mul_nonneg hl0.le (Yt_bounds hl _).1
  have hly1 : l * Yt l (nodeFin (k + 1) ts) ≤ 1 := by
    have hyr := (Yt_bounds hl (nodeFin (k + 1) ts)).2
    have := mul_le_mul_of_nonneg_left hyr hl0.le
    rwa [mul_one_div, div_self hl0.ne'] at this
  have hpow : powSum n (Yt l (ts 0)) ≤ powSum n (l * Yt l (nodeFin (k + 1) ts)) := by
    unfold powSum
    apply Finset.sum_le_sum
    intro j _
    exact pow_le_pow_left₀ (hts 0).1.le hy0l j
  unfold rootResidual
  calc
    _ = (1 - l * Yt l (nodeFin (k + 1) ts)) * powSum n (Yt l (ts 0)) := by rw [← hid]
    _ ≤ (1 - l * Yt l (nodeFin (k + 1) ts)) *
        powSum n (l * Yt l (nodeFin (k + 1) ts)) :=
      mul_le_mul_of_nonneg_left hpow (sub_nonneg.mpr hly1)
    _ = 1 - (l * Yt l (nodeFin (k + 1) ts)) ^ n := by
      unfold powSum
      simpa [mul_comm] using geom_sum_mul_neg (l * Yt l (nodeFin (k + 1) ts)) n

private lemma integrable_rootResidual {l : ℝ} (hl : 1 < l) (n : ℕ)
    {ν : Measure Tree} [IsProbabilityMeasure ν] : Integrable (rootResidual l n) ν := by
  apply integrable_bounded_ae 1
    ((measurable_const.sub ((measurable_const.mul (measurable_Yt l)).pow_const n))).aemeasurable
  apply Filter.Eventually.of_forall
  intro T
  have hy := Yt_bounds hl T
  have hly0 : 0 ≤ l * Yt l T := mul_nonneg (by linarith) hy.1
  have hly1 : l * Yt l T ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hy.2 (by linarith : 0 ≤ l)
    rwa [mul_one_div, div_self (by linarith : l ≠ 0)] at this
  change ‖1 - (l * Yt l T) ^ n‖ ≤ 1
  rw [Real.norm_of_nonneg (sub_nonneg.mpr (pow_le_one₀ hly0 hly1))]
  have hp := pow_nonneg hly0 n
  linarith

private lemma integrable_fiberResidual (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (k : ℕ) :
    Integrable (fun p : Tree × (Fin k → Tree) => fiberResidual l n p.1 p.2)
      ((GW μ).prod (Measure.pi fun _ : Fin k => GW μ)) := by
  have hm : Measurable (fun p : Tree × (Fin k → Tree) => fiberResidual l n p.1 p.2) := by
    have hy : Measurable (fun p : Tree × (Fin k → Tree) => Yt l p.1) :=
      (measurable_Yt l).comp measurable_fst
    have hfac : Measurable (fun p : Tree × (Fin k → Tree) =>
        resetFactor l (Yt l p.1) p.2) := by
      apply Measurable.inv
      apply Measurable.add measurable_const
      apply Measurable.mul _ (measurable_const.sub hy)
      apply Finset.measurable_sum
      intro i _
      have hti : Measurable (fun p : Tree × (Fin k → Tree) => Yt l (p.2 i)) :=
        (measurable_Yt l).comp ((measurable_pi_apply i).comp measurable_snd)
      exact hti.div (measurable_const.sub hti)
    apply Measurable.mul (Measurable.mul (measurable_const.sub hy) hfac)
    apply Finset.measurable_sum
    intro j _
    exact hy.pow_const j
  apply integrable_bounded_ae (n : ℝ) hm.aemeasurable
  have hh : ∀ᵐ p ∂(GW μ).prod (Measure.pi fun _ : Fin k => GW μ),
      p.1 ∈ {T | Yt l T ∈ Set.Ioo 0 (1 / l)} :=
    (Measure.quasiMeasurePreserving_fst (μ := GW μ)
      (ν := Measure.pi fun _ : Fin k => GW μ)).ae (ae_Yt_range μ h hl hlm)
  have ht : ∀ᵐ p ∂(GW μ).prod (Measure.pi fun _ : Fin k => GW μ),
      p.2 ∈ {ts | ∀ i, Yt l (ts i) ∈ Set.Ioo 0 (1 / l)} :=
    (Measure.quasiMeasurePreserving_snd (μ := GW μ)
      (ν := Measure.pi fun _ : Fin k => GW μ)).ae (ae_Yt_pi_range μ h hl hlm k)
  filter_upwards [hh, ht] with p hpY hpT
  have hy1 : Yt l p.1 < 1 := hpY.2.trans ((div_lt_one (by linarith)).2 (by linarith))
  have hreset := resetFactor_mem_of_mem (l := l) (y := Yt l p.1)
    ⟨hpY.1.le, hy1.le⟩ p.2 (fun i => ⟨(hpT i).1.le, (hpT i).2.le.trans
      ((div_le_one (by linarith)).2 (by linarith))⟩)
  have hpows : powSum n (Yt l p.1) ∈ Set.Icc 0 (n : ℝ) := by
    unfold powSum
    constructor
    · exact Finset.sum_nonneg fun j _ => pow_nonneg hpY.1.le _
    · calc
        _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => pow_le_one₀ hpY.1.le hy1.le
        _ = (n : ℝ) := by simp
  have hnonneg : 0 ≤ fiberResidual l n p.1 p.2 := by
    unfold fiberResidual
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hy1.le) hreset.1) hpows.1
  rw [Real.norm_of_nonneg hnonneg]
  unfold fiberResidual
  have hfactor : (1 - Yt l p.1) * resetFactor l (Yt l p.1) p.2 ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul (by linarith [hpY.1.le] : 1 - Yt l p.1 ≤ 1) hreset.2 hreset.1 (by positivity)
      _ = 1 := one_mul 1
  calc
    _ ≤ 1 * (n : ℝ) := mul_le_mul hfactor hpows.2 hpows.1 zero_le_one
    _ = (n : ℝ) := by ring

private lemma fixed_fiber_inequality (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (k : ℕ) :
    (∫ p : Tree × (Fin k → Tree), fiberResidual l n p.1 p.2
      ∂(GW μ).prod (Measure.pi fun _ : Fin k => GW μ)) ≤
    ∫ ts : Fin (k + 1) → Tree, rootResidual l n (nodeFin (k + 1) ts)
      ∂Measure.pi (fun _ : Fin (k + 1) => GW μ) := by
  have hRi := integrable_fiberResidual μ h hl hlm n k
  have hFi : Integrable (fun p : Tree × (Fin k → Tree) =>
      rootResidual l n (nodeFin (k + 1) (Fin.cons p.1 p.2)))
      ((GW μ).prod (Measure.pi fun _ : Fin k => GW μ)) := by
    have hc : Measurable (fun p : Tree × (Fin k → Tree) =>
        Fin.cons (α := fun _ => Tree) p.1 p.2) := by
      rw [measurable_pi_iff]
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact measurable_fst
      · exact (measurable_pi_apply j).comp measurable_snd
    have hrootm : Measurable (fun p : Tree × (Fin k → Tree) =>
        Yt l (nodeFin (k + 1) (Fin.cons p.1 p.2))) :=
      (measurable_Yt l).comp ((measurable_nodeFin (k + 1)).comp hc)
    apply integrable_bounded_ae 1
      (measurable_const.sub ((measurable_const.mul hrootm).pow_const n)).aemeasurable
    apply Filter.Eventually.of_forall
    intro p
    have hy := Yt_bounds hl (nodeFin (k + 1) (Fin.cons p.1 p.2))
    have hly0 : 0 ≤ l * Yt l (nodeFin (k + 1) (Fin.cons p.1 p.2)) :=
      mul_nonneg (by linarith) hy.1
    have hly1 : l * Yt l (nodeFin (k + 1) (Fin.cons p.1 p.2)) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hy.2 (by linarith : 0 ≤ l)
      rwa [mul_one_div, div_self (by linarith : l ≠ 0)] at this
    change ‖1 - (l * Yt l (nodeFin (k + 1) (Fin.cons p.1 p.2))) ^ n‖ ≤ 1
    rw [Real.norm_of_nonneg (sub_nonneg.mpr (pow_le_one₀ hly0 hly1))]
    have hp := pow_nonneg hly0 n
    linarith
  calc
    _ ≤ ∫ p : Tree × (Fin k → Tree),
        rootResidual l n (nodeFin (k + 1) (Fin.cons p.1 p.2))
        ∂(GW μ).prod (Measure.pi fun _ : Fin k => GW μ) := by
      apply integral_mono_ae hRi hFi
      have hh := (Measure.quasiMeasurePreserving_fst (μ := GW μ)
        (ν := Measure.pi fun _ : Fin k => GW μ)).ae (ae_Yt_range μ h hl hlm)
      have ht := (Measure.quasiMeasurePreserving_snd (μ := GW μ)
        (ν := Measure.pi fun _ : Fin k => GW μ)).ae (ae_Yt_pi_range μ h hl hlm k)
      filter_upwards [hh, ht] with p hpY hpT
      have hts : ∀ i, Yt l (Fin.cons (α := fun _ => Tree) p.1 p.2 i) ∈ Set.Ioo 0 (1 / l) := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hpY
        · exact hpT j
      simpa [fiberResidual] using residual_split_inequality μ h hl hlm
        (Fin.cons p.1 p.2) hts n
    _ = _ := by
      have hs := integral_pi_succ μ (fun head tail =>
        rootResidual l n (nodeFin (k + 1) (Fin.cons head tail))) hFi
      simpa using hs.symm


private lemma fixed_fiber_eq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (k : ℕ) :
    (∫ p : Tree × (Fin k → Tree), fiberResidual l n p.1 p.2
      ∂(GW μ).prod (Measure.pi fun _ : Fin k => GW μ)) =
    ∫ T, (1 - Yt l T) * powSum n (Yt l T) * resetMean (μ := μ) l k (Yt l T) ∂GW μ := by
  have hi := integrable_fiberResidual μ h hl hlm n k
  rw [show (fun p : Tree × (Fin k → Tree) => fiberResidual l n p.1 p.2) =
      (fun p => ((1 - Yt l p.1) * powSum n (Yt l p.1)) * resetFactor l (Yt l p.1) p.2) by
    funext p
    unfold fiberResidual
    ring] at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro T
  change (∫ ts : Fin k → Tree, ((1 - Yt l T) * powSum n (Yt l T)) *
      resetFactor l (Yt l T) ts ∂Measure.pi (fun _ : Fin k => GW μ)) = _
  rw [integral_const_mul (L := ℝ)]
  rfl

private lemma ae_fiber_good (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (k : ℕ) : ∀ᵐ p ∂(GW μ).prod (Measure.pi fun _ : Fin k => GW μ),
      Yt l p.1 ∈ Set.Ioo 0 (1 / l) ∧ ∀ i, Yt l (p.2 i) ∈ Set.Ioo 0 (1 / l) := by
  have hh := (Measure.quasiMeasurePreserving_fst (μ := GW μ)
    (ν := Measure.pi fun _ : Fin k => GW μ)).ae (ae_Yt_range μ h hl hlm)
  have ht := (Measure.quasiMeasurePreserving_snd (μ := GW μ)
    (ν := Measure.pi fun _ : Fin k => GW μ)).ae (ae_Yt_pi_range μ h hl hlm k)
  filter_upwards [hh, ht] with p hpY hpT
  exact ⟨hpY, hpT⟩

private lemma fiberResidual_bounds (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (k : ℕ) :
    ∀ᵐ p ∂(GW μ).prod (Measure.pi fun _ : Fin k => GW μ),
      0 ≤ fiberResidual l n p.1 p.2 ∧ fiberResidual l n p.1 p.2 ≤ (n : ℝ) := by
  filter_upwards [ae_fiber_good μ h hl hlm k] with p hp
  have hpY := hp.1
  have hpT := hp.2
  have hy1 : Yt l p.1 < 1 := hpY.2.trans ((div_lt_one (by linarith)).2 (by linarith))
  have hreset := resetFactor_mem_of_mem (l := l) (y := Yt l p.1)
    ⟨hpY.1.le, hy1.le⟩ p.2 (fun i => ⟨(hpT i).1.le, (hpT i).2.le.trans
      ((div_le_one (by linarith)).2 (by linarith))⟩)
  have hpows : powSum n (Yt l p.1) ∈ Set.Icc 0 (n : ℝ) := by
    unfold powSum
    constructor
    · exact Finset.sum_nonneg fun j _ => pow_nonneg hpY.1.le _
    · calc
        _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => pow_le_one₀ hpY.1.le hy1.le
        _ = (n : ℝ) := by simp
  constructor
  · exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hy1.le) hreset.1) hpows.1
  · have hfactor : (1 - Yt l p.1) * resetFactor l (Yt l p.1) p.2 ≤ 1 := by
      calc
        _ ≤ 1 * 1 := mul_le_mul (by linarith [hpY.1.le] : 1 - Yt l p.1 ≤ 1)
          hreset.2 hreset.1 (by positivity)
        _ = 1 := one_mul 1
    calc
      _ ≤ 1 * (n : ℝ) := mul_le_mul hfactor hpows.2 hpows.1 zero_le_one
      _ = (n : ℝ) := by ring

private lemma summable_weighted_integrals {F : ℕ → Type*} [∀ k, MeasurableSpace (F k)]
    (ν : ∀ k, Measure (F k)) [∀ k, IsProbabilityMeasure (ν k)]
    (w : ℕ → ℝ) (hw : Summable w) (hw0 : ∀ k, 0 ≤ w k)
    (f : ∀ k, F k → ℝ) (C : ℝ) (hi : ∀ k, Integrable (f k) (ν k))
    (h0 : ∀ k, 0 ≤ᵐ[ν k] f k) (hb : ∀ k, f k ≤ᵐ[ν k] fun _ => C) :
    Summable fun k => w k * ∫ x, f k x ∂ν k := by
  apply (hw.mul_right C).of_nonneg_of_le
  · intro k
    exact mul_nonneg (hw0 k) (integral_nonneg_of_ae (h0 k))
  · intro k
    apply mul_le_mul_of_nonneg_left _ (hw0 k)
    calc
      (∫ x, f k x ∂ν k) ≤ ∫ _x, C ∂ν k := integral_mono_ae (hi k) (integrable_const C) (hb k)
      _ = C := by simp [Measure.real]

private noncomputable def headFactor (l : ℝ) (n : ℕ) (k : ℕ) (T : Tree) : ℝ :=
  (1 - Yt l T) * powSum n (Yt l T) * resetMean (μ := μ) l k (Yt l T)

private lemma headFactor_bounds (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (k : ℕ) :
    ∀ᵐ T ∂GW μ, 0 ≤ headFactor (μ := μ) l n k T ∧ headFactor (μ := μ) l n k T ≤ (n : ℝ) := by
  filter_upwards [ae_Yt_range μ h hl hlm] with T hT
  have hy1 : Yt l T < 1 := hT.2.trans ((div_lt_one (by linarith)).2 (by linarith))
  have hy : Yt l T ∈ Set.Icc (0 : ℝ) 1 := ⟨hT.1.le, hy1.le⟩
  have hreset := resetMean_mem μ h hl hlm hy k
  have hpows : powSum n (Yt l T) ∈ Set.Icc 0 (n : ℝ) := by
    unfold powSum
    constructor
    · exact Finset.sum_nonneg fun j _ => pow_nonneg hT.1.le _
    · calc
        _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => pow_le_one₀ hT.1.le hy1.le
        _ = (n : ℝ) := by simp
  constructor
  · exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hy1.le) hpows.1) hreset.1
  · have hfactor : (1 - Yt l T) * powSum n (Yt l T) ≤ (n : ℝ) := by
      have hb : (1 - Yt l T) * powSum n (Yt l T) ≤ 1 * (n : ℝ) :=
        mul_le_mul (by linarith [hT.1.le] : 1 - Yt l T ≤ 1) hpows.2 hpows.1 zero_le_one
      simpa using hb
    unfold headFactor
    calc
      _ ≤ (n : ℝ) * resetMean (μ := μ) l k (Yt l T) :=
        mul_le_mul_of_nonneg_right hfactor hreset.1
      _ ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hreset.2 (by positivity : 0 ≤ (n : ℝ))
      _ = (n : ℝ) := mul_one _

private lemma integrable_headFactor (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (k : ℕ) : Integrable (headFactor (μ := μ) l n k) (GW μ) := by
  have hm : Measurable (headFactor (μ := μ) l n k) := by
    apply Measurable.mul
      (Measurable.mul (measurable_const.sub (measurable_Yt l)) _)
      ((measurable_resetMean μ l k).comp (measurable_Yt l))
    unfold powSum
    apply Finset.measurable_sum
    intro j _
    exact (measurable_Yt l).pow_const j
  apply integrable_bounded_ae (n : ℝ) hm.aemeasurable
  filter_upwards [headFactor_bounds μ h hl hlm n k] with T hT
  rw [Real.norm_of_nonneg hT.1]
  exact hT.2

private lemma integral_headFactor_tsum (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) :
    (∑' k, tailWeight μ k * ∫ T, headFactor (μ := μ) l n k T ∂GW μ) =
      ∫ T, (1 - Yt l T) * powSum n (Yt l T) * meanReset μ l (Yt l T) ∂GW μ := by
  let F : ℕ → Tree → ℝ := fun k T => tailWeight μ k * headFactor (μ := μ) l n k T
  have hFi (k : ℕ) : Integrable (F k) (GW μ) :=
    (integrable_headFactor μ h hl hlm n k).const_mul (tailWeight μ k)
  have hsum : Summable fun k => ∫ T, ‖F k T‖ ∂GW μ := by
    have hmajor : Summable (fun k => tailWeight μ k * (n : ℝ)) :=
      (summable_tailWeight μ).mul_right _
    apply hmajor.of_nonneg_of_le
    · intro k
      exact integral_nonneg fun T => norm_nonneg _
    · intro k
      calc
        (∫ T, ‖F k T‖ ∂GW μ) = tailWeight μ k * ∫ T, headFactor (μ := μ) l n k T ∂GW μ := by
          rw [integral_congr_ae (g := fun T => tailWeight μ k * headFactor (μ := μ) l n k T) ?_]
          · exact integral_const_mul (L := ℝ) _ _
          · filter_upwards [headFactor_bounds μ h hl hlm n k] with T hT
            change ‖tailWeight μ k * headFactor (μ := μ) l n k T‖ = _
            rw [Real.norm_eq_abs]
            exact abs_of_nonneg (mul_nonneg (show 0 ≤ tailWeight μ k from
              ENNReal.toReal_nonneg) hT.1)
        _ ≤ tailWeight μ k * (n : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          calc
            _ ≤ ∫ _T : Tree, (n : ℝ) ∂GW μ := integral_mono_ae
              (integrable_headFactor μ h hl hlm n k) (integrable_const _)
              ((headFactor_bounds μ h hl hlm n k).mono fun T hT => hT.2)
            _ = (n : ℝ) := by simp [Measure.real]
  calc
    (∑' k, tailWeight μ k * ∫ T, headFactor (μ := μ) l n k T ∂GW μ) =
        ∑' k, ∫ T, F k T ∂GW μ := by
      apply tsum_congr
      intro k
      exact (integral_const_mul (L := ℝ) _ _).symm
    _ = ∫ T, ∑' k, F k T ∂GW μ := integral_tsum_of_summable_integral_norm hFi hsum
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro T
      unfold F headFactor meanReset
      change (∑' k, tailWeight μ k * (((1 - Yt l T) * powSum n (Yt l T)) *
        resetMean (μ := μ) l k (Yt l T))) = (1 - Yt l T) * powSum n (Yt l T) *
          ∑' k, tailWeight μ k * resetMean (μ := μ) l k (Yt l T)
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      ring


private lemma rootResidual_bounds {l : ℝ} (hl : 1 < l) (n : ℕ) (T : Tree) :
    0 ≤ rootResidual l n T ∧ rootResidual l n T ≤ 1 := by
  have hy := Yt_bounds hl T
  have hly0 : 0 ≤ l * Yt l T := mul_nonneg (by linarith) hy.1
  have hly1 : l * Yt l T ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hy.2 (by linarith : 0 ≤ l)
    rwa [mul_one_div, div_self (by linarith : l ≠ 0)] at this
  have hp : (l * Yt l T) ^ n ∈ Set.Icc (0 : ℝ) 1 := ⟨pow_nonneg hly0 _, pow_le_one₀ hly0 hly1⟩
  exact ⟨sub_nonneg.mpr hp.2, by dsimp [rootResidual]; linarith [hp.1]⟩

private lemma integral_rootResidual (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : ∫ T, rootResidual l n T ∂GW μ = 1 - l ^ n * momY μ l n := by
  have hi : Integrable (fun T => l ^ n * Yt l T ^ n) (GW μ) :=
    (integrable_Yt_pow μ h hl hlm n).const_mul _
  rw [show rootResidual l n = fun T => 1 - l ^ n * Yt l T ^ n by
    funext T
    unfold rootResidual
    rw [mul_pow]]
  rw [integral_sub (integrable_const 1) hi, integral_const_mul (L := ℝ)]
  simp [Measure.real, momY]

private lemma integrable_node_rootResidual {l : ℝ} (hl : 1 < l) (n : ℕ) (k : ℕ) :
    Integrable (fun ts : Fin k → Tree => rootResidual l n (nodeFin k ts))
      (Measure.pi (fun _ : Fin k => GW μ)) := by
  have hrootm : Measurable (fun ts : Fin k → Tree => Yt l (nodeFin k ts)) :=
    (measurable_Yt l).comp (measurable_nodeFin k)
  apply integrable_bounded_ae 1
    (measurable_const.sub ((measurable_const.mul hrootm).pow_const n)).aemeasurable
  apply Filter.Eventually.of_forall
  intro ts
  have hy := rootResidual_bounds hl n (nodeFin k ts)
  exact Real.norm_of_nonneg hy.1 ▸ hy.2

private lemma root_integral_tail_tsum (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) :
    (∫ T, rootResidual l n T ∂GW μ) = ∑' k, tailWeight μ k *
      ∫ ts : Fin (k + 1) → Tree, rootResidual l n (nodeFin (k + 1) ts)
        ∂Measure.pi (fun _ : Fin (k + 1) => GW μ) := by
  have hs : Summable fun k : ℕ => (μ {k}).toReal *
      ∫ ts : Fin k → Tree, rootResidual l n (nodeFin k ts)
        ∂Measure.pi (fun _ : Fin k => GW μ) := by
    apply summable_weighted_integrals
      (fun k => Measure.pi (fun _ : Fin k => GW μ)) (fun k => (μ {k}).toReal)
      (summable_mass μ) (fun k => ENNReal.toReal_nonneg)
      (fun k ts => rootResidual l n (nodeFin k ts)) 1
    · intro k
      exact integrable_node_rootResidual (μ := μ) hl n k
    · intro k
      exact Filter.Eventually.of_forall fun ts => (rootResidual_bounds hl n _).1
    · intro k
      exact Filter.Eventually.of_forall fun ts => (rootResidual_bounds hl n _).2
  rw [integral_GW_eq_tsum (rootResidual l n) (integrable_rootResidual hl n),
    hs.tsum_eq_zero_add, h.zero]
  simp only [ENNReal.toReal_zero, zero_mul, zero_add]
  rfl

private lemma fixed_fiber_identity_one (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (k : ℕ) :
    (∫ T, headFactor (μ := μ) l 1 k T ∂GW μ) =
      ∫ ts : Fin (k + 1) → Tree, rootResidual l 1 (nodeFin (k + 1) ts)
        ∂Measure.pi (fun _ : Fin (k + 1) => GW μ) := by
  unfold headFactor
  rw [← fixed_fiber_eq μ h hl hlm 1 k]
  have hRi := integrable_fiberResidual μ h hl hlm 1 k
  have hFi : Integrable (fun p : Tree × (Fin k → Tree) =>
      rootResidual l 1 (nodeFin (k + 1) (Fin.cons p.1 p.2)))
      ((GW μ).prod (Measure.pi fun _ : Fin k => GW μ)) := by
    have hc : Measurable (fun p : Tree × (Fin k → Tree) =>
        Fin.cons (α := fun _ => Tree) p.1 p.2) := by
      rw [measurable_pi_iff]
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact measurable_fst
      · exact (measurable_pi_apply j).comp measurable_snd
    have hrootm : Measurable (fun p : Tree × (Fin k → Tree) =>
        Yt l (nodeFin (k + 1) (Fin.cons p.1 p.2))) :=
      (measurable_Yt l).comp ((measurable_nodeFin (k + 1)).comp hc)
    apply integrable_bounded_ae 1
      (measurable_const.sub ((measurable_const.mul hrootm).pow_const 1)).aemeasurable
    apply Filter.Eventually.of_forall
    intro p
    have hy := rootResidual_bounds hl 1 (nodeFin (k + 1) (Fin.cons p.1 p.2))
    exact Real.norm_of_nonneg hy.1 ▸ hy.2
  calc
    _ = ∫ p : Tree × (Fin k → Tree),
        rootResidual l 1 (nodeFin (k + 1) (Fin.cons p.1 p.2))
        ∂(GW μ).prod (Measure.pi fun _ : Fin k => GW μ) := by
      apply integral_congr_ae
      filter_upwards [ae_fiber_good μ h hl hlm k] with p hp
      have hts : ∀ i, Yt l (Fin.cons (α := fun _ => Tree) p.1 p.2 i) ∈ Set.Ioo 0 (1 / l) := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hp.1
        · exact hp.2 j
      have hid := residual_split_identity μ h hl hlm (Fin.cons p.1 p.2) hts
      simpa [fiberResidual, headFactor, powSum, rootResidual, pow_one] using hid.symm
    _ = _ := by
      have hs := integral_pi_succ μ (fun head tail =>
        rootResidual l 1 (nodeFin (k + 1) (Fin.cons head tail))) hFi
      simpa using hs.symm

/-- The integrated one-child lower bound on every fixed root-degree fiber. -/
private lemma global_residual_bound (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) :
    ∫ T, (1 - Yt l T) * powSum n (Yt l T) * meanReset μ l (Yt l T) ∂GW μ ≤
      1 - l ^ n * momY μ l n := by
  let R : ℕ → ℝ := fun k => ∫ p : Tree × (Fin k → Tree), fiberResidual l n p.1 p.2
    ∂(GW μ).prod (Measure.pi fun _ : Fin k => GW μ)
  let F : ℕ → ℝ := fun k => ∫ ts : Fin (k + 1) → Tree,
    rootResidual l n (nodeFin (k + 1) ts) ∂Measure.pi (fun _ : Fin (k + 1) => GW μ)
  have hRs : Summable fun k => tailWeight μ k * R k := by
    apply summable_weighted_integrals
      (fun k => (GW μ).prod (Measure.pi fun _ : Fin k => GW μ)) (tailWeight μ)
      (summable_tailWeight μ) (fun k => ENNReal.toReal_nonneg) (fun k p => fiberResidual l n p.1 p.2) (n : ℝ)
    · intro k
      exact integrable_fiberResidual μ h hl hlm n k
    · intro k
      exact (fiberResidual_bounds μ h hl hlm n k).mono fun p hp => hp.1
    · intro k
      exact (fiberResidual_bounds μ h hl hlm n k).mono fun p hp => hp.2
  have hFs : Summable fun k => tailWeight μ k * F k := by
    apply summable_weighted_integrals
      (fun k => Measure.pi (fun _ : Fin (k + 1) => GW μ)) (tailWeight μ)
      (summable_tailWeight μ) (fun k => ENNReal.toReal_nonneg)
      (fun k ts => rootResidual l n (nodeFin (k + 1) ts)) 1
    · intro k
      exact integrable_node_rootResidual (μ := μ) hl n (k + 1)
    · intro k
      exact Filter.Eventually.of_forall fun ts => (rootResidual_bounds hl n _).1
    · intro k
      exact Filter.Eventually.of_forall fun ts => (rootResidual_bounds hl n _).2
  have hle : (∑' k, tailWeight μ k * R k) ≤ ∑' k, tailWeight μ k * F k := by
    apply hRs.tsum_le_tsum _ hFs
    intro k
    exact mul_le_mul_of_nonneg_left (fixed_fiber_inequality μ h hl hlm n k)
      ENNReal.toReal_nonneg
  rw [← integral_rootResidual μ h hl hlm n, root_integral_tail_tsum μ h hl hlm n,
    ← integral_headFactor_tsum μ h hl hlm n]
  calc
    _ ≤ ∑' k, tailWeight μ k * R k := by
      apply le_of_eq
      apply tsum_congr
      intro k
      dsimp only [R]
      exact congrArg (fun x : ℝ => tailWeight μ k * x)
        (fixed_fiber_eq μ h hl hlm n k).symm
    _ ≤ _ := hle

private lemma meanReset_integral (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    ∫ T, (1 - Yt l T) * meanReset μ l (Yt l T) ∂GW μ = 1 - l * muY μ l := by
  have hroot := root_integral_tail_tsum μ h hl hlm 1
  have hswap := integral_headFactor_tsum μ h hl hlm 1
  have heq : ∫ T, rootResidual l 1 T ∂GW μ =
      ∫ T, (1 - Yt l T) * meanReset μ l (Yt l T) ∂GW μ := by
    calc
      _ = ∑' k, tailWeight μ k * ∫ ts : Fin (k + 1) → Tree,
          rootResidual l 1 (nodeFin (k + 1) ts)
          ∂Measure.pi (fun _ : Fin (k + 1) => GW μ) := hroot
      _ = ∑' k, tailWeight μ k * ∫ T, headFactor (μ := μ) l 1 k T ∂GW μ := by
        apply tsum_congr
        intro k
        rw [fixed_fiber_identity_one μ h hl hlm k]
      _ = ∫ T, (1 - Yt l T) * powSum 1 (Yt l T) * meanReset μ l (Yt l T) ∂GW μ := hswap
      _ = _ := by simp [powSum]
  have hm : momY μ l 1 = muY μ l := by simp only [momY, muY, pow_one]
  have hi := integral_rootResidual μ h hl hlm 1
  rw [hm] at hi
  calc
    _ = ∫ T, rootResidual l 1 T ∂GW μ := heq.symm
    _ = 1 - l ^ 1 * muY μ l := hi
    _ = _ := by rw [pow_one]


private noncomputable def tiltDensity (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (T : Tree) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - Yt l T) / (1 - muY μ l))

private noncomputable def tiltLaw (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) : Measure Tree := (GW μ).withDensity (tiltDensity μ l)

private lemma measurable_tiltDensity (l : ℝ) : Measurable (tiltDensity μ l) := by
  apply ENNReal.measurable_ofReal.comp
  exact (measurable_const.sub (measurable_Yt l)).div_const _

private lemma tiltLaw_absolutelyContinuous (l : ℝ) : tiltLaw μ l ≪ GW μ := by
  exact withDensity_absolutelyContinuous _ _

private lemma integral_tiltLaw (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (f : Tree → ℝ) :
    ∫ T, f T ∂tiltLaw μ l =
      ∫ T, ((1 - Yt l T) / (1 - muY μ l)) * f T ∂GW μ := by
  unfold tiltLaw
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_tiltDensity μ l)
    (Filter.Eventually.of_forall fun T => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  filter_upwards [ae_Yt_range μ h hl hlm] with T hT
  have hy1 : Yt l T < 1 := hT.2.trans ((div_lt_one (by linarith)).2 (by linarith))
  have hm1 : muY μ l < 1 := (muY_mem μ h hl hlm).2.trans
    ((div_lt_one (by linarith)).2 (by linarith))
  dsimp only [tiltDensity]
  rw [ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr hy1.le) (sub_nonneg.mpr hm1.le))]
  change ((1 - Yt l T) / (1 - muY μ l)) * f T = _
  rfl

private lemma tiltLaw_probability (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : IsProbabilityMeasure (tiltLaw μ l) := by
  have hm : 0 < muY μ l ∧ muY μ l < 1 := by
    have hm' := muY_mem μ h hl hlm
    exact ⟨hm'.1, hm'.2.trans ((div_lt_one (by linarith)).2 (by linarith))⟩
  have hy : Integrable (Yt l) (GW μ) := by simpa using integrable_Yt_pow μ h hl hlm 1
  apply isProbabilityMeasure_iff_real.2
  have hmass : (∫ T, ((1 - Yt l T) / (1 - muY μ l)) * (1 : ℝ) ∂GW μ) = 1 := by
    have hi : Integrable (fun T => (1 - Yt l T) / (1 - muY μ l)) (GW μ) :=
      ((integrable_const 1).sub hy).div_const _
    simp only [mul_one]
    rw [show (fun T => (1 - Yt l T) / (1 - muY μ l)) =
        fun T => (1 - muY μ l)⁻¹ * (1 - Yt l T) by funext T; ring,
      integral_const_mul (L := ℝ), integral_sub (integrable_const 1) hy]
    have hone : ∫ _T : Tree, (1 : ℝ) ∂GW μ = 1 := by simp [Measure.real]
    rw [hone]
    change (1 - muY μ l)⁻¹ * (1 - muY μ l) = 1
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hm.2.ne')
  rw [show (tiltLaw μ l).real Set.univ = ∫ T, (1 : ℝ) ∂tiltLaw μ l by
    rw [integral_const]; simp [Measure.real]]
  rw [integral_tiltLaw μ h hl hlm]
  exact hmass

private lemma integrable_on_tilt_of_bound (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {f : Tree → ℝ} (C : ℝ) (hf : Measurable f)
    (hb : ∀ᵐ T ∂GW μ, ‖f T‖ ≤ C) : Integrable f (tiltLaw μ l) := by
  letI : IsProbabilityMeasure ((GW μ).withDensity (tiltDensity μ l)) :=
    tiltLaw_probability μ h hl hlm
  apply integrable_bounded_ae C (hf.aemeasurable.mono_ac
    (withDensity_absolutelyContinuous (GW μ) (tiltDensity μ l)))
  exact (withDensity_absolutelyContinuous (GW μ) (tiltDensity μ l)).ae_le hb

private lemma tilt_meanReset (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : ∫ T, meanReset μ l (Yt l T) ∂tiltLaw μ l = 1 - peff μ l := by
  have hm : 0 < muY μ l ∧ muY μ l < 1 := by
    have hm' := muY_mem μ h hl hlm
    exact ⟨hm'.1, hm'.2.trans ((div_lt_one (by linarith)).2 (by linarith))⟩
  rw [integral_tiltLaw μ h hl hlm]
  have heq : (∫ T, (1 - Yt l T) / (1 - muY μ l) * meanReset μ l (Yt l T) ∂GW μ) =
      (1 - l * muY μ l) / (1 - muY μ l) := by
    rw [show (fun T => (1 - Yt l T) / (1 - muY μ l) * meanReset μ l (Yt l T)) =
      fun T => (1 - muY μ l)⁻¹ * ((1 - Yt l T) * meanReset μ l (Yt l T)) by
        funext T; ring, integral_const_mul (L := ℝ), meanReset_integral μ h hl hlm]
    ring
  rw [heq]
  unfold peff
  field_simp [sub_ne_zero.mpr hm.2.ne'] <;> ring_nf

private lemma tilt_powSum (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) :
    ∫ T, powSum n (Yt l T) ∂tiltLaw μ l = (1 - momY μ l n) / (1 - muY μ l) := by
  have hm : 0 < muY μ l ∧ muY μ l < 1 := by
    have hm' := muY_mem μ h hl hlm
    exact ⟨hm'.1, hm'.2.trans ((div_lt_one (by linarith)).2 (by linarith))⟩
  rw [integral_tiltLaw μ h hl hlm]
  have hi : Integrable (fun T => (1 - momY μ l n) / (1 - muY μ l)) (GW μ) := integrable_const _
  have heq : (∫ T, (1 - Yt l T) / (1 - muY μ l) * powSum n (Yt l T) ∂GW μ) =
      ∫ T, (1 - muY μ l)⁻¹ * (1 - Yt l T ^ n) ∂GW μ := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro T
    have hg := geom_sum_mul_neg (Yt l T) n
    calc
      (1 - Yt l T) / (1 - muY μ l) * powSum n (Yt l T) =
          ((1 - Yt l T) * powSum n (Yt l T)) / (1 - muY μ l) := by ring
      _ = (1 - Yt l T ^ n) / (1 - muY μ l) := by
        rw [show (1 - Yt l T) * powSum n (Yt l T) = 1 - Yt l T ^ n by
          unfold powSum
          nlinarith [hg]]
      _ = (1 - muY μ l)⁻¹ * (1 - Yt l T ^ n) := by ring
  rw [heq, integral_const_mul (L := ℝ), integral_sub (integrable_const 1)
    (integrable_Yt_pow μ h hl hlm n)]
  simp only [integral_const, probReal_univ, one_smul]
  change (1 - muY μ l)⁻¹ * (1 - momY μ l n) = _
  ring

private lemma tilted_covariance (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) :
    (1 - peff μ l) * (1 - momY μ l n) ≤
      ∫ T, (1 - Yt l T) * powSum n (Yt l T) * meanReset μ l (Yt l T) ∂GW μ := by
  letI := tiltLaw_probability μ h hl hlm
  let P := tiltLaw μ l
  let Z : Tree → ℝ := Yt l
  let A : ℝ → ℝ := powSum n
  let H : ℝ → ℝ := meanReset μ l
  have hZ : ∀ᵐ T ∂P, Z T ∈ Set.Icc (0 : ℝ) 1 := by
    exact (withDensity_absolutelyContinuous (GW μ) (tiltDensity μ l)).ae_le (ae_Yt_Icc μ h hl hlm)
  have hA : MonotoneOn A (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    unfold A powSum
    exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hx.1 hxy j
  have hH : MonotoneOn H (Set.Icc (0 : ℝ) 1) := meanReset_monotone μ h hl hlm
  have hAi : Integrable (A ∘ Z) P := by
    apply integrable_on_tilt_of_bound μ h hl hlm (n : ℝ)
    · change Measurable (fun T => ∑ j ∈ Finset.range n, Yt l T ^ j)
      apply Finset.measurable_sum
      intro j _
      exact (measurable_Yt l).pow_const j
    · filter_upwards [ae_Yt_Icc μ h hl hlm] with T hT
      change ‖powSum n (Yt l T)‖ ≤ (n : ℝ)
      unfold powSum
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => pow_nonneg hT.1 _)]
      calc
        _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => pow_le_one₀ hT.1 hT.2
        _ = (n : ℝ) := by simp
  have hHi : Integrable (H ∘ Z) P := by
    apply integrable_on_tilt_of_bound μ h hl hlm 1
      ((measurable_meanReset μ l).comp (measurable_Yt l))
    filter_upwards [ae_Yt_Icc μ h hl hlm] with T hT
    have hb := meanReset_mem μ h hl hlm hT
    exact Real.norm_of_nonneg hb.1 ▸ hb.2
  have hAHi : Integrable (fun T => A (Z T) * H (Z T)) P := by
    apply integrable_on_tilt_of_bound μ h hl hlm (n : ℝ) (by
      apply Measurable.mul _ ((measurable_meanReset μ l).comp (measurable_Yt l))
      apply Finset.measurable_sum
      intro j _
      exact (measurable_Yt l).pow_const j)
    filter_upwards [ae_Yt_Icc μ h hl hlm] with T hT
    have hHb := meanReset_mem μ h hl hlm hT
    have hA0 : 0 ≤ A (Z T) := Finset.sum_nonneg fun j _ => pow_nonneg hT.1 _
    have hA1 : A (Z T) ≤ (n : ℝ) := by
      unfold A powSum Z
      calc
        _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => pow_le_one₀ hT.1 hT.2
        _ = (n : ℝ) := by simp
    rw [Real.norm_of_nonneg (mul_nonneg hA0 hHb.1)]
    exact (mul_le_mul hA1 hHb.2 hHb.1 (by positivity)).trans_eq (by ring)
  have hcov := integral_mul_ge_of_monotone (P := P) (Z := Z) (Set.Icc 0 1)
    hZ hA hH hAi hHi hAHi
  have hm : 0 < 1 - muY μ l := by
    have hm' := (muY_mem μ h hl hlm).2.trans ((div_lt_one (by linarith)).2 (by linarith))
    linarith
  have hAura : ∫ T, A (Z T) ∂P = (1 - momY μ l n) / (1 - muY μ l) :=
    tilt_powSum μ h hl hlm n
  have hHura : ∫ T, H (Z T) ∂P = 1 - peff μ l := tilt_meanReset μ h hl hlm
  rw [hAura, hHura] at hcov
  have hmull := mul_le_mul_of_nonneg_right hcov hm.le
  have hprod : (∫ T, A (Z T) * H (Z T) ∂P) =
      ∫ T, (1 - Yt l T) / (1 - muY μ l) *
        (powSum n (Yt l T) * meanReset μ l (Yt l T)) ∂GW μ :=
    integral_tiltLaw μ h hl hlm _
  calc
    (1 - peff μ l) * (1 - momY μ l n) =
        ((1 - momY μ l n) / (1 - muY μ l)) * (1 - peff μ l) * (1 - muY μ l) := by
      field_simp [hm.ne']
    _ ≤ (∫ T, A (Z T) * H (Z T) ∂P) * (1 - muY μ l) := hmull
    _ = ∫ T, (1 - Yt l T) * powSum n (Yt l T) * meanReset μ l (Yt l T) ∂GW μ := by
      rw [hprod, show (fun T => (1 - Yt l T) / (1 - muY μ l) *
        (powSum n (Yt l T) * meanReset μ l (Yt l T))) = fun T =>
          (1 - muY μ l)⁻¹ * ((1 - Yt l T) * powSum n (Yt l T) * meanReset μ l (Yt l T)) by
            funext T; ring, integral_const_mul (L := ℝ)]
      field_simp [hm.ne']

/-- **Lemma 3.2** (`lem:convex-order`): every positive transformed-escape moment is
dominated by the matching geometric moment. -/
theorem momY_le_geom (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (hn : 1 ≤ n) :
    momY μ l n ≤ peff μ l / (l ^ n - 1 + peff μ l) := by
  have hb := peff_mem μ h hl hlm
  have hcov := tilted_covariance μ h hl hlm n
  have hg := global_residual_bound μ h hl hlm n
  have hden : 0 < l ^ n - 1 + peff μ l := by
    have hl' : 1 < l ^ n := one_lt_pow₀ hl (by omega)
    exact add_pos (by linarith) hb.1
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Lemma 3.2 (`lem:convex-order`): normalized second-moment bound. -/
theorem momY_two_div_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : momY μ l 2 / muY μ l ≤ (1 + l * (1 - muY μ l))⁻¹ := by
  have hm : 0 < muY μ l ∧ muY μ l < 1 := by
    have hm' := muY_mem μ h hl hlm
    exact ⟨hm'.1, hm'.2.trans ((div_lt_one (by linarith)).2 (by linarith))⟩
  have hb := peff_mem μ h hl hlm
  have hmom := momY_le_geom μ h hl hlm 2 (by omega)
  have hd : 0 < l ^ 2 - 1 + peff μ l := by
    have hl2 : 0 < l ^ 2 - 1 := by nlinarith [mul_lt_mul_of_pos_left hl (by linarith : 0 < l)]
    exact add_pos hl2 hb.1
  have ht : 0 < 1 + l * (1 - muY μ l) := by
    nlinarith [mul_pos (by linarith : 0 < l) (sub_pos.mpr hm.2)]
  calc
    momY μ l 2 / muY μ l ≤ (peff μ l / (l ^ 2 - 1 + peff μ l)) / muY μ l :=
      div_le_div_of_nonneg_right hmom hm.1.le
    _ = (1 + l * (1 - muY μ l))⁻¹ := by
      rw [div_div, inv_eq_one_div,
        div_eq_div_iff (mul_ne_zero hd.ne' hm.1.ne') ht.ne']
      unfold peff
      field_simp [sub_ne_zero.mpr hm.2.ne'] <;> ring_nf

end LPPMonotonicityProof.Analytic
