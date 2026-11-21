module

public import LPPMonotonicityProof.Analytic.ChildResponse.PrefixAverage
public import LPPMonotonicityProof.Analytic.Interface2

/-!
# Averaging at the first split

This module averages the child-response recursion over the children of the split,
giving `Bₙ ≥ M_* x (ιₙ Bₙ + Aₙ² ηₙ)` from the proof of Lemma 4.5
(`lem:scaled-two-children`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private noncomputable def siblingFactor (l : ℝ) {k : ℕ} (us : Fin k → Tree) : ℝ :=
  (l - 1) / (l - 1 + ∑ j, escape l (us j))

/-- The weight of the marked child uses only the other coordinates. -/
private theorem deltaChild_nodeFin_removeNth (l : ℝ) {k : ℕ}
    (i : Fin (k + 1)) (ts : Fin (k + 1) → Tree) :
    deltaChild l (nodeFin (k + 1) ts) (i.val + 1) = siblingFactor l (i.removeNth ts) := by
  rw [deltaChild, childSum_nodeFin, children_nodeFin,
    Fin.sum_univ_succAbove (fun j => escape l (ts j)) i]
  unfold siblingFactor
  simp only [Fin.removeNth]
  congr 1
  ring

private theorem integral_childResponse_coord {l : ℝ} (n : ℕ) {k : ℕ}
    (i : Fin (k + 1)) :
    (∫ ts, deltaChild l (nodeFin (k + 1) ts) (i.val + 1) ^ 2 * childTerm l n (ts i)
        ∂Measure.pi (fun _ : Fin (k + 1) => GW μ)) =
      (∫ ts, deltaChild l (nodeFin (k + 1) ts) (i.val + 1) ^ 2
        ∂Measure.pi (fun _ : Fin (k + 1) => GW μ)) *
        (∫ T, childTerm l n T ∂GW μ) := by
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => GW μ) i
  let g : (Fin k → Tree) → ℝ := fun us => siblingFactor l us ^ 2
  have hw := he.integral_comp' (fun p : Tree × (Fin k → Tree) => (1 : ℝ) * g p.2)
  have hf := he.integral_comp' (fun p : Tree × (Fin k → Tree) => childTerm l n p.1 * g p.2)
  change (∫ ts, 1 * g (i.removeNth ts) ∂Measure.pi (fun _ : Fin (k + 1) => GW μ)) =
    _ at hw
  change (∫ ts, childTerm l n (ts i) * g (i.removeNth ts)
    ∂Measure.pi (fun _ : Fin (k + 1) => GW μ)) = _ at hf
  rw [integral_prod_mul (fun _ : Tree => (1 : ℝ)) g] at hw
  rw [integral_prod_mul (childTerm l n) g] at hf
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hw
  simp_rw [deltaChild_nodeFin_removeNth]
  change (∫ ts, g (i.removeNth ts) * childTerm l n (ts i)
    ∂Measure.pi (fun _ : Fin (k + 1) => GW μ)) = _
  calc
    _ = ∫ ts, childTerm l n (ts i) * g (i.removeNth ts)
        ∂Measure.pi (fun _ : Fin (k + 1) => GW μ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
    _ = _ := hf
    _ = _ := by rw [← hw, mul_comm]

private noncomputable def splitChildResponse (l : ℝ) (n : ℕ) (T : Tree) : ℝ :=
  ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2 * childTerm l n (child T (i + 1))

private noncomputable def splitResponseWeight (l : ℝ) (T : Tree) : ℝ :=
  ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2

private theorem measurable_splitChildResponse (l : ℝ) (n : ℕ) :
    Measurable (splitChildResponse l n) := by
  have hchild (j : ℕ) : Measurable (fun T : Tree => child T (j + 1)) :=
    measurable_child.comp ((measurable_const (a := j + 1)).prodMk measurable_id)
  have hm : Measurable (fun p : ℕ × Tree =>
      ∑ j ∈ Finset.range p.1, deltaChild l p.2 (j + 1) ^ 2 * childTerm l n (child p.2 (j + 1))) :=
    measurable_from_prod_countable_right fun k =>
      (Finset.range k).measurable_sum fun j _ =>
        ((measurable_deltaChild l (j + 1)).pow_const 2).mul
          ((measurable_childTerm l n).comp (hchild j))
  convert hm.comp (continuous_degree.measurable.prodMk measurable_id) using 1
  ext T
  exact Fin.sum_univ_eq_sum_range
    (fun j => deltaChild l T (j + 1) ^ 2 * childTerm l n (child T (j + 1))) (degree T)

private theorem integral_splitChildResponse_nodeFin (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (n k : ℕ) :
    (∫ ts, splitChildResponse l n (nodeFin (k + 1) ts) ∂Measure.pi (fun _ : Fin (k + 1) => GW μ)) =
      (∫ ts, splitResponseWeight l (nodeFin (k + 1) ts) ∂Measure.pi (fun _ : Fin (k + 1) => GW μ)) *
        (∫ T, childTerm l n T ∂GW μ) := by
  let δ (i : Fin (k + 1)) (ts : Fin (k + 1) → Tree) : ℝ :=
    deltaChild l (nodeFin (k + 1) ts) (i.val + 1) ^ 2
  let f (i : Fin (k + 1)) (ts : Fin (k + 1) → Tree) : ℝ :=
    δ i ts * childTerm l n (ts i)
  have hdelta (i : Fin (k + 1)) :
      Measurable (fun ts => deltaChild l (nodeFin (k + 1) ts) (i.val + 1) ^ 2) :=
    ((measurable_deltaChild l (i.val + 1)).comp (measurable_nodeFin (k + 1))).pow_const 2
  have hbound (i : Fin (k + 1)) (ts : Fin (k + 1) → Tree) :
      ‖deltaChild l (nodeFin (k + 1) ts) (i.val + 1) ^ 2‖ ≤ 1 := by
    have hd := deltaChild_mem_Icc' hl (nodeFin (k + 1) ts)
      (Fin.cast (degree_nodeFin (k + 1) ts).symm i)
    rw [Real.norm_of_nonneg (sq_nonneg (deltaChild l (nodeFin (k + 1) ts) (i.val + 1)))]
    exact (sq_le_one_iff₀ hd.1).2 hd.2
  have hδ (i : Fin (k + 1)) : Integrable
      (fun ts => deltaChild l (nodeFin (k + 1) ts) (i.val + 1) ^ 2)
      (Measure.pi fun _ : Fin (k + 1) => GW μ) :=
    Integrable.of_bound (hdelta i).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (hbound i))
  have hterm (i : Fin (k + 1)) : Integrable
      (fun ts => deltaChild l (nodeFin (k + 1) ts) (i.val + 1) ^ 2 * childTerm l n (ts i))
      (Measure.pi fun _ : Fin (k + 1) => GW μ) := by
    have hi := (measurePreserving_eval (fun _ : Fin (k + 1) => GW μ) i)
      |>.integrable_comp_of_integrable (integrable_childTerm h hl hlm n)
    apply hi.mono ((hdelta i).mul ((measurable_childTerm l n).comp
      (measurable_pi_apply i))).aestronglyMeasurable
    filter_upwards with ts
    change ‖δ i ts * childTerm l n (ts i)‖ ≤ ‖childTerm l n (ts i)‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hbound i ts)
  have hc (ts : Fin (k + 1) → Tree) :
      splitChildResponse l n (nodeFin (k + 1) ts) = ∑ i, f i ts := by
    unfold splitChildResponse
    rw [degree_nodeFin]
    apply Finset.sum_congr rfl
    intro i _
    rw [children_nodeFin]
  have hw (ts : Fin (k + 1) → Tree) :
      splitResponseWeight l (nodeFin (k + 1) ts) = ∑ i, δ i ts := by
    unfold splitResponseWeight
    rw [degree_nodeFin]
  simp_rw [hc, hw]
  rw [integral_finsetSum Finset.univ (f := f) (fun i _ => hterm i),
    integral_finsetSum Finset.univ (f := δ) (fun i _ => hδ i),
    Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => integral_childResponse_coord (μ := μ) n i)

private theorem integrable_splitMomentResponse (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    Integrable (fun T => Wt l T ^ (n - 1) * Wresp l T) (splitLaw μ) := by
  let a := (1 + l) / 2
  let b := (l + mean μ) / 2
  have ha : 1 < a := by dsimp [a]; linarith
  have hb : b < mean μ := by dsimp [b]; linarith
  have hx : l ∈ Set.Icc a b := by dsimp [a, b]; constructor <;> linarith
  have hab := hx.1.trans hx.2
  apply ((integrable_deriv_bound h ha hab hb 1).const_mul (l - 1)).mono'
    (((measurable_Wt l).pow_const _).mul (measurable_Wresp l)).aestronglyMeasurable
  filter_upwards [ae_regTree_split h, ae_norm_deriv_Wt_pow_le h ha hab hb 1] with T hT hbound
  have hd := hbound l hx
  simp only [Nat.cast_one, Nat.sub_self, pow_zero, mul_one, one_mul] at hd
  obtain ⟨hw0, hw1⟩ := Wt_mem_Icc' hl T
  change ‖Wt l T ^ (n - 1) * Wresp l T‖ ≤ _
  rw [Wresp_eq_deriv hT hl hlm, norm_mul, norm_mul, norm_neg,
    Real.norm_of_nonneg (pow_nonneg hw0 _), Real.norm_of_nonneg (by linarith : 0 ≤ l - 1)]
  calc
    _ ≤ 1 * ((l - 1) * ‖deriv (fun l' => Wt l' T) l‖) :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hw0 hw1) (by positivity)
    _ ≤ _ := by simpa only [one_mul, Nat.cast_one] using
      mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ l - 1)

private theorem ae_splitChildResponse_bounds (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    ∀ᵐ T ∂splitLaw μ,
      0 ≤ splitChildResponse l n T ∧ splitChildResponse l n T ≤ Wt l T ^ (n - 1) * Wresp l T := by
  filter_upwards [ae_regTree_split h] with T hT
  refine ⟨Finset.sum_nonneg fun i _ => ?_, ?_⟩
  · have hβ := (escape_mem_Icc (by linarith : 0 < l) (child T (i + 1))).1
    have hY : 0 ≤ Yt l (child T (i + 1)) := by
      unfold Yt
      positivity
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hY _) (Yresp_nonneg (regTree_child hT i) hl hlm))
  · rw [← Bresp_eq_Wresp hT hl hlm]
    exact Wt_pow_mul_Bresp_ge_sum h hT hl hlm n

private theorem integral_splitChildResponse_restrict (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (n k : ℕ) :
    (∫ T in {T | degree T = k}, splitChildResponse l n T ∂splitLaw μ) =
      (∫ T in {T | degree T = k}, splitResponseWeight l T ∂splitLaw μ) *
        (∫ T, childTerm l n T ∂GW μ) := by
  by_cases hk : 2 ≤ k
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    have hm : Measurable (splitResponseWeight l) := measurable_sum_delta_sq' l
    rw [splitLaw_restrict_degree h (k + 1) hk, integral_smul_measure, integral_smul_measure]
    simp only [smul_eq_mul]
    rw [integral_map (measurable_nodeFin (k + 1)).aemeasurable
        (measurable_splitChildResponse l n).aestronglyMeasurable,
      integral_map (measurable_nodeFin (k + 1)).aemeasurable hm.aestronglyMeasurable,
      integral_splitChildResponse_nodeFin h hl hlm n k, mul_assoc]
  · have hempty : {T : Tree | degree T = k} ∩ {T | 2 ≤ degree T} = ∅ := by
      ext T
      simp
      omega
    have hm : MeasurableSet {T : Tree | degree T = k} :=
      continuous_degree.measurable (measurableSet_singleton k)
    rw [splitLaw, Measure.restrict_smul, Measure.restrict_restrict hm, hempty,
      Measure.restrict_empty, smul_zero, integral_zero_measure, integral_zero_measure, zero_mul]

/-- The averaged split response dominates the sibling-weighted child response. -/
theorem Bn_ge (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (n : ℕ) (hn : 1 ≤ n) :
    Mstar μ l * xS μ l * (iota μ l n * Bn μ l n + Acoef μ l n ^ 2 * etaW μ l n) ≤
      Bn μ l n := by
  rw [Bn_eq_BnMeasurable h hl hlm n, mul_assoc, ← integral_childTerm_eq h hl hlm n hn]
  let ρ := fun k : ℕ => (splitLaw μ).restrict {T | degree T = k}
  have hρ : Measure.sum ρ = splitLaw μ := by
    have hd : Pairwise (fun i j => Disjoint {T : Tree | degree T = i} {T | degree T = j}) :=
      fun _ _ hij => Set.disjoint_left.mpr fun _ hi hj => hij (hi.symm.trans hj)
    have hu : (⋃ k : ℕ, {T : Tree | degree T = k}) = Set.univ := by ext T; simp
    rw [← Measure.restrict_iUnion hd
      (fun k => continuous_degree.measurable (measurableSet_singleton k)), hu, Measure.restrict_univ]
  have hp := integrable_splitMomentResponse h hl hlm n
  have hbounds := ae_splitChildResponse_bounds h hl hlm n
  have hw : Integrable (splitResponseWeight l) (splitLaw μ) := integrable_sum_delta_sq' h hl
  have hc : Integrable (splitChildResponse l n) (splitLaw μ) :=
    hp.mono_nonneg (measurable_splitChildResponse l n).aestronglyMeasurable
      (hbounds.mono fun _ hT => hT.1) (hbounds.mono fun _ hT => hT.2)
  have hfixed (k : ℕ) :
      (∫ T, splitResponseWeight l T ∂ρ k) * (∫ T, childTerm l n T ∂GW μ) ≤
        ∫ T, Wt l T ^ (n - 1) * Wresp l T ∂ρ k := by
    change (∫ T in {T | degree T = k}, splitResponseWeight l T ∂splitLaw μ) * _ ≤ _
    rw [← integral_splitChildResponse_restrict h hl hlm n k]
    exact integral_mono_ae hc.restrict hp.restrict
      (ae_restrict_of_ae (hbounds.mono fun _ hT => hT.2))
  have hweight : HasSum (fun k => ∫ T, splitResponseWeight l T ∂ρ k) (Mstar μ l) := by
    unfold Mstar
    rw [← hρ]
    exact hasSum_integral_measure (hρ ▸ hw)
  have hmoment : HasSum (fun k => ∫ T, Wt l T ^ (n - 1) * Wresp l T ∂ρ k)
      (BnMeasurable μ l n) := by
    unfold BnMeasurable
    rw [← hρ]
    exact hasSum_integral_measure (hρ ▸ hp)
  exact hasSum_le hfixed (hweight.mul_right _) hmoment

end LPPMonotonicityProof.Analytic
