module

public import LPPMonotonicityProof.Analytic.FirstSplit3
public import LPPMonotonicityProof.Analytic.Regularity.Mean
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Terminal-response moment estimates

This module proves the mean condition giving `w ≤ 4/9` in the proof of Corollary 4.6
(`cor:small-terminal`), and the normalized terminal-moment bounds in the proof of
Lemma A.1 (`lem:large-finite`). It also states the root decomposition of the split law
as a signed integral; the declarations whose names end in `Prov` belong to that
decomposition, and the public ones are also used in `Analytic/Joint.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private lemma integrable_Wt_pow_terminal (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : Integrable (fun T => Wt l T ^ n) (splitLaw μ) := by
  letI := splitLaw_prob h
  apply (integrable_const (1 : ℝ)).mono' ((measurable_Wt l).pow_const n).aestronglyMeasurable
  filter_upwards [ae_Wt_mem h hl hlm] with T hT
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hT.1.le _)]
  exact pow_le_one₀ hT.1.le hT.2.le

private lemma wbar_pos_terminal (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : 0 < wbar μ l := by
  letI := splitLaw_prob h
  have hi : Integrable (Wt l) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow_terminal h hl hlm 1
  have hn : 0 ≤ᵐ[splitLaw μ] Wt l := (ae_Wt_mem h hl hlm).mono fun _ hT => hT.1.le
  rw [wbar, etaW]
  simp only [pow_one]
  rw [integral_pos_iff_support_of_nonneg_ae hn hi]
  have hs : Function.support (Wt l) =ᵐ[splitLaw μ] Set.univ := by
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    simp [Function.support, hT.1.ne']
  rw [measure_congr hs]
  simp

private lemma convex_tangent_pow (k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y ^ k + (k : ℝ) * y ^ (k - 1) * (x - y) ≤ x ^ k := by
  cases k with
  | zero => simp
  | succ k =>
      by_cases hxy : x = y
      · subst x
        simp
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · have hs := (convexOn_pow (𝕜 := ℝ) (k + 1)).slope_le_of_hasDerivAt
          (show x ∈ Set.Ici (0 : ℝ) from hx) (show y ∈ Set.Ici (0 : ℝ) from hy) hlt
          (hasDerivAt_pow (k + 1) y)
        rw [slope_def_field] at hs
        have hm := (div_le_iff₀ (sub_pos.mpr hlt)).mp hs
        simp only [Nat.add_sub_cancel, pow_succ] at hm ⊢
        push_cast at hm ⊢
        nlinarith [hm]
      · have hs := (convexOn_pow (𝕜 := ℝ) (k + 1)).le_slope_of_hasDerivAt
          (show y ∈ Set.Ici (0 : ℝ) from hy) (show x ∈ Set.Ici (0 : ℝ) from hx) hgt
          (hasDerivAt_pow (k + 1) y)
        rw [slope_def_field] at hs
        have hm := (le_div_iff₀ (sub_pos.mpr hgt)).mp hs
        simp only [Nat.add_sub_cancel, pow_succ] at hm ⊢
        push_cast at hm ⊢
        nlinarith [hm]

private lemma normalized_pow_lower (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {n : ℕ} (hn : 2 ≤ n) :
    (tW μ l) ^ (n - 1) ≤ etaW μ l n / wbar μ l := by
  letI := splitLaw_prob h
  let w := wbar μ l
  let t := tW μ l
  let k := n - 1
  have hw : 0 < w := wbar_pos_terminal h hl hlm
  have hW : Integrable (Wt l) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow_terminal h hl hlm 1
  have hWk : Integrable (fun T => Wt l T ^ (k + 1)) (splitLaw μ) :=
    integrable_Wt_pow_terminal h hl hlm (k + 1)
  have hprod : Integrable (fun T => Wt l T * (Wt l T - t)) (splitLaw μ) := by
    apply ((integrable_Wt_pow_terminal h hl hlm 2).sub (hW.const_mul t)).congr
    filter_upwards with T
    change Wt l T ^ 2 - t * Wt l T = Wt l T * (Wt l T - t)
    ring
  have hleft : Integrable (fun T => t ^ k * Wt l T) (splitLaw μ) := hW.const_mul _
  have hright : Integrable
      (fun T => Wt l T ^ (k + 1) - (k : ℝ) * t ^ (k - 1) * (Wt l T * (Wt l T - t)))
      (splitLaw μ) := hWk.sub (hprod.const_mul _)
  have hmono : (∫ T, t ^ k * Wt l T ∂splitLaw μ) ≤
      ∫ T, Wt l T ^ (k + 1) - (k : ℝ) * t ^ (k - 1) * (Wt l T * (Wt l T - t))
        ∂splitLaw μ := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    have ht : 0 ≤ t := by
      dsimp [t, tW]
      exact div_nonneg (integral_nonneg_of_ae ((ae_Wt_mem h hl hlm).mono fun S hS =>
        pow_nonneg hS.1.le 2)) hw.le
    have htan := convex_tangent_pow k hT.1.le ht
    have hm := mul_le_mul_of_nonneg_left htan hT.1.le
    simp only [pow_succ] at hm ⊢
    push_cast at hm ⊢
    nlinarith [hm]
  rw [integral_const_mul, integral_sub hWk (hprod.const_mul _), integral_const_mul] at hmono
  have hzero : (∫ T, Wt l T * (Wt l T - t) ∂splitLaw μ) = 0 := by
    have heq : (fun T => Wt l T * (Wt l T - t)) =
        (fun T => Wt l T ^ 2 - t * Wt l T) := by funext T; ring
    rw [heq, integral_sub (integrable_Wt_pow_terminal h hl hlm 2) (hW.const_mul t),
      integral_const_mul]
    have htw : t * w = etaW μ l 2 := by
      dsimp [t, w, tW]
      exact div_mul_cancel₀ _ hw.ne'
    have hw' : (∫ T, Wt l T ∂splitLaw μ) = w := by
      simp [w, wbar, etaW]
    rw [show (∫ T, Wt l T ^ 2 ∂splitLaw μ) = t * w from htw.symm, ← hw']
    ring
  rw [hzero, mul_zero, sub_zero] at hmono
  have hkn : k + 1 = n := by dsimp [k]; omega
  rw [hkn] at hmono
  apply (le_div_iff₀ hw).2
  change t ^ k * w ≤ etaW μ l n
  simpa only [w, etaW, wbar, pow_one] using hmono

/-- The root-decomposition weight of the split law, `P(ν = k)/P(ν ≥ 2)` for `k ≥ 2`.
It repeats a private definition of `Analytic/FirstSplit3.lean`, so that this module and
`Analytic/Joint.lean` can use the same signed root integral. -/
noncomputable def splitWeightProv (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) : ℝ≥0∞ :=
  if 2 ≤ k then μ {k} / μ (Set.Ici 2) else 0

private lemma splitLaw_eq_sum_rootProv (h : OffspringHyp μ) :
    splitLaw μ = Measure.sum fun k : ℕ =>
      splitWeightProv μ k • (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k) := by
  have hdisj : Pairwise (fun i j => Disjoint {T : Tree | degree T = i} {T : Tree | degree T = j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun T hi hj => hij (hi.symm.trans hj)
  calc
    splitLaw μ = (splitLaw μ).restrict Set.univ := by simp
    _ = (splitLaw μ).restrict (⋃ k : ℕ, {T | degree T = k}) := by
      congr 1
      ext T
      simp
    _ = Measure.sum fun k : ℕ => (splitLaw μ).restrict {T | degree T = k} :=
      Measure.restrict_iUnion hdisj fun k => continuous_degree.measurable (measurableSet_singleton k)
    _ = _ := by
      apply congrArg Measure.sum
      funext k
      by_cases hk : 2 ≤ k
      · simpa [splitWeightProv, hk] using splitLaw_restrict_degree h k hk
      · simp only [splitWeightProv, hk, ↓reduceIte, zero_smul]
        rw [splitLaw, Measure.restrict_smul]
        have he : {T : Tree | degree T = k} ∩ {T | 2 ≤ degree T} = ∅ := by
          ext T
          simp
          omega
        have hr : ((GW μ).restrict {T | 2 ≤ degree T}).restrict {T | degree T = k} = 0 := by
          apply Measure.restrict_eq_zero.2
          change (GW μ).restrict {T | 2 ≤ degree T} (degree ⁻¹' {k}) = 0
          rw [Measure.restrict_apply (continuous_degree.measurable (measurableSet_singleton k))]
          change GW μ ({T : Tree | degree T = k} ∩ {T | 2 ≤ degree T}) = 0
          rw [he, measure_empty]
        rw [hr, smul_zero]

/-- Signed integral form of the root decomposition of the split law. -/
theorem integral_splitLaw_rootProv (h : OffspringHyp μ) {G : Tree → ℝ}
    (hG : Integrable G (splitLaw μ)) :
    ∫ T, G T ∂splitLaw μ = ∑' k : ℕ, (splitWeightProv μ k).toReal *
      ∫ ts, G (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ) := by
  have hlaw := splitLaw_eq_sum_rootProv (μ := μ) h
  have hsumint : Integrable G (Measure.sum fun k : ℕ =>
      splitWeightProv μ k • (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k)) := hlaw ▸ hG
  calc
    _ = ∫ T, G T ∂Measure.sum (fun k : ℕ =>
        splitWeightProv μ k • (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k)) := by rw [← hlaw]
    _ = ∑' k : ℕ, ∫ T, G T ∂(splitWeightProv μ k •
        (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k)) := integral_sum_measure hsumint
    _ = _ := by
      apply tsum_congr
      intro k
      by_cases hk : splitWeightProv μ k = 0
      · simp [hk]
      let ρ := (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k)
      have hs : AEStronglyMeasurable G (splitWeightProv μ k • ρ) :=
        hsumint.aestronglyMeasurable.mono_measure
          (show splitWeightProv μ k • ρ ≤ Measure.sum (fun k : ℕ =>
            splitWeightProv μ k • (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k)) from
            Measure.le_sum (fun k : ℕ => splitWeightProv μ k •
              (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k)) k)
      have hmap : AEStronglyMeasurable G ρ := by
        exact ⟨hs.mk, hs.stronglyMeasurable_mk,
          by simpa only [Measure.ae_ennreal_smul_measure_eq hk] using hs.ae_eq_mk⟩
      calc
        _ = (splitWeightProv μ k).toReal * ∫ T, G T ∂ρ := by
          rw [integral_smul_measure]
          rfl
        _ = _ := by
          apply congrArg (fun x : ℝ => (splitWeightProv μ k).toReal * x)
          exact integral_map (measurable_nodeFin k).aemeasurable hmap

private lemma integrable_escape_terminal {l : ℝ} (hl : 0 < l) :
    Integrable (escape l) (GW μ) := by
  apply Integrable.of_bound (measurable_escape l).aestronglyMeasurable 1
  filter_upwards with T
  rw [Real.norm_eq_abs, abs_of_nonneg (escape_mem_Icc hl T).1]
  exact (escape_mem_Icc hl T).2

private lemma integral_pi_sum_escape_terminal {l : ℝ} (hl : 0 < l) (k : ℕ) :
    (∫ ts : Fin k → Tree, (∑ i, escape l (ts i)) ∂Measure.pi (fun _ : Fin k => GW μ)) =
      k * ∫ T, escape l T ∂GW μ := by
  rw [integral_finsetSum]
  · calc
      _ = ∑ _i : Fin k, ∫ T, escape l T ∂GW μ := by
        apply Finset.sum_congr rfl
        intro i _
        have hp := measurePreserving_eval (fun _ : Fin k => GW μ) i
        have hg : AEStronglyMeasurable (escape l)
            ((Measure.pi (fun _ : Fin k => GW μ)).map (fun ts => ts i)) := by
          rw [hp.map_eq]
          exact (measurable_escape l).aestronglyMeasurable
        calc
          _ = ∫ T, escape l T ∂((Measure.pi (fun _ : Fin k => GW μ)).map (fun ts => ts i)) :=
            (integral_map (measurable_pi_apply i).aemeasurable hg).symm
          _ = _ := by rw [hp.map_eq]
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  · intro i _
    exact (measurePreserving_eval (fun _ : Fin k => GW μ) i).integrable_comp_of_integrable
      (integrable_escape_terminal hl)

private lemma integrable_degree_split_terminal (h : OffspringHyp μ) :
    Integrable (fun T : Tree => (degree T : ℝ)) (splitLaw μ) := by
  have hnat : Integrable (fun k : ℕ => (k : ℝ)) μ := by
    rw [← lintegral_ofReal_ne_top_iff_integrable
      (measurable_of_countable _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => by positivity)]
    simpa only [ENNReal.ofReal_natCast] using ne_of_lt h.mean_lt_top
  have hbranch : GW μ {T | 2 ≤ degree T} = μ (Set.Ici 2) := by
    have hmap := congrArg (fun ν : Measure ℕ => ν (Set.Ici 2)) (bienaymeLaw_map_degree μ)
    rwa [Measure.map_apply continuous_degree.measurable measurableSet_Ici] at hmap
  have hne : GW μ {T | 2 ≤ degree T} ≠ 0 := by
    rw [hbranch]
    intro hz
    have hp := pBr_pos h
    rw [pBr, hz, ENNReal.toReal_zero] at hp
    exact lt_irrefl 0 hp
  have htree : Integrable (fun T : Tree => (degree T : ℝ)) (GW μ) := by
    have hmapint : Integrable (fun k : ℕ => (k : ℝ)) ((GW μ).map degree) := by
      rw [bienaymeLaw_map_degree]
      exact hnat
    change Integrable ((fun k : ℕ => (k : ℝ)) ∘ degree) (GW μ)
    exact (integrable_map_measure
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).aestronglyMeasurable
      continuous_degree.measurable.aemeasurable).1 hmapint
  exact htree.restrict.smul_measure (ENNReal.inv_ne_top.2 hne)

private lemma ratio_concaveOn_terminal {a : ℝ} (ha : 0 < a) :
    ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x / (a + x)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy u v hu hv huv
  have hvval : v = 1 - u := by linarith
  subst v
  simp only [smul_eq_mul]
  have hax : 0 < a + x := add_pos_of_pos_of_nonneg ha hx
  have hay : 0 < a + y := add_pos_of_pos_of_nonneg ha hy
  have hau : 0 < a + (u * x + (1 - u) * y) :=
    add_pos_of_pos_of_nonneg ha (add_nonneg (mul_nonneg hu hx) (mul_nonneg (by linarith) hy))
  have hid : (u * x + (1 - u) * y) / (a + (u * x + (1 - u) * y)) -
      (u * (x / (a + x)) + (1 - u) * (y / (a + y))) =
    u * (1 - u) * a * (x - y) ^ 2 /
      ((a + x) * (a + y) * (a + (u * x + (1 - u) * y))) := by
    field_simp [hax.ne', hay.ne', hau.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity

private lemma ratio_continuousOn_terminal {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => x / (a + x)) (Set.Ici 0) := by
  apply ContinuousOn.div continuousOn_id (continuousOn_const.add continuousOn_id)
  intro x hx
  exact (add_pos_of_pos_of_nonneg ha hx).ne'

/-- **Proof of Corollary 4.6.** The mean-degree condition implies the terminal-mean
bound `w ≤ 4/9`. -/
theorem wbar_le_of_meanJ (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (hc : (mean μ - l) * meanJ μ ≤ 4 / 5 * mean μ * (l - 1)) :
    wbar μ l ≤ 4 / 9 := by
  letI := splitLaw_prob h
  let a := l - 1
  let b := ∫ T, escape l T ∂GW μ
  let U : Tree → ℝ := fun T => childSum l T
  have ha : 0 < a := by dsimp [a]; linarith
  have hb0 : 0 ≤ b := integral_nonneg_of_ae (ae_of_all _ fun T => (escape_mem_Icc (by positivity) _).1)
  have hdeg := integrable_degree_split_terminal h
  have hchild : Integrable (childSum l) (splitLaw μ) := by
    apply hdeg.mono' (measurable_childSum l).aestronglyMeasurable
    filter_upwards with T
    have h0 : 0 ≤ childSum l T := Finset.sum_nonneg fun i _ => (escape_mem_Icc (by positivity) _).1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    unfold childSum
    calc
      (∑ i : Fin (degree T), escape l (child T (i.val + 1))) ≤ ∑ _i : Fin (degree T), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => (escape_mem_Icc (by positivity) _).2
      _ = degree T := by simp
  have hUint : Integrable U (splitLaw μ) := hchild
  have hU0 : ∀ᵐ T ∂splitLaw μ, U T ∈ Set.Ici (0 : ℝ) := by
    filter_upwards with T
    exact Finset.sum_nonneg fun i _ => (escape_mem_Icc (by positivity) _).1
  have hUnode (k : ℕ) :
      (∫ ts, U (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ)) = (k : ℝ) * b := by
    have hnode (ts : Fin k → Tree) : U (nodeFin k ts) = ∑ i, escape l (ts i) := by
      dsimp [U]
      unfold childSum
      rw [degree_nodeFin]
      apply Finset.sum_congr rfl
      intro i _
      rw [children_nodeFin]
    simp_rw [hnode]
    exact integral_pi_sum_escape_terminal (by positivity : 0 < l) k
  have hmeanJ : meanJ μ = ∑' k : ℕ, (splitWeightProv μ k).toReal * (k : ℝ) := by
    change (∫ T, (degree T : ℝ) ∂splitLaw μ) = _
    simpa using (integral_splitLaw_rootProv h hdeg)
  have hmeanU : (∫ T, U T ∂splitLaw μ) = meanJ μ * b := by
    calc
      _ = ∑' k : ℕ, (splitWeightProv μ k).toReal * ((k : ℝ) * b) := by
        rw [integral_splitLaw_rootProv h hUint]
        apply tsum_congr
        intro k
        rw [hUnode]
      _ = ∑' k : ℕ, ((splitWeightProv μ k).toReal * (k : ℝ)) * b := by
        apply tsum_congr
        intro k
        ring
      _ = (∑' k : ℕ, (splitWeightProv μ k).toReal * (k : ℝ)) * b := by
        rw [tsum_mul_right]
      _ = meanJ μ * b := by
        rw [← hmeanJ]
  have hW : Integrable (Wt l) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow_terminal h hl hlm 1
  have hUW (T : Tree) : U T / (a + U T) = Wt l T := by
    dsimp [U, Wt, a]
  have hJensen := (ratio_concaveOn_terminal ha).le_map_integral
    (ratio_continuousOn_terminal ha) isClosed_Ici hU0 hUint (by
      apply hW.congr
      filter_upwards with T
      exact (hUW T).symm)
  rw [hmeanU] at hJensen
  have hwJensen : wbar μ l ≤ (meanJ μ * b) / (a + meanJ μ * b) := by
    simpa only [hUW, wbar, etaW, pow_one] using hJensen
  have hb : b ≤ (mean μ - l) / mean μ := (mean_escape_bounds h (by positivity) hlm).2.2.2
  have hmean0 : 0 ≤ meanJ μ := integral_nonneg_of_ae (ae_of_all _ fun T => Nat.cast_nonneg _)
  have hm : 0 < mean μ := by
    have hreal : 1 < mean μ :=
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top h.mean_lt_top.ne).2 h.one_lt_mean
    exact zero_lt_one.trans hreal
  have hEU : meanJ μ * b ≤ 4 * a / 5 := by
    have hbmul : meanJ μ * b ≤ meanJ μ * ((mean μ - l) / mean μ) :=
      mul_le_mul_of_nonneg_left hb hmean0
    have hc' : meanJ μ * ((mean μ - l) / mean μ) ≤ 4 * a / 5 := by
      have hc0 : meanJ μ * (mean μ - l) ≤ (4 * a / 5) * mean μ := by
        dsimp [a]
        convert hc using 1 <;> ring
      calc
        meanJ μ * ((mean μ - l) / mean μ) = meanJ μ * (mean μ - l) / mean μ := by ring
        _ ≤ 4 * a / 5 := (div_le_iff₀ hm).2 hc0
    exact hbmul.trans hc'
  have hratio : (meanJ μ * b) / (a + meanJ μ * b) ≤ 4 / 9 := by
    have hU0' : 0 ≤ meanJ μ * b := mul_nonneg hmean0 hb0
    have hden : 0 < a + meanJ μ * b := by positivity
    rw [show (4 / 9 : ℝ) = (4 * a / 5) / (a + 4 * a / 5) by field_simp [ha.ne']; ring]
    apply (div_le_div_iff₀ hden (by positivity : 0 < a + 4 * a / 5)).2
    nlinarith
  exact hwJensen.trans hratio

/-- **Proof of Lemma A.1.** The normalized terminal-moment bounds. -/
theorem normalized_moments (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    let w := wbar μ l; let t := tW μ l; let e := fun n => etaW μ l n / w
    w ≤ t ∧ t ≤ 1 ∧ e 1 = 1 ∧ e 2 = t ∧ (∀ n ≥ 2, t ^ (n-1) ≤ e n ∧ e n ≤ t) ∧
    (∀ n ≥ 1, 0 ≤ e n - e (n+1) ∧ e n - e (n+1) ≤ 1 - t) ∧ e 1 - e 2 = 1 - t := by
  letI := splitLaw_prob h
  dsimp only
  have hw := wbar_pos_terminal h hl hlm
  have hW : Integrable (Wt l) (splitLaw μ) := by
    simpa only [pow_one] using integrable_Wt_pow_terminal h hl hlm 1
  have hW2 := integrable_Wt_pow_terminal h hl hlm 2
  have hJensen : wbar μ l ^ 2 ≤ etaW μ l 2 := by
    have hj := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le (continuousOn_pow 2)
      isClosed_Ici ((ae_Wt_mem h hl hlm).mono fun T hT => hT.1.le) hW hW2
    simpa only [wbar, etaW, pow_one] using hj
  have hw_t : wbar μ l ≤ tW μ l := by
    apply (le_div_iff₀ hw).2
    nlinarith
  have he2w : etaW μ l 2 ≤ wbar μ l := by
    have hm : (∫ T, Wt l T ^ 2 ∂splitLaw μ) ≤ ∫ T, Wt l T ∂splitLaw μ := by
      apply integral_mono_ae hW2 hW
      filter_upwards [ae_Wt_mem h hl hlm] with T hT
      nlinarith [sq_nonneg (Wt l T), mul_nonneg hT.1.le (sub_nonneg.mpr hT.2.le)]
    simpa only [etaW, wbar, pow_one] using hm
  have ht1 : tW μ l ≤ 1 := (div_le_one hw).2 he2w
  have he1 : etaW μ l 1 / wbar μ l = 1 := by
    exact div_self hw.ne'
  refine ⟨hw_t, ht1, he1, rfl, ?_, ?_, ?_⟩
  · intro n hn
    refine ⟨normalized_pow_lower h hl hlm hn, ?_⟩
    apply (div_le_iff₀ hw).2
    rw [tW, div_mul_cancel₀ _ hw.ne']
    have hWn := integrable_Wt_pow_terminal h hl hlm n
    apply integral_mono_ae hWn hW2
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    exact pow_le_pow_of_le_one hT.1.le hT.2.le hn
  · intro n hn
    have hWn := integrable_Wt_pow_terminal h hl hlm n
    have hWn1 := integrable_Wt_pow_terminal h hl hlm (n + 1)
    have hdiff : etaW μ l n - etaW μ l (n + 1) =
        ∫ T, Wt l T ^ n * (1 - Wt l T) ∂splitLaw μ := by
      unfold etaW
      rw [← integral_sub hWn hWn1]
      apply integral_congr_ae
      filter_upwards with T
      ring
    have hbase : wbar μ l - etaW μ l 2 = ∫ T, Wt l T * (1 - Wt l T) ∂splitLaw μ := by
      unfold wbar etaW
      simp only [pow_one]
      rw [← integral_sub hW hW2]
      apply integral_congr_ae
      filter_upwards with T
      ring
    have hnonneg : 0 ≤ etaW μ l n / wbar μ l - etaW μ l (n + 1) / wbar μ l := by
      rw [← sub_div]
      apply div_nonneg _ hw.le
      rw [hdiff]
      apply integral_nonneg_of_ae
      filter_upwards [ae_Wt_mem h hl hlm] with T hT
      exact mul_nonneg (pow_nonneg hT.1.le _) (sub_nonneg.mpr hT.2.le)
    refine ⟨hnonneg, ?_⟩
    rw [← sub_div]
    apply (div_le_iff₀ hw).2
    have hwt : (1 - tW μ l) * wbar μ l = wbar μ l - etaW μ l 2 := by
      unfold tW
      field_simp [hw.ne']
    rw [hwt, hdiff, hbase]
    have hni : Integrable (fun T => Wt l T ^ n * (1 - Wt l T)) (splitLaw μ) := by
      apply (hWn.sub hWn1).congr
      filter_upwards with T
      change Wt l T ^ n - Wt l T ^ (n + 1) = Wt l T ^ n * (1 - Wt l T)
      ring
    have h1i : Integrable (fun T => Wt l T * (1 - Wt l T)) (splitLaw μ) := by
      apply (hW.sub hW2).congr
      filter_upwards with T
      change Wt l T - Wt l T ^ 2 = Wt l T * (1 - Wt l T)
      ring
    apply integral_mono_ae hni h1i
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    have hpow : Wt l T ^ n ≤ Wt l T := by
      simpa only [pow_one] using pow_le_pow_of_le_one hT.1.le hT.2.le hn
    exact mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr hT.2.le)
  · rw [he1]
    rfl

end LPPMonotonicityProof.Analytic
