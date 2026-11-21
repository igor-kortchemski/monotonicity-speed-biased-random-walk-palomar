module

public import LPPMonotonicityProof.Analytic.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Lean.Elab.Tactic.Omega

/-!
# Analytic interface lemmas: tree form of `N` and `Z`, offspring scalars

The first part writes the two-copy quantities `N = E[ββ'/D]` and `Z = E[τ/D]` of
Section 2 (the copies `NvalProv` and `ZvalProv` of `LPPMonotonicityProof.Analytic.Defs`)
as integrals over two independent Bienaymé trees.  The second part relates the
offspring scalars `p₁ = P(ν = 1)`, `p = P(ν ≥ 2)` and `e = E[1/J]` of Section 4,
where `J` has the law of `ν` given `ν ≥ 2`, and identifies the inverse mean
`LPPMonotonicity.inverseMean` of the public statement with `invMean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-! ## Tree form of N and Z -/

private theorem measurable_DfunProv_pair (l : ℝ) :
    Measurable (fun p : ℝ × ℝ => DfunProv l p.1 p.2) := by
  exact (((measurable_const.sub measurable_const).add measurable_fst).add measurable_snd).sub
    (measurable_fst.mul measurable_snd)

/-- `N` as an integral over two independent Bienaymé trees. -/
theorem Nval_eq_pairE (l : ℝ) :
    NvalProv μ l = pairE μ l fun b b' => b * b' / DfunProv l b b' := by
  unfold NvalProv pairE escLawProv
  rw [Measure.map_prod_map (GW μ) (GW μ) (measurable_escape l) (measurable_escape l)]
  exact integral_map ((measurable_escape l).prodMap (measurable_escape l)).aemeasurable
    (show AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 * p.2 / DfunProv l p.1 p.2) _ from
      ((measurable_fst.mul measurable_snd).div
        (measurable_DfunProv_pair l)).aestronglyMeasurable)

/-- `Z` as an integral over two independent Bienaymé trees. -/
theorem Zval_eq_pairE (l : ℝ) :
    ZvalProv μ l = pairE μ l fun b b' => tau b b' / DfunProv l b b' := by
  unfold ZvalProv pairE escLawProv tau
  rw [Measure.map_prod_map (GW μ) (GW μ) (measurable_escape l) (measurable_escape l)]
  exact integral_map ((measurable_escape l).prodMap (measurable_escape l)).aemeasurable
    (show AEStronglyMeasurable
      (fun p : ℝ × ℝ => (p.1 + p.2 - p.1 * p.2) / DfunProv l p.1 p.2) _ from
      (((measurable_fst.add measurable_snd).sub (measurable_fst.mul measurable_snd)).div
        (measurable_DfunProv_pair l)).aestronglyMeasurable)

/-! ## Offspring scalars and the public inverse mean -/

private theorem integrable_nat_inv : Integrable (fun k : ℕ => (k : ℝ)⁻¹) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  filter_upwards with k
  cases k with
  | zero => simp
  | succ k =>
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.succ_pos k

private theorem compl_one_ae_eq (h : OffspringHyp μ) :
    ({1} : Set ℕ)ᶜ =ᵐ[μ] Set.Ici 2 := by
  rw [ae_eq_set]
  constructor
  · have hs : ({1} : Set ℕ)ᶜ \ Set.Ici 2 = {0} := by
      ext k
      simp only [Set.mem_sdiff, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_Ici, not_le]
      omega
    rw [hs]
    exact h.zero
  · have hs : Set.Ici 2 \ ({1} : Set ℕ)ᶜ = ∅ := by
      ext k
      simp
    rw [hs, measure_empty]

private theorem GW_branch : GW μ {T | 2 ≤ degree T} = μ (Set.Ici 2) := by
  have hmap := congrArg (fun ν : Measure ℕ => ν (Set.Ici 2)) (bienaymeLaw_map_degree μ)
  rwa [Measure.map_apply continuous_degree.measurable measurableSet_Ici] at hmap

/-- Leaflessness splits the offspring law into degrees one and at least two. -/
theorem p1_add_pBr (h : OffspringHyp μ) : p1 μ + pBr μ = 1 := by
  have hcomp : μ ({1} : Set ℕ)ᶜ = μ (Set.Ici 2) := measure_congr (compl_one_ae_eq h)
  change (μ {1}).toReal + (μ (Set.Ici 2)).toReal = 1
  rw [← hcomp]
  simpa [Measure.real] using probReal_add_probReal_compl (μ := μ) (measurableSet_singleton 1)

/-- Supercriticality gives positive mass to degrees at least two. -/
theorem pBr_pos (h : OffspringHyp μ) : 0 < pBr μ := by
  obtain ⟨k, hk, hμk⟩ := exists_degree_ge_two h
  have hsub : ({k} : Set ℕ) ⊆ Set.Ici 2 := by
    intro j hj
    rw [Set.mem_singleton_iff] at hj
    subst j
    exact hk
  have hpos : 0 < μ (Set.Ici 2) :=
    (pos_iff_ne_zero.mpr hμk).trans_le (measure_mono hsub)
  unfold pBr
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)

private theorem pBr_ne_zero (h : OffspringHyp μ) : μ (Set.Ici 2) ≠ 0 := by
  intro hzero
  have hp := pBr_pos h
  rw [pBr, hzero, ENNReal.toReal_zero] at hp
  exact lt_irrefl 0 hp

/-- The split law is the normalized degree restriction, up to the root-degree map. -/
theorem splitLaw_map_degree (_h : OffspringHyp μ) :
    (splitLaw μ).map degree = (μ (Set.Ici 2))⁻¹ • μ.restrict (Set.Ici 2) := by
  rw [splitLaw, Measure.map_smul _ continuous_degree.measurable.aemeasurable]
  change ((GW μ) (degree ⁻¹' Set.Ici 2))⁻¹ •
    Measure.map degree ((GW μ).restrict (degree ⁻¹' Set.Ici 2)) = _
  rw [← Measure.restrict_map continuous_degree.measurable measurableSet_Ici,
    bienaymeLaw_map_degree]
  have hb : (GW μ) (degree ⁻¹' Set.Ici 2) = μ (Set.Ici 2) := GW_branch
  rw [hb]

/-- The normalized split law is a probability measure. -/
theorem splitLaw_prob (h : OffspringHyp μ) : IsProbabilityMeasure (splitLaw μ) := by
  refine ⟨?_⟩
  rw [splitLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, GW_branch]
  exact ENNReal.inv_mul_cancel (pBr_ne_zero h) (measure_ne_top _ _)

/-- Conditioning on the first split scales the reciprocal-degree integral. -/
theorem invMean_eq_p1_add (h : OffspringHyp μ) : invMean μ = p1 μ + pBr μ * eJ μ := by
  have hInt : Integrable (fun k : ℕ => (k : ℝ)⁻¹) μ := integrable_nat_inv
  have heJ : eJ μ = (μ (Set.Ici 2)).toReal⁻¹ * ∫ k in Set.Ici 2, (k : ℝ)⁻¹ ∂μ := by
    calc
      eJ μ = ∫ k, (k : ℝ)⁻¹ ∂(splitLaw μ).map degree := by
        symm
        exact integral_map continuous_degree.measurable.aemeasurable
          (measurable_of_countable _).aestronglyMeasurable
      _ = ∫ k, (k : ℝ)⁻¹ ∂(μ (Set.Ici 2))⁻¹ • μ.restrict (Set.Ici 2) := by
        rw [splitLaw_map_degree h]
      _ = _ := by simp only [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
  have hsplit : invMean μ =
      (∫ k in {1}, (k : ℝ)⁻¹ ∂μ) + ∫ k in Set.Ici 2, (k : ℝ)⁻¹ ∂μ := by
    calc
      invMean μ = ∫ k, (k : ℝ)⁻¹
          ∂(μ.restrict {1} + μ.restrict ({1} : Set ℕ)ᶜ) := by
        unfold invMean
        rw [Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_singleton 1)]
      _ = (∫ k in {1}, (k : ℝ)⁻¹ ∂μ) + ∫ k in ({1} : Set ℕ)ᶜ, (k : ℝ)⁻¹ ∂μ := by
        rw [integral_add_measure
          (hInt.mono_measure Measure.restrict_le_self) (hInt.mono_measure Measure.restrict_le_self)]
      _ = _ := by rw [Measure.restrict_congr_set (compl_one_ae_eq h)]
  rw [hsplit, integral_singleton, heJ]
  simp only [Nat.cast_one, inv_one, smul_eq_mul, mul_one, p1, pBr, Measure.real]
  have hc : (μ (Set.Ici 2)).toReal ≠ 0 := ne_of_gt (pBr_pos h)
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- The PMF series `LPPMonotonicity.inverseMean` of the public statement is the measure
integral `invMean` used by the analytic lemmas.  The leafless hypothesis `μ' 0 = 0` is not
used: the identity also holds without it because both terms vanish at degree zero. -/
theorem inverseMean_eq (μ' : PMF ℕ) (_hμ0 : μ' 0 = 0) :
    LPPMonotonicity.inverseMean μ' = invMean μ'.toMeasure := by
  unfold LPPMonotonicity.inverseMean invMean
  rw [PMF.integral_eq_tsum μ' (fun k : ℕ => (k : ℝ)⁻¹) integrable_nat_inv]
  apply tsum_congr
  intro n
  simp [smul_eq_mul, div_eq_mul_inv]

end LPPMonotonicityProof.Analytic
