module

public import LPPMonotonicityProof.Analytic.ScaledSeries
public import LPPMonotonicityProof.Analytic.FirstSplit3
public import LPPMonotonicityProof.Analytic.ScaledPrefix2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Deterministic response bounds and the moment derivative

This module proves three steps of the child-response recursion in the proof of
Lemma 4.5 (`lem:scaled-two-children`): `B ≥ W(1 - W)`, `x ∂ₓ ηₙ = n Bₙ`, and
`M ≤ M_*`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

theorem deriv_escape_nonpos_of_reg {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    deriv (fun x => escape x T) l ≤ 0 := by
  let a := l / 2
  let b := (l + mean μ) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hb : b < mean μ := by dsimp [b]; linarith
  have hx : l ∈ Set.Icc a b := ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
  exact (neg_deriv_escape_le hT ha hab hb hx).2.1 |> neg_nonneg.mp

private theorem childSumDeriv_nonpos {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) : childSumDeriv T l ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  exact deriv_escape_nonpos_of_reg (regTree_child hT i) hl hlm

/-- The child response dominates `W (1 - W)`. -/
theorem Bresp_ge (h : OffspringHyp μ) {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : Wt l T * (1 - Wt l T) ≤ Bresp l T := by
  have ha : 0 < l - 1 := by linarith
  have hS : 0 ≤ childSum l T :=
    Finset.sum_nonneg fun i _ => (escape_mem_Icc (by linarith) _).1
  have hD : 0 < l - 1 + childSum l T := by linarith
  have hSd : childSumDeriv T l ≤ 0 := childSumDeriv_nonpos hT (by linarith) hlm
  rw [Bresp, (hasDerivAt_Wt hT hl hlm).deriv]
  have hrewrite :
      - (l - 1) *
          ((childSumDeriv T l * (l - 1 + childSum l T) -
            childSum l T * (1 + childSumDeriv T l)) /
            (l - 1 + childSum l T) ^ 2) =
        ((l - 1) * childSum l T - (l - 1) ^ 2 * childSumDeriv T l) /
          (l - 1 + childSum l T) ^ 2 := by
    ring
  rw [hrewrite]
  have hleft : Wt l T * (1 - Wt l T) =
      (l - 1) * childSum l T / (l - 1 + childSum l T) ^ 2 := by
    unfold Wt
    field_simp [hD.ne']
    ring
  rw [hleft]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hnonneg : 0 ≤ -(l - 1) ^ 2 * childSumDeriv T l := by
    have hm := mul_nonneg (sq_nonneg (l - 1)) (neg_nonneg.mpr hSd)
    nlinarith
  linarith

/-- `x ∂ₓ ηₙ = n Bₙ`. -/
theorem x_dx_etaW (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) (hn : 1 ≤ n) :
    xS μ l * dx μ (fun l => etaW μ l n) l = n * Bn μ l n := by
  have hp := pBr_pos h
  have ha : 0 < l - 1 := by linarith
  unfold xS dx
  rw [(hasDerivAt_etaW h hl hlm n).deriv]
  calc
    pBr μ / (l - 1) * (-((l - 1) ^ 2 / pBr μ) *
        ∫ T, (n : ℝ) * Wt l T ^ (n - 1) * deriv (fun l' => Wt l' T) l ∂splitLaw μ) =
        -(l - 1) * ∫ T, (n : ℝ) * Wt l T ^ (n - 1) *
          deriv (fun l' => Wt l' T) l ∂splitLaw μ := by
      field_simp [hp.ne', ha.ne']
    _ = ∫ T, -(l - 1) * ((n : ℝ) * Wt l T ^ (n - 1) *
        deriv (fun l' => Wt l' T) l) ∂splitLaw μ := by rw [integral_const_mul]
    _ = ∫ T, (n : ℝ) * (Wt l T ^ (n - 1) *
        (-(l - 1) * deriv (fun l' => Wt l' T) l)) ∂splitLaw μ := by
      apply integral_congr_ae
      filter_upwards with T
      ring
    _ = n * Bn μ l n := by
      unfold Bn Bresp
      rw [integral_const_mul]

theorem deltaChild_mem_Icc' {l : ℝ} (hl : 1 < l) (T : Tree)
    (i : Fin (degree T)) : deltaChild l T (i + 1) ∈ Set.Icc (0 : ℝ) 1 := by
  have hβ0 : ∀ j : Fin (degree T), 0 ≤ escape l (child T (j + 1)) :=
    fun j => (escape_mem_Icc (by linarith) _).1
  have hβle : escape l (child T (i + 1)) ≤ childSum l T :=
    Finset.single_le_sum (fun j _ => hβ0 j) (Finset.mem_univ i)
  have hden : 0 < l - 1 + childSum l T - escape l (child T (i + 1)) := by
    linarith
  constructor
  · exact div_nonneg (by linarith) hden.le
  · exact (div_le_one hden).2 (by linarith)

private theorem one_sub_Wt_le_deltaChild {l : ℝ} (hl : 1 < l) (T : Tree)
    (i : Fin (degree T)) : 1 - Wt l T ≤ deltaChild l T (i + 1) := by
  have hβ : 0 ≤ escape l (child T (i + 1)) := (escape_mem_Icc (by linarith) _).1
  have hβ0 : ∀ j : Fin (degree T), 0 ≤ escape l (child T (j + 1)) :=
    fun j => (escape_mem_Icc (by linarith) _).1
  have hβle : escape l (child T (i + 1)) ≤ childSum l T :=
    Finset.single_le_sum (fun j _ => hβ0 j) (Finset.mem_univ i)
  have hS : 0 ≤ childSum l T := Finset.sum_nonneg fun j _ => hβ0 j
  have hD : 0 < l - 1 + childSum l T := by linarith
  have hDi : 0 < l - 1 + childSum l T - escape l (child T (i + 1)) := by linarith
  have hleft : 1 - Wt l T = (l - 1) / (l - 1 + childSum l T) := by
    unfold Wt
    field_simp [hD.ne']
    ring
  rw [hleft, deltaChild, div_le_div_iff₀ hD hDi]
  nlinarith

theorem measurable_sum_delta_sq' (l : ℝ) :
    Measurable (fun T : Tree => ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2) := by
  have hm : Measurable (fun p : ℕ × Tree =>
      ∑ j ∈ Finset.range p.1, deltaChild l p.2 (j + 1) ^ 2) :=
    measurable_from_prod_countable_right fun k =>
      (Finset.range k).measurable_sum fun j _ =>
        (measurable_deltaChild l (j + 1)).pow_const 2
  convert hm.comp (continuous_degree.measurable.prodMk measurable_id) using 1
  ext T
  exact Fin.sum_univ_eq_sum_range (fun j => deltaChild l T (j + 1) ^ 2) (degree T)

private theorem integrable_degree_split' (h : OffspringHyp μ) :
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

theorem integrable_sum_delta_sq' (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) :
    Integrable (fun T : Tree => ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2)
      (splitLaw μ) := by
  apply (integrable_degree_split' h).mono_nonneg (measurable_sum_delta_sq' l).aestronglyMeasurable
  · filter_upwards with T
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · filter_upwards with T
    calc
      (∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2) ≤
          ∑ _i : Fin (degree T), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hd := deltaChild_mem_Icc' hl T i
        exact (sq_le_one_iff₀ hd.1).2 hd.2
      _ = (degree T : ℝ) := by simp

private theorem ae_degree_two_split (h : OffspringHyp μ) :
    ∀ᵐ T ∂splitLaw μ, 2 ≤ degree T := by
  exact (Measure.ae_smul_measure
    (ae_restrict_mem (measurableSet_le measurable_const continuous_degree.measurable)) _)

/-- At least two children give `M ≤ M_*`. -/
theorem Mtwo_le_Mstar (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : Mtwo μ l ≤ Mstar μ l := by
  letI := splitLaw_prob h
  have hWint : Integrable (fun T : Tree => (1 - Wt l T) ^ 2) (splitLaw μ) := by
    apply Integrable.of_bound ((measurable_const.sub (measurable_Wt l)).pow_const 2).aestronglyMeasurable 1
    filter_upwards with T
    obtain ⟨hW0, hW1⟩ := Wt_mem_Icc' hl T
    simp only [Pi.sub_apply, Pi.one_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff₀ (by linarith)).2 (by linarith)
  have hpoint : ∀ᵐ T ∂splitLaw μ, 2 * (1 - Wt l T) ^ 2 ≤
      ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2 := by
    filter_upwards [ae_degree_two_split h] with T hT
    have hsum : (∑ _i : Fin (degree T), (1 - Wt l T) ^ 2) ≤
        ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hd := one_sub_Wt_le_deltaChild hl T i
      have hW0 : 0 ≤ 1 - Wt l T := by linarith [(Wt_mem_Icc' hl T).2]
      exact (sq_le_sq₀ hW0 (deltaChild_mem_Icc' hl T i).1).2 hd
    have hJ : (2 : ℝ) ≤ degree T := by exact_mod_cast hT
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    nlinarith [sq_nonneg (1 - Wt l T)]
  have hcomp := integral_mono_ae (hWint.const_mul 2) (integrable_sum_delta_sq' h hl) hpoint
  unfold Mtwo Mstar
  rw [← integral_const_mul]
  exact hcomp

end LPPMonotonicityProof.Analytic
