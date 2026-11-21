module

public import LPPMonotonicityProof.Analytic.Regularity.Mean
public import LPPMonotonicityProof.RTL.Leafless
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Inverse escape moments: scalar bounds and finite depth

First part of Lemma 2.4 (`lem:inverse-moment`): the scalar bounds `1/m ≤ U < 1` for
`U = E[1/ν]`, and integrability of the reciprocal finite-depth escape. The inverse
moment itself is bounded in `Regularity/InverseMoment.lean`. Private helper lemmas
whose names end in `Prov` are local measurability and root-child facts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem integrable_nat_invProv : Integrable (fun k : ℕ => (k : ℝ)⁻¹) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  filter_upwards with k
  cases k with
  | zero => simp
  | succ k =>
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((k + 1 : ℕ) : ℝ)⁻¹)]
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.succ_pos k

private theorem integrable_natCast_invProv (h : OffspringHyp μ) :
    Integrable (fun k : ℕ => (k : ℝ)) μ := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun k => Nat.cast_nonneg k)).2
  simpa only [ENNReal.ofReal_natCast] using h.mean_lt_top


private theorem integral_natCast_eq_mean_invProv :
    (∫ k : ℕ, (k : ℝ) ∂μ) = mean μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun k => Nat.cast_nonneg k)
    (measurable_of_countable _).aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast, mean]

private theorem leaflessBelow_invProv {T : Tree}
    (hT : ∀ v, Present T v → 1 ≤ T.val v) :
    ∀ (N : ℕ) (v : Address), Present T v → LeaflessBelow T.val N v := by
  intro N
  induction N with
  | zero => intro v _; trivial
  | succ N ih =>
      intro v hv
      refine ⟨hT v hv, fun i => ih _ ?_⟩
      exact (present_append_singleton T v (i.val + 1) hv).2 ⟨Nat.succ_pos _, i.isLt⟩
private theorem ae_nat_one_leProv (h : OffspringHyp μ) : ∀ᵐ k : ℕ ∂μ, 1 ≤ k := by
  rw [ae_iff]
  have hs : {k : ℕ | ¬1 ≤ k} = {0} := by ext k; simp
  rw [hs]
  exact h.zero

private theorem invMean_nonnegProv : 0 ≤ invMean μ := by
  apply integral_nonneg_of_ae
  exact ae_of_all _ fun k => inv_nonneg.mpr (Nat.cast_nonneg k)

/-- The two scalar bounds for `U = E[1/ν]`. -/
theorem invMean_bounds (h : OffspringHyp μ) : 1 / mean μ ≤ invMean μ ∧ invMean μ < 1 := by
  have hnat := integrable_natCast_invProv h
  have hinv := integrable_nat_invProv (μ := μ)
  have hle : ∀ᵐ k : ℕ ∂μ, (k : ℝ) ∈ Set.Ici 1 := by
    filter_upwards [ae_nat_one_leProv h] with k hk
    change (1 : ℝ) ≤ k
    exact_mod_cast hk
  have hcomp : Integrable ((fun x : ℝ => x⁻¹) ∘ (fun k : ℕ => (k : ℝ))) μ := by
    simpa only [Function.comp_def] using hinv
  have hconv : ConvexOn ℝ (Set.Ici 1) (fun x : ℝ => x⁻¹) := by
    have hc := (convexOn_zpow (-1 : ℤ) (𝕜 := ℝ)).subset (s := Set.Ici 1)
      (fun x hx => lt_of_lt_of_le zero_lt_one hx) (convex_Ici 1)
    simpa only [zpow_neg_one] using hc
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Ici 1) := by
    apply continuousOn_inv₀.mono
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
  have hj := hconv.map_integral_le hc isClosed_Ici hle hnat hcomp
  rw [integral_natCast_eq_mean_invProv] at hj
  have hmean : 1 / mean μ ≤ invMean μ := by
    change 1 / mean μ ≤ ∫ k : ℕ, (k : ℝ)⁻¹ ∂μ
    simpa only [Function.comp_def, one_div] using hj
  have hdiffInt : Integrable (fun k : ℕ => 1 - (k : ℝ)⁻¹) μ := (integrable_const 1).sub hinv
  have hdiffNonneg : 0 ≤ᵐ[μ] (fun k : ℕ => 1 - (k : ℝ)⁻¹) := by
    filter_upwards [ae_nat_one_leProv h] with k hk
    apply sub_nonneg.mpr
    apply inv_le_one_of_one_le₀
    exact_mod_cast hk
  obtain ⟨k, hk, hμk⟩ := exists_degree_ge_two h
  have hsupp : ({k} : Set ℕ) ⊆ Function.support (fun k : ℕ => 1 - (k : ℝ)⁻¹) := by
    intro j hj
    rw [Set.mem_singleton_iff] at hj
    subst j
    simp only [Function.mem_support]
    have hkreal : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    have hinvlt : (k : ℝ)⁻¹ < 1 := by
      apply (inv_lt_one₀ (by linarith : (0 : ℝ) < k)).2
      exact hkreal
    linarith
  have hmpos : 0 < μ (Function.support (fun k : ℕ => 1 - (k : ℝ)⁻¹)) :=
    (pos_iff_ne_zero.mpr hμk).trans_le (measure_mono hsupp)
  have hpos := (integral_pos_iff_support_of_nonneg_ae hdiffNonneg hdiffInt).2 hmpos
  rw [integral_sub (integrable_const 1) hinv, integral_const, probReal_univ, one_smul] at hpos
  exact ⟨hmean, by unfold invMean; linarith⟩

private theorem measurable_escapeN_treeProv (l : ℝ) (N : ℕ) (v : Address) :
    Measurable (fun T : Tree => escapeN T.val l N v) := by
  induction N generalizing v with
  | zero => simp [escapeN]
  | succ N ih =>
      have hsum : Measurable (fun T : Tree =>
          ∑ j ∈ Finset.range (T.val v), escapeN T.val l N (v ++ [j + 1])) := by
        have h : Measurable (fun p : ℕ × Tree =>
            ∑ j ∈ Finset.range p.1, escapeN p.2.val l N (v ++ [j + 1])) :=
          measurable_from_prod_countable_right fun k =>
            (Finset.range k).measurable_sum fun j _ => ih (v ++ [j + 1])
        exact h.comp ((continuous_offspring v).measurable.prodMk measurable_id)
      have hsum' : Measurable (fun T : Tree =>
          ∑ i : Fin (T.val v), escapeN T.val l N (offChild T.val v i)) := by
        have heq : (fun T : Tree => ∑ i : Fin (T.val v),
            escapeN T.val l N (offChild T.val v i)) =
            (fun T : Tree => ∑ j ∈ Finset.range (T.val v),
              escapeN T.val l N (v ++ [j + 1])) := by
          funext T
          simpa only [offChild] using Fin.sum_univ_eq_sum_range
            (fun j => escapeN T.val l N (v ++ [j + 1])) (T.val v)
        rw [heq]
        exact hsum
      change Measurable (fun T : Tree =>
        (∑ i : Fin (T.val v), escapeN T.val l N (offChild T.val v i)) /
          (l + ∑ i : Fin (T.val v), escapeN T.val l N (offChild T.val v i)))
      exact hsum'.div (measurable_const.add hsum')

private noncomputable def recipN (l : ℝ) (T : Tree) (N : ℕ) : ℝ :=
  (escapeN T.val l N [])⁻¹

private theorem recipN_nonneg {l : ℝ} (hl : 0 < l) (T : Tree) (N : ℕ) : 0 ≤ recipN l T N := by
  exact inv_nonneg.mpr (escapeN_nonneg' T.val hl N [])

private theorem escapeN_ge_pow_prov {ω : Address → ℕ} {l : ℝ} (hl : 0 < l) :
    ∀ (N : ℕ) (v : Address), LeaflessBelow ω N v →
      (1 + l)⁻¹ ^ N ≤ escapeN ω l N v := by
  intro N
  induction N with
  | zero => intro v _; simp [escapeN]
  | succ N ih =>
      intro v hv
      let q : ℝ := (1 + l)⁻¹
      have hq : 0 < q := inv_pos.mpr (by linarith)
      have hq1 : q ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have hqN : 0 < q ^ N := pow_pos hq N
      have hqN1 : q ^ N ≤ 1 := pow_le_one₀ hq.le hq1
      have hb (i : Fin (ω v)) : q ^ N ≤ escapeN ω l N (offChild ω v i) := ih _ (hv.2 i)
      have hb0 (i : Fin (ω v)) : 0 < escapeN ω l N (offChild ω v i) :=
        escapeN_pos ω hl N _ (hv.2 i)
      let i0 : Fin (ω v) := ⟨0, hv.1⟩
      have hS : q ^ N ≤ ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i) := by
        calc
          q ^ N ≤ escapeN ω l N (offChild ω v i0) := hb i0
          _ ≤ _ := Finset.single_le_sum (fun i _ => (hb0 i).le) (Finset.mem_univ i0)
      rw [escapeN]
      have hSpos : 0 < ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i) :=
        hqN.trans_le hS
      have hstep : q ^ N / (l + q ^ N) ≤
          (∑ i : Fin (ω v), escapeN ω l N (offChild ω v i)) /
            (l + ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i)) := by
        apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg hl hqN.le)
          (add_pos_of_pos_of_nonneg hl hSpos.le)).2
        nlinarith [mul_le_mul_of_nonneg_left hS hl.le]
      have hstep2 : q ^ (N + 1) ≤ q ^ N / (l + q ^ N) := by
        have hden : 0 < l + q ^ N := add_pos_of_pos_of_nonneg hl hqN.le
        have hqle : q ≤ 1 / (l + q ^ N) := by
          apply (le_div_iff₀ hden).2
          have hmul : q * (l + q ^ N) = (l + q ^ N) / (1 + l) := by
            dsimp only [q]
            field_simp [(show 0 < 1 + l by linarith).ne']
          rw [hmul]
          exact (div_le_one (by linarith : 0 < 1 + l)).2 (by linarith)
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hqle) hqN.le
      exact hstep2.trans hstep

private theorem recipN_le {l : ℝ} (hl : 0 < l) {T : Tree}
    (hT : ∀ v, Present T v → 1 ≤ T.val v) (N : ℕ) :
    recipN l T N ≤ (1 + l) ^ N := by
  have hb := escapeN_ge_pow_prov (ω := T.val) hl N []
  specialize hb (leaflessBelow_invProv hT N [] (present_nil T))
  have hq : 0 < (1 + l)⁻¹ ^ N := pow_pos (inv_pos.mpr (by linarith)) N
  have hle : 1 / escapeN T.val l N [] ≤ 1 / ((1 + l)⁻¹ ^ N) :=
    one_div_le_one_div_of_le hq hb
  simpa only [recipN, one_div, inv_pow, inv_inv] using hle

private theorem integrable_recipN (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (N : ℕ) :
    Integrable (recipN l · N) (GW μ) := by
  apply Integrable.of_bound ((measurable_escapeN_treeProv l N []).inv).aestronglyMeasurable
    ((1 + l) ^ N)
  filter_upwards [LPPMonotonicityProof.RTL.Leafless.ae_present_offspring_pos μ h.zero] with T hT
  change |(escapeN T.val l N [])⁻¹| ≤ (1 + l) ^ N
  rw [abs_of_nonneg (inv_nonneg.mpr (escapeN_nonneg' T.val hl N []))]
  exact recipN_le hl hT N

private theorem lintegral_recipN (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (N : ℕ) :
    ∫⁻ T, ENNReal.ofReal (recipN l T N) ∂GW μ =
      ENNReal.ofReal (∫ T, recipN l T N ∂GW μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_recipN h hl N)
    (ae_of_all _ fun T => recipN_nonneg hl T N)]

end LPPMonotonicityProof.Analytic
