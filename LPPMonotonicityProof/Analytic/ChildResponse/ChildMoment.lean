module

public import LPPMonotonicityProof.Analytic.ChildResponse.Recursion
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Response of one child and its geometric-prefix average

This module splits the response of one child's transformed escape `Y = L W` into a
split-response term and a prefix-length term, for the child-response recursion in
the proof of Lemma 4.5 (`lem:scaled-two-children`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- The split response averaged against `W^(n-1)`, using the measurable
representative. -/
noncomputable def BnMeasurable (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (n : ℕ) : ℝ := ∫ T, Wt l T ^ (n - 1) * Wresp l T ∂splitLaw μ

theorem Bn_eq_BnMeasurable (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : Bn μ l n = BnMeasurable μ l n := by
  unfold Bn BnMeasurable
  apply integral_congr_ae
  filter_upwards [ae_regTree_split h] with T hT
  rw [Bresp_eq_Wresp hT hl hlm]

theorem Wresp_nonneg {T : Tree} (hT : RegTree μ T) (h : OffspringHyp μ)
    {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) : 0 ≤ Wresp l T := by
  rw [← Bresp_eq_Wresp hT hl hlm]
  have h0 : 0 ≤ Wt l T * (1 - Wt l T) :=
    mul_nonneg (Wt_mem_Icc' hl T).1 (sub_nonneg.mpr (Wt_mem_Icc' hl T).2)
  exact h0.trans (Bresp_ge h hT hl hlm)

private theorem present_replicate_prefix {T : Tree} (hT : RegTree μ T) (j : ℕ)
    (hj : j ≤ prefixLen T) : Present T (List.replicate j 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [List.replicate_succ']
      apply (present_append_one_iff _ _ _).2
      have hprev := ih (by omega)
      refine ⟨hprev, ?_⟩
      have hlt : j < prefixLen T := by omega
      have hd : degree (subtree T (List.replicate j 1)) = 1 := by
        by_contra hne
        exact (Nat.notMem_of_lt_sInf hlt) hne
      have hv : T.val (List.replicate j 1) = 1 := by
        have hd' := hd
        change (subtree T (List.replicate j 1)).val [] = 1 at hd'
        simpa only [Speed.subtree_val, List.append_nil] using hd'
      exact ⟨by omega, by omega⟩

theorem regTree_splitTree {T : Tree} (hT : RegTree μ T) : RegTree μ (splitTree T) := by
  exact hT.subtree (present_replicate_prefix hT (prefixLen T) le_rfl)

private theorem Yresp_prefix {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (hsplit : 2 ≤ degree (splitTree T)) :
    Yresp l T = l ^ (-(Gt T : ℤ)) * Wresp l (splitTree T) +
      (l - 1) / l * (Gt T : ℝ) * Yt l T := by
  have hl0 : 0 < l := by positivity
  let z : ℤ := -(Gt T : ℤ)
  have hL : HasDerivAt (fun x : ℝ => x ^ z) ((z : ℝ) * l ^ (z - 1)) l :=
    hasDerivAt_zpow z l (Or.inl hl0.ne')
  have hW := hasDerivAt_Wt (regTree_splitTree hT) hl hlm
  have hprod := hL.fun_mul hW
  have heq : (fun x => Yt x T) =ᶠ[𝓝 l] fun x => x ^ z * Wt x (splitTree T) := by
    filter_upwards [lt_mem_nhds hl] with x hx
    exact Yt_eq_prefix hx T hsplit
  have hYt := hprod.congr_of_eventuallyEq heq
  rw [Yresp_eq_deriv hT hl hlm, hYt.deriv, ← Bresp_eq_Wresp (regTree_splitTree hT) hl hlm,
    Yt_eq_prefix hl T hsplit, Bresp]
  rw [← hW.deriv]
  have hz : (z : ℝ) * l ^ (z - 1) = -(Gt T : ℝ) / l * l ^ z := by
    dsimp [z]
    rw [zpow_sub_one₀ hl0.ne']
    push_cast
    field_simp [hl0.ne']
  rw [hz]
  push_cast
  ring

private theorem integrable_escape_childMoment {l : ℝ} (hl : 0 < l) :
    Integrable (escape l) (GW μ) := by
  apply Integrable.of_bound (measurable_escape l).aestronglyMeasurable 1
  filter_upwards with T
  rw [Real.norm_eq_abs, abs_of_nonneg (escape_mem_Icc hl T).1]
  exact (escape_mem_Icc hl T).2

/-- Integrability of the transformed child response. -/
theorem integrable_Yresp (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : Integrable (Yresp l) (GW μ) := by
  let a := l / 2
  let b := (l + mean μ) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hb : b < mean μ := by dsimp [b]; linarith
  have hx : l ∈ Set.Icc a b := ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
  have hfin : ∫⁻ T, envelope a b T ∂GW μ ≠ ⊤ :=
    (lintegral_envelope_lt_top h ha hab hb).ne
  have hK : Integrable (fun T => (envelope a b T).toReal) (GW μ) :=
    integrable_toReal_of_lintegral_ne_top (measurable_envelope a b).aemeasurable hfin
  have hdom : Integrable (fun T => escape l T / (l - 1) + (envelope a b T).toReal) (GW μ) :=
    (integrable_escape_childMoment (by positivity)).div_const (l - 1) |>.add hK
  apply Integrable.mono' hdom (measurable_Yresp l).aestronglyMeasurable
  filter_upwards [ae_regTree h] with T hT
  have hβ := (escape_mem_Icc (by linarith : 0 < l) T).1
  have hβ1 := (escape_mem_Icc (by linarith : 0 < l) T).2
  have hd := deriv_escape_nonpos_of_reg hT (by linarith) hlm
  have ha1 : 0 < l - 1 := by linarith
  have hD : 0 < l - 1 + escape l T := by linarith
  have hD2 : (l - 1) ^ 2 ≤ (l - 1 + escape l T) ^ 2 := by nlinarith [sq_nonneg (escape l T)]
  have hreg := neg_deriv_escape_le hT ha hab hb hx
  have hC : 0 ≤ -deriv (fun x => escape x T) l := hreg.2.1
  have hCK : -deriv (fun x => escape x T) l ≤ (envelope a b T).toReal := by
    calc
      _ ≤ (envelope a b T).toReal * escape l T := hreg.2.2
      _ ≤ (envelope a b T).toReal * 1 :=
        mul_le_mul_of_nonneg_left hβ1 ENNReal.toReal_nonneg
      _ = _ := mul_one _
  have hfirst : (l - 1) * escape l T / (l - 1 + escape l T) ^ 2 ≤ escape l T / (l - 1) := by
    rw [div_le_div_iff₀ (pow_pos hD 2) ha1]
    nlinarith [mul_nonneg hβ (sub_nonneg.mpr hD2)]
  have hsecond : (l - 1) ^ 2 * (-deriv (fun x => escape x T) l) /
      (l - 1 + escape l T) ^ 2 ≤ -deriv (fun x => escape x T) l := by
    rw [div_le_iff₀ (pow_pos hD 2)]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hD2)]
  rw [Real.norm_eq_abs, abs_of_nonneg (Yresp_nonneg hT hl hlm)]
  calc
    Yresp l T = (l - 1) * escape l T / (l - 1 + escape l T) ^ 2 +
        (l - 1) ^ 2 * (-deriv (fun x => escape x T) l) /
          (l - 1 + escape l T) ^ 2 := by
      rw [Yresp_eq_direct hT hl hlm]
      ring
    _ ≤ escape l T / (l - 1) + (-deriv (fun x => escape x T) l) := add_le_add hfirst hsecond
    _ ≤ escape l T / (l - 1) + (envelope a b T).toReal := add_le_add_right hCK _

/-- Integrability of `Y^(n-1)` times the child response. -/
theorem integrable_childTerm (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (n : ℕ) : Integrable (childTerm l n) (GW μ) := by
  apply Integrable.mono' (integrable_Yresp h hl hlm) (measurable_childTerm l n).aestronglyMeasurable
  filter_upwards [ae_regTree h] with T hT
  have hβ := (escape_mem_Icc (by positivity : 0 < l) T).1
  have hY0 : 0 ≤ Yt l T := by
    exact div_nonneg hβ (by positivity)
  have hY1 : Yt l T ≤ 1 := by
    have hden : 0 < l - 1 + escape l T := by positivity
    exact (div_le_one hden).2 (by linarith)
  have hp : ‖Yt l T ^ (n - 1)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hY0 _)]
    exact pow_le_one₀ hY0 hY1
  rw [childTerm, Real.norm_eq_abs, abs_mul]
  calc
    |Yt l T ^ (n - 1)| * |Yresp l T| ≤ 1 * |Yresp l T| :=
      mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ = Yresp l T := by rw [one_mul, abs_of_nonneg (Yresp_nonneg hT hl hlm)]

/-- The two geometric-prefix pieces of one child response. -/
noncomputable def childPrefixResponse (l : ℝ) (n : ℕ) (g : ℕ) (T : Tree) : ℝ :=
  (l ^ (-(g : ℤ))) ^ n * Wt l T ^ (n - 1) * Wresp l T

noncomputable def childPrefixEscape (l : ℝ) (n : ℕ) (g : ℕ) (T : Tree) : ℝ :=
  (l - 1) / l * (g : ℝ) * (l ^ (-(g : ℤ))) ^ n * Wt l T ^ n

theorem childTerm_eq_prefix (h : OffspringHyp μ) {T : Tree} (hT : RegTree μ T)
    {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) (hsplit : 2 ≤ degree (splitTree T))
    (n : ℕ) (hn : 1 ≤ n) :
    childTerm l n T = childPrefixResponse l n (Gt T) (splitTree T) +
      childPrefixEscape l n (Gt T) (splitTree T) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := n) (by omega)
  rw [childTerm, Yt_eq_prefix hl T hsplit, Yresp_prefix hT hl hlm hsplit,
    Yt_eq_prefix hl T hsplit]
  unfold childPrefixResponse childPrefixEscape
  simp only [Nat.succ_sub_one, mul_pow, pow_succ]
  ring

end LPPMonotonicityProof.Analytic
