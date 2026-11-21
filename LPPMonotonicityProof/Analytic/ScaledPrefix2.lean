module

public import LPPMonotonicityProof.Analytic.Interface
public import LPPMonotonicityProof.Analytic.ScaledPrefix
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Scalar prefix factors, second part

This module proves the two remaining prefix-factor derivative bounds of the proof of
Lemma 4.5 (`lem:scaled-two-children`), among them `∂ₓAₙ ≥ Aₙ²(cₙ - 1)`, and the lower
bound `M_* ≥ 2 - 9w/4` of the proof of Corollary 4.6 (`cor:small-terminal`). It uses
the definitions of `Analytic/Defs.lean` and the scalar estimates from `ScaledPrefix`.
-/

@[expose] public section

namespace LPPMonotonicityProof.Analytic

open MeasureTheory Filter Topology
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite
open scoped BigOperators

noncomputable section

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem hasDerivAt_Ugeo_kS {l : ℝ} (hl : 1 < l) (n : ℕ) :
    HasDerivAt (fun y => Ugeo (kS y) n)
      (∑ j ∈ Finset.range n,
        (((2 * (j : ℤ) - n + 1 : ℤ) : ℝ) * kS l ^ (2 * (j : ℤ) - n)) *
          (1 / (2 * kS l))) l := by
  have hl0 : l ≠ 0 := by linarith
  have hk0 : kS l ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  unfold Ugeo
  apply HasDerivAt.fun_sum
  intro j hj
  have he : 2 * (j : ℤ) - n + 1 - 1 = 2 * (j : ℤ) - n := by ring
  convert (hasDerivAt_zpow (2 * (j : ℤ) - n + 1) (kS l) (Or.inl hk0)).comp l
    (Real.hasDerivAt_sqrt hl0) using 1
  · ext y
    rfl
  · simp only [kS, he]

private theorem hasDerivAt_xS (μ : Measure ℕ) {l : ℝ} (hl : 1 < l) :
    HasDerivAt (xS μ) (-pBr μ / (l - 1) ^ 2) l := by
  have ha : l - 1 ≠ 0 := by linarith
  convert (hasDerivAt_const l (pBr μ)).div ((hasDerivAt_id l).sub_const 1) ha using 1
  · ext y
    rfl
  · simp only [id_eq]
    ring

private theorem hasDerivAt_kS_zpow {l : ℝ} (hl : 1 < l) (e : ℤ) :
    HasDerivAt (fun y => kS y ^ e)
      ((e : ℝ) * kS l ^ (e - 1) * (1 / (2 * kS l))) l := by
  have hk : 0 < kS l := Real.sqrt_pos.2 (by linarith)
  convert (hasDerivAt_zpow e (kS l) (Or.inl hk.ne')).comp l
    (Real.hasDerivAt_sqrt (by linarith : l ≠ 0)) using 1
  · ext y
    rfl
  · simp only [kS]

/-- The derivative of the non-geometric term in `Acoef⁻¹` is at most one. -/
private theorem dx_prefix_first_le (μ : Measure ℕ) {l : ℝ} (hl : 1 < l)
    (hp : 0 < pBr μ) {n : ℕ} (hn : 1 ≤ n) :
    dx μ (fun y => xS μ y * kS y ^ (1 - (n : ℤ))) l ≤ 1 := by
  have hk : 0 < kS l := Real.sqrt_pos.2 (by linarith)
  have hk1 : 1 ≤ kS l := Real.one_le_sqrt.2 (by linarith)
  have hprod := (hasDerivAt_xS μ hl).mul (hasDerivAt_kS_zpow hl (1 - (n : ℤ)))
  have hprod_fun : (fun y => xS μ y * kS y ^ (1 - (n : ℤ))) =ᶠ[𝓝 l]
      (xS μ * fun y => kS y ^ (1 - (n : ℤ))) :=
    Filter.Eventually.of_forall fun y => rfl
  have hdx : dx μ (fun y => xS μ y * kS y ^ (1 - (n : ℤ))) l =
      kS l ^ (1 - (n : ℤ)) *
        (1 - ((1 - (n : ℤ) : ℝ) * (l - 1) / (2 * l))) := by
    dsimp [dx]
    rw [hprod_fun.deriv_eq, hprod.deriv]
    have hkz : kS l ^ (1 - (n : ℤ) - 1) =
        kS l ^ (1 - (n : ℤ)) / kS l := by
      rw [zpow_sub₀ hk.ne', zpow_one]
    rw [hkz]
    have hks : kS l ^ 2 = l := Real.sq_sqrt (by linarith)
    dsimp [xS]
    field_simp [ne_of_gt hk, ne_of_gt hp, show l - 1 ≠ 0 by linarith]
    push_cast
    rw [hks]
    ring
  cases n with
  | zero => omega
  | succ r =>
      rw [hdx]
      have hpow : kS l ^ (1 - ((r + 1 : ℕ) : ℤ)) = (kS l ^ r)⁻¹ := by
        rw [show 1 - ((r + 1 : ℕ) : ℤ) = -(r : ℤ) by push_cast; ring,
          zpow_neg, zpow_natCast]
      have hfactor : 1 - ((1 - ((r + 1 : ℕ) : ℤ) : ℝ) * (l - 1) / (2 * l)) =
          1 + (r : ℝ) * (l - 1) / (2 * l) := by
        push_cast
        ring
      rw [hpow, hfactor]
      have hstep : (l - 1) / (2 * l) ≤ kS l - 1 := by
        have hks : kS l ^ 2 = l := Real.sq_sqrt (by linarith)
        have hp' : 0 ≤ (2 * kS l + 1) * (kS l - 1) := by positivity
        have hl' : kS l + 1 ≤ 2 * l := by nlinarith
        apply (div_le_iff₀ (by linarith : 0 < 2 * l)).2
        nlinarith
      have hbern : 1 + (r : ℝ) * (kS l - 1) ≤ kS l ^ r := by
        simpa using one_add_mul_le_pow (show -2 ≤ kS l - 1 by linarith) r
      have hscale := mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg r)
      have hfac : 1 + (r : ℝ) * (l - 1) / (2 * l) ≤ kS l ^ r := by
        have hs : 1 + (r : ℝ) * (l - 1) / (2 * l) ≤
            1 + (r : ℝ) * (kS l - 1) := by
          convert add_le_add_left hscale 1 using 1 <;> ring
        exact hs.trans hbern
      calc
        (kS l ^ r)⁻¹ * (1 + (r : ℝ) * (l - 1) / (2 * l)) ≤
            (kS l ^ r)⁻¹ * kS l ^ r :=
          mul_le_mul_of_nonneg_left hfac (inv_nonneg.mpr (pow_pos hk r).le)
        _ = 1 := inv_mul_cancel₀ (pow_ne_zero r hk.ne')

private theorem Acoef_pos' (μ : Measure ℕ) {l : ℝ} (hl : 1 < l) {n : ℕ}
    (hn : 1 ≤ n) : 0 < Acoef μ l n := by
  have hk0 : 0 < kS l := Real.sqrt_pos.2 (by linarith)
  have hx0 : 0 ≤ xS μ l := by
    dsimp [xS, pBr]
    positivity
  have hQ : 0 < Qgeo l n := by
    dsimp [Qgeo]
    exact geom_sum_pos (by linarith) (by omega)
  have hi : 0 < iota μ l n := by
    dsimp [iota]
    positivity
  dsimp [Acoef]
  positivity

/-- Prefix-factor derivatives: the scaled derivative of the inverse paired sum is
nonnegative. -/
theorem dx_inv_Ugeo_nonneg (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (_h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ dx μ (fun y => (Ugeo (kS y) n)⁻¹) l := by
  have hUderiv := hasDerivAt_Ugeo_kS hl n
  have hU : (n : ℝ) ≤ Ugeo (kS l) n := by
    rw [Ugeo_eq_symSum]
    exact CertA.symSum_lower _ (Real.one_le_sqrt.2 (by linarith)) _
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hU0 : 0 < Ugeo (kS l) n := hnR.trans_le hU
  have hinv := hUderiv.inv (ne_of_gt hU0)
  have hinv_fun : (fun y => (Ugeo (kS y) n)⁻¹) =ᶠ[𝓝 l]
      (fun y => Ugeo (kS y) n)⁻¹ :=
    Filter.Eventually.of_forall fun y => rfl
  have hrel : dx μ (fun y => (Ugeo (kS y) n)⁻¹) l =
      (-dx μ (fun y => Ugeo (kS y) n) l) / (Ugeo (kS l) n ^ 2) := by
    dsimp [dx]
    rw [hinv_fun.deriv_eq, hinv.deriv, hUderiv.deriv]
    field_simp
  have hcn0 : 0 ≤ cn μ l n := by
    have hxS : 0 < xS μ l := div_pos (pBr_pos _h) (by linarith)
    have hnp : (0 : ℝ) ≤ (n : ℝ) ^ 2 - 1 := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    dsimp [cn]
    positivity
  have hp : 0 < pBrProv μ := pBr_pos _h
  have hnon : 0 ≤ -dx μ (fun y => Ugeo (kS y) n) l :=
    hcn0.trans (neg_dx_Ugeo_ge μ hl hp hn)
  rw [hrel]
  positivity

/-- Prefix-factor derivatives: `∂ₓAₙ ≥ Aₙ²(cₙ - 1)`. -/
theorem dx_Acoef_ge (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) {n : ℕ} (hn : 1 ≤ n) :
    Acoef μ l n ^ 2 * (cn μ l n - 1) ≤ dx μ (fun y => Acoef μ y n) l := by
  have hp : 0 < pBr μ := pBr_pos h
  have hk : 0 < kS l := Real.sqrt_pos.2 (by linarith)
  have hprod := (hasDerivAt_xS μ hl).mul (hasDerivAt_kS_zpow hl (1 - (n : ℤ)))
  have hprod_fun : (fun y => xS μ y * kS y ^ (1 - (n : ℤ))) =ᶠ[𝓝 l]
      (xS μ * fun y => kS y ^ (1 - (n : ℤ))) :=
    Filter.Eventually.of_forall fun y => rfl
  have hUderiv := hasDerivAt_Ugeo_kS hl n
  have hsum := hprod.add hUderiv
  have heq : (fun y => (Acoef μ y n)⁻¹) =ᶠ[𝓝 l]
      (fun y => xS μ y * kS y ^ (1 - (n : ℤ)) + Ugeo (kS y) n) := by
    filter_upwards [Ioi_mem_nhds hl] with y hy
    exact Acoef_inv μ hy hn
  have hinv := hsum.congr_of_eventuallyEq heq
  have hA0 := Acoef_pos' μ hl hn
  have hback := hinv.inv (inv_ne_zero (ne_of_gt hA0))
  have hdx : dx μ (fun y => Acoef μ y n) l =
      -(Acoef μ l n ^ 2) *
        (dx μ (fun y => xS μ y * kS y ^ (1 - (n : ℤ))) l +
          dx μ (fun y => Ugeo (kS y) n) l) := by
    have hback_fun : (fun y => Acoef μ y n) =ᶠ[𝓝 l]
        (fun y => (Acoef μ y n)⁻¹)⁻¹ :=
      Filter.Eventually.of_forall fun y => by simp
    have hback' := hback.congr_of_eventuallyEq hback_fun
    dsimp [dx]
    rw [hback'.deriv, hprod_fun.deriv_eq, hprod.deriv, hUderiv.deriv]
    field_simp [ne_of_gt hA0]
    ring
  rw [hdx]
  have hfirst := dx_prefix_first_le μ hl hp hn
  have hsecond : cn μ l n ≤ -dx μ (fun y => Ugeo (kS y) n) l :=
    neg_dx_Ugeo_ge μ hl hp hn
  have hcombined : cn μ l n - 1 ≤
      -(dx μ (fun y => xS μ y * kS y ^ (1 - (n : ℤ))) l +
        dx μ (fun y => Ugeo (kS y) n) l) := by linarith
  calc
    Acoef μ l n ^ 2 * (cn μ l n - 1) ≤ Acoef μ l n ^ 2 *
      -(dx μ (fun y => xS μ y * kS y ^ (1 - (n : ℤ))) l +
        dx μ (fun y => Ugeo (kS y) n) l) :=
      mul_le_mul_of_nonneg_left hcombined (sq_nonneg _)
    _ = -Acoef μ l n ^ 2 *
      (dx μ (fun y => xS μ y * kS y ^ (1 - (n : ℤ))) l +
        dx μ (fun y => Ugeo (kS y) n) l) := by ring


/-- Summing the tangent-line inequality for `x⁻²` gives Jensen's inequality
in the algebraic form needed for the child odds. -/
private theorem card_cube_div_sum_sq_le {ι : Type*} (s : Finset ι) (d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 < d i) :
    (s.card : ℝ) ^ 3 / (∑ i ∈ s, d i) ^ 2 ≤ ∑ i ∈ s, (d i)⁻¹ ^ 2 := by
  classical
  by_cases hs : s.Nonempty
  · let N : ℝ := s.card
    let S : ℝ := ∑ i ∈ s, d i
    let m : ℝ := S / N
    have hN : 0 < N := by
      dsimp [N]
      exact_mod_cast hs.card_pos
    have hS : 0 < S := Finset.sum_pos hd hs
    have hm : 0 < m := div_pos hS hN
    have htangent (i : ι) (hi : i ∈ s) :
        1 / m ^ 2 - 2 * (d i - m) / m ^ 3 ≤ (d i)⁻¹ ^ 2 := by
      have heq : (d i)⁻¹ ^ 2 - (1 / m ^ 2 - 2 * (d i - m) / m ^ 3) =
          (d i - m) ^ 2 * (m + 2 * d i) / (d i ^ 2 * m ^ 3) := by
        field_simp [ne_of_gt (hd i hi), ne_of_gt hm]
        ring
      have hnon : 0 ≤ (d i - m) ^ 2 * (m + 2 * d i) / (d i ^ 2 * m ^ 3) := by
        exact div_nonneg
          (mul_nonneg (sq_nonneg _) (by linarith [hd i hi])) (by positivity)
      rw [← heq] at hnon
      linarith
    have hsum := Finset.sum_le_sum fun i hi => htangent i hi
    have hlin : (∑ i ∈ s, (1 / m ^ 2 - 2 * (d i - m) / m ^ 3)) = N / m ^ 2 := by
      have hrw (i : ι) : 1 / m ^ 2 - 2 * (d i - m) / m ^ 3 =
          (1 / m ^ 2 + 2 * m / m ^ 3) - (2 / m ^ 3) * d i := by ring
      simp_rw [hrw, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum]
      have hNS : S = N * m := by
        dsimp [m]
        field_simp
      change N * (1 / m ^ 2 + 2 * m / m ^ 3) - 2 / m ^ 3 * S = N / m ^ 2
      rw [hNS]
      field_simp
      ring
    rw [hlin] at hsum
    have hNm : N / m ^ 2 = N ^ 3 / S ^ 2 := by
      dsimp [m]
      field_simp
    exact hNm ▸ hsum
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    subst s
    simp

private theorem Wt_mem_Icc {l : ℝ} (hl : 1 < l) (T : Tree) :
    Wt l T ∈ Set.Icc (0 : ℝ) 1 := by
  have hS : 0 ≤ childSum l T := by
    exact Finset.sum_nonneg fun i _ => (escape_mem_Icc (by linarith) _).1
  have hden : 0 < l - 1 + childSum l T := by linarith
  constructor
  · exact div_nonneg hS hden.le
  · exact (div_le_one hden).2 (by linarith)

private theorem deltaChild_mem_Icc {l : ℝ} (hl : 1 < l) (T : Tree)
    (_hgood : ∀ i : Fin (degree T), 0 < escape l (child T (i + 1)))
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

/-- Jensen across the child odds (proof of Corollary 4.6): `Σᵢ δᵢ² ≥ f_J(W)`.
The hypothesis `_hgood`, positivity of the child escapes, is not used by the proof. -/
theorem sum_delta_sq_ge {l : ℝ} (hl : 1 < l) (T : Tree) (hdeg : 2 ≤ degree T)
    (_hgood : ∀ i : Fin (degree T), 0 < escape l (child T (i + 1))) :
    (degree T : ℝ) ^ 3 * (1 - Wt l T) ^ 2 / (degree T - Wt l T) ^ 2 ≤
      ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2 := by
  let a : ℝ := l - 1
  let d : Fin (degree T) → ℝ := fun i =>
    a + childSum l T - escape l (child T (i + 1))
  have ha : 0 < a := by dsimp [a]; linarith
  have hS : 0 ≤ childSum l T := by
    exact Finset.sum_nonneg fun i _ => (escape_mem_Icc (by linarith) _).1
  have hd : ∀ i ∈ Finset.univ, 0 < d i := by
    intro i hi
    have hβle : escape l (child T (i + 1)) ≤ childSum l T :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin (degree T) => escape l (child T (j + 1)))
        (fun j _ => (escape_mem_Icc (by linarith) (child T (j + 1))).1)
        (Finset.mem_univ i)
    dsimp [d]
    linarith
  have hden : 0 < a + childSum l T := by linarith
  have hsumd : (∑ i : Fin (degree T), d i) =
      (degree T : ℝ) * a + ((degree T : ℝ) - 1) * childSum l T := by
    dsimp [d]
    simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ]
    simp only [Fintype.card_fin]
    rw [childSum]
    ring
  have hDpos : 0 < ∑ i : Fin (degree T), d i := Finset.sum_pos hd
    (let ⟨i⟩ : Nonempty (Fin (degree T)) := ⟨⟨0, by omega⟩⟩
     ⟨i, Finset.mem_univ i⟩)
  have hone : 1 - Wt l T = a / (a + childSum l T) := by
    dsimp [Wt, a]
    field_simp
    ring
  have hJ : (degree T : ℝ) - Wt l T =
      (∑ i : Fin (degree T), d i) / (a + childSum l T) := by
    rw [hsumd]
    dsimp [Wt]
    field_simp
    ring
  have hJensen := card_cube_div_sum_sq_le Finset.univ d hd
  have hmul := mul_le_mul_of_nonneg_left hJensen (sq_nonneg a)
  have hleft : (degree T : ℝ) ^ 3 * (1 - Wt l T) ^ 2 /
      (degree T - Wt l T) ^ 2 =
      a ^ 2 * ((degree T : ℝ) ^ 3 / (∑ i : Fin (degree T), d i) ^ 2) := by
    rw [hone, hJ]
    field_simp [ne_of_gt hden, ne_of_gt hDpos]
  have hright : a ^ 2 * (∑ i : Fin (degree T), (d i)⁻¹ ^ 2) =
      ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change a ^ 2 * (d i)⁻¹ ^ 2 = (a / d i) ^ 2
    field_simp [ne_of_gt (hd i hi)]
  rw [hleft, ← hright]
  simpa only [Finset.card_univ, Fintype.card_fin] using hmul

private theorem measurable_sum_delta_sq (l : ℝ) :
    Measurable (fun T : Tree => ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2) := by
  have h : Measurable (fun p : ℕ × Tree =>
      ∑ j ∈ Finset.range p.1, deltaChild l p.2 (j + 1) ^ 2) :=
    measurable_from_prod_countable_right fun k =>
      (Finset.range k).measurable_sum fun j _ =>
        (measurable_deltaChild l (j + 1)).pow_const 2
  convert h.comp (continuous_degree.measurable.prodMk measurable_id) using 1
  ext T
  exact Fin.sum_univ_eq_sum_range (fun j => deltaChild l T (j + 1) ^ 2) (degree T)

private theorem ae_split_good (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    ∀ᵐ T ∂splitLaw μ, 2 ≤ degree T ∧
      ∀ i : Fin (degree T), 0 < escape l (child T (i + 1)) := by
  have hbase : ∀ᵐ T ∂GW μ, ∀ i : Fin (degree T),
      0 < escape l (child T (i + 1)) := by
    filter_upwards [ae_escape_pos_subtrees h (by linarith) hlm] with T hT
    intro i
    have hp : Present T [(i : ℕ) + 1] := by
      simp only [present_cons, present_nil, and_true]
      omega
    have hi := hT [(i : ℕ) + 1] hp
    simpa only [subtree_cons, subtree_nil, List.append_nil] using hi
  have hdeg : ∀ᵐ T ∂(GW μ).restrict {T | 2 ≤ degree T}, 2 ≤ degree T :=
    ae_restrict_mem (measurableSet_le measurable_const continuous_degree.measurable)
  have hgood : ∀ᵐ T ∂(GW μ).restrict {T | 2 ≤ degree T},
      ∀ i : Fin (degree T), 0 < escape l (child T (i + 1)) := ae_restrict_of_ae hbase
  exact (Measure.ae_smul_measure hdeg _).and (Measure.ae_smul_measure hgood _)

private theorem integrable_degree_split (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h : OffspringHyp μ) : Integrable (fun T : Tree => (degree T : ℝ)) (splitLaw μ) := by
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

/-- Proof of Corollary 4.6: averaging the pointwise estimate over the split law gives
`M_* ≥ 2 - 9w/4`. -/
theorem Mstar_ge (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    2 - 9 * wbar μ l / 4 ≤ Mstar μ l := by
  letI := splitLaw_prob h
  have hgood : ∀ᵐ T ∂splitLaw μ, 2 ≤ degree T ∧
      ∀ i : Fin (degree T), 0 < escape l (child T (i + 1)) := ae_split_good μ h hl hlm
  have hMint : Integrable
      (fun T : Tree => ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2)
      (splitLaw μ) := by
    apply (integrable_degree_split μ h).mono_nonneg
      (measurable_sum_delta_sq l).aestronglyMeasurable
    · filter_upwards with T
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    · filter_upwards [hgood] with T hT
      calc
        (∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2) ≤
            ∑ _i : Fin (degree T), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have hd := deltaChild_mem_Icc hl T hT.2 i
          exact (sq_le_one_iff₀ hd.1).2 hd.2
        _ = (degree T : ℝ) := by simp
  have hWint : Integrable (Wt l) (splitLaw μ) := by
    apply Integrable.of_bound (measurable_Wt l).aestronglyMeasurable 1
    filter_upwards with T
    have hW := Wt_mem_Icc hl T
    rw [Real.norm_eq_abs, abs_of_nonneg hW.1]
    exact hW.2
  have hLint : Integrable (fun T : Tree => 2 - 9 * Wt l T / 4) (splitLaw μ) :=
    (integrable_const 2).sub ((hWint.const_mul 9).div_const 4)
  have hpoint : (fun T : Tree => 2 - 9 * Wt l T / 4) ≤ᵐ[splitLaw μ]
      fun T => ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2 := by
    filter_upwards [hgood] with T hT
    have hS : 0 < childSum l T := by
      apply Finset.sum_pos (fun i _ => hT.2 i)
      let i : Fin (degree T) := ⟨0, by have := hT.1; omega⟩
      exact ⟨i, Finset.mem_univ i⟩
    have hden : 0 < l - 1 + childSum l T := by linarith
    have hWlt : Wt l T < 1 := by
      exact (div_lt_one hden).2 (by linarith)
    have hj : (2 : ℝ) ≤ degree T := by exact_mod_cast hT.1
    exact (fj_ge hj ⟨(Wt_mem_Icc hl T).1, hWlt⟩).trans
      (sum_delta_sq_ge hl T hT.1 hT.2)
  have hcomp := integral_mono_ae hLint hMint hpoint
  have heval : (∫ T : Tree, (2 - 9 * Wt l T / 4) ∂splitLaw μ) =
      2 - 9 * wbar μ l / 4 := by
    rw [integral_sub (integrable_const 2) ((hWint.const_mul 9).div_const 4),
      integral_div, integral_const_mul]
    simp [wbar, etaW]
  rw [Mstar, ← heval]
  exact hcomp

end
end LPPMonotonicityProof.Analytic
