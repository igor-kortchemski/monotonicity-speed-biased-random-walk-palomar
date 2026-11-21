module

public import LPPMonotonicityProof.CertA.Prefix
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Polyrith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Scalar prefix factors and the first-split lower bound

This module proves the deterministic estimates on the prefix factors `Aₙ` used in the
proof of Lemma 4.5 (`lem:scaled-two-children`) (the paired powers `Uₙ`, the bound
`-∂ₓUₙ ≥ cₙ`, and the exact inverse of `Aₙ`), and the scalar lower bound behind
`M_* ≥ 2 - 9w/4` in the proof of Corollary 4.6 (`cor:small-terminal`).

The definitions with the suffix `Prov` repeat, with the same bodies, the definitions
`pBr`, `Qgeo`, `xS`, `kS`, `iota`, `Acoef`, `dx` and `cn` of `Analytic/Defs.lean`, so
that this module does not depend on that file.
-/

@[expose] public section

namespace LPPMonotonicityProof.Analytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The branching probability `p = P(ν ≥ 2)` (same body as `pBr`). -/
noncomputable def pBrProv (μ : Measure ℕ) : ℝ := (μ (Set.Ici 2)).toReal
/-- The finite geometric sum `Qₙ = Σ_{i<n} λⁱ` (same body as `Qgeo`). -/
def QgeoProv (l : ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, l ^ i
/-- The scaled variable `x = p/(λ-1)` (same body as `xS`). -/
noncomputable def xSProv (μ : Measure ℕ) (l : ℝ) : ℝ := pBrProv μ / (l - 1)
/-- The square-root factor `k = √λ` (same body as `kS`). -/
noncomputable def kSProv (l : ℝ) : ℝ := Real.sqrt l
/-- `ιₙ = (x + Qₙ)⁻¹` (same body as `iota`). -/
noncomputable def iotaProv (μ : Measure ℕ) (l : ℝ) (n : ℕ) : ℝ :=
  (xSProv μ l + QgeoProv l n)⁻¹
/-- The prefix coefficient `Aₙ = kⁿ⁻¹ ιₙ` (same body as `Acoef`). -/
noncomputable def AcoefProv (μ : Measure ℕ) (l : ℝ) (n : ℕ) : ℝ :=
  kSProv l ^ (n - 1) * iotaProv μ l n
/-- The scaled derivative `∂ₓ` (same body as `dx`). -/
noncomputable def dxProv (μ : Measure ℕ) (f : ℝ → ℝ) (l : ℝ) : ℝ :=
  -((l - 1) ^ 2 / pBrProv μ) * deriv f l
/-- The prefix-response coefficient `cₙ` of Lemma 4.5 (same body as `cn`). -/
noncomputable def cnProv (μ : Measure ℕ) (l : ℝ) (n : ℕ) : ℝ :=
  (l - 1) ^ 2 * n * (n ^ 2 - 1) / (12 * xSProv μ l * l ^ (3 / 2 : ℝ))

/-- The paired powers in the inverse prefix factor. -/
def Ugeo (k : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, k ^ (2 * (j : ℤ) - n + 1)

/-- Pair the two new extreme exponents when `n` increases by two. -/
theorem Ugeo_add_two (k : ℝ) (n : ℕ) :
    Ugeo k (n + 2) = k ^ (n + 1) + (k ^ (n + 1))⁻¹ + Ugeo k n := by
  unfold Ugeo
  push_cast
  rw [Finset.sum_range_succ']
  rw [Finset.sum_range_succ]
  push_cast
  rw [show (0 : ℤ) - (↑n + 2) + 1 = -(n + 1 : ℤ) by ring]
  rw [show (2 : ℤ) * (↑n + 1) - (↑n + 2) + 1 = (n + 1 : ℤ) by ring]
  have hterms :
      (∑ x ∈ Finset.range n,
        k ^ (2 * ((x : ℤ) + 1) - (↑n + 2) + 1)) =
        ∑ j ∈ Finset.range n, k ^ (2 * (j : ℤ) - n + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    push_cast
    ring
  rw [hterms]
  rw [show (↑n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) by omega]
  simp only [zpow_natCast, zpow_neg]
  ring

/-- `Ugeo` agrees with the paired symmetric sum `CertA.symSum` of `CertA/Prefix.lean`. -/
theorem Ugeo_eq_symSum (k : ℝ) (n : ℕ) : Ugeo k n = CertA.symSum n k := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Ugeo, CertA.symSum]
  | one => simp [Ugeo, CertA.symSum]
  | more n ihn _ =>
      rw [Ugeo_add_two, ihn]
      rfl

/-- A reciprocal pair is increasing on `[1,∞)`. -/
theorem add_inv_le_add_inv_of_le {z Z : ℝ} (hz : 1 ≤ z) (hzZ : z ≤ Z) :
    z + z⁻¹ ≤ Z + Z⁻¹ := by
  have hz0 : 0 < z := zero_lt_one.trans_le hz
  have hZ0 : 0 < Z := hz0.trans_le hzZ
  have hZ : 1 ≤ Z := hz.trans hzZ
  have hmul : 1 ≤ z * Z := one_le_mul_of_one_le_of_one_le hz hZ
  have hinv : (z * Z)⁻¹ ≤ 1 := (inv_le_one₀ (mul_pos hz0 hZ0)).2 hmul
  have heq : Z + Z⁻¹ - (z + z⁻¹) = (Z - z) * (1 - (z * Z)⁻¹) := by
    field_simp
    ring
  rw [← sub_nonneg, heq]
  exact mul_nonneg (sub_nonneg.mpr hzZ) (sub_nonneg.mpr hinv)

/-- Prefix-factor derivatives (proof of Lemma 4.5): paired powers are monotone above
one. -/
theorem Ugeo_monotoneOn (n : ℕ) : MonotoneOn (fun k => Ugeo k n) (Set.Ici 1) := by
  induction n using Nat.twoStepInduction with
  | zero => intro a ha b hb hab; simp [Ugeo]
  | one => intro a ha b hb hab; simp [Ugeo]
  | more n ihn _ =>
      intro a ha b hb hab
      have ha0 : 0 < a := zero_lt_one.trans_le ha
      have hb0 : 0 < b := zero_lt_one.trans_le hb
      have hpow : a ^ (n + 1) ≤ b ^ (n + 1) :=
        pow_le_pow_left₀ (zero_le_one.trans ha) hab _
      have hpair := add_inv_le_add_inv_of_le (one_le_pow₀ ha) hpow
      simp only [Ugeo_add_two]
      exact add_le_add hpair (ihn ha hb hab)

private theorem hasDerivAt_Ugeo_sqrt {l : ℝ} (hl : 1 < l) (n : ℕ) :
    HasDerivAt (fun y => Ugeo (kSProv y) n)
      (∑ j ∈ Finset.range n,
        (((2 * (j : ℤ) - n + 1 : ℤ) : ℝ) * kSProv l ^ (2 * (j : ℤ) - n)) *
          (1 / (2 * kSProv l))) l := by
  have hl0 : l ≠ 0 := by linarith
  have hk0 : kSProv l ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  unfold Ugeo
  apply HasDerivAt.fun_sum
  intro j hj
  have he : 2 * (j : ℤ) - n + 1 - 1 = 2 * (j : ℤ) - n := by ring
  convert (hasDerivAt_zpow (2 * (j : ℤ) - n + 1) (kSProv l) (Or.inl hk0)).comp l
    (Real.hasDerivAt_sqrt hl0) using 1
  · ext y
    rfl
  · simp only [kSProv, he]

private theorem hasDerivAt_reciprocal_pair {l : ℝ} (hl : 1 < l) (r : ℕ) :
    HasDerivAt (fun y => kSProv y ^ r + (kSProv y ^ r)⁻¹)
      ((r : ℝ) * kSProv l ^ (r - 1) * (1 / (2 * kSProv l)) +
        -((r : ℝ) * kSProv l ^ (r - 1) * (1 / (2 * kSProv l))) /
          (kSProv l ^ r) ^ 2) l := by
  have hl0 : l ≠ 0 := by linarith
  have hk0 : kSProv l ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hk := Real.hasDerivAt_sqrt hl0
  exact (hk.pow r).add ((hk.pow r).inv (pow_ne_zero r hk0))

private theorem dx_Ugeo_add_two (μ : Measure ℕ) {l : ℝ} (hl : 1 < l) (n : ℕ) :
    dxProv μ (fun y => Ugeo (kSProv y) (n + 2)) l =
      dxProv μ (fun y => kSProv y ^ (n + 1) + (kSProv y ^ (n + 1))⁻¹) l +
        dxProv μ (fun y => Ugeo (kSProv y) n) l := by
  have h := (hasDerivAt_reciprocal_pair hl (n + 1)).add (hasDerivAt_Ugeo_sqrt hl n)
  have hfun : ((fun y => kSProv y ^ (n + 1) + (kSProv y ^ (n + 1))⁻¹) +
      (fun y => Ugeo (kSProv y) n)) = (fun y => Ugeo (kSProv y) (n + 2)) := by
    funext y
    exact (Ugeo_add_two _ _).symm
  rw [hfun] at h
  have hderiv := h.deriv
  dsimp [dxProv]
  rw [hderiv, (hasDerivAt_reciprocal_pair hl (n + 1)).deriv,
    (hasDerivAt_Ugeo_sqrt hl n).deriv]
  ring

private theorem cnProv_eq (μ : Measure ℕ) {l : ℝ} (hl : 1 < l)
    (hp : 0 < pBrProv μ) (n : ℕ) :
    cnProv μ l n = (l - 1) ^ 3 * n * (n ^ 2 - 1) /
      (12 * pBrProv μ * kSProv l ^ 3) := by
  have ha : l - 1 ≠ 0 := by linarith
  have hp0 : pBrProv μ ≠ 0 := ne_of_gt hp
  have hrpow : l ^ (3 / 2 : ℝ) = kSProv l ^ 3 := by
    simpa [kSProv] using Real.rpow_div_two_eq_sqrt (3 : ℝ) (by linarith : 0 ≤ l)
  dsimp [cnProv, xSProv]
  rw [hrpow]
  field_simp

private theorem Ugeo_eq_inv_mul_geom {k : ℝ} (hk : 0 < k) {r : ℕ} (hr : 1 ≤ r) :
    Ugeo k r = (k ^ (r - 1))⁻¹ * QgeoProv (k ^ 2) r := by
  rw [Ugeo, QgeoProv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← pow_mul]
  symm
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hk.ne']
  congr 1
  omega

private theorem pow_sub_inv_eq_mul_Ugeo {k : ℝ} (hk : 0 < k) {r : ℕ} (hr : 1 ≤ r) :
    k ^ r - (k ^ r)⁻¹ = (k - k⁻¹) * Ugeo k r := by
  rw [Ugeo_eq_inv_mul_geom hk hr]
  have hgeom := geom_sum_mul (k ^ 2) r
  have hk1 : k ^ (r - 1) ≠ 0 := pow_ne_zero _ hk.ne'
  have hkr : k ^ r ≠ 0 := pow_ne_zero _ hk.ne'
  have hpred : k * k ^ (r - 1) = k ^ r := by
    rw [mul_comm, ← pow_succ]
    congr 1
    omega
  have hkr2 : k ^ (2 * r) = (k ^ r) ^ 2 := by
    simpa [Nat.mul_comm] using pow_mul k r 2
  dsimp [QgeoProv] at *
  calc
    k ^ r - (k ^ r)⁻¹ = (k ^ r)⁻¹ * (k ^ (2 * r) - 1) := by
      rw [hkr2]
      field_simp [hkr]
    _ = (k ^ r)⁻¹ * ((∑ i ∈ Finset.range r, (k ^ 2) ^ i) * (k ^ 2 - 1)) := by
      rw [hgeom, ← pow_mul]
    _ = ((k ^ r)⁻¹ * (k ^ 2 - 1)) * ∑ i ∈ Finset.range r, (k ^ 2) ^ i := by ring
    _ = (k - k⁻¹) * (k ^ (r - 1))⁻¹ * ∑ i ∈ Finset.range r, (k ^ 2) ^ i := by
      have hscalar : (k ^ r)⁻¹ * (k ^ 2 - 1) =
          (k - k⁻¹) * (k ^ (r - 1))⁻¹ := by
        rw [← hpred, mul_inv_rev]
        field_simp [hk.ne']
      simpa only [hscalar, mul_assoc]
    _ = (k - k⁻¹) * ((k ^ (r - 1))⁻¹ * ∑ i ∈ Finset.range r, (k ^ 2) ^ i) :=
      mul_assoc _ _ _

private theorem neg_dx_reciprocal_pair_ge (μ : Measure ℕ) {l : ℝ} (hl : 1 < l)
    (hp : 0 < pBrProv μ) {r : ℕ} (hr : 1 ≤ r) :
    (l - 1) ^ 3 * r ^ 2 / (2 * pBrProv μ * kSProv l ^ 3) ≤
      -dxProv μ (fun y => kSProv y ^ r + (kSProv y ^ r)⁻¹) l := by
  have hk : 0 < kSProv l := Real.sqrt_pos.2 (by linarith)
  have hk1 : 1 ≤ kSProv l := Real.one_le_sqrt.2 (by linarith)
  have hU : (r : ℝ) ≤ Ugeo (kSProv l) r := by
    rw [Ugeo_eq_symSum]
    exact CertA.symSum_lower _ hk1 _
  have hderiv := (hasDerivAt_reciprocal_pair hl r).deriv
  have hdx : -dxProv μ (fun y => kSProv y ^ r + (kSProv y ^ r)⁻¹) l =
      (l - 1) ^ 2 * r / (2 * pBrProv μ) * (kSProv l ^ 2)⁻¹ *
        (kSProv l ^ r - (kSProv l ^ r)⁻¹) := by
    dsimp [dxProv]
    rw [hderiv]
    field_simp [ne_of_gt hk, ne_of_gt hp]
    have hpred : kSProv l ^ (r - 1) * kSProv l = kSProv l ^ r := by
      rw [← pow_succ]
      congr 1
      omega
    simpa [hpred, sub_eq_add_neg]
  rw [hdx, pow_sub_inv_eq_mul_Ugeo hk hr]
  have hfactor : 0 ≤ (l - 1) ^ 2 * r / (2 * pBrProv μ) * (kSProv l ^ 2)⁻¹ := by
    positivity
  have hkdiff : 0 ≤ kSProv l - (kSProv l)⁻¹ := by
    have : (kSProv l)⁻¹ ≤ 1 := (inv_le_one₀ hk).2 hk1
    linarith
  have hmul := mul_le_mul_of_nonneg_left hU
    (mul_nonneg hfactor hkdiff)
  have heq : (l - 1) ^ 2 * r / (2 * pBrProv μ) * (kSProv l ^ 2)⁻¹ *
      (kSProv l - (kSProv l)⁻¹) * r =
      (l - 1) ^ 3 * r ^ 2 / (2 * pBrProv μ * kSProv l ^ 3) := by
    have hk_eq : kSProv l - (kSProv l)⁻¹ = (l - 1) / kSProv l := by
      have hks : kSProv l ^ 2 = l := Real.sq_sqrt (by linarith)
      field_simp [ne_of_gt hk]
      nlinarith
    rw [hk_eq]
    field_simp [ne_of_gt hk, ne_of_gt hp]
  rw [← heq]
  convert hmul using 1 <;> ring


/-- Prefix-factor derivatives (proof of Lemma 4.5): `-∂ₓUₙ ≥ cₙ`. -/
theorem neg_dx_Ugeo_ge (μ : Measure ℕ) {l : ℝ} (hl : 1 < l)
    (hp : 0 < pBrProv μ) {n : ℕ} (hn : 1 ≤ n) :
    cnProv μ l n ≤ -dxProv μ (fun y => Ugeo (kSProv y) n) l := by
  induction n using Nat.twoStepInduction with
  | zero => simp [cnProv, dxProv, Ugeo]
  | one => simp [cnProv, dxProv, Ugeo]
  | more n ihn _ =>
      have hpair := neg_dx_reciprocal_pair_ge μ hl hp (Nat.succ_le_succ (Nat.zero_le n))
      have hrec : cnProv μ l (n + 2) =
          (l - 1) ^ 3 * (n + 1) ^ 2 / (2 * pBrProv μ * kSProv l ^ 3) + cnProv μ l n := by
        rw [cnProv_eq μ hl hp, cnProv_eq μ hl hp]
        push_cast
        ring
      have hpair' : (l - 1) ^ 3 * (n + 1) ^ 2 /
          (2 * pBrProv μ * kSProv l ^ 3) ≤
          -dxProv μ (fun y => kSProv y ^ (n + 1) + (kSProv y ^ (n + 1))⁻¹) l := by
        convert hpair using 1 <;> push_cast <;> ring
      have ihn' : cnProv μ l n ≤ -dxProv μ (fun y => Ugeo (kSProv y) n) l := by
        by_cases hn1 : 1 ≤ n
        · exact ihn hn1
        · have hn0 : n = 0 := by omega
          subst n
          simp [cnProv, dxProv, Ugeo]
      rw [dx_Ugeo_add_two μ hl n, hrec]
      linarith

private theorem inv_pow_eq_zpow {k : ℝ} (_hk : k ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    (k ^ (n - 1))⁻¹ = k ^ (1 - (n : ℤ)) := by
  rw [show 1 - (n : ℤ) = -((n - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]

private theorem inv_pow_mul_pow {k : ℝ} (hk : k ≠ 0) (a b : ℕ) :
    (k ^ a)⁻¹ * k ^ b = k ^ ((b : ℤ) - a) := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hk]
  congr 1
  omega

private theorem QgeoProv_eq_pow {l : ℝ} (hl : 0 ≤ l) (n : ℕ) :
    QgeoProv l n = ∑ i ∈ Finset.range n, kSProv l ^ (2 * i) := by
  apply Finset.sum_congr rfl
  intro i hi
  change l ^ i = (Real.sqrt l) ^ (2 * i)
  calc
    l ^ i = (Real.sqrt l ^ 2) ^ i := by rw [Real.sq_sqrt hl]
    _ = Real.sqrt l ^ (2 * i) := (pow_mul _ _ _).symm

/-- Prefix-factor derivatives (proof of Lemma 4.5): exact inverse
`Aₙ⁻¹ = x k¹⁻ⁿ + Uₙ` of the prefix coefficient. -/
theorem Acoef_inv (μ : Measure ℕ) {l : ℝ} (hl : 1 < l) {n : ℕ} (hn : 1 ≤ n) :
    (AcoefProv μ l n)⁻¹ =
      xSProv μ l * kSProv l ^ (1 - (n : ℤ)) + Ugeo (kSProv l) n := by
  have hk0 : kSProv l ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  rw [AcoefProv, iotaProv, QgeoProv_eq_pow (by linarith : 0 ≤ l)]
  rw [mul_inv_rev, inv_inv, add_mul, Ugeo]
  rw [inv_pow_eq_zpow hk0 hn]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← zpow_natCast, ← zpow_add₀ hk0]
  congr 1
  omega

private theorem Acoef_pos (μ : Measure ℕ) {l : ℝ} (hl : 1 < l) {n : ℕ} (hn : 1 ≤ n) :
    0 < AcoefProv μ l n := by
  have hk0 : 0 < kSProv l := Real.sqrt_pos.2 (by linarith)
  have hx0 : 0 ≤ xSProv μ l := by
    dsimp [xSProv, pBrProv]
    positivity
  have hQ : 0 < QgeoProv l n := by
    dsimp [QgeoProv]
    exact geom_sum_pos (by linarith) (by omega)
  have hi : 0 < iotaProv μ l n := by
    dsimp [iotaProv]
    positivity
  dsimp [AcoefProv]
  positivity

/-- The two deterministic prefix estimates used in the tails of the proof of
Lemma A.1. -/
theorem Acoef_le (μ : Measure ℕ) {l : ℝ} (hl : 1 < l) {n : ℕ} (hn : 1 ≤ n)
    (hp : 0 < pBrProv μ) :
    AcoefProv μ l n ≤ 1 / n ∧
      AcoefProv μ l n ^ 2 ≤ iotaProv μ l (n - 1) - iotaProv μ l n := by
  have hl0 : 0 < l := by linarith
  have hk0 : 0 < kSProv l := Real.sqrt_pos.2 (by linarith)
  have hk1 : 1 ≤ kSProv l := Real.one_le_sqrt.2 (by linarith)
  have hx0 : 0 ≤ xSProv μ l := by
    dsimp [xSProv, pBrProv]
    positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : 0 < AcoefProv μ l n := Acoef_pos μ hl hn
  have hU : (n : ℝ) ≤ Ugeo (kSProv l) n := by
    rw [Ugeo_eq_symSum]
    exact CertA.symSum_lower _ hk1 _
  have hfirst : AcoefProv μ l n ≤ 1 / n := by
    have hinv : (n : ℝ) ≤ (AcoefProv μ l n)⁻¹ := by
      rw [Acoef_inv μ hl hn]
      have : 0 ≤ xSProv μ l * kSProv l ^ (1 - (n : ℤ)) := by positivity
      linarith
    simpa using one_div_le_one_div_of_le hnR hinv
  refine ⟨hfirst, ?_⟩
  have hxpos : 0 < xSProv μ l := by
    dsimp [xSProv]
    exact div_pos hp (by linarith)
  have hQprev : 0 < xSProv μ l + QgeoProv l (n - 1) := by
    have : 0 ≤ QgeoProv l (n - 1) := by
      dsimp [QgeoProv]
      exact Finset.sum_nonneg fun _ _ => pow_nonneg hl0.le _
    positivity
  have hQn : 0 < xSProv μ l + QgeoProv l n := by
    have : 0 < QgeoProv l n := by
      dsimp [QgeoProv]
      exact geom_sum_pos hl0.le (by omega)
    positivity
  have hQle : QgeoProv l (n - 1) ≤ QgeoProv l n := by
    have hns : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [← hns]
    dsimp [QgeoProv]
    rw [Finset.sum_range_succ]
    linarith [pow_nonneg hl0.le (n - 1)]
  have hden : xSProv μ l + QgeoProv l (n - 1) ≤ xSProv μ l + QgeoProv l n := by
    linarith
  have hdiff : QgeoProv l n - QgeoProv l (n - 1) = l ^ (n - 1) := by
    have hns : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [← hns]
    dsimp [QgeoProv]
    rw [Finset.sum_range_succ]
    ring
  have hiota_diff : iotaProv μ l (n - 1) - iotaProv μ l n =
      l ^ (n - 1) / ((xSProv μ l + QgeoProv l (n - 1)) *
        (xSProv μ l + QgeoProv l n)) := by
    dsimp [iotaProv]
    field_simp
    ring_nf
    exact hdiff
  have hfrac : l ^ (n - 1) / (xSProv μ l + QgeoProv l n) ^ 2 ≤
      l ^ (n - 1) / ((xSProv μ l + QgeoProv l (n - 1)) *
        (xSProv μ l + QgeoProv l n)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hQn) (mul_pos hQprev hQn)).2
    have hpow0 : 0 ≤ l ^ (n - 1) := pow_nonneg hl0.le _
    have hmul := mul_le_mul_of_nonneg_right hden hQn.le
    exact mul_le_mul_of_nonneg_left (by nlinarith) hpow0
  rw [hiota_diff]
  have hAsq : AcoefProv μ l n ^ 2 =
      l ^ (n - 1) / (xSProv μ l + QgeoProv l n) ^ 2 := by
    dsimp [AcoefProv, iotaProv]
    have hks : (kSProv l ^ (n - 1)) ^ 2 = l ^ (n - 1) := by
      calc
        (kSProv l ^ (n - 1)) ^ 2 = kSProv l ^ ((n - 1) * 2) := (pow_mul _ _ _).symm
        _ = kSProv l ^ (2 * (n - 1)) := by congr 1; omega
        _ = (kSProv l ^ 2) ^ (n - 1) := pow_mul _ _ _
        _ = l ^ (n - 1) := by rw [show kSProv l ^ 2 = l from Real.sq_sqrt hl0.le]
    calc
      (kSProv l ^ (n - 1) * (xSProv μ l + QgeoProv l n)⁻¹) ^ 2 =
          l ^ (n - 1) * ((xSProv μ l + QgeoProv l n)⁻¹) ^ 2 := by rw [pow_two, ← hks]; ring
      _ = l ^ (n - 1) / (xSProv μ l + QgeoProv l n) ^ 2 := by
        rw [div_eq_mul_inv, inv_pow]
  exact hAsq.trans_le hfrac

/-- Proof of Corollary 4.6: the universal scalar lower bound
`fⱼ(z) = j³(1-z)²/(j-z)² ≥ 2 - 9z/4` for `j ≥ 2`. -/
theorem fj_ge {j z : ℝ} (hj : 2 ≤ j) (hz : 0 ≤ z ∧ z < 1) :
    2 - 9 * z / 4 ≤ j ^ 3 * (1 - z) ^ 2 / (j - z) ^ 2 := by
  have hjz : 0 < j - z := by linarith
  have h2z : 0 < 2 - z := by linarith
  by_cases hcase : 3 * z ≤ 2
  · let Q : ℝ := (2 - z) ^ 2 * j ^ 2 + 2 * z * (z - 4) * j + 4 * z ^ 2
    have hfour : 0 ≤ 4 * (2 - z) ^ 2 + 2 * z * (z - 4) := by
      nlinarith [sq_nonneg z]
    have hB : 0 ≤ (2 - z) ^ 2 * (j + 2) + 2 * z * (z - 4) := by
      have hj4 : 4 ≤ j + 2 := by linarith
      have := mul_le_mul_of_nonneg_left hj4 (sq_nonneg (2 - z))
      nlinarith
    have hQ : 0 ≤ Q := by
      have hQeq : Q = 4 * (2 - z) * (2 - 3 * z) +
          (j - 2) * ((2 - z) ^ 2 * (j + 2) + 2 * z * (z - 4)) := by
        dsimp [Q]
        ring
      rw [hQeq]
      exact add_nonneg (by positivity) (mul_nonneg (by linarith) hB)
    have hcompare : 8 * (1 - z) ^ 2 / (2 - z) ^ 2 ≤
        j ^ 3 * (1 - z) ^ 2 / (j - z) ^ 2 := by
      have hid : j ^ 3 * (1 - z) ^ 2 / (j - z) ^ 2 -
          8 * (1 - z) ^ 2 / (2 - z) ^ 2 =
          (1 - z) ^ 2 * (j - 2) * Q / ((2 - z) ^ 2 * (j - z) ^ 2) := by
        dsimp [Q]
        field_simp
        ring
      have hnon : 0 ≤ (1 - z) ^ 2 * (j - 2) * Q / ((2 - z) ^ 2 * (j - z) ^ 2) := by
        exact div_nonneg
          (mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hQ) (by positivity)
      rw [← hid] at hnon
      linarith
    have hid : 2 - 9 * z / 4 = 8 * (1 - z) ^ 2 / (2 - z) ^ 2 -
        z * (2 - 3 * z) ^ 2 / (4 * (2 - z) ^ 2) := by
      field_simp
      ring
    have hzex : 0 ≤ z * (2 - 3 * z) ^ 2 / (4 * (2 - z) ^ 2) := by
      exact div_nonneg (mul_nonneg hz.1 (sq_nonneg _)) (by positivity)
    rw [hid]
    linarith
  · have hz23 : 2 / 3 ≤ z := by linarith
    have hz0 : 0 < z := by linarith
    have hcompare : 27 * z * (1 - z) ^ 2 / 4 ≤
        j ^ 3 * (1 - z) ^ 2 / (j - z) ^ 2 := by
      have hid : j ^ 3 * (1 - z) ^ 2 / (j - z) ^ 2 -
          27 * z * (1 - z) ^ 2 / 4 =
          (1 - z) ^ 2 * (j - 3 * z) ^ 2 * (4 * j - 3 * z) /
            (4 * (j - z) ^ 2) := by
        field_simp
        ring
      have : 0 ≤ j ^ 3 * (1 - z) ^ 2 / (j - z) ^ 2 -
          27 * z * (1 - z) ^ 2 / 4 := by
        rw [hid]
        have hfactor : 0 ≤ 4 * j - 3 * z := by linarith
        exact div_nonneg
          (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hfactor) (by positivity)
      linarith
    have hend : 2 - 9 * z / 4 ≤ 27 * z * (1 - z) ^ 2 / 4 := by
      have hid : 27 * z * (1 - z) ^ 2 / 4 - (2 - 9 * z / 4) =
          (3 * z - 2) ^ 3 / 4 := by ring
      have : 0 ≤ (3 * z - 2) ^ 3 / 4 := by exact div_nonneg (pow_nonneg (by linarith) _) (by norm_num)
      linarith
    exact hend.trans hcompare

end
end LPPMonotonicityProof.Analytic
