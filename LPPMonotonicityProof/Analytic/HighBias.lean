module

public import LPPMonotonicityProof.Analytic.GeomSum
public import LPPMonotonicityProof.HighBias.Polynomial
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# High-bias analytic estimates

This module proves two steps of the proof of Theorem 3.7 (`thm:above-two`): the
two-term upper bound `S(q) ≤ S₂`, from two steps of the exact recursion for the
geometric reset sum followed by (3.3) (`eq:geometric-sum`), and the positivity of
`F(S₂)` on the high-bias region `24b + 10a ≥ 8`.  The geometric sums are `Qgeo` and
`Sgeo` of `LPPMonotonicityProof.Analytic.Defs`.
-/

@[expose] public section

namespace LPPMonotonicityProof.Analytic

open scoped BigOperators

private lemma Qgeo_pos' {l : ℝ} (hl : 1 < l) (n : ℕ) (hn : 1 ≤ n) :
    0 < Qgeo l n := by
  have hmid : 0 < (1 + l) / 2 := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  exact (div_pos_iff_of_pos_right hnpos).mp <|
    lt_of_lt_of_le (pow_pos hmid _) (pow_le_Qgeo_div hl.le n hn)

private lemma Sgeo_term_rec {l q : ℝ} (hl : 1 < l) (j : ℕ) :
    (j + 1) * q ^ j / Qgeo l (j + 1) =
      (l - 1) / l * (j + 1) * (q / l) ^ j +
        (1 / l) * ((j + 1) * (q / l) ^ j / Qgeo l (j + 1)) := by
  have hQ : 0 < Qgeo l (j + 1) := Qgeo_pos' hl (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
  have hgeom : Qgeo l (j + 1) * (l - 1) = l ^ (j + 1) - 1 :=
    geom_sum_mul_of_one_le hl.le (j + 1)
  have hl0 : l ≠ 0 := by positivity
  rw [div_pow]
  field_simp [hQ.ne', hl0, pow_ne_zero j hl0, (sub_pos.mpr hl).ne']
  ring_nf at hgeom ⊢
  linear_combination -q ^ j * hgeom

private lemma tsum_succ_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' j : ℕ, (j + 1) * r ^ j) = 1 / (1 - r) ^ 2 := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hns : Summable (fun j : ℕ => (j : ℝ) * r ^ j) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have hgs : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_lt_one hr0 hr1
  calc
    (∑' j : ℕ, (j + 1) * r ^ j) = ∑' j : ℕ, ((j : ℝ) * r ^ j + r ^ j) := by
      apply tsum_congr
      intro j
      ring
    _ = (∑' j : ℕ, (j : ℝ) * r ^ j) + ∑' j : ℕ, r ^ j := hns.tsum_add hgs
    _ = r / (1 - r) ^ 2 + (1 - r)⁻¹ := by
      rw [tsum_coe_mul_geometric_of_norm_lt_one hr, tsum_geometric_of_lt_one hr0 hr1]
    _ = 1 / (1 - r) ^ 2 := by
      have hrne : 1 - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr1)
      field_simp [hrne]
      ring

/-- The exact one-step recursion for the geometric reset sum. -/
theorem Sgeo_rec {l q : ℝ} (hl : 1 < l) (hq : 0 ≤ q ∧ q < 1) :
    Sgeo l q = (l - 1) * l / (l - q) ^ 2 + Sgeo l (q / l) / l := by
  have hr0 : 0 ≤ q / l := div_nonneg hq.1 (by positivity)
  have hr1 : q / l < 1 := (div_lt_one (by positivity)).2 (by linarith [hq.2])
  have hsr := summable_Sgeo hl ⟨hr0, hr1⟩
  have hr : ‖q / l‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hns : Summable (fun j : ℕ => (j : ℝ) * (q / l) ^ j) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have hgs : Summable (fun j : ℕ => (q / l) ^ j) := summable_geometric_of_lt_one hr0 hr1
  have hsC : Summable (fun j : ℕ => (l - 1) / l * (j + 1) * (q / l) ^ j) := by
    exact (hns.add hgs).mul_left ((l - 1) / l) |>.congr (fun j => by ring)
  have hsB : Summable (fun j : ℕ =>
      (1 / l) * ((j + 1) * (q / l) ^ j / Qgeo l (j + 1))) := hsr.mul_left (1 / l)
  have hne : 1 - q / l ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr1)
  calc
    Sgeo l q = ∑' j : ℕ, ((l - 1) / l * (j + 1) * (q / l) ^ j +
        (1 / l) * ((j + 1) * (q / l) ^ j / Qgeo l (j + 1))) := by
      apply tsum_congr
      exact Sgeo_term_rec hl
    _ = (∑' j : ℕ, (l - 1) / l * (j + 1) * (q / l) ^ j) +
        ∑' j : ℕ, (1 / l) * ((j + 1) * (q / l) ^ j / Qgeo l (j + 1)) :=
      hsC.tsum_add hsB
    _ = (l - 1) * l / (l - q) ^ 2 + Sgeo l (q / l) / l := by
      simp_rw [mul_assoc]
      rw [tsum_mul_left, tsum_mul_left]
      change (l - 1) / l * (∑' j : ℕ, (j + 1) * (q / l) ^ j) +
        1 / l * Sgeo l (q / l) = _
      rw [tsum_succ_mul_pow hr0 hr1]
      field_simp [hl.ne', hne, (sub_pos.mpr (show q < l by linarith [hq.2])).ne']

/-- The two-term bound `S(q) ≤ S₂`: two exact recursion steps followed by (3.3). -/
theorem Sgeo_le_S2 {l q : ℝ} (hl : 1 < l) (hq : 0 ≤ q ∧ q < 1) :
    Sgeo l q ≤ HighBias.S2Real (l - 1) (1 - q) := by
  have hr0 : 0 ≤ q / l := div_nonneg hq.1 (by positivity)
  have hr1 : q / l < 1 := (div_lt_one (by positivity)).2 (by linarith [hq.2])
  have hl2 : 1 < l ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hl) (show 0 < l + 1 by linarith)]
  have hs0 : 0 ≤ q / l ^ 2 := div_nonneg hq.1 (by positivity)
  have hs1 : q / l ^ 2 < 1 := (div_lt_one (by positivity)).2 (by linarith [hq.2])
  have hbound := Sgeo_le hl ⟨hs0, hs1⟩
  have hrec0 := Sgeo_rec hl hq
  have hrec1 := Sgeo_rec hl ⟨hr0, hr1⟩
  have hlq : l - q ≠ 0 := by nlinarith [hq.2]
  have hlqr : l - q / l ≠ 0 := by nlinarith
  have hl2q : l ^ 2 - q ≠ 0 := by nlinarith [hq.2]
  have hlast : l ^ 2 * (l + 1) - 2 * q ≠ 0 := by nlinarith [hq.1, hq.2]
  have hlast' : l ^ 2 + l ^ 3 - q * 2 ≠ 0 := by nlinarith [hq.1, hq.2]
  have hden : 1 + l - 2 * (q / l ^ 2) ≠ 0 := by nlinarith [hs1]
  have hthird : ((1 + l) / (1 + l - 2 * (q / l ^ 2))) / l ^ 2 =
      (l + 1) / (l ^ 2 * (l + 1) - 2 * q) := by
    have hl0 : l ≠ 0 := by positivity
    have hinner : 1 + l - 2 * (q / l ^ 2) = (l ^ 2 * (l + 1) - 2 * q) / l ^ 2 := by
      field_simp [hl0, pow_ne_zero 2 hl0]
      ring
    rw [hinner, div_div, div_mul_cancel₀ _ (pow_ne_zero 2 hl0)]
    ring
  calc
    Sgeo l q = (l - 1) * l / (l - q) ^ 2 + Sgeo l (q / l) / l := hrec0
    _ = (l - 1) * l / (l - q) ^ 2 +
        ((l - 1) * l / (l - q / l) ^ 2 + Sgeo l (q / l / l) / l) / l := by rw [hrec1]
    _ = (l - 1) * l / (l - q) ^ 2 + (l - 1) * l ^ 2 / (l ^ 2 - q) ^ 2 +
        Sgeo l (q / l ^ 2) / l ^ 2 := by
      field_simp [hl.ne', hlq, hlqr, hl2q, pow_ne_zero 2 (by positivity : l ≠ 0)]
      ring
    _ ≤ (l - 1) * l / (l - q) ^ 2 + (l - 1) * l ^ 2 / (l ^ 2 - q) ^ 2 +
        ((1 + l) / (1 + l - 2 * (q / l ^ 2))) / l ^ 2 := by gcongr
    _ = HighBias.S2Real (l - 1) (1 - q) := by
      rw [hthird]
      simp only [HighBias.S2Real]
      ring


/-! ## The algebraic factorization and its monotonicity lemmas -/

private noncomputable def highBiasZ (a b : ℝ) : ℝ := a * (1 + a) / (a + b)

private noncomputable def highBiasC (z : ℝ) : ℝ := 1 + 3 * z + z ^ 2

private noncomputable def highBiasPre (L z : ℝ) : ℝ :=
  L - z - L * z / (1 + z) ^ 2 - (1 + L) / (2 + (L + 2) * z)

private noncomputable def highBiasTail (L z : ℝ) : ℝ :=
  L * z ^ 2 / (highBiasC z - L)

private noncomputable def highBiasPhi (L z : ℝ) : ℝ := highBiasPre L z + highBiasTail L z

private lemma highBiasC_sub_pos {L z : ℝ} (hz : 0 < z) (hL : L ≤ 1 + z) :
    0 < highBiasC z - L := by
  have h := sub_nonneg.mpr hL
  simp only [highBiasC]
  nlinarith [sq_nonneg z, mul_pos hz hz]

set_option maxRecDepth 4000 in
private lemma F_S2_eq {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hb1 : b < 1) :
    HighBias.FReal (1 + a) (1 - b) (HighBias.S2Real a b) =
      a * (1 + a) ^ 2 * (highBiasC (highBiasZ a b) - (1 + a)) *
        highBiasPhi (1 + a) (highBiasZ a b) / (highBiasZ a b) ^ 2 := by
  have hab : 0 < a + b := by linarith
  have hu : 1 + a - (1 - b) ≠ 0 := by nlinarith
  have hv : (1 + a) ^ 2 - (1 - b) ≠ 0 := by nlinarith [sq_nonneg a]
  have hw : (1 + a) ^ 2 * (1 + a + 1) - 2 * (1 - b) ≠ 0 := by
    nlinarith [sq_nonneg a]
  have hclear : HighBias.clearingFactorReal a b ≠ 0 := by
    simp only [HighBias.clearingFactorReal]
    exact mul_ne_zero (mul_ne_zero hu (pow_ne_zero 2 hv)) hw
  apply mul_left_cancel₀ hclear
  rw [HighBias.S2Real_clear_denominators a b hu hv hw]
  have hz : 0 < highBiasZ a b := by
    simp only [highBiasZ]
    positivity
  have hza : a ≤ highBiasZ a b := by
    simp only [highBiasZ]
    apply (le_div_iff₀ hab).2
    nlinarith
  have hCz := highBiasC_sub_pos hz (show 1 + a ≤ 1 + highBiasZ a b by linarith)
  have hD : 2 + ((1 + a) + 2) * highBiasZ a b ≠ 0 := by positivity
  have hCz' : -a + highBiasZ a b * 3 + (highBiasZ a b) ^ 2 ≠ 0 := by
    simp only [highBiasC] at hCz
    nlinarith [hCz]
  set z : ℝ := highBiasZ a b with hzdef
  have hzrel : z * (a + b) = a * (1 + a) := by
    rw [hzdef]
    simp only [highBiasZ]
    field_simp [hab.ne']
  have hb_eq : b = a * (1 + a - z) / z := by
    apply (eq_div_iff hz.ne').2
    nlinarith [hzrel]
  rw [hb_eq]
  simp only [HighBias.clearingFactorReal, HighBias.clearedPolynomialReal, highBiasPhi, highBiasPre,
    highBiasTail]
  field_simp [hz.ne', hCz.ne', hD, pow_ne_zero 2 (show 1 + z ≠ 0 by positivity)]
  simp only [highBiasC]
  ring

private lemma highBiasPre_mono {L M z : ℝ} (hz : 0 < z) (hM : 0 ≤ M)
    (hL : M ≤ L) : highBiasPre M z ≤ highBiasPre L z := by
  have hL0 : 0 ≤ L := hM.trans hL
  have hDL : 0 < 2 + (L + 2) * z := by positivity
  have hDM : 0 < 2 + (M + 2) * z := by positivity
  have hid : highBiasPre L z - highBiasPre M z =
      (L - M) * (L * M * z ^ 4 + L * M * z ^ 3 + L * M * z ^ 2 +
        2 * L * z ^ 4 + 4 * L * z ^ 3 + 4 * L * z ^ 2 + 2 * L * z +
        2 * M * z ^ 4 + 4 * M * z ^ 3 + 4 * M * z ^ 2 + 2 * M * z +
        4 * z ^ 4 + 11 * z ^ 3 + 12 * z ^ 2 + 7 * z + 2) /
        ((z + 1) ^ 2 * (L * z + 2 * z + 2) * (M * z + 2 * z + 2)) := by
    simp only [highBiasPre]
    field_simp [hDL.ne', hDM.ne', (show 1 + z ≠ 0 by positivity)]
    ring
  have hnonneg : 0 ≤ highBiasPre L z - highBiasPre M z := by
    rw [hid]
    positivity
  linarith

private lemma highBiasTail_mono {L M z : ℝ} (hz : 0 < z)
    (hML : M ≤ L) (hM : M ≤ 1 + z) (hL : L ≤ 1 + z) :
    highBiasTail M z ≤ highBiasTail L z := by
  have hCM := highBiasC_sub_pos hz hM
  have hCL := highBiasC_sub_pos hz hL
  have hid : highBiasTail L z - highBiasTail M z =
      z ^ 2 * (L - M) * highBiasC z / ((highBiasC z - L) * (highBiasC z - M)) := by
    simp only [highBiasTail]
    field_simp [hCL.ne', hCM.ne']
    simp only [highBiasC]
    ring
  have hnonneg : 0 ≤ highBiasTail L z - highBiasTail M z := by
    rw [hid]
    have hC : 0 ≤ highBiasC z := by simp only [highBiasC]; positivity
    positivity
  linarith

private lemma highBiasPhi_mono {L M z : ℝ} (hz : 0 < z) (hM0 : 0 ≤ M)
    (hML : M ≤ L) (hM : M ≤ 1 + z) (hL : L ≤ 1 + z) :
    highBiasPhi M z ≤ highBiasPhi L z := by
  exact add_le_add (highBiasPre_mono hz hM0 hML) (highBiasTail_mono hz hML hM hL)

private lemma highBiasPrefactor_mono {L M z : ℝ} (_hz : 0 < z) (hM1 : 1 ≤ M)
    (hML : M ≤ L) (hL : L ≤ 1 + z) :
    (M - 1) * M ^ 2 * (highBiasC z - M) ≤ (L - 1) * L ^ 2 * (highBiasC z - L) := by
  let m := M - 1
  let u := L - M
  let t := 1 + z - L
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hMeq : M = 1 + m := by dsimp [m]; ring
  have hLeq : L = 1 + m + u := by dsimp [m, u]; ring
  have hzeq : z = (1 + m + u) - 1 + t := by dsimp [t]; rw [← hLeq]; ring
  rw [hMeq, hLeq]
  simp only [highBiasC]
  rw [hzeq, ← sub_nonneg]
  ring_nf
  positivity


private lemma highBiasPhi_zero_eq (z : ℝ) :
    highBiasPhi z z = z ^ 2 * (z - 1) / (1 + z) ^ 2 - (z + 1) / ((z + 1) ^ 2 + 1) := by
  simp only [highBiasPhi, highBiasPre, highBiasTail, highBiasC]
  ring_nf

private lemma highBiasPhi_zero_pos {z : ℝ} (hz : 9 / 5 ≤ z) : 0 < highBiasPhi z z := by
  let w : ℝ := 9 / 5
  have hw : 0 < w := by dsimp [w]; norm_num
  have hz0 : 0 < z := hw.trans_le hz
  have hratio : w / (w + 1) ≤ z / (z + 1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    dsimp [w]
    nlinarith
  have hleft : 81 / 245 ≤ z ^ 2 * (z - 1) / (1 + z) ^ 2 := by
    have hsq : (w / (w + 1)) ^ 2 ≤ (z / (z + 1)) ^ 2 := by gcongr
    have hmul := mul_le_mul hsq (show w - 1 ≤ z - 1 by dsimp [w]; linarith)
      (by dsimp [w]; norm_num) (sq_nonneg (z / (z + 1)))
    calc
      (81 : ℝ) / 245 = w ^ 2 * (w - 1) / (1 + w) ^ 2 := by dsimp [w]; norm_num
      _ = (w / (w + 1)) ^ 2 * (w - 1) := by ring
      _ ≤ (z / (z + 1)) ^ 2 * (z - 1) := hmul
      _ = z ^ 2 * (z - 1) / (1 + z) ^ 2 := by rw [add_comm 1 z, div_pow]; ring
  have hright : (z + 1) / ((z + 1) ^ 2 + 1) ≤ 70 / 221 := by
    have hfactor : 0 ≤ (z - w) * ((z + 1) * (w + 1) - 1) := by
      apply mul_nonneg (by dsimp [w]; linarith)
      dsimp [w]
      nlinarith
    have hc : (z + 1) * ((w + 1) ^ 2 + 1) ≤ (w + 1) * ((z + 1) ^ 2 + 1) := by
      nlinarith [hfactor]
    calc
      (z + 1) / ((z + 1) ^ 2 + 1) ≤ (w + 1) / ((w + 1) ^ 2 + 1) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        exact hc
      _ = 70 / 221 := by dsimp [w]; norm_num
  rw [highBiasPhi_zero_eq]
  linarith

private lemma F_S2_mono {a b a₀ b₀ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hb1 : b < 1)
    (ha₀ : 0 < a₀) (hb₀ : 0 ≤ b₀) (hb₀1 : b₀ < 1) (hML : a₀ ≤ a)
    (hzq : highBiasZ a₀ b₀ = highBiasZ a b) (hza₀ : a₀ ≤ highBiasZ a b)
    (hphi₀ : 0 < highBiasPhi (1 + a₀) (highBiasZ a b)) :
    HighBias.FReal (1 + a₀) (1 - b₀) (HighBias.S2Real a₀ b₀) ≤
      HighBias.FReal (1 + a) (1 - b) (HighBias.S2Real a b) := by
  have hab : 0 < a + b := by linarith
  have hz : 0 < highBiasZ a b := by simp only [highBiasZ]; positivity
  have hza : a ≤ highBiasZ a b := by
    simp only [highBiasZ]
    apply (le_div_iff₀ hab).2
    nlinarith
  have hCL := highBiasC_sub_pos hz (show 1 + a ≤ 1 + highBiasZ a b by linarith)
  have hCM := highBiasC_sub_pos hz (show 1 + a₀ ≤ 1 + highBiasZ a b by linarith)
  have hpre := highBiasPrefactor_mono hz (show 1 ≤ 1 + a₀ by linarith)
    (show 1 + a₀ ≤ 1 + a by linarith) (show 1 + a ≤ 1 + highBiasZ a b by linarith)
  have hphi := highBiasPhi_mono hz (show 0 ≤ 1 + a₀ by linarith)
    (show 1 + a₀ ≤ 1 + a by linarith) (show 1 + a₀ ≤ 1 + highBiasZ a b by linarith)
    (show 1 + a ≤ 1 + highBiasZ a b by linarith)
  rw [F_S2_eq ha hb hb1, F_S2_eq ha₀ hb₀ hb₀1, hzq]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hz)).2
  calc
    a₀ * (1 + a₀) ^ 2 * (highBiasC (highBiasZ a b) - (1 + a₀)) *
        highBiasPhi (1 + a₀) (highBiasZ a b) ≤
      a * (1 + a) ^ 2 * (highBiasC (highBiasZ a b) - (1 + a)) *
        highBiasPhi (1 + a₀) (highBiasZ a b) := by
      apply mul_le_mul_of_nonneg_right ?_ hphi₀.le
      convert hpre using 1 <;> ring
    _ ≤ a * (1 + a) ^ 2 * (highBiasC (highBiasZ a b) - (1 + a)) *
        highBiasPhi (1 + a) (highBiasZ a b) := by
      apply mul_le_mul_of_nonneg_left hphi
      have haL : 0 < a * (1 + a) ^ 2 := by positivity
      exact (mul_pos haL hCL).le


private lemma F_S2_bzero_pos {a : ℝ} (ha : 0 < a)
    (hz : 9 / 5 ≤ highBiasZ a 0) :
    0 < HighBias.FReal (1 + a) (1 - 0) (HighBias.S2Real a 0) := by
  have hzL : highBiasZ a 0 = 1 + a := by
    simp only [highBiasZ, add_zero]
    field_simp [ha.ne']
  rw [hzL] at hz
  have hz0 : 0 < (1 + a : ℝ) := by positivity
  have hphi := highBiasPhi_zero_pos hz
  have hCL : 0 < highBiasC (1 + a) - (1 + a) := highBiasC_sub_pos hz0 (by linarith)
  rw [F_S2_eq ha (le_refl (0 : ℝ)) (by norm_num), hzL]
  have haL : 0 < a * (1 + a) ^ 2 := by positivity
  have hCphi : 0 < (highBiasC (1 + a) - (1 + a)) * highBiasPhi (1 + a) (1 + a) :=
    mul_pos hCL hphi
  positivity

private lemma phi_pos_of_F_S2_pos {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hb1 : b < 1)
    (hF : 0 < HighBias.FReal (1 + a) (1 - b) (HighBias.S2Real a b)) :
    0 < highBiasPhi (1 + a) (highBiasZ a b) := by
  have hab : 0 < a + b := by linarith
  have hz : 0 < highBiasZ a b := by simp only [highBiasZ]; positivity
  have hza : a ≤ highBiasZ a b := by
    simp only [highBiasZ]
    apply (le_div_iff₀ hab).2
    nlinarith
  have hCz := highBiasC_sub_pos hz (show 1 + a ≤ 1 + highBiasZ a b by linarith)
  rw [F_S2_eq ha hb hb1] at hF
  have hnum := (div_pos_iff_of_pos_right (sq_pos_of_pos hz)).mp hF
  have hpref : 0 < a * (1 + a) ^ 2 * (highBiasC (highBiasZ a b) - (1 + a)) := by
    have haL : 0 < a * (1 + a) ^ 2 := by positivity
    exact mul_pos haL hCz
  exact (mul_pos_iff_of_pos_left hpref).mp hnum


private noncomputable def pressure (z x : ℝ) : ℝ :=
  24 * ((x - 1) * (x - z) / z) + 10 * (x - 1)

/-- Proof of Theorem 3.7: positivity of `F(S₂)` on the high-bias region. -/
theorem F_S2_pos {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hb1 : b < 1)
    (hab : 8 ≤ 24 * b + 10 * a) :
    0 < HighBias.FReal (1 + a) (1 - b) (HighBias.S2Real a b) := by
  let L : ℝ := 1 + a
  let z : ℝ := highBiasZ a b
  have hL : 1 < L := by dsimp [L]; linarith
  have hsum : 0 < a + b := by linarith
  have hz : 0 < z := by dsimp [z, highBiasZ]; positivity
  have hza : a ≤ z := by
    dsimp [z, highBiasZ]
    apply (le_div_iff₀ hsum).2
    nlinarith
  have hzL : z ≤ L := by
    dsimp [z, L, highBiasZ]
    apply (div_le_iff₀ hsum).2
    nlinarith [mul_nonneg ha.le hb]
  have hLz : L ≤ 1 + z := by dsimp [L]; linarith
  have hzrel : z * (a + b) = a * (1 + a) := by
    dsimp [z, highBiasZ]
    field_simp [hsum.ne']
  have hbexpr : b = (L - 1) * (L - z) / z := by
    apply (eq_div_iff hz.ne').2
    dsimp [L] at hzrel ⊢
    nlinarith [hzrel]
  have hPL : pressure z L = 24 * b + 10 * a := by
    rw [hbexpr]
    dsimp [pressure, L]
    ring
  let m₀ : ℝ := max 1 z
  have hm₀1 : 1 ≤ m₀ := le_max_left _ _
  have hm₀z : z ≤ m₀ := le_max_right _ _
  have hm₀L : m₀ ≤ L := max_le hL.le hzL
  have hPm₀ : pressure z m₀ = 10 * (m₀ - 1) := by
    rcases le_total 1 z with hz1 | hz1
    · rw [show m₀ = z from max_eq_right hz1]
      simp [pressure]
    · rw [show m₀ = 1 from max_eq_left hz1]
      simp [pressure]
  have hpcont : ContinuousOn (pressure z) (Set.Icc m₀ L) := by
    have hc : Continuous (pressure z) := by
      unfold pressure
      fun_prop
    exact hc.continuousOn
  by_cases hzero : 8 ≤ pressure z m₀
  · have hz1 : 1 ≤ z := by
      by_contra hn
      have hzlt : z < 1 := lt_of_not_ge hn
      have hm : m₀ = 1 := max_eq_left hzlt.le
      rw [hm, show pressure z 1 = 10 * (1 - 1) from hm ▸ hPm₀] at hzero
      norm_num at hzero
    have hmz : m₀ = z := max_eq_right hz1
    rw [hPm₀, hmz] at hzero
    have hz95 : 9 / 5 ≤ z := by linarith
    let a₀ : ℝ := z - 1
    have ha₀ : 0 < a₀ := by dsimp [a₀]; linarith
    have hzq : highBiasZ a₀ 0 = z := by
      dsimp [a₀, highBiasZ]
      rw [add_zero]
      have hne : z - 1 ≠ 0 := by linarith
      convert mul_div_cancel_left₀ (1 + (z - 1)) hne using 1
      ring
    have hF₀ := F_S2_bzero_pos ha₀ (by rw [hzq]; exact hz95)
    exact lt_of_lt_of_le hF₀ <| F_S2_mono (a₀ := a₀) (b₀ := 0) ha hb hb1 ha₀
      (le_refl 0) (by norm_num) (by dsimp [a₀]; linarith) hzq
      (by dsimp [a₀]; exact sub_le_self z (by norm_num))
      (by simpa [a₀] using highBiasPhi_zero_pos hz95)
  · have hmem : 8 ∈ Set.Icc (pressure z m₀) (pressure z L) := by
      constructor
      · exact le_of_lt (lt_of_not_ge hzero)
      · rw [hPL]
        exact hab
    obtain ⟨M, hMI, hM8⟩ := intermediate_value_Icc hm₀L hpcont hmem
    have hMle : 1 ≤ M := hm₀1.trans hMI.1
    have hM1 : 1 < M := by
      by_contra hn
      have heq : M = 1 := le_antisymm (le_of_not_gt hn) hMle
      subst M
      simp [pressure] at hM8
    have hMz : z ≤ M := hm₀z.trans hMI.1
    let a₀ : ℝ := M - 1
    let b₀ : ℝ := (M - 1) * (M - z) / z
    have ha₀ : 0 < a₀ := by dsimp [a₀]; linarith
    have hb₀ : 0 ≤ b₀ := by
      dsimp [b₀]
      positivity
    have hb_le : b₀ ≤ b := by
      rw [hbexpr]
      dsimp [b₀]
      apply (div_le_div_iff_of_pos_right hz).2
      have hfac : 0 ≤ (L - M) * (L + M - 1 - z) :=
        mul_nonneg (by linarith [hMI.2]) (by linarith)
      dsimp [L] at hfac ⊢
      nlinarith [hfac]
    have hb₀1 : b₀ < 1 := hb_le.trans_lt hb1
    have hzq : highBiasZ a₀ b₀ = z := by
      dsimp [highBiasZ, a₀, b₀]
      field_simp [hz.ne', ha₀.ne']
      ring
    have hab₀ : 24 * b₀ + 10 * a₀ = 8 := hM8
    let u : ℝ := 8 * b₀ / (3 * a₀)
    have hu : 0 ≤ u := by dsimp [u]; positivity
    have huA : HighBias.boundaryAReal u = a₀ := by
      simp only [HighBias.boundaryAReal]
      apply (div_eq_iff (by positivity : 10 + 9 * u ≠ 0)).2
      dsimp [u]
      field_simp [ha₀.ne']
      nlinarith [hab₀]
    have huB : HighBias.boundaryBReal u = b₀ := by
      simp only [HighBias.boundaryBReal]
      apply (div_eq_iff (by positivity : 10 + 9 * u ≠ 0)).2
      dsimp [u]
      field_simp [ha₀.ne']
      nlinarith [hab₀]
    have hF₀ := HighBias.boundary_F_S2_pos hu
    rw [huA, huB] at hF₀
    have hphi₀ := phi_pos_of_F_S2_pos ha₀ hb₀ hb₀1 hF₀
    exact lt_of_lt_of_le hF₀ <| F_S2_mono (a₀ := a₀) (b₀ := b₀) ha hb hb1 ha₀ hb₀ hb₀1
      (by dsimp [a₀, L] at *; linarith [hMI.2]) hzq
      (by dsimp [a₀]; change M - 1 ≤ z; linarith [hMI.2, hLz]) (by rwa [hzq] at hphi₀)

end LPPMonotonicityProof.Analytic
