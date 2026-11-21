module

public import LPPMonotonicityProof.Analytic.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Geometric-sum estimates for the high-bias argument

This module proves equation (3.3) (`eq:geometric-sum`),
`S(q) ≤ (1 + λ) / (1 + λ - 2q)`, together with the summability of the geometric
reset sum `S(q)`.  Both are used in Lemma 3.3 (`lem:speed-ceiling`) and in the
proof of Theorem 3.7 (`thm:above-two`).

The first proof uses reflection of a finite sum rather than an integral:
pairing exponents `i` and `n - 1 - i` gives the desired Jensen bound.
-/

@[expose] public section

namespace LPPMonotonicityProof.Analytic

open scoped BigOperators

private lemma tangent_pow_le {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) (n : ℕ) :
    c ^ n + n * c ^ n * ((u - c) / c) ≤ u ^ n := by
  have hx : -2 ≤ (u - c) / c := by
    have hx' : -1 ≤ (u - c) / c := by
      rw [le_div_iff₀ hc]
      linarith
    linarith
  have hbern := one_add_mul_le_pow hx n
  have hmul := mul_le_mul_of_nonneg_left hbern (pow_nonneg hc.le n)
  have hid : 1 + (u - c) / c = u / c := by field_simp [hc.ne']; ring
  have hpow : c ^ n * (1 + (u - c) / c) ^ n = u ^ n := by
    rw [hid, div_pow]
    field_simp [hc.ne']
  calc
    c ^ n + n * c ^ n * ((u - c) / c) = c ^ n * (1 + n * ((u - c) / c)) := by ring
    _ ≤ c ^ n * (1 + (u - c) / c) ^ n := hmul
    _ = u ^ n := hpow

/-- Proof of (3.3), first estimate: the normalized geometric sum dominates
powers of the midpoint `(1 + l) / 2`. -/
theorem pow_le_Qgeo_div {l : ℝ} (hl : 1 ≤ l) (j : ℕ) (hj : 1 ≤ j) :
    ((1 + l) / 2) ^ (j - 1) ≤ Qgeo l j / j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hj))
  rcases eq_or_lt_of_le hl with rfl | hl1
  · simp only [Qgeo, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_succ, Nat.succ_sub_one]
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    norm_num [hk]
  let c : ℝ := (1 + l) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hcont : IntervalIntegrable (fun u : ℝ => c ^ k + k * c ^ k * ((u - c) / c))
      MeasureTheory.volume 1 l := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hpowcont : IntervalIntegrable (fun u : ℝ => u ^ k) MeasureTheory.volume 1 l :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hint : (∫ u in (1 : ℝ)..l, (c ^ k + k * c ^ k * ((u - c) / c))) ≤
      ∫ u in (1 : ℝ)..l, u ^ k := by
    apply intervalIntegral.integral_mono_on hl1.le hcont hpowcont
    intro u hu
    exact tangent_pow_le hc (le_trans (by norm_num) hu.1) k
  have hleft : (∫ u in (1 : ℝ)..l, (c ^ k + k * c ^ k * ((u - c) / c))) =
      (l - 1) * c ^ k := by
    have hconst : IntervalIntegrable (fun _ : ℝ => c ^ k) MeasureTheory.volume 1 l :=
      (by fun_prop : Continuous _).intervalIntegrable _ _
    have hlin : IntervalIntegrable (fun u : ℝ => k * c ^ k * ((u - c) / c))
        MeasureTheory.volume 1 l := (by fun_prop : Continuous _).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hconst hlin]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_sub
        ((by fun_prop : Continuous (fun u : ℝ => u)).intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun _ : ℝ => c)).intervalIntegrable _ _)]
    simp [intervalIntegral.integral_const, integral_id, smul_eq_mul, hc.ne']
    dsimp [c]
    ring_nf
    all_goals exact Or.inr trivial
  rw [hleft, integral_pow] at hint
  have hgeom : Qgeo l (k + 1) * (l - 1) = l ^ (k + 1) - 1 := by
    exact geom_sum_mul_of_one_le hl (k + 1)
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  norm_num only [Nat.cast_succ, Nat.succ_sub_one]
  change c ^ k ≤ Qgeo l (k + 1) / ((k : ℝ) + 1)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).2
  apply (mul_le_mul_iff_of_pos_left (sub_pos.mpr hl1)).mp
  calc
    (l - 1) * (c ^ k * ((k : ℝ) + 1)) = ((l - 1) * c ^ k) * ((k : ℝ) + 1) := by ring
    _ ≤ l ^ (k + 1) - 1 := by
      apply (le_div_iff₀ hkpos).mp
      convert hint using 2; norm_num
    _ = Qgeo l (k + 1) * (l - 1) := hgeom.symm
    _ = (l - 1) * Qgeo l (k + 1) := by ring

private lemma Qgeo_pos {l : ℝ} (hl : 1 ≤ l) (n : ℕ) (hn : 1 ≤ n) :
    0 < Qgeo l n := by
  have hmid : 0 < (1 + l) / 2 := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hpow : 0 < ((1 + l) / 2) ^ (n - 1) := pow_pos hmid _
  have hdiv : 0 < Qgeo l n / n :=
    lt_of_lt_of_le hpow (pow_le_Qgeo_div hl n hn)
  exact (div_pos_iff_of_pos_right hnpos).mp hdiv

private lemma Sgeo_term_le {l q : ℝ} (hl : 1 < l) (hq : 0 ≤ q) (j : ℕ) :
    (j + 1) * q ^ j / Qgeo l (j + 1) ≤ (q / ((1 + l) / 2)) ^ j := by
  let c : ℝ := (1 + l) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hQ : 0 < Qgeo l (j + 1) := Qgeo_pos hl.le (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
  have hpow := pow_le_Qgeo_div hl.le (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
  have hjpos : (0 : ℝ) < j + 1 := by positivity
  have hpow' : c ^ j ≤ Qgeo l (j + 1) / ((j : ℝ) + 1) := by
    convert hpow using 1
    all_goals simp [c]
  have hcoef : ((j : ℝ) + 1) * c ^ j ≤ Qgeo l (j + 1) := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mp hpow'
    simpa [mul_comm] using h
  change (j + 1) * q ^ j / Qgeo l (j + 1) ≤ (q / c) ^ j
  rw [div_pow]
  apply (div_le_div_iff₀ hQ (pow_pos hc j)).2
  have hmul := mul_le_mul_of_nonneg_left hcoef (pow_nonneg hq j)
  nlinarith

/-- Absolute convergence of the geometric reset sum. -/
theorem summable_Sgeo {l q : ℝ} (hl : 1 < l) (hq : 0 ≤ q ∧ q < 1) :
    Summable fun j : ℕ => (j + 1) * q ^ j / Qgeo l (j + 1) := by
  let c : ℝ := (1 + l) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hqc0 : 0 ≤ q / c := div_nonneg hq.1 hc.le
  have hqc1 : q / c < 1 := (div_lt_one hc).2 (by dsimp [c]; linarith [hq.2])
  apply (summable_geometric_of_lt_one hqc0 hqc1).of_nonneg_of_le
  · intro j
    have hQ : 0 < Qgeo l (j + 1) :=
      Qgeo_pos hl.le (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
    exact div_nonneg (mul_nonneg (by positivity) (pow_nonneg hq.1 _)) hQ.le
  · intro j
    exact Sgeo_term_le hl hq.1 j

/-- Equation (3.3) (`eq:geometric-sum`): one-step geometric majoration of `Sgeo`. -/
theorem Sgeo_le {l q : ℝ} (hl : 1 < l) (hq : 0 ≤ q ∧ q < 1) :
    Sgeo l q ≤ (1 + l) / (1 + l - 2 * q) := by
  let c : ℝ := (1 + l) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hqc0 : 0 ≤ q / c := div_nonneg hq.1 hc.le
  have hqc1 : q / c < 1 := (div_lt_one hc).2 (by dsimp [c]; linarith [hq.2])
  have hs := summable_Sgeo hl hq
  have hden : 1 + l - 2 * q ≠ 0 := by nlinarith [hq.2]
  have hcq : c - q ≠ 0 := sub_ne_zero.mpr (ne_of_gt (by dsimp [c]; linarith [hq.2]))
  calc
    Sgeo l q = ∑' j : ℕ, (j + 1) * q ^ j / Qgeo l (j + 1) := rfl
    _ ≤ ∑' j : ℕ, (q / c) ^ j :=
      hs.tsum_le_tsum (fun j => Sgeo_term_le hl hq.1 j)
        (summable_geometric_of_lt_one hqc0 hqc1)
    _ = (1 - q / c)⁻¹ := tsum_geometric_of_lt_one hqc0 hqc1
    _ = (1 + l) / (1 + l - 2 * q) := by
      rw [show 1 - q / c = (c - q) / c by field_simp [hc.ne']]
      rw [inv_div]
      apply (div_eq_div_iff hcq hden).2
      dsimp [c]
      ring

end LPPMonotonicityProof.Analytic
