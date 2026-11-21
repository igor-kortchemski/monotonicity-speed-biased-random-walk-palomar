module

public import LPPMonotonicityProof.CertA.Enclosure
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp

/-!
# Geometric prefix brackets

The exact `symSum` is the symmetric geometric sum `U_n` of the paper, from the
prefix-factor derivatives in the proof of Lemma 4.5 (`lem:scaled-two-children`).
Its two-step recursion pairs reciprocal powers and avoids a singular
geometric-series formula at `k = 1`.
-/

@[expose] public section

namespace LPPMonotonicityProof.CertA

noncomputable section

/-- $\sum_{j=0}^{n-1}k^{2j-n+1}$ in paired recursive form. -/
def symSum : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 1
  | n + 2, k => k ^ (n + 1) + (k ^ (n + 1))⁻¹ + symSum n k

private lemma reciprocal_pair {z : ℝ} (hz : 0 < z) : 2 ≤ z + z⁻¹ := by
  have heq : z + z⁻¹ - 2 = (z - 1) ^ 2 / z := by
    field_simp
    ring
  have h := div_nonneg (sq_nonneg (z - 1)) hz.le
  linarith

/-- The symmetric sum is at least its number of terms when `k ≥ 1`. -/
theorem symSum_lower (k : ℝ) (hk : 1 ≤ k) (n : ℕ) : (n : ℝ) ≤ symSum n k := by
  induction n using Nat.twoStepInduction with
  | zero => simp [symSum]
  | one => simp [symSum]
  | more n _ ih =>
      have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
      have hp := reciprocal_pair (pow_pos hk0 (n + 1))
      simp only [symSum]
      push_cast
      linarith

/-- A convenient upper bracket, uniform in `1 ≤ k ≤ K`. -/
theorem symSum_upper {k K : ℝ} (hk : 1 ≤ k) (hkK : k ≤ K) (n : ℕ) :
    symSum n k ≤ (n : ℝ) * K ^ (n + 1) := by
  have hK : 1 ≤ K := hk.trans hkK
  induction n using Nat.twoStepInduction with
  | zero => simp [symSum]
  | one =>
      simp only [symSum, Nat.cast_one, one_mul]
      have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hK 2
      norm_num at h ⊢
      exact h
  | more n ih _ =>
      have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
      have hz : 1 ≤ k ^ (n + 1) := one_le_pow₀ hk
      have hzK : k ^ (n + 1) ≤ K ^ (n + 1) :=
        pow_le_pow_left₀ (le_trans zero_le_one hk) hkK (n + 1)
      have hinv : (k ^ (n + 1))⁻¹ ≤ 1 := (inv_le_one₀ (pow_pos hk0 _)).2 hz
      have hKpow : 1 ≤ K ^ (n + 1) := one_le_pow₀ hK
      have hK3 : K ^ (n + 1) ≤ K ^ (n + 2 + 1) :=
        pow_le_pow_right₀ hK (by omega)
      have hmul : (n : ℝ) * K ^ (n + 1) ≤ (n : ℝ) * K ^ (n + 2 + 1) :=
        mul_le_mul_of_nonneg_left hK3 (Nat.cast_nonneg n)
      simp only [symSum]
      push_cast
      nlinarith

/-- Exact prefix factor $A_n=(x k^{1-n}+U_n)^{-1}$. -/
def prefixA (x k : ℝ) (n : ℕ) : ℝ :=
  (x * (k ^ (n - 1))⁻¹ + symSum n k)⁻¹

/-- A rational enclosure of `prefixA`; no square root is computed here. -/
def prefixEnc (x k : Enc) (n : ℕ) (hn : 0 < n) (hx0 : 0 ≤ x.lower)
    (hk : 1 ≤ k.lower) : Enc := Enc.round {
  value := prefixA x.value k.value n
  lower := (x.upper + (n : ℚ) * k.upper ^ (n + 1))⁻¹
  upper := (n : ℚ)⁻¹
  lower_le := by
    have hxr : (0 : ℝ) ≤ x.value := le_trans (by exact_mod_cast hx0) x.lower_le
    have hkr : (1 : ℝ) ≤ k.value := le_trans (by exact_mod_cast hk) k.lower_le
    have hK : (1 : ℝ) ≤ (k.upper : ℝ) := hkr.trans k.le_upper
    have hk0 : 0 < k.value := lt_of_lt_of_le zero_lt_one hkr
    have hz : 1 ≤ k.value ^ (n - 1) := one_le_pow₀ hkr
    have hz0 : 0 < (k.value ^ (n - 1))⁻¹ := inv_pos.mpr (pow_pos hk0 _)
    have hz1 : (k.value ^ (n - 1))⁻¹ ≤ 1 := (inv_le_one₀ (pow_pos hk0 _)).2 hz
    have hxK : x.value * (k.value ^ (n - 1))⁻¹ ≤ x.upper :=
      by simpa using mul_le_mul x.le_upper hz1 hz0.le (le_trans hxr x.le_upper)
    have hlower := symSum_lower k.value hkr n
    have hupper := symSum_upper hkr k.le_upper n
    have hdenLower : (n : ℝ) ≤ x.value * (k.value ^ (n - 1))⁻¹ + symSum n k.value := by
      have := mul_nonneg hxr hz0.le
      linarith
    have hdenUpper : x.value * (k.value ^ (n - 1))⁻¹ + symSum n k.value ≤
        (x.upper : ℝ) + (n : ℝ) * (k.upper : ℝ) ^ (n + 1) := by
      linarith
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hpos : 0 < x.value * (k.value ^ (n - 1))⁻¹ + symSum n k.value :=
      lt_of_lt_of_le hnpos hdenLower
    unfold prefixA
    simp only [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow]
    simpa only [one_div] using one_div_le_one_div_of_le hpos hdenUpper
  le_upper := by
    have hxr : (0 : ℝ) ≤ x.value := le_trans (by exact_mod_cast hx0) x.lower_le
    have hkr : (1 : ℝ) ≤ k.value := le_trans (by exact_mod_cast hk) k.lower_le
    have hk0 : 0 < k.value := lt_of_lt_of_le zero_lt_one hkr
    have hz0 : 0 < (k.value ^ (n - 1))⁻¹ := inv_pos.mpr (pow_pos hk0 _)
    have hlower := symSum_lower k.value hkr n
    have hdenLower : (n : ℝ) ≤ x.value * (k.value ^ (n - 1))⁻¹ + symSum n k.value := by
      have := mul_nonneg hxr hz0.le
      linarith
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    unfold prefixA
    simp only [Rat.cast_inv, Rat.cast_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le hnpos hdenLower }

end
end LPPMonotonicityProof.CertA
