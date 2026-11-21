module

public import LPPMonotonicityProof.Escape.FiniteFlow
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite-depth response calculus

The finite-depth logarithmic response `wN = -λ ∂λ log β⁽ᴺ⁾`, its recursion, and the
finite-depth response defect `2u - (1-b) ≥ 0` for `0 < λ ≤ 1`, from the proof of
Proposition 2.5 (`prop:regularity`).
-/

@[expose] public section

open scoped BigOperators

namespace LPPMonotonicityProof.Analytic

/-- `wN = -λ ∂λ log escapeN`, defined recursively at positive depth. -/
noncomputable def wN (ω : List ℕ → ℕ) (l : ℝ) : ℕ → List ℕ → ℝ
  | 0, _ => 0
  | N + 1, v => (1 - escapeN ω l (N + 1) v) *
      (1 + ∑ i, escapeN ω l N (offChild ω v i) /
        (∑ j, escapeN ω l N (offChild ω v j)) * wN ω l N (offChild ω v i))

private noncomputable def childEscapeSum (ω : List ℕ → ℕ) (l : ℝ) (N : ℕ)
    (v : List ℕ) : ℝ :=
  ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i)

private noncomputable def responseN (ω : List ℕ → ℕ) (l : ℝ) (N : ℕ)
    (v : List ℕ) : ℝ :=
  escapeN ω l N v * wN ω l N v

private theorem childEscapeSum_pos (ω : List ℕ → ℕ) {l : ℝ} (hl : 0 < l)
    {N : ℕ} {v : List ℕ} (hω : LeaflessBelow ω (N + 1) v) :
    0 < childEscapeSum ω l N v := by
  apply Finset.sum_pos
  · intro i _
    exact escapeN_pos ω hl N (offChild ω v i) (hω.2 i)
  · let i0 : Fin (ω v) := ⟨0, hω.1⟩
    exact ⟨i0, Finset.mem_univ i0⟩

/-- The finite-depth derivative formula, for every remaining height and vertex. -/
theorem hasDerivAt_escapeN (ω : List ℕ → ℕ) {l : ℝ} (hl : 0 < l) :
    ∀ (N : ℕ) (v : List ℕ), LeaflessBelow ω N v →
      HasDerivAt (fun l' => escapeN ω l' N v)
        (-(escapeN ω l N v * wN ω l N v) / l) l := by
  intro N
  induction N with
  | zero =>
      intro v _
      simpa [escapeN, wN] using (hasDerivAt_const l (1 : ℝ))
  | succ N ih =>
      intro v hω
      have hS : 0 < childEscapeSum ω l N v := childEscapeSum_pos ω hl hω
      have hchildren : HasDerivAt (fun l' => childEscapeSum ω l' N v)
          (∑ i : Fin (ω v),
            (-(escapeN ω l N (offChild ω v i) * wN ω l N (offChild ω v i)) / l)) l := by
        exact HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
          ih (offChild ω v i) (hω.2 i))
      have hdiv := hchildren.div ((hasDerivAt_id l).add hchildren)
        (ne_of_gt (add_pos hl hS))
      have hA : (∑ i : Fin (ω v),
          (-(escapeN ω l N (offChild ω v i) * wN ω l N (offChild ω v i)) / l)) =
          -(∑ i : Fin (ω v),
            escapeN ω l N (offChild ω v i) * wN ω l N (offChild ω v i)) / l := by
        rw [← Finset.sum_div, Finset.sum_neg_distrib]
      have hB : (∑ i : Fin (ω v), escapeN ω l N (offChild ω v i) /
          childEscapeSum ω l N v * wN ω l N (offChild ω v i)) =
          (∑ i : Fin (ω v),
            escapeN ω l N (offChild ω v i) * wN ω l N (offChild ω v i)) /
              childEscapeSum ω l N v := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      simp only [Pi.add_apply, id_eq] at hdiv
      rw [hA] at hdiv
      convert hdiv using 1
      · ext l'
        rfl
      · simp only [wN, escapeN]
        have hSdef : childEscapeSum ω l N v =
            ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i) := rfl
        rw [← hSdef, hB]
        simp only [childEscapeSum] at *
        field_simp
        ring

/-- Nonnegativity of the logarithmic response. -/
theorem wN_nonneg (ω : List ℕ → ℕ) {l : ℝ} (hl : 0 < l) :
    ∀ (N : ℕ) (v : List ℕ), LeaflessBelow ω N v → 0 ≤ wN ω l N v := by
  intro N
  induction N with
  | zero => intro v _; simp [wN]
  | succ N ih =>
      intro v hω
      have hS : 0 < childEscapeSum ω l N v := childEscapeSum_pos ω hl hω
      have hb : escapeN ω l (N + 1) v ≤ 1 := escapeN_le_one ω hl (N + 1) v
      rw [wN]
      apply mul_nonneg (sub_nonneg.mpr hb)
      apply add_nonneg zero_le_one
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (div_nonneg (escapeN_pos ω hl N _ (hω.2 i)).le hS.le) (ih _ (hω.2 i))

/-- The product recursion `uᴺ = b(1-b) + l/(l+S)² Σuᵢ`, with all
abbreviations of the finite-depth response defect argument (proof of
Proposition 2.5) expanded. -/
theorem uN_rec (ω : List ℕ → ℕ) {l : ℝ} (hl : 0 < l) {N : ℕ} {v : List ℕ}
    (hω : LeaflessBelow ω (N + 1) v) :
    escapeN ω l (N + 1) v * wN ω l (N + 1) v =
      escapeN ω l (N + 1) v * (1 - escapeN ω l (N + 1) v) +
        l / (l + ∑ j : Fin (ω v), escapeN ω l N (offChild ω v j)) ^ 2 *
          ∑ i : Fin (ω v),
            escapeN ω l N (offChild ω v i) * wN ω l N (offChild ω v i) := by
  change responseN ω l (N + 1) v =
    escapeN ω l (N + 1) v * (1 - escapeN ω l (N + 1) v) +
      l / (l + childEscapeSum ω l N v) ^ 2 *
        ∑ i : Fin (ω v), responseN ω l N (offChild ω v i)
  have hS : 0 < childEscapeSum ω l N v := childEscapeSum_pos ω hl hω
  have hb : escapeN ω l (N + 1) v = childEscapeSum ω l N v /
      (l + childEscapeSum ω l N v) := by rfl
  have hsum : (∑ i : Fin (ω v),
      responseN ω l N (offChild ω v i)) = childEscapeSum ω l N v *
      ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i) /
        childEscapeSum ω l N v * wN ω l N (offChild ω v i) := by
    have hS0 : (∑ i : Fin (ω v), escapeN ω l N (offChild ω v i)) ≠ 0 := by
      simpa only [childEscapeSum] using hS.ne'
    simp only [responseN, childEscapeSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hS0]
  rw [hsum]
  simp only [responseN, wN]
  rw [hb]
  have hSdef : childEscapeSum ω l N v =
      ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i) := rfl
  rw [← hSdef]
  field_simp
  ring

private theorem defectN_rec (ω : List ℕ → ℕ) {l : ℝ} (hl : 0 < l) {N : ℕ} {v : List ℕ}
    (hω : LeaflessBelow ω (N + 1) v) :
    (l + childEscapeSum ω l N v) ^ 2 *
        (2 * responseN ω l (N + 1) v - (1 - escapeN ω l (N + 1) v)) / l =
      (ω v : ℝ) - l +
        ∑ i : Fin (ω v),
          (2 * responseN ω l N (offChild ω v i) -
            (1 - escapeN ω l N (offChild ω v i))) := by
  have hS : 0 < childEscapeSum ω l N v := childEscapeSum_pos ω hl hω
  have hb : escapeN ω l (N + 1) v = childEscapeSum ω l N v /
      (l + childEscapeSum ω l N v) := by rfl
  have hu : responseN ω l (N + 1) v =
      escapeN ω l (N + 1) v * (1 - escapeN ω l (N + 1) v) +
        l / (l + childEscapeSum ω l N v) ^ 2 *
          ∑ i : Fin (ω v), responseN ω l N (offChild ω v i) := uN_rec ω hl hω
  rw [hu, hb]
  have hcard : (Finset.univ : Finset (Fin (ω v))).card = ω v := Finset.card_fin (ω v)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum]
  field_simp
  simp only [childEscapeSum, responseN] at *
  ring

/-- The finite-depth response defect `2u - (1-b)` is nonnegative for `0 < l ≤ 1`. -/
theorem defectN_nonneg (ω : List ℕ → ℕ) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    ∀ (N : ℕ) (v : List ℕ), LeaflessBelow ω N v →
      0 ≤ 2 * (escapeN ω l N v * wN ω l N v) - (1 - escapeN ω l N v) := by
  change ∀ (N : ℕ) (v : List ℕ), LeaflessBelow ω N v →
    0 ≤ 2 * responseN ω l N v - (1 - escapeN ω l N v)
  intro N
  induction N with
  | zero => intro v _; simp [responseN, escapeN, wN]
  | succ N ih =>
      intro v hω
      have hS : 0 < childEscapeSum ω l N v := childEscapeSum_pos ω hl hω
      have hroot : 0 ≤ (ω v : ℝ) - l := by
        have hv : (1 : ℝ) ≤ (ω v : ℝ) := by exact_mod_cast hω.1
        linarith
      have hchildren : 0 ≤ ∑ i : Fin (ω v),
          (2 * responseN ω l N (offChild ω v i) -
            (1 - escapeN ω l N (offChild ω v i))) :=
        Finset.sum_nonneg fun i _ => ih _ (hω.2 i)
      have hrhs : 0 ≤ (ω v : ℝ) - l +
          ∑ i : Fin (ω v),
            (2 * responseN ω l N (offChild ω v i) -
              (1 - escapeN ω l N (offChild ω v i))) := add_nonneg hroot hchildren
      rw [← defectN_rec ω hl hω] at hrhs
      have hfactor : 0 < (l + childEscapeSum ω l N v) ^ 2 / l := by positivity
      have hrew : (l + childEscapeSum ω l N v) ^ 2 *
          (2 * responseN ω l (N + 1) v - (1 - escapeN ω l (N + 1) v)) / l =
          ((l + childEscapeSum ω l N v) ^ 2 / l) *
            (2 * responseN ω l (N + 1) v - (1 - escapeN ω l (N + 1) v)) := by ring
      rw [hrew] at hrhs
      exact (mul_nonneg_iff_of_pos_left hfactor).mp hrhs

end LPPMonotonicityProof.Analytic
