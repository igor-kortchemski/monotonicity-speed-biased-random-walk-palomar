module

public import LPPMonotonicityProof.Speed.Signed.Algebra

/-! # Joint forward/backward escape law and escape-recursion algebra -/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The forward and backward root escapes are independent under `ref`. -/
theorem map_ref_escape (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) (hl : 0 < l) :
    (ref μ l hl).map (fun e => (escape l e.fwd, escape l e.bwd)) =
      (escLaw μ l).prod (escLaw μ l) := by
  let backLaw := (bienaymeLaw μ) ⊗ₘ harm l hl
  have hfst : backLaw.map Prod.fst = bienaymeLaw μ := Measure.fst_compProd _ _
  have hback : backLaw.map (escape l ∘ Prod.fst) = escLaw μ l := by
    rw [← Measure.map_map (measurable_escape l) measurable_fst, hfst, escLaw]
  change (Measure.prod (bienaymeLaw μ) backLaw).map
    (fun e => (escape l e.1, escape l e.2.1)) = _
  rw [show (fun e : Tree × (Tree × (ℕ → ℕ)) => (escape l e.1, escape l e.2.1)) =
      Prod.map (escape l) (escape l ∘ Prod.fst) by rfl,
    ← Measure.map_prod_map _ _ (measurable_escape l)
      ((measurable_escape l).comp measurable_fst), hback, escLaw]

theorem integral_ref_escape_prod (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (g : ℝ × ℝ → ℝ)
    (hg : AEStronglyMeasurable g ((escLaw μ l).prod (escLaw μ l))) :
    ∫ e, g (escape l e.fwd, escape l e.bwd) ∂ref μ l hl =
      ∫ p, g p ∂(escLaw μ l).prod (escLaw μ l) := by
  rw [← map_ref_escape μ l hl] at hg ⊢
  exact (integral_map
    (((measurable_escape l).comp measurable_fst).prodMk
      ((measurable_escape l).comp (measurable_fst.comp measurable_snd))).aemeasurable hg).symm

/-- The two-copy denominator is `(1-r)` times the reference denominator,
where `r = S/(l+S)` is the forward root escape. -/
lemma Dfun_mul_Hfun {l r b S : ℝ} (hl : 0 < l) (hS : 0 ≤ S) (hr : r = S / (l + S)) :
    Dfun l r b = (1 - r) * Hfun l b S := by
  have hden : l + S ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hl hS)
  unfold Dfun Hfun
  rw [hr]
  field_simp [hden]
  ring

/-- Algebraic forms of the positive and negative signed numerators. -/
lemma plus_num_div_eq {l r b S : ℝ} (hl : 0 < l) (hS : 0 ≤ S) (hr : r = S / (l + S))
    (hD : Dfun l r b ≠ 0) :
    (S + l * b) / Hfun l b S = l * (r + b - r * b) / Dfun l r b := by
  have hden : l + S ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hl hS)
  have h1 : 1 - r ≠ 0 := by
    intro h
    apply hD
    rw [Dfun_mul_Hfun hl hS hr, h, zero_mul]
  have hH : Hfun l b S ≠ 0 := by
    intro h
    apply hD
    rw [Dfun_mul_Hfun hl hS hr, h, mul_zero]
  rw [Dfun_mul_Hfun hl hS hr, hr]
  field_simp [hden, h1, hH, ne_of_gt hl]
  ring

lemma minus_num_div_eq {l r b S : ℝ} (hl : 0 < l) (hS : 0 ≤ S) (hr : r = S / (l + S))
    (hD : Dfun l r b ≠ 0) :
    (S - l * b) / Hfun l b S = l * (r - b + r * b) / Dfun l r b := by
  have hden : l + S ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hl hS)
  have h1 : 1 - r ≠ 0 := by
    intro h
    apply hD
    rw [Dfun_mul_Hfun hl hS hr, h, zero_mul]
  have hH : Hfun l b S ≠ 0 := by
    intro h
    apply hD
    rw [Dfun_mul_Hfun hl hS hr, h, mul_zero]
  rw [Dfun_mul_Hfun hl hS hr, hr]
  field_simp [hden, h1, hH, ne_of_gt hl]
  ring

/-- Under the symmetric product law, the negative numerator has the same
integral as `b·b'/D`, assuming its integrability. -/
theorem integral_minusTwoCopy_eq_Nval (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ)
    (hint : Integrable (fun p : ℝ × ℝ => l * (p.1 - p.2 + p.1 * p.2) / Dfun l p.1 p.2)
      ((escLaw μ l).prod (escLaw μ l))) :
    (∫ p, l * (p.1 - p.2 + p.1 * p.2) / Dfun l p.1 p.2
      ∂(escLaw μ l).prod (escLaw μ l)) = l * Nval μ l := by
  let ρ := (escLaw μ l).prod (escLaw μ l)
  let M : ℝ × ℝ → ℝ := fun p => l * (p.1 - p.2 + p.1 * p.2) / Dfun l p.1 p.2
  change Integrable M ρ at hint
  let N : ℝ × ℝ → ℝ := fun p => l * (p.1 * p.2) / Dfun l p.1 p.2
  have hms : Integrable (M ∘ Prod.swap) ρ :=
    (Measure.measurePreserving_swap (μ := escLaw μ l) (ν := escLaw μ l)).integrable_comp_of_integrable hint
  have hN : N = fun p => (M p + M p.swap) / 2 := by
    funext p
    dsimp only [M, N, Dfun, Prod.swap]
    ring
  calc
    _ = ∫ p, M p ∂ρ := rfl
    _ = ∫ p, N p ∂ρ := by
      rw [hN]
      simp_rw [div_eq_mul_inv, integral_mul_const]
      have hadd : (∫ a, M a + M a.swap ∂ρ) =
          (∫ a, M a ∂ρ) + ∫ a, M a.swap ∂ρ := integral_add hint hms
      rw [hadd]
      rw [show (∫ p, M p.swap ∂ρ) = ∫ p, M p ∂ρ from integral_prod_swap M]
      ring
    _ = l * Nval μ l := by
      change (∫ p, l * (p.1 * p.2) / Dfun l p.1 p.2 ∂ρ) = l * Nval μ l
      rw [Nval]
      simp_rw [mul_div_assoc]
      exact integral_const_mul l _

end LPPMonotonicityProof.Speed
