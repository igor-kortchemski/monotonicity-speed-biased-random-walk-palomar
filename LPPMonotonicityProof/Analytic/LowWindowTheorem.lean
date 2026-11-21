module

public import LPPMonotonicityProof.Analytic.BelowOneTheorem
public import LPPMonotonicityProof.Analytic.CostExport
public import LPPMonotonicityProof.Analytic.LowWindow
public import LPPMonotonicityProof.Analytic.LowWindowReduced
public import LPPMonotonicityProof.Analytic.LowWindowScalar2
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Strict negativity on the low-bias window

This module proves Theorem 4.3 (`thm:low-window`).
It combines the reduced low-window inequality with the scalar positivity test,
and uses a first nonnegative derivative point to reduce to biases whose speed
is at most the speed at bias one.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open LPPMonotonicityProof.Speed

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private lemma pBr_le_one (h : OffspringHyp μ) : pBr μ ≤ 1 := by
  have hpq := p1_add_pBr h
  have hq : 0 ≤ p1 μ := ENNReal.toReal_nonneg
  linarith

/-- The reduced estimate and the scalar test give a positive cost whenever the
speed has not risen above its bias-one value. -/
private lemma cost_pos_of_speedValue_le_one (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8)
    (hv : Speed.speedValue μ l ≤ Speed.speedValue μ 1) : 0 < cost μ l := by
  let p := pBr μ
  let e := eJ μ
  let s := sS μ l
  let q := 1 - p
  let U := q + p * e
  let A := 1 - e - s * U
  let d := (1 - s * q ^ 2 / 2) / A - q * (1 + p) / 4
  let hh := 2 + s * (p + d)
  let L := s * (1 / A - p) / ((1 + s) * (3 + s / A))
  have hp : 0 < p := pBr_pos h
  have hp1 : p ≤ 1 := pBr_le_one h
  have he : 0 < e ∧ e ≤ 1 / 2 := eJ_mem h
  have hs0 : 0 < s := by dsimp only [s, sS]; positivity
  have hq0 : 0 ≤ q := sub_nonneg.mpr hp1
  have hq1 : q ≤ 1 := by dsimp only [q]; linarith
  have hA := lowWindow_A_bounds ⟨hp, hp1⟩ he ⟨hs0, hs⟩
  change 3 / 8 ≤ A ∧ A < 1 at hA
  have hA0 : 0 < A := by linarith [hA.1]
  have hx1 : 1 ≤ 1 / A := (le_div_iff₀ hA0).2 (by simpa using hA.2.le)
  have hsq : s * q ^ 2 ≤ 1 / 8 := by
    calc
      s * q ^ 2 ≤ (1 / 8) * 1 :=
        mul_le_mul hs (by simpa [pow_two] using mul_le_mul hq1 hq1 hq0 zero_le_one)
          (sq_nonneg _) (by norm_num)
      _ = 1 / 8 := by ring
  have hqprod2 : q * (1 + p) ≤ 2 := by
    calc
      q * (1 + p) ≤ 1 * 2 :=
        mul_le_mul hq1 (by linarith) (by linarith) zero_le_one
      _ = 2 := by ring
  have hd : 0 < d := by
    dsimp only [d]
    rw [div_eq_mul_one_div]
    have hm := mul_le_mul
      (show (15 : ℝ) / 16 ≤ 1 - s * q ^ 2 / 2 by linarith)
      hx1 (by norm_num) (by linarith)
    linarith
  have hhpos : 0 < hh := by dsimp only [hh]; positivity
  have hscalar : 0 < 1 - Vsc μ l * d - hh * L := by
    exact lowWindow_scalar ⟨hp, hp1⟩ he ⟨hs0, hs⟩ (Vsc_le h hl hlm hv)
  have hred : 1 - Vsc μ l * d - hh * L ≤ hh * cost μ l := by
    have hr := lowWindow_reduced h hl hlm hs
    dsimp only at hr
    have hqeq : p1 μ = 1 - pBr μ := by linarith [p1_add_pBr h]
    rw [hqeq] at hr
    exact hr
  exact pos_of_mul_pos_right (hscalar.trans_le hred) hhpos.le

private lemma deriv_neg_of_speedValue_le_one (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8)
    (hv : Speed.speedValue μ l ≤ Speed.speedValue μ 1) :
    deriv (Speed.speedValue μ) l < 0 := by
  have hc := cost_pos_of_speedValue_le_one h hl hlm hs hv
  by_contra hn
  have hd : 0 ≤ deriv (Speed.speedValue μ) l := le_of_not_gt hn
  have hZ : 0 < ZvalProv μ l := by
    exact Speed.Zval_pos μ (by linarith) h hlm
  have hd' : 0 ≤ deriv (speedValueProv μ) l := by
    change 0 ≤ deriv (Speed.speedValue μ) l
    exact hd
  have hcn : cost μ l ≤ 0 := by
    unfold cost
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by linarith : 0 ≤ l)) hZ.le) hd'
  exact (not_le_of_gt hc) hcn

/-- **Theorem 4.3** (`thm:low-window`). The speed derivative is strictly negative
throughout the low-bias window. -/
theorem deriv_neg_low_window (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : (l - 1) / pBr μ ≤ 1 / 8) :
    deriv (Speed.speedValue μ) l < 0 := by
  by_contra hn
  have hdl : 0 ≤ deriv (Speed.speedValue μ) l := le_of_not_gt hn
  let S : Set ℝ := Set.Icc 1 l ∩ (deriv (Speed.speedValue μ) ⁻¹' Set.Ici 0)
  have hcont : ContinuousOn (deriv (Speed.speedValue μ)) (Set.Icc 1 l) :=
    (continuousOn_deriv_speedValue h).mono fun x hx =>
      ⟨by linarith [hx.1], hx.2.trans_lt hlm⟩
  have hSclosed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := ⟨l, ⟨⟨hl.le, le_rfl⟩, hdl⟩⟩
  have hSbdd : BddBelow S := ⟨1, fun _ hx => hx.1.1⟩
  let a := sInf S
  have haS : a ∈ S := hSclosed.csInf_mem hSne hSbdd
  have ha1 : 1 ≤ a := haS.1.1
  have hal : a ≤ l := haS.1.2
  have hda : 0 ≤ deriv (Speed.speedValue μ) a := haS.2
  have ha1lt : 1 < a := by
    refine lt_of_le_of_ne ha1 ?_
    intro h1a
    rw [← h1a] at hda
    exact (not_le_of_gt (deriv_neg_of_le_one h zero_lt_one le_rfl)) hda
  have halc : Set.Icc 1 a ⊆ Set.Ico 0 (mean μ) := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2.trans_lt (hal.trans_lt hlm)⟩
  have hanti : AntitoneOn (Speed.speedValue μ) (Set.Icc 1 a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 1 a)
      ((continuousOn_speedValue h).mono halc)
    · rw [interior_Icc]
      intro x hx
      exact (hasDerivAt_speedValue h
        ⟨by linarith [hx.1], hx.2.trans (hal.trans_lt hlm)⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hxS : x ∉ S := by
        intro hxmem
        exact (not_le_of_gt hx.2) (csInf_le hSbdd hxmem)
      have hxneg : ¬0 ≤ deriv (Speed.speedValue μ) x := by
        intro hdx
        exact hxS ⟨⟨hx.1.le, (hx.2.trans_le hal).le⟩, hdx⟩
      exact le_of_not_ge hxneg
  have hv : Speed.speedValue μ a ≤ Speed.speedValue μ 1 :=
    hanti (Set.left_mem_Icc.mpr ha1lt.le) (Set.right_mem_Icc.mpr ha1lt.le) ha1lt.le
  have hsa : sS μ a ≤ 1 / 8 := by
    apply (div_le_div_of_nonneg_right (sub_le_sub_right hal 1) (pBr_pos h).le).trans
    exact hs
  exact (not_le_of_gt (deriv_neg_of_speedValue_le_one h ha1lt (hal.trans_lt hlm) hsa hv)) hda

end LPPMonotonicityProof.Analytic
