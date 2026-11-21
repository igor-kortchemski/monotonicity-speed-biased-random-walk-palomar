module

public import LPPMonotonicityProof.Analytic.FirstSplit3
public import LPPMonotonicityProof.Analytic.LowWindowReciprocal
public import LPPMonotonicityProof.Analytic.Tools
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal-escape estimates near bias one, continued

This module proves the third reciprocal-escape estimate of the proof of Theorem 4.3
(`thm:low-window`), `AM ≤ 1 - λeΔ`. Product integrals are decomposed by the root
degree and then by fixed finite products; no dependent product law is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]
variable {l : ℝ}

private noncomputable def RR (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (T : Tree) : ℝ := pBr μ / escape l T

private noncomputable def DD (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (x : Tree × Tree) : ℝ :=
  (RR μ l x.1 - RR μ l x.2) ^ 2 / (RR μ l x.1 + RR μ l x.2)

private noncomputable def HH (x y : ℝ) : ℝ := 2 * x * y / (x + y)

private lemma RR_eq (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) (T : Tree) :
    RR μ l T = pBr μ * (escape l T)⁻¹ := by
  rw [RR, div_eq_mul_inv]

private lemma measurable_RR (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) :
    Measurable (RR μ l) := measurable_const.div (measurable_escape l)

private lemma ae_RR_pos (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : ∀ᵐ T ∂GW μ, 0 < RR μ l T := by
  filter_upwards [ae_escape_pos h (by positivity) hlm] with T hT
  exact div_pos (pBr_pos h) hT

private lemma RR_lower (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (T : Tree)
    (hT : 0 < escape l T) : pBr μ ≤ RR μ l T := by
  have he := (escape_mem_Icc (by positivity : 0 < l) T).2
  exact (le_div_iff₀ hT).2 (by nlinarith [pBr_pos h])

private lemma lowWindow_invMean_identity' (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) :
    1 - l * invMean μ = pBr μ *
      (1 - eJ μ - sS μ l * (p1 μ + pBr μ * eJ μ)) := by
  have hq : p1 μ = 1 - pBr μ := by linarith [p1_add_pBr h]
  rw [invMean_eq_p1_add h, hq, sS]
  have hp := (pBr_pos h).ne'
  field_simp [hp]
  ring

private lemma lowWindow_linvMean_lt_one (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) : l * invMean μ < 1 := by
  have hA : 3 / 8 ≤ 1 - eJ μ - sS μ l * (p1 μ + pBr μ * eJ μ) :=
    lowWindow_reciprocal_A_lower h hl hlm hs
  have hX := lowWindow_invMean_identity' h hl
  have hp := pBr_pos h
  nlinarith

private lemma integrable_RR (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) : Integrable (RR μ l) (GW μ) := by
  have hU : l * invMean μ < 1 := lowWindow_linvMean_lt_one h hl hlm hs
  rw [show RR μ l = fun T => pBr μ * (escape l T)⁻¹ by funext T; exact RR_eq μ l T]
  exact (integrable_inv_escape h (by positivity) hU).2.const_mul _


private lemma measurePreserving_pi_pair (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {k : ℕ} (i j : Fin k) (hij : i ≠ j) :
    MeasurePreserving (fun ts : Fin k → Tree => (ts i, ts j))
      (Measure.pi fun _ : Fin k => GW μ) ((GW μ).prod (GW μ)) := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ n =>
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hij.symm
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Tree) i
    have he : MeasurePreserving e (Measure.pi fun _ : Fin (n + 1) => GW μ)
        ((GW μ).prod (Measure.pi fun _ : Fin n => GW μ)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => GW μ) i
    have hp := ((MeasurePreserving.id (GW μ)).prod
      (measurePreserving_eval (fun _ : Fin n => GW μ) j')).comp he
    have heq (ts : Fin (n + 1) → Tree) : e ts = (ts i, i.removeNth ts) := rfl
    exact hp

private lemma harmonic_le_pair_average {k : ℕ} (hk : 2 ≤ k) (a : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) :
    (k : ℝ) / (∑ i, a i) ≤
      ((k : ℝ) * ((k : ℝ) - 1))⁻¹ *
        ∑ ij ∈ (Finset.univ : Finset (Fin k)).offDiag, 2 / (a ij.1 + a ij.2) := by
  classical
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let S : ℝ := ∑ i, a i
  let N : ℝ := (k : ℝ) * ((k : ℝ) - 1)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hS : 0 < S := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hN : 0 < N := mul_pos hk0 (by linarith)
  have hcard : (((Finset.univ : Finset (Fin k)).offDiag.card : ℕ) : ℝ) = N := by
    have hkk : k ≤ k * k := by nlinarith
    simp only [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub hkk, Nat.cast_mul]
    dsimp only [N]
    ring
  have hsplit (f : Fin k × Fin k → ℝ) :
      (∑ ij ∈ Finset.univ.diag, f ij) + (∑ ij ∈ (Finset.univ : Finset (Fin k)).offDiag, f ij) =
        ∑ ij ∈ Finset.univ ×ˢ Finset.univ, f ij := by
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag _),
      Finset.diag_union_offDiag]
  have hdiag : (∑ ij ∈ Finset.univ.diag, (a ij.1 + a ij.2)) = 2 * S := by
    simp [Finset.diag, S, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hfull : (∑ ij ∈ Finset.univ ×ˢ Finset.univ, (a ij.1 + a ij.2)) =
      2 * (k : ℝ) * S := by
    simp only [Finset.sum_product, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp only [S]
    simp only [← Finset.mul_sum]
    ring
  have hoff : (∑ ij ∈ (Finset.univ : Finset (Fin k)).offDiag, (a ij.1 + a ij.2)) =
      2 * ((k : ℝ) - 1) * S := by
    have hh := hsplit (fun ij => a ij.1 + a ij.2)
    rw [hdiag, hfull] at hh
    linarith
  have hw0 : ∀ ij ∈ (Finset.univ : Finset (Fin k)).offDiag, 0 ≤ N⁻¹ := fun _ _ => inv_nonneg.mpr hN.le
  have hw1 : ∑ _ij ∈ (Finset.univ : Finset (Fin k)).offDiag, N⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    exact mul_inv_cancel₀ hN.ne'
  have hconv : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x⁻¹) := by
    simpa only [zpow_neg_one] using (convexOn_zpow (-1 : ℤ) (𝕜 := ℝ))
  have hj := hconv.map_sum_le hw0 hw1 (fun ij _ => add_pos (ha ij.1) (ha ij.2))
  simp only [smul_eq_mul] at hj
  have hcenter : (∑ ij ∈ (Finset.univ : Finset (Fin k)).offDiag, N⁻¹ * (a ij.1 + a ij.2)) =
      2 * S / (k : ℝ) := by
    rw [← Finset.mul_sum, hoff]
    dsimp only [N]
    field_simp [hk0.ne', hN.ne']
  rw [hcenter] at hj
  calc
    (k : ℝ) / (∑ i, a i) = 2 * (2 * S / (k : ℝ))⁻¹ := by
      dsimp only [S]
      field_simp [hk0.ne', hS.ne']
    _ ≤ 2 * ∑ ij ∈ (Finset.univ : Finset (Fin k)).offDiag, N⁻¹ * (a ij.1 + a ij.2)⁻¹ :=
      mul_le_mul_of_nonneg_left hj (by norm_num)
    _ = N⁻¹ * ∑ ij ∈ (Finset.univ : Finset (Fin k)).offDiag, 2 / (a ij.1 + a ij.2) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ij _
      field_simp

private lemma ae_RR_pos_prod (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : ∀ᵐ x ∂(GW μ).prod (GW μ), 0 < RR μ l x.1 ∧ 0 < RR μ l x.2 := by
  have hfst : ∀ᵐ x ∂(GW μ).prod (GW μ), 0 < RR μ l x.1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae (ae_RR_pos h hl hlm)
  have hsnd : ∀ᵐ x ∂(GW μ).prod (GW μ), 0 < RR μ l x.2 :=
    measurePreserving_snd.quasiMeasurePreserving.ae (ae_RR_pos h hl hlm)
  filter_upwards [hfst, hsnd] with x hx hy
  exact ⟨hx, hy⟩

private lemma measurable_DD (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) :
    Measurable (DD μ l) := by
  exact (((measurable_RR μ l).comp measurable_fst).sub
    ((measurable_RR μ l).comp measurable_snd)).pow_const 2 |>.div
      (((measurable_RR μ l).comp measurable_fst).add
        ((measurable_RR μ l).comp measurable_snd))

private lemma DD_nonneg {x : Tree × Tree}
    (hx : 0 ≤ RR μ l x.1) (hy : 0 ≤ RR μ l x.2) : 0 ≤ DD μ l x := by
  exact div_nonneg (sq_nonneg _) (add_nonneg hx hy)

private lemma DD_le_sum {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x - y) ^ 2 / (x + y) ≤ x + y := by
  apply (div_le_iff₀ (add_pos hx hy)).2
  nlinarith [mul_pos hx hy]

private lemma HH_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ HH x y := by
  exact div_nonneg (by positivity [HH]) (add_nonneg hx hy)

private lemma HH_le_sum {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : HH x y ≤ x + y := by
  rw [HH]
  apply (div_le_iff₀ (add_pos hx hy)).2
  nlinarith [sq_nonneg (x - y)]

private lemma two_HH_add_diff_sq_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 * HH x y + (x - y) ^ 2 / (x + y) = x + y := by
  rw [HH]
  field_simp [(add_pos hx hy).ne']
  ring

private lemma integrable_DD (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) : Integrable (DD μ l) ((GW μ).prod (GW μ)) := by
  have hr := integrable_RR h hl hlm hs
  have hsum := (hr.comp_fst (GW μ)).add (hr.comp_snd (GW μ))
  apply hsum.mono' (measurable_DD μ l).aestronglyMeasurable
  filter_upwards [ae_RR_pos_prod h hl hlm] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (DD_nonneg hx.1.le hx.2.le)]
  exact DD_le_sum hx.1 hx.2

private lemma measurable_HH (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) :
    Measurable (fun x : Tree × Tree => HH (RR μ l x.1) (RR μ l x.2)) := by
  exact (measurable_const.mul ((measurable_RR μ l).comp measurable_fst)).mul
    ((measurable_RR μ l).comp measurable_snd) |>.div
      (((measurable_RR μ l).comp measurable_fst).add
        ((measurable_RR μ l).comp measurable_snd))

private lemma integrable_HH (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    Integrable (fun x : Tree × Tree => HH (RR μ l x.1) (RR μ l x.2))
      ((GW μ).prod (GW μ)) := by
  have hr := integrable_RR h hl hlm hs
  have hsum := (hr.comp_fst (GW μ)).add (hr.comp_snd (GW μ))
  apply hsum.mono' (measurable_HH μ l).aestronglyMeasurable
  filter_upwards [ae_RR_pos_prod h hl hlm] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (HH_nonneg hx.1.le hx.2.le)]
  exact HH_le_sum hx.1 hx.2

private lemma integral_RR_fst (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    (∫ x, RR μ l x.1 ∂(GW μ).prod (GW μ)) = ∫ T, RR μ l T ∂GW μ := by
  have hi := (integrable_RR h hl hlm hs).comp_fst (GW μ)
  rw [integral_prod _ hi]
  simp

private lemma integral_RR_snd (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    (∫ x, RR μ l x.2 ∂(GW μ).prod (GW μ)) = ∫ T, RR μ l T ∂GW μ := by
  have hi := (integrable_RR h hl hlm hs).comp_snd (GW μ)
  rw [integral_prod _ hi]
  simp

private lemma integral_HH_eq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    (∫ x, HH (RR μ l x.1) (RR μ l x.2) ∂(GW μ).prod (GW μ)) =
      (∫ T, RR μ l T ∂GW μ) - (1 / 2) * ∫ x, DD μ l x ∂(GW μ).prod (GW μ) := by
  have hd := integrable_DD h hl hlm hs
  have hh := integrable_HH h hl hlm hs
  have hr := integrable_RR h hl hlm hs
  have hsum := (hr.comp_fst (GW μ)).add (hr.comp_snd (GW μ))
  have heq : 2 * (∫ x, HH (RR μ l x.1) (RR μ l x.2) ∂(GW μ).prod (GW μ)) +
      (∫ x, DD μ l x ∂(GW μ).prod (GW μ)) = 2 * ∫ T, RR μ l T ∂GW μ := by
    rw [← integral_const_mul, ← integral_add (hh.const_mul 2) hd]
    calc
      _ = ∫ x, (RR μ l x.1 + RR μ l x.2) ∂(GW μ).prod (GW μ) := by
        apply integral_congr_ae
        filter_upwards [ae_RR_pos_prod h hl hlm] with x hx
        exact two_HH_add_diff_sq_div hx.1 hx.2
      _ = (∫ x, RR μ l x.1 ∂(GW μ).prod (GW μ)) +
          (∫ x, RR μ l x.2 ∂(GW μ).prod (GW μ)) :=
        integral_add (hr.comp_fst _) (hr.comp_snd _)
      _ = _ := by rw [integral_RR_fst h hl hlm hs, integral_RR_snd h hl hlm hs]; ring
  linarith

private noncomputable def HFin (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) {k : ℕ} (ts : Fin k → Tree) : ℝ :=
  (k : ℝ) / ∑ i, (RR μ l (ts i))⁻¹

private lemma ae_RR_pos_pi (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (k : ℕ) :
    ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => GW μ), ∀ i, 0 < RR μ l (ts i) := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun _ : Fin k => GW μ) i).quasiMeasurePreserving.ae
    (ae_RR_pos h hl hlm)

private lemma integral_pi_pair_eq (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {k : ℕ} (i j : Fin k) (hij : i ≠ j) (F : Tree × Tree → ℝ)
    (hF : Measurable F) :
    (∫ ts, F (ts i, ts j) ∂Measure.pi (fun _ : Fin k => GW μ)) =
      ∫ x, F x ∂(GW μ).prod (GW μ) := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ n =>
    let hp := measurePreserving_pi_pair μ i j hij
    calc
    _ = ∫ x, F x ∂Measure.map (fun ts : Fin (n + 1) → Tree => (ts i, ts j))
        (Measure.pi fun _ : Fin (n + 1) => GW μ) :=
      (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]

private lemma HFin_nonneg {k : ℕ} (hk : 0 < k) {ts : Fin k → Tree}
    (hts : ∀ i, 0 < RR μ l (ts i)) : 0 ≤ HFin μ l ts := by
  apply div_nonneg (Nat.cast_nonneg k)
  exact Finset.sum_nonneg fun i _ => inv_nonneg.mpr (hts i).le

private lemma HFin_le_sum {k : ℕ} (hk : 0 < k) {ts : Fin k → Tree}
    (hts : ∀ i, 0 < RR μ l (ts i)) : HFin μ l ts ≤ ∑ i, RR μ l (ts i) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hS : 0 < ∑ i, (RR μ l (ts i))⁻¹ :=
    Finset.sum_pos (fun i _ => inv_pos.mpr (hts i)) Finset.univ_nonempty
  have hR : 0 ≤ ∑ i, RR μ l (ts i) := Finset.sum_nonneg fun i _ => (hts i).le
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc := Finset.sq_sum_div_le_sum_sq_div (g := fun i => (RR μ l (ts i))⁻¹)
    Finset.univ (fun _ : Fin k => (1 : ℝ)) (fun i _ => inv_pos.mpr (hts i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_pow, one_div, inv_inv] at hc
  rw [HFin]
  calc
    (k : ℝ) / (∑ i, (RR μ l (ts i))⁻¹) =
        ((k : ℝ) ^ 2 / (∑ i, (RR μ l (ts i))⁻¹)) / (k : ℝ) := by
      field_simp [hk0.ne', hS.ne']
    _ ≤ (∑ i, RR μ l (ts i)) / (k : ℝ) := div_le_div_of_nonneg_right hc hk0.le
    _ ≤ ∑ i, RR μ l (ts i) := by
      apply (div_le_iff₀ hk0).2
      nlinarith

private lemma integrable_HFin (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) {k : ℕ} (hk : 0 < k) :
    Integrable (HFin μ l) (Measure.pi fun _ : Fin k => GW μ) := by
  have hr := integrable_RR h hl hlm hs
  have hi (i : Fin k) : Integrable (fun ts : Fin k → Tree => RR μ l (ts i))
      (Measure.pi fun _ : Fin k => GW μ) := by
    exact (measurePreserving_eval (fun _ : Fin k => GW μ) i).integrable_comp_of_integrable hr
  have hsum : Integrable (fun ts : Fin k → Tree => ∑ i, RR μ l (ts i))
      (Measure.pi fun _ : Fin k => GW μ) := integrable_finsetSum _ fun i _ => hi i
  apply hsum.mono'
    ((measurable_const.div (Finset.univ.measurable_sum fun i _ =>
      ((measurable_RR μ l).comp (measurable_pi_apply i)).inv))).aestronglyMeasurable
  filter_upwards [ae_RR_pos_pi h hl hlm k] with ts hts
  change ‖HFin μ l ts‖ ≤ ∑ i, RR μ l (ts i)
  rw [Real.norm_eq_abs, abs_of_nonneg (HFin_nonneg hk hts)]
  exact HFin_le_sum hk hts

private lemma two_inv_add_inv_eq_HH {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 / (x⁻¹ + y⁻¹) = HH x y := by
  rw [HH]
  field_simp [hx.ne', hy.ne', (add_pos hx hy).ne']
  ring

private lemma integral_HFin_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) {k : ℕ} (hk : 2 ≤ k) :
    (∫ ts, HFin μ l ts ∂Measure.pi (fun _ : Fin k => GW μ)) ≤
      ∫ x, HH (RR μ l x.1) (RR μ l x.2) ∂(GW μ).prod (GW μ) := by
  let N : ℝ := (k : ℝ) * ((k : ℝ) - 1)
  let t : Finset (Fin k × Fin k) := (Finset.univ : Finset (Fin k)).offDiag
  have hN : 0 < N := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    exact mul_pos hk0 (by linarith)
  have hcard : (t.card : ℝ) = N := by
    dsimp only [t]
    rw [Finset.offDiag_card]
    have hkk : k ≤ k * k := by nlinarith
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub hkk, Nat.cast_mul]
    dsimp only [N]
    ring
  have hpair (ij : Fin k × Fin k) (hij : ij ∈ t) :
      Integrable (fun ts : Fin k → Tree => HH (RR μ l (ts ij.1)) (RR μ l (ts ij.2)))
        (Measure.pi fun _ : Fin k => GW μ) := by
    have hne : ij.1 ≠ ij.2 := ((Finset.mem_offDiag.mp hij).2.2)
    simpa only [Function.comp_def] using
      (measurePreserving_pi_pair μ ij.1 ij.2 hne).integrable_comp_of_integrable
        (integrable_HH h hl hlm hs)
  have hintsum : Integrable (fun ts : Fin k → Tree =>
      ∑ ij ∈ t, HH (RR μ l (ts ij.1)) (RR μ l (ts ij.2)))
      (Measure.pi fun _ : Fin k => GW μ) := integrable_finsetSum _ hpair
  have hpoint : ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => GW μ),
      HFin μ l ts ≤ N⁻¹ * ∑ ij ∈ t, HH (RR μ l (ts ij.1)) (RR μ l (ts ij.2)) := by
    filter_upwards [ae_RR_pos_pi h hl hlm k] with ts hts
    have hh := harmonic_le_pair_average hk (fun i => (RR μ l (ts i))⁻¹)
      (fun i => inv_pos.mpr (hts i))
    have heq (ij : Fin k × Fin k) :
        2 / ((RR μ l (ts ij.1))⁻¹ + (RR μ l (ts ij.2))⁻¹) =
          HH (RR μ l (ts ij.1)) (RR μ l (ts ij.2)) :=
      two_inv_add_inv_eq_HH (hts ij.1) (hts ij.2)
    simp_rw [heq] at hh
    exact hh
  calc
    _ ≤ ∫ ts, N⁻¹ * ∑ ij ∈ t, HH (RR μ l (ts ij.1)) (RR μ l (ts ij.2))
        ∂Measure.pi (fun _ : Fin k => GW μ) :=
      integral_mono_ae (integrable_HFin h hl hlm hs (by omega)) (hintsum.const_mul N⁻¹) hpoint
    _ = N⁻¹ * ∑ _ij ∈ t, ∫ x, HH (RR μ l x.1) (RR μ l x.2) ∂(GW μ).prod (GW μ) := by
      rw [integral_const_mul, integral_finsetSum _ hpair]
      apply congrArg (N⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro ij hij
      exact integral_pi_pair_eq μ ij.1 ij.2 (Finset.mem_offDiag.mp hij).2.2 _ (measurable_HH μ l)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, ← mul_assoc]
      exact inv_mul_cancel₀ hN.ne' ▸ one_mul _

private lemma RR_nodeFin_eq (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {k : ℕ} (hk : 0 < k) :
    ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => GW μ),
      RR μ l (nodeFin k ts) = pBr μ + (l / (k : ℝ)) * HFin μ l ts := by
  filter_upwards [ae_RR_pos_pi h hl hlm k] with ts hts
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hS : 0 < ∑ i, (RR μ l (ts i))⁻¹ := by
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    exact Finset.sum_pos (fun i _ => inv_pos.mpr (hts i)) Finset.univ_nonempty
  have hC : (∑ i, escape l (ts i)) = pBr μ * ∑ i, (RR μ l (ts i))⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [RR, inv_div]
    field_simp [(pBr_pos h).ne']
  rw [RR, escape_eq (by positivity), childSum_nodeFin, hC, HFin]
  have hl0 : (0 : ℝ) < l := by positivity
  have hden : 0 < l + pBr μ * ∑ i, (RR μ l (ts i))⁻¹ :=
    add_pos hl0 (mul_pos (pBr_pos h) hS)
  field_simp [(pBr_pos h).ne', hS.ne', hk0.ne', hden.ne']
  ring

private lemma integral_RR_nodeFin (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) {k : ℕ} (hk : 0 < k) :
    (∫ ts, RR μ l (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ)) =
      pBr μ + (l / (k : ℝ)) * ∫ ts, HFin μ l ts ∂Measure.pi (fun _ : Fin k => GW μ) := by
  calc
    _ = ∫ ts, (pBr μ + (l / (k : ℝ)) * HFin μ l ts)
        ∂Measure.pi (fun _ : Fin k => GW μ) :=
      integral_congr_ae (RR_nodeFin_eq h hl hlm hk)
    _ = _ := by
      rw [integral_add (integrable_const _)
        ((integrable_HFin h hl hlm hs hk).const_mul _), integral_const,
        integral_const_mul]
      simp


private lemma summable_masses (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Summable (fun k : ℕ => (μ {k}).toReal) := by
  simpa only [Measure.real] using
    (summable_measure_toReal (μ := μ) (f := fun k : ℕ => {k})
      (fun _ => measurableSet_singleton _) (by
        intro i j hij
        simpa using hij))

private lemma tsum_masses (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (∑' k : ℕ, (μ {k}).toReal) = 1 := by
  have hi := integral_countable (μ := μ) (f := fun _ : ℕ => (1 : ℝ)) (integrable_const 1)
  simpa [Measure.real] using hi.symm

private lemma summable_invDegree (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Summable (fun k : ℕ => (μ {k}).toReal * (k : ℝ)⁻¹) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg ENNReal.toReal_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k)))
    (fun k => ?_) (summable_masses μ)
  by_cases hk : k = 0
  · simp [hk]
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (inv_le_one_of_one_le₀ hk1)

private lemma integrable_inverse_nat (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Integrable (fun k : ℕ => (k : ℝ)⁻¹) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  filter_upwards with k
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k))]
  by_cases hk : k = 0
  · simp [hk]
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk))

private lemma tsum_invDegree (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (∑' k : ℕ, (μ {k}).toReal * (k : ℝ)⁻¹) = invMean μ := by
  rw [invMean, integral_countable (integrable_inverse_nat μ)]
  apply tsum_congr
  intro k
  simp only [Measure.real, smul_eq_mul]

private lemma integral_HFin_one (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    (∫ ts, HFin μ l ts ∂Measure.pi (fun _ : Fin 1 => GW μ)) = ∫ T, RR μ l T ∂GW μ := by
  have heq (ts : Fin 1 → Tree) : HFin μ l ts = RR μ l (ts 0) := by
    simp [HFin]
  rw [integral_congr_ae (ae_of_all _ heq)]
  let hp := measurePreserving_eval (fun _ : Fin 1 => GW μ) 0
  calc
    _ = ∫ T, RR μ l T ∂Measure.map (Function.eval 0) (Measure.pi fun _ : Fin 1 => GW μ) :=
      (integral_map hp.measurable.aemeasurable (measurable_RR μ l).aestronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]

private lemma lowWindow_root_recurrence (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    let M := ∫ T, RR μ l T ∂GW μ
    let H := ∫ x, HH (RR μ l x.1) (RR μ l x.2) ∂(GW μ).prod (GW μ)
    M ≤ pBr μ + l * p1 μ * M + l * (invMean μ - p1 μ) * H := by
  intro M H
  let w : ℕ → ℝ := fun k => (μ {k}).toReal
  let B : ℕ → ℝ := fun k => if k = 1 then M else H
  let C : ℕ → ℝ := fun k => w k * (pBr μ + (l / (k : ℝ)) * B k)
  let D : ℕ → ℝ := fun k => w k * pBr μ + (l * H) * (w k * (k : ℝ)⁻¹) +
    (if k = 1 then (l * (M - H)) * w k else 0)
  have hp : 0 < pBr μ := pBr_pos h
  have hl0 : 0 < l := by positivity
  have hM : 0 ≤ M := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_RR_pos h hl hlm] with T hT
    exact hT.le
  have hH : 0 ≤ H := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_RR_pos_prod h hl hlm] with x hx
    exact HH_nonneg hx.1.le hx.2.le
  have hw0 (k : ℕ) : 0 ≤ w k := ENNReal.toReal_nonneg
  have hCD (k : ℕ) : C k = D k := by
    by_cases hk : k = 1
    · subst k
      simp [C, D, B]
      ring
    · simp only [C, D, B, hk, ↓reduceIte, add_zero]
      ring
  have hsingle : Summable (fun k : ℕ => if k = 1 then (l * (M - H)) * w k else 0) := by
    apply Summable.of_norm_bounded (g := fun k => |l * (M - H)| * w k)
      ((summable_masses μ).mul_left |l * (M - H)|)
    intro k
    by_cases hk : k = 1
    · subst k
      simp [abs_mul, abs_of_nonneg (hw0 1)]
    · simp only [hk, ↓reduceIte, norm_zero]
      positivity
  have hmassR := (summable_masses μ).mul_right (pBr μ)
  have hinvL := (summable_invDegree μ).mul_left (l * H)
  have hDsum : Summable D := by
    rw [show D = (fun k => w k * pBr μ) + (fun k => (l * H) * (w k * (k : ℝ)⁻¹)) +
      (fun k => if k = 1 then (l * (M - H)) * w k else 0) by rfl]
    exact (hmassR.add hinvL).add hsingle
  have hCsum : Summable C := hDsum.congr (fun k => (hCD k).symm)
  have hbound (k : ℕ) :
      w k * (∫ ts, RR μ l (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ)) ≤ C k := by
    by_cases hk0 : k = 0
    · subst k
      simp [w, C, h.zero]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    rw [integral_RR_nodeFin h hl hlm hs hkpos]
    apply mul_le_mul_of_nonneg_left _ (hw0 k)
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hl0.le (Nat.cast_nonneg k))
    by_cases hk1 : k = 1
    · subst k
      simpa only [B, ↓reduceIte] using (integral_HFin_one h hl hlm hs).le
    · have hk2 : 2 ≤ k := by omega
      simpa only [B, hk1, ↓reduceIte] using integral_HFin_le h hl hlm hs hk2
  have hleft0 (k : ℕ) :
      0 ≤ w k * (∫ ts, RR μ l (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ)) := by
    by_cases hk0 : k = 0
    · subst k
      simp [w, h.zero]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    apply mul_nonneg (hw0 k)
    apply integral_nonneg_of_ae
    filter_upwards [RR_nodeFin_eq h hl hlm hkpos, ae_RR_pos_pi h hl hlm k] with ts he hts
    rw [he]
    exact add_nonneg hp.le (mul_nonneg (div_nonneg hl0.le (Nat.cast_nonneg k))
      (HFin_nonneg hkpos hts))
  have hC0 (k : ℕ) : 0 ≤ C k := by
    apply mul_nonneg (hw0 k)
    apply add_nonneg hp.le
    apply mul_nonneg (div_nonneg hl0.le (Nat.cast_nonneg k))
    by_cases hk : k = 1
    · simp [B, hk, hM]
    · simp [B, hk, hH]
  have hleftSum : Summable (fun k => w k *
      (∫ ts, RR μ l (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ))) :=
    Summable.of_nonneg_of_le hleft0 hbound hCsum
  have hmain : M ≤ ∑' k, C k := by
    change M ≤ ∑' k, w k * (pBr μ + (l / (k : ℝ)) * B k)
    calc
      M = ∑' k, w k * (∫ ts, RR μ l (nodeFin k ts)
          ∂Measure.pi (fun _ : Fin k => GW μ)) := integral_GW_eq_tsum _ (integrable_RR h hl hlm hs)
      _ ≤ _ := Summable.tsum_le_tsum hbound hleftSum hCsum
  rw [show (∑' k, C k) = ∑' k, D k from tsum_congr hCD] at hmain
  have hDval : (∑' k, D k) = pBr μ + l * p1 μ * M + l * (invMean μ - p1 μ) * H := by
    rw [show D = (fun k => w k * pBr μ) + (fun k => (l * H) * (w k * (k : ℝ)⁻¹)) +
      (fun k => if k = 1 then (l * (M - H)) * w k else 0) by rfl]
    simp only [Pi.add_apply]
    rw [(hmassR.add hinvL).tsum_add hsingle, hmassR.tsum_add hinvL,
      tsum_mul_right, tsum_mul_left, tsum_masses μ, tsum_invDegree μ]
    have hone : (∑' k : ℕ, if k = 1 then (l * (M - H)) * w k else 0) =
        (l * (M - H)) * p1 μ := by
      rw [tsum_eq_single 1 (fun k hk => by simp [hk])]
      simp [w, p1]
    rw [hone]
    ring
  rw [hDval] at hmain
  exact hmain

/-- **`AM ≤ 1 - λeΔ`.**  Harmonic means of at least two children give
`A * M ≤ 1 - l * e * Δ`. -/
theorem lowWindow_reciprocal_AM_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    let p := pBr μ
    let q := p1 μ
    let e := eJ μ
    let s := sS μ l
    let A := 1 - e - s * (q + p * e)
    let M := ∫ T, p / escape l T ∂GW μ
    let Δ := (1 / 2) * ∫ x, (p / escape l x.1 - p / escape l x.2) ^ 2 /
      (p / escape l x.1 + p / escape l x.2) ∂(GW μ).prod (GW μ)
    A * M ≤ 1 - l * e * Δ := by
  intro p q e s A M Δ
  have hrec := lowWindow_root_recurrence h hl hlm hs
  have hH := integral_HH_eq h hl hlm hs
  have hX := lowWindow_invMean_identity' h hl
  have hU := invMean_eq_p1_add h
  have hp := pBr_pos h
  change M ≤ p + l * q * M + l * (invMean μ - q) *
    (∫ x, HH (p / escape l x.1) (p / escape l x.2) ∂(GW μ).prod (GW μ)) at hrec
  change (∫ x, HH (p / escape l x.1) (p / escape l x.2) ∂(GW μ).prod (GW μ)) =
    M - Δ at hH
  change A * M ≤ 1 - l * e * Δ
  rw [hH] at hrec
  have hXp : 1 - l * invMean μ = p * A := hX
  rw [hU] at hX
  change invMean μ = q + p * e at hU
  have hcoef : invMean μ - q = p * e := by linarith
  rw [hcoef] at hrec
  have hApos : 0 < A := by
    have := lowWindow_reciprocal_A_lower h hl hlm hs
    change 3 / 8 ≤ A at this
    linarith
  have hrec' : (1 - l * invMean μ) * M ≤ p - l * (p * e) * Δ := by
    rw [hU]
    nlinarith [hrec]
  apply (mul_le_mul_iff_of_pos_left hp).mp
  calc
    p * (A * M) = (1 - l * invMean μ) * M := by rw [hXp]; ring
    _ ≤ p - l * (p * e) * Δ := hrec'
    _ = p * (1 - l * e * Δ) := by ring


end LPPMonotonicityProof.Analytic
