module

public import LPPMonotonicityProof.Analytic.Regularity.Inverse
public import LPPMonotonicityProof.Analytic.Interface2
public import LPPMonotonicityProof.Analytic.Tools
public import LPPMonotonicityProof.RTL.GeneratingFunction
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# The inverse escape moment

This module proves Lemma 2.4 (`lem:inverse-moment`): it proves the finite-depth
harmonic--arithmetic recursion in `ℝ≥0∞` and passes to the infinite escape by monotone
convergence. The tree measurability lemma, which is private in
`Regularity/Inverse.lean`, has a private copy here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- Tree form of the measurability of the finite-depth escape (private copy). -/
private theorem measurable_escapeN_treeProv2 (l : ℝ) (N : ℕ) (v : Address) :
    Measurable (fun T : Tree => escapeN T.val l N v) := by
  induction N generalizing v with
  | zero => simp [escapeN]
  | succ N ih =>
      have hsum : Measurable (fun T : Tree =>
          ∑ j ∈ Finset.range (T.val v), escapeN T.val l N (v ++ [j + 1])) := by
        have h : Measurable (fun p : ℕ × Tree =>
            ∑ j ∈ Finset.range p.1, escapeN p.2.val l N (v ++ [j + 1])) :=
          measurable_from_prod_countable_right fun k =>
            (Finset.range k).measurable_sum fun j _ => ih (v ++ [j + 1])
        exact h.comp ((continuous_offspring v).measurable.prodMk measurable_id)
      have hsum' : Measurable (fun T : Tree =>
          ∑ i : Fin (T.val v), escapeN T.val l N (offChild T.val v i)) := by
        have heq : (fun T : Tree => ∑ i : Fin (T.val v),
            escapeN T.val l N (offChild T.val v i)) =
            (fun T : Tree => ∑ j ∈ Finset.range (T.val v),
              escapeN T.val l N (v ++ [j + 1])) := by
          funext T
          simpa only [offChild] using Fin.sum_univ_eq_sum_range
            (fun j => escapeN T.val l N (v ++ [j + 1])) (T.val v)
        rw [heq]
        exact hsum
      change Measurable (fun T : Tree =>
        (∑ i : Fin (T.val v), escapeN T.val l N (offChild T.val v i)) /
          (l + ∑ i : Fin (T.val v), escapeN T.val l N (offChild T.val v i)))
      exact hsum'.div (measurable_const.add hsum')

private noncomputable def Renn (l : ℝ) (N : ℕ) (T : Tree) : ℝ≥0∞ :=
  ENNReal.ofReal ((escapeN T.val l N [])⁻¹)

private theorem measurable_Renn (l : ℝ) (N : ℕ) : Measurable (Renn l N) := by
  exact ENNReal.continuous_ofReal.measurable.comp (measurable_escapeN_treeProv2 l N []).inv

private theorem ae_leafless_pi (h : OffspringHyp μ) (k : ℕ) :
    ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => GW μ),
      ∀ i, ∀ v, Present (ts i) v → 0 < (ts i).val v := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun _ : Fin k => GW μ) i).quasiMeasurePreserving.ae
    (LPPMonotonicityProof.RTL.Leafless.ae_present_offspring_pos μ h.zero)

private theorem leaflessBelow_of_all {T : Tree}
    (hT : ∀ v, Present T v → 0 < T.val v) (N : ℕ) (v : Address) (hv : Present T v) :
    LeaflessBelow T.val N v := by
  induction N generalizing v with
  | zero => trivial
  | succ N ih =>
      refine ⟨hT v hv, fun i => ih _ ?_⟩
      exact (present_append_singleton T v (i.val + 1) hv).2 ⟨Nat.succ_pos _, i.isLt⟩

private theorem escapeN_nodeFin_child (l : ℝ) (k : ℕ) (ts : Fin k → Tree)
    (i : Fin k) (N : ℕ) :
    escapeN (nodeFin k ts).val l N [i.val + 1] = escapeN (ts i).val l N [] := by
  rw [← escapeN_shift (nodeFin k ts).val l (i.val + 1) N []]
  have hst : Speed.subtree (nodeFin k ts) [i.val + 1] = ts i := by
    rw [Speed.subtree_cons, Speed.subtree_nil, children_nodeFin]
  exact congrArg (fun T : Tree => escapeN T.val l N []) hst

private theorem harmonic_recip_bound {k : ℕ} (hk : 0 < k) (l : ℝ)
    (r b : Fin k → ℝ) (hr : ∀ i, 0 < r i) (hb : ∀ i, b i = (r i)⁻¹) :
    (∑ i, b i)⁻¹ ≤ (∑ i, r i) / (k : ℝ) ^ 2 := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hA : 0 < ∑ i, r i := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  have hB : 0 < ∑ i, b i := by
    apply Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    rw [hb i]
    exact inv_pos.mpr (hr i)
  have hkR : 0 < (k : ℝ) ^ 2 := by positivity
  have hcs := Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun _ : Fin k => (1 : ℝ))
    (g := r) (fun i _ => hr i)
  have hcs' : (k : ℝ) ^ 2 / (∑ i, r i) ≤ ∑ i, b i := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      one_pow, one_mul, hb, mul_one, one_div] using hcs
  have hi := (inv_le_inv₀ hB (div_pos hkR hA)).2 hcs'
  simpa only [inv_div] using hi

private theorem recipN_nodeFin_succ_le (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (N : ℕ) {k : ℕ} (hk : 0 < k) :
    ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => GW μ),
      (escapeN (nodeFin k ts).val l (N + 1) [])⁻¹ ≤
        1 + l / (k : ℝ) ^ 2 * ∑ i, (escapeN (ts i).val l N [])⁻¹ := by
  filter_upwards [ae_leafless_pi h k] with ts hts
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hr (i : Fin k) : 0 < (escapeN (ts i).val l N [])⁻¹ := by
    exact inv_pos.mpr (escapeN_pos (ts i).val hl N []
      (leaflessBelow_of_all (hts i) N [] (present_nil _)))
  have hb (i : Fin k) : escapeN (ts i).val l N [] =
      ((escapeN (ts i).val l N [])⁻¹)⁻¹ := (inv_inv _).symm
  let S : ℝ := ∑ i, escapeN (ts i).val l N []
  have hS : 0 < S := by
    apply Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    exact escapeN_pos (ts i).val hl N []
      (leaflessBelow_of_all (hts i) N [] (present_nil _))
  have hroot : (escapeN (nodeFin k ts).val l (N + 1) [])⁻¹ = 1 + l / S := by
    change (escapeN (nodeFin k ts).val l (Nat.succ N) [])⁻¹ = 1 + l / S
    rw [escapeN]
    simp only [offChild, List.nil_append]
    change (((∑ i : Fin k, escapeN (nodeFin k ts).val l N [i.val + 1]) /
      (l + ∑ i : Fin k, escapeN (nodeFin k ts).val l N [i.val + 1]))⁻¹ = 1 + l / S)
    have heq : (∑ i : Fin k, escapeN (nodeFin k ts).val l N [i.val + 1]) = S := by
      apply Finset.sum_congr rfl
      intro i _
      exact escapeN_nodeFin_child l k ts i N
    rw [heq, inv_div]
    field_simp [hS.ne']
    ring
  rw [hroot]
  apply add_le_add le_rfl
  have hh := harmonic_recip_bound hk l (fun i => (escapeN (ts i).val l N [])⁻¹)
    (fun i => escapeN (ts i).val l N []) hr hb
  dsimp only [S]
  have hm := mul_le_mul_of_nonneg_left hh hl.le
  convert hm using 1 <;> ring

private theorem Rinv_nodeFin_succ_le (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (N : ℕ) {k : ℕ} (hk : 0 < k) :
    ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => GW μ),
      Renn l (N + 1) (nodeFin k ts) ≤
        1 + ENNReal.ofReal (l / (k : ℝ) ^ 2) * ∑ i, Renn l N (ts i) := by
  filter_upwards [recipN_nodeFin_succ_le h hl N hk, ae_leafless_pi h k] with ts hbound hts
  calc
    Renn l (N + 1) (nodeFin k ts) ≤ ENNReal.ofReal (1 + l / (k : ℝ) ^ 2 *
        ∑ i, (escapeN (ts i).val l N [])⁻¹) := ENNReal.ofReal_le_ofReal hbound
    _ = 1 + ENNReal.ofReal (l / (k : ℝ) ^ 2) * ∑ i, Renn l N (ts i) := by
      have hn : 0 ≤ l / (k : ℝ) ^ 2 * ∑ i, (escapeN (ts i).val l N [])⁻¹ := by
        apply mul_nonneg (by positivity)
        exact Finset.sum_nonneg fun i _ => inv_nonneg.mpr (escapeN_nonneg' (ts i).val hl N [])
      rw [ENNReal.ofReal_add (by positivity) hn, ENNReal.ofReal_one,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg]
      · rfl
      · intro i _
        exact inv_nonneg.mpr (escapeN_nonneg' (ts i).val hl N [])

private theorem lintegral_Renn_nodeFin_succ_le (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (N : ℕ) {k : ℕ} (hk : 0 < k) :
    (∫⁻ ts, Renn l (N + 1) (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ)) ≤
      1 + ENNReal.ofReal (l * (k : ℝ)⁻¹) * ∫⁻ T, Renn l N T ∂GW μ := by
  have hm (i : Fin k) : Measurable (fun ts : Fin k → Tree => Renn l N (ts i)) :=
    (measurable_Renn l N).comp (measurable_pi_apply i)
  have hsum : Measurable (fun ts : Fin k → Tree => ∑ i, Renn l N (ts i)) :=
    Finset.univ.measurable_sum fun i _ => hm i
  have heval (i : Fin k) :
      (∫⁻ ts, Renn l N (ts i) ∂Measure.pi (fun _ : Fin k => GW μ)) =
        ∫⁻ T, Renn l N T ∂GW μ :=
    (measurePreserving_eval (fun _ : Fin k => GW μ) i).lintegral_comp (measurable_Renn l N)
  have hcoeff : ENNReal.ofReal (l / (k : ℝ) ^ 2) * (k : ℝ≥0∞) =
      ENNReal.ofReal (l * (k : ℝ)⁻¹) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [ne_of_gt (show (0 : ℝ) < k by exact_mod_cast hk)]
  calc
    _ ≤ ∫⁻ ts, (1 + ENNReal.ofReal (l / (k : ℝ) ^ 2) * ∑ i, Renn l N (ts i))
        ∂Measure.pi (fun _ : Fin k => GW μ) :=
      lintegral_mono_ae (Rinv_nodeFin_succ_le h hl N hk)
    _ = 1 + ENNReal.ofReal (l / (k : ℝ) ^ 2) * ∑ i,
        (∫⁻ ts, Renn l N (ts i) ∂Measure.pi (fun _ : Fin k => GW μ)) := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul _ hsum,
        lintegral_finsetSum Finset.univ (fun i _ => hm i)]
      simp
    _ = 1 + ENNReal.ofReal (l / (k : ℝ) ^ 2) * (k : ℝ≥0∞) *
        (∫⁻ T, Renn l N T ∂GW μ) := by simp_rw [heval]; simp [mul_assoc]
    _ = _ := by rw [hcoeff]

private theorem lintegral_offspring_inv {l : ℝ} (hl : 0 < l) :
    (∫⁻ k, ENNReal.ofReal (l * (k : ℝ)⁻¹) ∂μ) = ENNReal.ofReal (l * invMean μ) := by
  have hbase : Integrable (fun k : ℕ => (k : ℝ)⁻¹) μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    filter_upwards with k
    cases k with
    | zero => simp
    | succ k =>
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((k + 1 : ℕ) : ℝ)⁻¹)]
        exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_pos k)
  have hint : Integrable (fun k : ℕ => l * (k : ℝ)⁻¹) μ := hbase.const_mul l
  have hn : ∀ k : ℕ, 0 ≤ l * (k : ℝ)⁻¹ := fun k =>
    mul_nonneg hl.le (inv_nonneg.mpr (Nat.cast_nonneg k))
  rw [show l * invMean μ = ∫ k, l * (k : ℝ)⁻¹ ∂μ by
    rw [integral_const_mul]
    rfl]
  exact (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hn)).symm

private theorem lintegral_Renn_succ_le (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (N : ℕ) :
    (∫⁻ T, Renn l (N + 1) T ∂GW μ) ≤
      1 + ENNReal.ofReal (l * invMean μ) * ∫⁻ T, Renn l N T ∂GW μ := by
  let A : ℝ≥0∞ := ∫⁻ T, Renn l N T ∂GW μ
  have hterm (k : ℕ) : μ {k} * (∫⁻ ts, Renn l (N + 1) (nodeFin k ts)
      ∂Measure.pi (fun _ : Fin k => GW μ)) ≤
      μ {k} * (1 + ENNReal.ofReal (l * (k : ℝ)⁻¹) * A) := by
    by_cases hk : k = 0
    · subst k
      simp [h.zero]
    · gcongr
      exact lintegral_Renn_nodeFin_succ_le h hl N (Nat.pos_of_ne_zero hk)
  have hmass : (∑' k : ℕ, μ {k} * ENNReal.ofReal (l * (k : ℝ)⁻¹)) =
      ENNReal.ofReal (l * invMean μ) := by
    calc
      _ = ∑' k : ℕ, ENNReal.ofReal (l * (k : ℝ)⁻¹) * μ {k} := by
        apply tsum_congr
        intro k
        exact mul_comm _ _
      _ = ∫⁻ k, ENNReal.ofReal (l * (k : ℝ)⁻¹) ∂μ := (lintegral_countable' _).symm
      _ = _ := lintegral_offspring_inv hl
  rw [lintegral_GW_eq_tsum (Renn l (N + 1)) (measurable_Renn l (N + 1))]
  calc
    _ ≤ ∑' k : ℕ, μ {k} * (1 + ENNReal.ofReal (l * (k : ℝ)⁻¹) * A) :=
      ENNReal.tsum_le_tsum hterm
    _ = (∑' k : ℕ, μ {k}) + (∑' k : ℕ, μ {k} * ENNReal.ofReal (l * (k : ℝ)⁻¹)) * A := by
      simp_rw [mul_add, mul_one, ← mul_assoc]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ = 1 + ENNReal.ofReal (l * invMean μ) * A := by rw [LPPMonotonicityProof.RTL.tsum_measure_singleton, hmass]
    _ = _ := rfl

private theorem lintegral_Renn_le (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hU : l * invMean μ < 1) (N : ℕ) :
    (∫⁻ T, Renn l N T ∂GW μ) ≤ ENNReal.ofReal (1 - l * invMean μ)⁻¹ := by
  let q : ℝ≥0∞ := ENNReal.ofReal (l * invMean μ)
  have hgeo : (1 - q)⁻¹ = ENNReal.ofReal (1 - l * invMean μ)⁻¹ := by
    dsimp only [q]
    rw [ENNReal.ofReal_inv_of_pos (sub_pos.mpr hU),
      ENNReal.ofReal_sub 1 (mul_nonneg hl.le (by
        apply integral_nonneg_of_ae
        exact ae_of_all _ fun k => inv_nonneg.mpr (Nat.cast_nonneg k))), ENNReal.ofReal_one]
  have hpartial : ∀ N : ℕ, (∫⁻ T, Renn l N T ∂GW μ) ≤ ∑ j ∈ Finset.range (N + 1), q ^ j := by
    intro N
    induction N with
    | zero => simp [Renn, escapeN, q]
    | succ N ih =>
        calc
          _ ≤ 1 + q * ∫⁻ T, Renn l N T ∂GW μ := lintegral_Renn_succ_le h hl N
          _ ≤ 1 + q * ∑ j ∈ Finset.range (N + 1), q ^ j := by gcongr
          _ = ∑ j ∈ Finset.range (N + 1 + 1), q ^ j := by
            symm
            rw [Finset.sum_range_succ']
            simp only [pow_zero, pow_succ', Finset.mul_sum]
            ac_rfl
  rw [← hgeo, ← ENNReal.tsum_geometric]
  exact (hpartial N).trans (ENNReal.sum_le_tsum (Finset.range (N + 1)))

private theorem lintegral_Renn_limit (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) :
    (∫⁻ T, (ENNReal.ofReal (escape l T))⁻¹ ∂GW μ) = ⨆ N, ∫⁻ T, Renn l N T ∂GW μ := by
  have hmono : ∀ N, ∀ᵐ T ∂GW μ, Renn l N T ≤ Renn l (N + 1) T := by
    intro N
    filter_upwards [LPPMonotonicityProof.RTL.Leafless.ae_present_offspring_pos μ h.zero] with T hT
    have hposN : 0 < escapeN T.val l N [] := escapeN_pos T.val hl N []
      (leaflessBelow_of_all hT N [] (present_nil T))
    have hposS : 0 < escapeN T.val l (N + 1) [] := escapeN_pos T.val hl (N + 1) []
      (leaflessBelow_of_all hT (N + 1) [] (present_nil T))
    apply ENNReal.ofReal_le_ofReal
    exact (inv_le_inv₀ hposN hposS).2 (escapeN_anti_height T.val hl N [])
  have hpoint : ∀ᵐ T ∂GW μ, (ENNReal.ofReal (escape l T))⁻¹ = ⨆ N, Renn l N T := by
    filter_upwards [LPPMonotonicityProof.RTL.Leafless.ae_present_offspring_pos μ h.zero] with T hT
    have hpos (N : ℕ) : 0 < escapeN T.val l N [] := escapeN_pos T.val hl N []
      (leaflessBelow_of_all hT N [] (present_nil T))
    change (ENNReal.ofReal (escapeRaw T.val l []))⁻¹ = _
    unfold escapeRaw
    rw [ENNReal.ofReal_iInf, ENNReal.inv_iInf]
    apply iSup_congr
    intro N
    exact (ENNReal.ofReal_inv_of_pos (hpos N)).symm
  calc
    _ = ∫⁻ T, ⨆ N, Renn l N T ∂GW μ := lintegral_congr_ae hpoint
    _ = _ := lintegral_iSup_ae (fun N => measurable_Renn l N) hmono

/-- Lemma 2.4 (`lem:inverse-moment`): the extended inverse escape moment is bounded by
`(1-lU)⁻¹`. -/
theorem lintegral_inv_escape_le (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hU : l * invMean μ < 1) :
    ∫⁻ T, (ENNReal.ofReal (escape l T))⁻¹ ∂GW μ ≤
      ENNReal.ofReal (1 - l * invMean μ)⁻¹ := by
  rw [lintegral_Renn_limit h hl]
  exact iSup_le fun N => lintegral_Renn_le h hl hU N

private theorem bias_lt_mean_of_linvMean_lt_one (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hU : l * invMean μ < 1) : l < mean μ := by
  have hm : 0 < mean μ := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt (lt_trans (by simp) h.one_lt_mean)
    · exact h.mean_lt_top.ne
  have hUp : 0 < invMean μ := (one_div_pos.mpr hm).trans_le (invMean_bounds h).1
  have hfrac : l / mean μ < 1 := by
    apply lt_of_le_of_lt _ hU
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ hl.le
    simpa only [one_div] using (invMean_bounds h).1
  exact (div_lt_one hm).mp hfrac

/-- Lemma 2.4 (`lem:inverse-moment`): almost-sure positivity and real integrability of
the reciprocal escape. -/
theorem integrable_inv_escape (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hU : l * invMean μ < 1) :
    (∀ᵐ T ∂GW μ, 0 < escape l T) ∧ Integrable (fun T => (escape l T)⁻¹) (GW μ) := by
  have hpos : ∀ᵐ T ∂GW μ, 0 < escape l T :=
    ae_escape_pos h hl (bias_lt_mean_of_linvMean_lt_one h hl hU)
  refine ⟨hpos, (measurable_escape l).inv.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (hpos.mono fun T hT => inv_nonneg.mpr hT.le)).2
  have heq : (fun T => ENNReal.ofReal ((escape l T)⁻¹)) =ᵐ[GW μ]
      (fun T => (ENNReal.ofReal (escape l T))⁻¹) :=
    hpos.mono fun T hT => ENNReal.ofReal_inv_of_pos hT
  rw [lintegral_congr_ae heq]
  exact (lintegral_inv_escape_le h hl hU).trans_lt ENNReal.ofReal_lt_top

end LPPMonotonicityProof.Analytic
