module

public import LPPMonotonicityProof.Analytic.CostExport
public import LPPMonotonicityProof.Analytic.Interface2
public import LPPMonotonicityProof.Analytic.RegularityExport
public import LPPMonotonicityProof.Analytic.SingleCrossing
public import LPPMonotonicityProof.Speed.Env.Swap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Subtree exchange

This module proves Theorem 3.5 (`thm:ward`).  The child exchange is performed after
the exact root-degree decomposition, with all integral rearrangements justified by
domination.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

local notation "ρ" => Measure.prod (GW μ) (GW μ)

private noncomputable def wardDen (l : ℝ) (T U : Tree) : ℝ :=
  l - 1 + childSum l T + escape l U

private lemma childSum_nonneg_ward {l : ℝ} (hl : 0 < l) (T : Tree) :
    0 ≤ childSum l T := by
  unfold childSum
  exact Finset.sum_nonneg fun i _ => (escape_mem_Icc hl _).1

private lemma ae_regTree_pair_ward (h : OffspringHyp μ) :
    ∀ᵐ p : Tree × Tree ∂ρ, RegTree μ p.1 ∧ RegTree μ p.2 :=
  (Measure.quasiMeasurePreserving_fst.ae (ae_regTree h)).and
    (Measure.quasiMeasurePreserving_snd.ae (ae_regTree h))

private lemma DfunProv_lower_ward {l x y : ℝ} (_hl : 1 < l)
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    l - 1 ≤ DfunProv l x y := by
  have hxy : 0 ≤ x * (1 - y) := mul_nonneg hx.1 (sub_nonneg.mpr hy.2)
  unfold DfunProv
  have hx0 : 0 ≤ x := hx.1
  have hy1 : y ≤ 1 := hy.2
  have hy0 : 0 ≤ y := hy.1
  linarith

private lemma measurable_Gam_escape_ward (l : ℝ) :
    Measurable (fun T => Gam μ l (escape l T)) := by
  have hm : Measurable (fun p : Tree × Tree =>
      Pol l (speedValueProv μ l) (escape l p.2) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2) := by
    have he := measurable_escape l
    unfold Pol DfunProv
    fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := GW μ)).measurable

private lemma measurable_Gam2_escape_ward (l : ℝ) :
    Measurable (fun T => Gam2 μ l (escape l T)) := by
  have hm : Measurable (fun p : Tree × Tree => escape l p.2 ^ 2 /
      DfunProv l (escape l p.1) (escape l p.2) ^ 2) := by
    have he := measurable_escape l
    unfold DfunProv
    fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := GW μ)).measurable

private lemma integrable_pair_resp_ward (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (q : ℝ → ℝ) (hq : Measurable q)
    (hq1 : ∀ x ∈ Set.Icc 0 1, |q x| ≤ 1) :
    Integrable (fun p : Tree × Tree => resp l p.1 * q (escape l p.2) /
      DfunProv l (escape l p.1) (escape l p.2) ^ 2) ρ := by
  have hl0 : l ∈ Set.Ioo 0 (mean μ) := ⟨by linarith, hlm⟩
  have ha : 0 < l - 1 := by linarith
  have hr : Integrable (fun p : Tree × Tree => resp l p.1 / (l - 1) ^ 2) ρ :=
    ((integrable_resp h hl0).comp_fst (GW μ)).div_const _
  have hm : AEStronglyMeasurable (fun p : Tree × Tree =>
      resp l p.1 * q (escape l p.2) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2) ρ := by
    have hr' := (aemeasurable_resp_of_mem h hl0).comp_fst (ν := GW μ)
    have hq' : Measurable (fun p : Tree × Tree => q (escape l p.2)) :=
      hq.comp ((measurable_escape l).comp measurable_snd)
    have hD : Measurable (fun p : Tree × Tree =>
        DfunProv l (escape l p.1) (escape l p.2)) := by
      have he := measurable_escape l
      unfold DfunProv
      fun_prop
    exact (hr'.mul hq'.aemeasurable).div (hD.pow_const 2).aemeasurable |>.aestronglyMeasurable
  apply hr.mono' hm
  filter_upwards [ae_regTree_pair_ward h] with p hp
  have hx : escape l p.1 ∈ Set.Icc 0 1 := escape_mem_Icc (by linarith) _
  have hy : escape l p.2 ∈ Set.Icc 0 1 := escape_mem_Icc (by linarith) _
  have hD0 : 0 < DfunProv l (escape l p.1) (escape l p.2) :=
    lt_of_lt_of_le ha (DfunProv_lower_ward hl hx hy)
  have hD2 : (l - 1) ^ 2 ≤ DfunProv l (escape l p.1) (escape l p.2) ^ 2 :=
    (sq_le_sq₀ ha.le hD0.le).2 (DfunProv_lower_ward hl hx hy)
  have hru : 0 ≤ resp l p.1 := by
    have hs : 0 ≤ escape l p.1 * (1 - escape l p.1) :=
      mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
    exact hs.trans (resp_ge hp.1 hl0)
  have hq' := hq1 (escape l p.2) hy
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos hD0,
    abs_of_nonneg hru]
  rw [div_le_div_iff₀ (sq_pos_of_pos hD0) (sq_pos_of_pos ha)]
  calc
    resp l p.1 * |q (escape l p.2)| * (l - 1) ^ 2 ≤
        resp l p.1 * (l - 1) ^ 2 :=
      mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left hq' hru)
        (sq_nonneg _)
    _ ≤ resp l p.1 * DfunProv l (escape l p.1) (escape l p.2) ^ 2 :=
      mul_le_mul_of_nonneg_left hD2 hru

private lemma wardDen_pos {l : ℝ} (hl : 1 < l) (T U : Tree) : 0 < wardDen l T U := by
  have hS : 0 ≤ childSum l T := childSum_nonneg_ward (by linarith) T
  have hU : 0 ≤ escape l U := (escape_mem_Icc (by linarith) U).1
  unfold wardDen
  linarith

private lemma Dfun_eq_wardDen {l : ℝ} (hl : 1 < l) (T U : Tree) :
    DfunProv l (escape l T) (escape l U) = l * wardDen l T U / (l + childSum l T) := by
  have hl0 : 0 < l := by linarith
  have hS : 0 ≤ childSum l T := childSum_nonneg_ward hl0 T
  have hLS : l + childSum l T ≠ 0 := (add_pos_of_pos_of_nonneg hl0 hS).ne'
  rw [escape_eq hl0 T]
  unfold DfunProv wardDen
  field_simp [hLS, hl0.ne']
  ring

private lemma response_ward_algebra {T U : Tree} (hT : RegTree μ T)
    {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    (resp l T - escape l T * (1 - escape l T)) * escape l U /
        DfunProv l (escape l T) (escape l U) ^ 2 =
      (1 / l) * ((∑ i : Fin (degree T), resp l (child T (i + 1))) * escape l U /
        wardDen l T U ^ 2) := by
  have hl0 : l ∈ Set.Ioo 0 (mean μ) := ⟨by linarith, hlm⟩
  have hLS : l + childSum l T ≠ 0 :=
    (add_pos_of_pos_of_nonneg hl0.1 (childSum_nonneg_ward hl0.1 T)).ne'
  have hden := (wardDen_pos hl T U).ne'
  rw [resp_eq hT hl0, Dfun_eq_wardDen hl]
  field_simp [hl0.1.ne', hLS, hden]
  ring

private lemma root_ward_algebra {l : ℝ} (hl : 1 < l) (T U : Tree) :
    resp l U * (escape l T * (1 - escape l T)) /
        DfunProv l (escape l T) (escape l U) ^ 2 =
      (1 / l) * (resp l U * childSum l T / wardDen l T U ^ 2) := by
  have hl0 : 0 < l := by linarith
  have hS : 0 ≤ childSum l T := childSum_nonneg_ward hl0 T
  have hLS : l + childSum l T ≠ 0 := (add_pos_of_pos_of_nonneg hl0 hS).ne'
  have hden := (wardDen_pos hl T U).ne'
  rw [Dfun_eq_wardDen hl, escape_eq hl0 T]
  field_simp [hl0.ne', hLS, hden]
  ring


private lemma integrable_div_sq_ward {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {a : ℝ} (ha : 0 < a) {f g d : Ω → ℝ} (hfint : Integrable f ν)
    (hf0 : ∀ᵐ ω ∂ν, 0 ≤ f ω) (hg : AEMeasurable g ν) (hd : Measurable d)
    (hg1 : ∀ᵐ ω ∂ν, |g ω| ≤ 1) (hdlow : ∀ᵐ ω ∂ν, a ≤ d ω) :
    Integrable (fun ω => f ω * g ω / d ω ^ 2) ν := by
  have hr : Integrable (fun ω => f ω / a ^ 2) ν := hfint.div_const _
  have hm : AEStronglyMeasurable (fun ω => f ω * g ω / d ω ^ 2) ν :=
    (hfint.aemeasurable.mul hg).div (hd.pow_const 2).aemeasurable |>.aestronglyMeasurable
  apply hr.mono' hm
  filter_upwards [hf0, hg1, hdlow] with ω hfω hgω hdω
  have hD : 0 < d ω := lt_of_lt_of_le ha hdω
  have hD2 : a ^ 2 ≤ d ω ^ 2 := (sq_le_sq₀ ha.le hD.le).2 hdω
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos hD,
    abs_of_nonneg hfω]
  rw [div_le_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos ha)]
  calc
    f ω * |g ω| * a ^ 2 ≤ f ω * a ^ 2 :=
      mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left hgω hfω)
        (sq_nonneg _)
    _ ≤ f ω * d ω ^ 2 := mul_le_mul_of_nonneg_left hD2 hfω

private lemma ae_regTree_tuple_ward (h : OffspringHyp μ) (k : ℕ) :
    ∀ᵐ q : (Fin k → Tree) × Tree ∂(Measure.pi fun _ : Fin k => GW μ).prod (GW μ),
      (∀ i, RegTree μ (q.1 i)) ∧ RegTree μ q.2 := by
  have hpi : ∀ᵐ ts : Fin k → Tree ∂Measure.pi (fun _ : Fin k => GW μ),
      ∀ i, RegTree μ (ts i) := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (μ := fun _ : Fin k => GW μ) i).quasiMeasurePreserving.ae
      (ae_regTree h)
  exact (Measure.quasiMeasurePreserving_fst.ae hpi).and
    (Measure.quasiMeasurePreserving_snd.ae (ae_regTree h))

private lemma measurable_wardDen_nodeFin (l : ℝ) (k : ℕ) :
    Measurable (fun q : (Fin k → Tree) × Tree => wardDen l (nodeFin k q.1) q.2) := by
  have hS : Measurable (fun q : (Fin k → Tree) × Tree => childSum l (nodeFin k q.1)) :=
    (measurable_childSum l).comp ((measurable_nodeFin k).comp measurable_fst)
  have hU : Measurable (fun q : (Fin k → Tree) × Tree => escape l q.2) :=
    (measurable_escape l).comp measurable_snd
  exact (measurable_const.add hS).add hU

private lemma wardDen_lower {l : ℝ} (hl : 1 < l) (T U : Tree) :
    l - 1 ≤ wardDen l T U := by
  have hS : 0 ≤ childSum l T := childSum_nonneg_ward (by linarith) T
  have hU : 0 ≤ escape l U := (escape_mem_Icc (by linarith) U).1
  unfold wardDen
  linarith

private lemma integrable_tuple_child_left_ward (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) {k : ℕ} (i : Fin k) :
    Integrable (fun q : (Fin k → Tree) × Tree =>
      resp l (q.1 i) * escape l q.2 / wardDen l (nodeFin k q.1) q.2 ^ 2)
      ((Measure.pi fun _ : Fin k => GW μ).prod (GW μ)) := by
  have hl0 : l ∈ Set.Ioo 0 (mean μ) := ⟨by linarith, hlm⟩
  have hi : Integrable (fun q : (Fin k → Tree) × Tree => resp l (q.1 i))
      ((Measure.pi fun _ : Fin k => GW μ).prod (GW μ)) := by
    have hbase := (measurePreserving_eval (μ := fun _ : Fin k => GW μ) i)
      |>.integrable_comp_of_integrable (integrable_resp h hl0)
    simpa [Function.comp_def] using hbase.comp_fst (GW μ)
  refine integrable_div_sq_ward (a := l - 1)
    (f := fun q : (Fin k → Tree) × Tree => resp l (q.1 i))
    (g := fun q : (Fin k → Tree) × Tree => escape l q.2)
    (d := fun q : (Fin k → Tree) × Tree => wardDen l (nodeFin k q.1) q.2)
    (by linarith) hi ?_ ?_ ?_ ?_ ?_
  · filter_upwards [ae_regTree_tuple_ward h k] with q hq
    have hx := escape_mem_Icc (show 0 < l by linarith) (q.1 i)
    exact (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)).trans
      (resp_ge (hq.1 i) hl0)
  · exact ((measurable_escape l).comp measurable_snd).aemeasurable
  · exact measurable_wardDen_nodeFin l k
  · filter_upwards with q
    rw [abs_of_nonneg (escape_mem_Icc (show 0 < l by linarith) q.2).1]
    exact (escape_mem_Icc (show 0 < l by linarith) q.2).2
  · filter_upwards with q
    exact wardDen_lower hl _ _

private lemma integrable_tuple_child_right_ward (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) {k : ℕ} (i : Fin k) :
    Integrable (fun q : (Fin k → Tree) × Tree =>
      resp l q.2 * escape l (q.1 i) / wardDen l (nodeFin k q.1) q.2 ^ 2)
      ((Measure.pi fun _ : Fin k => GW μ).prod (GW μ)) := by
  have hl0 : l ∈ Set.Ioo 0 (mean μ) := ⟨by linarith, hlm⟩
  have hu : Integrable (fun q : (Fin k → Tree) × Tree => resp l q.2)
      ((Measure.pi fun _ : Fin k => GW μ).prod (GW μ)) :=
    (integrable_resp h hl0).comp_snd _
  refine integrable_div_sq_ward (a := l - 1)
    (f := fun q : (Fin k → Tree) × Tree => resp l q.2)
    (g := fun q : (Fin k → Tree) × Tree => escape l (q.1 i))
    (d := fun q : (Fin k → Tree) × Tree => wardDen l (nodeFin k q.1) q.2)
    (by linarith) hu ?_ ?_ ?_ ?_ ?_
  · filter_upwards [ae_regTree_tuple_ward h k] with q hq
    have hx := escape_mem_Icc (show 0 < l by linarith) q.2
    exact (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)).trans (resp_ge hq.2 hl0)
  · have hchild : Measurable (fun q : (Fin k → Tree) × Tree => q.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    exact ((measurable_escape l).comp hchild).aemeasurable
  · exact measurable_wardDen_nodeFin l k
  · filter_upwards with q
    rw [abs_of_nonneg (escape_mem_Icc (show 0 < l by linarith) (q.1 i)).1]
    exact (escape_mem_Icc (show 0 < l by linarith) (q.1 i)).2
  · filter_upwards with q
    exact wardDen_lower hl _ _

private lemma swapFin_involutive_ward {k : ℕ} (i : Fin k)
    (q : (Fin k → Tree) × Tree) : swapFin i (swapFin i q) = q := by
  rcases q with ⟨ts, U⟩
  apply Prod.ext
  · funext j
    by_cases hji : j = i
    · subst j
      simp [swapFin]
    · simp [swapFin]
  · simp [swapFin]

private lemma wardDen_nodeFin_swapFin (l : ℝ) {k : ℕ} (i : Fin k)
    (q : (Fin k → Tree) × Tree) :
    wardDen l (nodeFin k (swapFin i q).1) (swapFin i q).2 =
      wardDen l (nodeFin k q.1) q.2 := by
  unfold wardDen
  simp only [swapFin, childSum_nodeFin]
  have hsum : (∑ j : Fin k, escape l (Function.update q.1 i q.2 j)) =
      ∑ j : Fin k, Function.update (fun j => escape l (q.1 j)) i (escape l q.2) j := by
    apply Finset.sum_congr rfl
    intro j _
    exact Function.apply_update (fun _ : Fin k => fun T : Tree => escape l T)
      q.1 i q.2 j
  rw [hsum, Finset.sum_update_of_mem (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

private lemma integral_pair_nodeFin_ward {f : Tree × Tree → ℝ}
    (hf : Integrable f ρ)
    (hfk : ∀ k : ℕ, Integrable (fun q : (Fin k → Tree) × Tree =>
      f (nodeFin k q.1, q.2)) ((Measure.pi fun _ : Fin k => GW μ).prod (GW μ))) :
    (∫ p, f p ∂ρ) = ∑' k : ℕ, (μ {k}).toReal *
      ∫ q : (Fin k → Tree) × Tree, f (nodeFin k q.1, q.2)
        ∂(Measure.pi fun _ : Fin k => GW μ).prod (GW μ) := by
  calc
    (∫ p, f p ∂ρ) = ∫ T, ∫ U, f (T, U) ∂GW μ ∂GW μ := integral_prod _ hf
    _ = ∑' k : ℕ, (μ {k}).toReal *
        ∫ q : (Fin k → Tree) × Tree, f (nodeFin k q.1, q.2)
          ∂(Measure.pi fun _ : Fin k => GW μ).prod (GW μ) := by
      rw [integral_GW_eq_tsum (fun T => ∫ U, f (T, U) ∂GW μ) hf.integral_prod_left]
      apply tsum_congr
      intro k
      rw [integral_prod _ (hfk k)]

private lemma integral_fixed_child_exchange_ward (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (k : ℕ) :
    (∫ q : (Fin k → Tree) × Tree,
        (∑ i, resp l (q.1 i)) * escape l q.2 / wardDen l (nodeFin k q.1) q.2 ^ 2
          ∂(Measure.pi fun _ : Fin k => GW μ).prod (GW μ)) =
      ∫ q : (Fin k → Tree) × Tree,
        resp l q.2 * childSum l (nodeFin k q.1) / wardDen l (nodeFin k q.1) q.2 ^ 2
          ∂(Measure.pi fun _ : Fin k => GW μ).prod (GW μ) := by
  let π := (Measure.pi fun _ : Fin k => GW μ).prod (GW μ)
  let L : Fin k → ((Fin k → Tree) × Tree) → ℝ := fun i q =>
    resp l (q.1 i) * escape l q.2 / wardDen l (nodeFin k q.1) q.2 ^ 2
  let R : Fin k → ((Fin k → Tree) × Tree) → ℝ := fun i q =>
    resp l q.2 * escape l (q.1 i) / wardDen l (nodeFin k q.1) q.2 ^ 2
  have hLR (i : Fin k) : (∫ q, L i q ∂π) = ∫ q, R i q ∂π := by
    let e : ((Fin k → Tree) × Tree) ≃ᵐ ((Fin k → Tree) × Tree) :=
      { toFun := swapFin i
        invFun := swapFin i
        left_inv := swapFin_involutive_ward i
        right_inv := swapFin_involutive_ward i
        measurable_toFun := measurable_swapFin i
        measurable_invFun := measurable_swapFin i }
    have he : MeasurePreserving e π π := measurePreserving_swapFin i
    have hint := he.integral_comp' (R i)
    calc
      (∫ q, L i q ∂π) = ∫ q, R i (e q) ∂π := by
        apply integral_congr_ae
        filter_upwards with q
        change resp l (q.1 i) * escape l q.2 / wardDen l (nodeFin k q.1) q.2 ^ 2 = _
        change _ = R i (swapFin i q)
        dsimp only [R, swapFin]
        have hd := wardDen_nodeFin_swapFin l i q
        dsimp only [swapFin] at hd
        rw [Function.update_self, hd]
      _ = _ := hint
  have hLsum : (fun q => (∑ i, resp l (q.1 i)) * escape l q.2 /
      wardDen l (nodeFin k q.1) q.2 ^ 2) = fun q => ∑ i, L i q := by
    funext q
    dsimp only [L]
    rw [Finset.sum_mul, Finset.sum_div]
  have hRsum : (fun q => resp l q.2 * childSum l (nodeFin k q.1) /
      wardDen l (nodeFin k q.1) q.2 ^ 2) = fun q => ∑ i, R i q := by
    funext q
    dsimp only [R]
    rw [childSum_nodeFin, Finset.mul_sum, Finset.sum_div]
  rw [hLsum, hRsum, integral_finsetSum, integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ => hLR i
  · intro i _
    exact integrable_tuple_child_right_ward h hl hlm i
  · intro i _
    exact integrable_tuple_child_left_ward h hl hlm i



private lemma abs_id_le_one_ward {x : ℝ} (hx : x ∈ Set.Icc 0 1) : |x| ≤ 1 := by
  rw [abs_of_nonneg hx.1]
  exact hx.2

private lemma abs_sq_le_one_ward {x : ℝ} (hx : x ∈ Set.Icc 0 1) : |x ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg x)]
  nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]

private lemma abs_root_le_one_ward {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    |x * (1 - x)| ≤ 1 := by
  have h0 : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  rw [abs_of_nonneg h0]
  nlinarith [sq_nonneg (x - 1 / 2)]

private lemma integrable_root_pair_ward (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (_hlm : l < mean μ) (q : ℝ → ℝ) (hq : Measurable q)
    (hq1 : ∀ x ∈ Set.Icc 0 1, |q x| ≤ 1) :
    Integrable (fun p : Tree × Tree =>
      escape l p.1 * (1 - escape l p.1) * q (escape l p.2) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2) ρ := by
  have hfm : Measurable (fun p : Tree × Tree =>
      escape l p.1 * (1 - escape l p.1)) := by
    have he := measurable_escape l
    fun_prop
  have hf : Integrable (fun p : Tree × Tree => escape l p.1 * (1 - escape l p.1)) ρ := by
    apply Integrable.of_bound hfm.aestronglyMeasurable 1
    filter_upwards with p
    have hx : escape l p.1 ∈ Set.Icc 0 1 := escape_mem_Icc (by linarith) _
    exact (Real.norm_eq_abs _).symm.trans_le (abs_root_le_one_ward hx)
  have hm : Measurable (fun p : Tree × Tree =>
      DfunProv l (escape l p.1) (escape l p.2)) := by
    have he := measurable_escape l
    unfold DfunProv
    fun_prop
  refine integrable_div_sq_ward (a := l - 1)
    (f := fun p : Tree × Tree => escape l p.1 * (1 - escape l p.1))
    (g := fun p : Tree × Tree => q (escape l p.2))
    (d := fun p : Tree × Tree => DfunProv l (escape l p.1) (escape l p.2))
    (by linarith) hf ?_ ?_ hm ?_ ?_
  · filter_upwards with p
    exact mul_nonneg (escape_mem_Icc (show 0 < l by linarith) _).1
      (sub_nonneg.mpr (escape_mem_Icc (show 0 < l by linarith) _).2)
  · exact (hq.comp ((measurable_escape l).comp measurable_snd)).aemeasurable
  · filter_upwards with p
    exact hq1 _ (escape_mem_Icc (show 0 < l by linarith) _)
  · filter_upwards [ae_regTree_pair_ward h] with p _
    exact DfunProv_lower_ward hl (escape_mem_Icc (show 0 < l by linarith) _)
      (escape_mem_Icc (show 0 < l by linarith) _)

private lemma Dfun_swap_ward (l x y : ℝ) : DfunProv l y x = DfunProv l x y := by
  unfold DfunProv
  ring

private lemma nodeFin_sum_resp_ward (l : ℝ) (k : ℕ) (ts : Fin k → Tree) :
    (∑ i : Fin (degree (nodeFin k ts)), resp l (child (nodeFin k ts) (i + 1))) =
      ∑ i : Fin k, resp l (ts i) := by
  rw [degree_nodeFin]
  apply Finset.sum_congr rfl
  intro i _
  rw [children_nodeFin]

private lemma pair_resp_swap_ward (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    Integrable (fun p : Tree × Tree =>
      resp l p.2 * (escape l p.1 * (1 - escape l p.1)) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2) ρ := by
  have hi := integrable_pair_resp_ward h hl hlm (fun x => x * (1 - x))
    (by fun_prop) (fun _ hx => abs_root_le_one_ward hx)
  have his := hi.swap
  apply his.congr
  filter_upwards with p
  dsimp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
  rw [Dfun_swap_ward l (escape l p.1) (escape l p.2)]

private lemma integral_resp_swap_ward {l : ℝ} :
    (∫ p : Tree × Tree, resp l p.1 * (escape l p.2 * (1 - escape l p.2)) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ) =
      ∫ p : Tree × Tree, resp l p.2 * (escape l p.1 * (1 - escape l p.1)) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ := by
  let f : Tree × Tree → ℝ := fun p => resp l p.1 *
    (escape l p.2 * (1 - escape l p.2)) /
      DfunProv l (escape l p.1) (escape l p.2) ^ 2
  calc
    _ = ∫ p : Tree × Tree, f p ∂ρ := rfl
    _ = ∫ p : Tree × Tree, f p.swap ∂ρ := (integral_prod_swap f).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      dsimp only [f, Prod.fst_swap, Prod.snd_swap]
      rw [Dfun_swap_ward l (escape l p.1) (escape l p.2)]

private lemma integral_global_child_exchange_ward (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    (∫ p : Tree × Tree, (1 / l) *
        ((∑ i : Fin (degree p.1), resp l (child p.1 (i + 1))) * escape l p.2 /
          wardDen l p.1 p.2 ^ 2) ∂ρ) =
      ∫ p : Tree × Tree, (1 / l) *
        (resp l p.2 * childSum l p.1 / wardDen l p.1 p.2 ^ 2) ∂ρ := by
  have hLid := integrable_pair_resp_ward h hl hlm (fun x => x) measurable_id
    (fun _ hx => abs_id_le_one_ward hx)
  have hRid := integrable_root_pair_ward h hl hlm (fun x => x) measurable_id
    (fun _ hx => abs_id_le_one_ward hx)
  have hres : Integrable (fun p : Tree × Tree =>
      (resp l p.1 - escape l p.1 * (1 - escape l p.1)) * escape l p.2 /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2) ρ := by
    apply (hLid.sub hRid).congr
    filter_upwards with p
    simp only [Pi.sub_apply]
    ring
  have hL : Integrable (fun p : Tree × Tree => (1 / l) *
      ((∑ i : Fin (degree p.1), resp l (child p.1 (i + 1))) * escape l p.2 /
        wardDen l p.1 p.2 ^ 2)) ρ := by
    apply hres.congr
    filter_upwards [ae_regTree_pair_ward h] with p hp
    exact response_ward_algebra hp.1 hl hlm
  have hswap := pair_resp_swap_ward h hl hlm
  have hR : Integrable (fun p : Tree × Tree => (1 / l) *
      (resp l p.2 * childSum l p.1 / wardDen l p.1 p.2 ^ 2)) ρ := by
    apply hswap.congr
    filter_upwards with p
    exact root_ward_algebra hl p.1 p.2
  have hLk : ∀ k : ℕ, Integrable (fun q : (Fin k → Tree) × Tree => (1 / l) *
      ((∑ i : Fin (degree (nodeFin k q.1)),
        resp l (child (nodeFin k q.1) (i + 1))) * escape l q.2 /
          wardDen l (nodeFin k q.1) q.2 ^ 2))
      ((Measure.pi fun _ : Fin k => GW μ).prod (GW μ)) := by
    intro k
    have hs : Integrable (fun q : (Fin k → Tree) × Tree =>
        ∑ i, resp l (q.1 i) * escape l q.2 / wardDen l (nodeFin k q.1) q.2 ^ 2)
        ((Measure.pi fun _ : Fin k => GW μ).prod (GW μ)) := by
      apply integrable_finsetSum
      intro i _
      exact integrable_tuple_child_left_ward h hl hlm i
    have hfun : (fun q : (Fin k → Tree) × Tree =>
        ∑ i, resp l (q.1 i) * escape l q.2 / wardDen l (nodeFin k q.1) q.2 ^ 2) =
        fun q => (∑ i, resp l (q.1 i)) * escape l q.2 /
          wardDen l (nodeFin k q.1) q.2 ^ 2 := by
      funext q
      rw [Finset.sum_mul, Finset.sum_div]
    rw [hfun] at hs
    apply (hs.const_mul (1 / l)).congr
    filter_upwards with q
    rw [nodeFin_sum_resp_ward]
  have hRk : ∀ k : ℕ, Integrable (fun q : (Fin k → Tree) × Tree => (1 / l) *
      (resp l q.2 * childSum l (nodeFin k q.1) / wardDen l (nodeFin k q.1) q.2 ^ 2))
      ((Measure.pi fun _ : Fin k => GW μ).prod (GW μ)) := by
    intro k
    have hs : Integrable (fun q : (Fin k → Tree) × Tree =>
        ∑ i, resp l q.2 * escape l (q.1 i) / wardDen l (nodeFin k q.1) q.2 ^ 2)
        ((Measure.pi fun _ : Fin k => GW μ).prod (GW μ)) := by
      apply integrable_finsetSum
      intro i _
      exact integrable_tuple_child_right_ward h hl hlm i
    have hfun : (fun q : (Fin k → Tree) × Tree =>
        ∑ i, resp l q.2 * escape l (q.1 i) / wardDen l (nodeFin k q.1) q.2 ^ 2) =
        fun q => resp l q.2 * childSum l (nodeFin k q.1) /
          wardDen l (nodeFin k q.1) q.2 ^ 2 := by
      funext q
      rw [childSum_nodeFin, Finset.mul_sum, Finset.sum_div]
    rw [hfun] at hs
    exact hs.const_mul (1 / l)
  rw [integral_pair_nodeFin_ward hL hLk, integral_pair_nodeFin_ward hR hRk]
  apply tsum_congr
  intro k
  simp_rw [nodeFin_sum_resp_ward]
  rw [integral_const_mul, integral_const_mul, integral_fixed_child_exchange_ward h hl hlm k]

private lemma integral_global_ward_residual (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    (∫ p : Tree × Tree,
        (resp l p.1 - escape l p.1 * (1 - escape l p.1)) * escape l p.2 /
          DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ) =
      ∫ p : Tree × Tree, resp l p.1 * (escape l p.2 * (1 - escape l p.2)) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ := by
  have hresponse : (∫ p : Tree × Tree,
      (resp l p.1 - escape l p.1 * (1 - escape l p.1)) * escape l p.2 /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ) =
      ∫ p : Tree × Tree, (1 / l) *
        ((∑ i : Fin (degree p.1), resp l (child p.1 (i + 1))) * escape l p.2 /
          wardDen l p.1 p.2 ^ 2) ∂ρ := by
    apply integral_congr_ae
    filter_upwards [ae_regTree_pair_ward h] with p hp
    exact response_ward_algebra hp.1 hl hlm
  have hroot : (∫ p : Tree × Tree, (1 / l) *
      (resp l p.2 * childSum l p.1 / wardDen l p.1 p.2 ^ 2) ∂ρ) =
      ∫ p : Tree × Tree, resp l p.2 * (escape l p.1 * (1 - escape l p.1)) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ := by
    apply integral_congr_ae
    filter_upwards with p
    exact (root_ward_algebra hl p.1 p.2).symm
  rw [hresponse, integral_global_child_exchange_ward h hl hlm, hroot,
    ← integral_resp_swap_ward]



private lemma RW_eq_root_pair_ward {l : ℝ} :
    RW μ l = ∫ p : Tree × Tree,
      escape l p.1 * (1 - escape l p.1) * escape l p.2 /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ := by
  let f : Tree × Tree → ℝ := fun p =>
    escape l p.1 * (1 - escape l p.1) * escape l p.2 /
      DfunProv l (escape l p.1) (escape l p.2) ^ 2
  rw [← integral_prod_swap f]
  unfold RW pairE
  apply integral_congr_ae
  filter_upwards with p
  dsimp only [f, Prod.fst_swap, Prod.snd_swap]
  rw [Dfun_swap_ward l (escape l p.1) (escape l p.2)]
  ring

/-- **Theorem 3.5** (`thm:ward`), subtree-exchange identity `E[u Γ₂(β)] = R_W`. -/
theorem ward_identity (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    ∫ T, resp l T * Gam2 μ l (escape l T) ∂GW μ = RW μ l := by
  have hLid := integrable_pair_resp_ward h hl hlm (fun x => x) measurable_id
    (fun _ hx => abs_id_le_one_ward hx)
  have hRid := integrable_root_pair_ward h hl hlm (fun x => x) measurable_id
    (fun _ hx => abs_id_le_one_ward hx)
  have hL2 := integrable_pair_resp_ward h hl hlm (fun x => x ^ 2) (by fun_prop)
    (fun _ hx => abs_sq_le_one_ward hx)
  have hS := integrable_pair_resp_ward h hl hlm (fun x => x * (1 - x)) (by fun_prop)
    (fun _ hx => abs_root_le_one_ward hx)
  have hresid := integral_global_ward_residual h hl hlm
  have hresid_form : (∫ p : Tree × Tree,
      (resp l p.1 - escape l p.1 * (1 - escape l p.1)) * escape l p.2 /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ) =
      (∫ p : Tree × Tree, resp l p.1 * escape l p.2 /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ) -
      ∫ p : Tree × Tree, escape l p.1 * (1 - escape l p.1) * escape l p.2 /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ := by
    rw [← integral_sub hLid hRid]
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hS_form : (∫ p : Tree × Tree,
      resp l p.1 * (escape l p.2 * (1 - escape l p.2)) /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ) =
      (∫ p : Tree × Tree, resp l p.1 * escape l p.2 /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ) -
      ∫ p : Tree × Tree, resp l p.1 * escape l p.2 ^ 2 /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ := by
    rw [← integral_sub hLid hL2]
    apply integral_congr_ae
    filter_upwards with p
    ring
  rw [hresid_form, hS_form] at hresid
  have hmain :
      (∫ p : Tree × Tree, resp l p.1 * escape l p.2 ^ 2 /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ) =
      ∫ p : Tree × Tree, escape l p.1 * (1 - escape l p.1) * escape l p.2 /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ := by
    linarith
  have hleft : (∫ T, resp l T * Gam2 μ l (escape l T) ∂GW μ) =
      ∫ p : Tree × Tree, resp l p.1 * escape l p.2 ^ 2 /
        DfunProv l (escape l p.1) (escape l p.2) ^ 2 ∂ρ := by
    rw [integral_prod _ hL2]
    simp only [Gam2]
    apply integral_congr_ae
    filter_upwards with T
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with U
    ring
  rw [hleft, hmain, ← RW_eq_root_pair_ward]



private lemma integrable_resp_Gam2_ward (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    Integrable (fun T => resp l T * Gam2 μ l (escape l T)) (GW μ) := by
  have hi := (integrable_pair_resp_ward h hl hlm (fun x => x ^ 2) (by fun_prop)
    (fun _ hx => abs_sq_le_one_ward hx)).integral_prod_left
  apply hi.congr
  filter_upwards with T
  rw [Gam2, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with U
  ring

/-- **Theorem 3.5** (`thm:ward`), lower bound on the cost. -/
theorem ward_lower (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    {θ : ℝ} (hθ : Admissible μ l θ) {ul : Tree → ℝ}
    (hul : AEMeasurable ul (GW μ)) (h0 : ∀ᵐ T ∂GW μ, 0 ≤ ul T ∧ ul T ≤ resp l T) :
    l * Hval μ l + 2 * θ * RW μ l +
      2 * ∫ T, ul T * (Gam μ l (escape l T) - θ * Gam2 μ l (escape l T)) ∂GW μ ≤
        cost μ l := by
  have hl0 : l ∈ Set.Ioo 0 (mean μ) := ⟨by linarith, hlm⟩
  have hRG : Integrable (fun T => resp l T * Gam μ l (escape l T)) (GW μ) :=
    integrable_resp_Gam h hl0
  have hRG2 : Integrable (fun T => resp l T * Gam2 μ l (escape l T)) (GW μ) :=
    integrable_resp_Gam2_ward h hl hlm
  have hRdiff : Integrable (fun T => resp l T *
      (Gam μ l (escape l T) - θ * Gam2 μ l (escape l T))) (GW μ) := by
    apply (hRG.sub (hRG2.const_mul θ)).congr
    filter_upwards with T
    simp only [Pi.sub_apply]
    ring
  have hm : AEMeasurable (fun T => ul T *
      (Gam μ l (escape l T) - θ * Gam2 μ l (escape l T))) (GW μ) :=
    hul.mul ((measurable_Gam_escape_ward l).sub
      ((measurable_Gam2_escape_ward l).const_mul θ)).aemeasurable
  have hU : Integrable (fun T => ul T *
      (Gam μ l (escape l T) - θ * Gam2 μ l (escape l T))) (GW μ) := by
    apply hRdiff.mono' hm.aestronglyMeasurable
    filter_upwards [h0, ae_regTree h] with T hulT hT
    have hD : 0 ≤ Gam μ l (escape l T) - θ * Gam2 μ l (escape l T) :=
      Gam_sub_Gam2_nonneg μ h hl hlm hθ (escape_mem_Icc hl0.1 T)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hulT.1 hD)]
    exact mul_le_mul_of_nonneg_right hulT.2 hD
  have hle : ∀ᵐ T ∂GW μ, ul T *
      (Gam μ l (escape l T) - θ * Gam2 μ l (escape l T)) ≤ resp l T *
        (Gam μ l (escape l T) - θ * Gam2 μ l (escape l T)) := by
    filter_upwards [h0, ae_regTree h] with T hulT hT
    exact mul_le_mul_of_nonneg_right hulT.2
      (Gam_sub_Gam2_nonneg μ h hl hlm hθ (escape_mem_Icc hl0.1 T))
  have hcompare := integral_mono_ae hU hRdiff hle
  have hdecomp : (∫ T, resp l T * Gam μ l (escape l T) ∂GW μ) =
      (∫ T, resp l T * (Gam μ l (escape l T) - θ * Gam2 μ l (escape l T)) ∂GW μ) +
        θ * ∫ T, resp l T * Gam2 μ l (escape l T) ∂GW μ := by
    rw [← integral_const_mul, ← integral_add hRdiff (hRG2.const_mul θ)]
    apply integral_congr_ae
    filter_upwards with T
    ring
  have hbase : θ * (∫ T, resp l T * Gam2 μ l (escape l T) ∂GW μ) +
      (∫ T, ul T * (Gam μ l (escape l T) - θ * Gam2 μ l (escape l T)) ∂GW μ) ≤
        ∫ T, resp l T * Gam μ l (escape l T) ∂GW μ := by
    rw [hdecomp]
    linarith
  rw [cost_eq h hl0, ← ward_identity h hl hlm]
  linarith


end LPPMonotonicityProof.Analytic
