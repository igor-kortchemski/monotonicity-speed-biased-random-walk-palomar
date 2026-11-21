module

public import LPPMonotonicityProof.Analytic.FirstSplit2
public import LPPMonotonicityProof.Analytic.Tools
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# First split: product law and deficit bound

This module proves two parts of Lemma 4.1 (`lem:prefix-terminal`): the law of `Y`
is the image of the product of the law of `L` and the law of `W` under
multiplication, and the deficit `d = 1 - w` satisfies `(1 - e) d ≤ s e` and `d ≤ s`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- Lemma 4.1 (`lem:prefix-terminal`): the prefix length and the split response are
independent at the measure level. -/
theorem Ylaw_eq_prod (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    Ylaw μ l = ((geomY l (pBr μ)).prod ((splitLaw μ).map (Wt l))).map
      (fun p => p.1 * p.2) := by
  letI := splitLaw_prob h
  ext B hB
  let F : ℕ → Tree → ℝ≥0∞ := fun n T =>
    B.indicator (fun _ => 1) (l ^ (-(n : ℤ)) * Wt l T)
  have hFm : Measurable (Function.uncurry F) := by
    apply measurable_from_prod_countable_right
    intro n
    change Measurable (fun T : Tree => B.indicator (fun _ => 1) (l ^ (-(n : ℤ)) * Wt l T))
    exact (measurable_const.indicator hB).comp (measurable_const.mul (measurable_Wt l))
  have hL : ∫⁻ T, B.indicator (fun _ => 1) (Yt l T) ∂GW μ =
      ∑' n : ℕ, ENNReal.ofReal (p1 μ ^ n * pBr μ) * ∫⁻ T, F (n + 1) T ∂splitLaw μ := by
    calc
      _ = ∫⁻ T, F (Gt T) (splitTree T) ∂GW μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_split_degree h] with T hT
        dsimp only [F]
        rw [Yt_eq_prefix hl T hT]
      _ = _ := lintegral_firstSplit h hFm
  have hmul : Measurable (fun p : ℝ × ℝ => p.1 * p.2) := measurable_fst.mul measurable_snd
  have hsect (x : ℝ) : Measurable (fun w : ℝ => B.indicator (fun _ => (1 : ℝ≥0∞)) (x * w)) :=
    (measurable_const.indicator hB).comp (measurable_const.mul measurable_id)
  have hR : ((geomY l (pBr μ)).prod ((splitLaw μ).map (Wt l))).map
      (fun p => p.1 * p.2) B =
      ∑' n : ℕ, ENNReal.ofReal (pBr μ * (1 - pBr μ) ^ n) *
        ∫⁻ T, F (n + 1) T ∂splitLaw μ := by
    rw [Measure.map_apply hmul hB, ← lintegral_indicator_one (hmul hB)]
    change (∫⁻ p : ℝ × ℝ, B.indicator (fun _ => 1) (p.1 * p.2)
      ∂(geomY l (pBr μ)).prod ((splitLaw μ).map (Wt l))) = _
    have hi : Measurable (fun p : ℝ × ℝ => B.indicator (fun _ => (1 : ℝ≥0∞)) (p.1 * p.2)) :=
      (measurable_const.indicator hB).comp hmul
    rw [lintegral_prod _ hi.aemeasurable]
    unfold geomY
    rw [lintegral_sum_measure]
    apply tsum_congr
    intro g
    rw [lintegral_smul_measure, lintegral_dirac]
    apply congrArg (fun c : ℝ≥0∞ => ENNReal.ofReal (pBr μ * (1 - pBr μ) ^ g) * c)
    rw [lintegral_map (hsect _) (measurable_Wt l)]
    apply lintegral_congr
    intro T
    dsimp only [F]
    congr 2
  calc
    Ylaw μ l B = ∫⁻ T, B.indicator (fun _ => 1) (Yt l T) ∂GW μ := by
      rw [Ylaw, Measure.map_apply (measurable_Yt l) hB,
        ← lintegral_indicator_one ((measurable_Yt l) hB)]
      rfl
    _ = ∑' n : ℕ, ENNReal.ofReal (p1 μ ^ n * pBr μ) * ∫⁻ T, F (n + 1) T ∂splitLaw μ := hL
    _ = ∑' n : ℕ, ENNReal.ofReal (pBr μ * (1 - pBr μ) ^ n) *
        ∫⁻ T, F (n + 1) T ∂splitLaw μ := by
      apply tsum_congr
      intro n
      have hpq : p1 μ = 1 - pBr μ := by linarith [p1_add_pBr h]
      rw [hpq, mul_comm (pBr μ)]
    _ = ((geomY l (pBr μ)).prod ((splitLaw μ).map (Wt l))).map
        (fun p => p.1 * p.2) B := hR.symm


private lemma ae_Yt_mem_prov (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : ∀ᵐ T ∂GW μ, 0 < Yt l T ∧ Yt l T < 1 := by
  filter_upwards [ae_escape_pos h (by positivity) hlm] with T hT
  have hden : 0 < l - 1 + escape l T := by linarith
  exact ⟨div_pos hT hden, (div_lt_one hden).2 (by linarith)⟩

private lemma integrable_Yt_prov (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : Integrable (Yt l) (GW μ) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_Yt l).aestronglyMeasurable
  filter_upwards [ae_Yt_mem_prov h hl hlm] with T hT
  rw [Real.norm_eq_abs, abs_of_nonneg hT.1.le]
  exact hT.2.le

private lemma integrable_of_ae_zero_le_le_one {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ} (hf : AEMeasurable f ν)
    (hf0 : ∀ᵐ x ∂ν, 0 ≤ f x) (hf1 : ∀ᵐ x ∂ν, f x ≤ 1) : Integrable f ν := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  filter_upwards [hf0, hf1] with x hx0 hx1
  rw [Real.norm_eq_abs, abs_of_nonneg hx0]
  exact hx1

/-- The one-child form of the reciprocal split response. -/
private noncomputable def splitMobius (c y : ℝ) : ℝ := (1 - y) / (1 + c - c * y)

private lemma splitMobius_den_pos {c y : ℝ} (hc : 0 ≤ c) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 + c - c * y := by
  have hp : 0 ≤ c * (1 - y) := mul_nonneg hc (sub_nonneg.mpr hy.2)
  nlinarith

private lemma splitMobius_mem {c y : ℝ} (hc : 0 ≤ c) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    splitMobius c y ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := splitMobius_den_pos hc hy
  have hp : 0 ≤ c * (1 - y) := mul_nonneg hc (sub_nonneg.mpr hy.2)
  exact ⟨div_nonneg (sub_nonneg.mpr hy.2) hd.le, (div_le_one hd).2 (by ring_nf at hp ⊢; nlinarith [hy.1])⟩

private lemma continuousOn_splitMobius {c : ℝ} (hc : 0 ≤ c) :
    ContinuousOn (splitMobius c) (Set.Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  exact (splitMobius_den_pos hc hx).ne'

/-- The reciprocal-degree Möbius map used in the second Jensen step. -/
private noncomputable def degreeMobius (m z : ℝ) : ℝ := (1 - m) * z / (m + (1 - m) * z)

private lemma degreeMobius_den_pos {m z : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (hz : 0 ≤ z) : 0 < m + (1 - m) * z := by
  have hp : 0 ≤ (1 - m) * z := mul_nonneg (sub_nonneg.mpr hm1) hz
  nlinarith

private lemma degreeMobius_mem {m z : ℝ} (hm : 0 < m) (hm1 : m < 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) : degreeMobius m z ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := degreeMobius_den_pos hm hm1.le hz.1
  have hp : 0 ≤ m * (1 - z) := mul_nonneg hm.le (sub_nonneg.mpr hz.2)
  exact ⟨div_nonneg (mul_nonneg (sub_nonneg.mpr hm1.le) hz.1) hd.le,
    (div_le_one hd).2 (by ring_nf at hp ⊢; nlinarith [hz.1])⟩

private lemma continuousOn_degreeMobius {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    ContinuousOn (degreeMobius m) (Set.Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro z hz
  exact (degreeMobius_den_pos hm hm1 hz.1).ne'

private lemma concaveOn_degreeMobius {m : ℝ} (hm : 0 < m) (hm1 : m < 1) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (degreeMobius m) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hbval : b = 1 - a := by linarith
  subst b
  have hzmem : a • x + (1 - a) • y ∈ Set.Icc (0 : ℝ) 1 :=
    convex_Icc 0 1 hx hy ha (by linarith) (by linarith)
  have hdx := degreeMobius_den_pos hm hm1.le hx.1
  have hdy := degreeMobius_den_pos hm hm1.le hy.1
  have hdz := degreeMobius_den_pos hm hm1.le hzmem.1
  have hdz' : 0 < m + (1 - m) * (a * x + (1 - a) * y) := by
    simpa only [smul_eq_mul] using hdz
  simp only [smul_eq_mul]
  dsimp [degreeMobius]
  rw [le_div_iff₀ hdz']
  field_simp [hdx.ne', hdy.ne']
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ha hb) hm.le)
    (mul_nonneg (sq_nonneg (1 - m)) (sq_nonneg (x - y)))]


private lemma splitMobius_eq_inv_mul_degree {c y : ℝ} (hc : 0 < c)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    splitMobius c y = c⁻¹ * degreeMobius (1 / (1 + c)) (1 - y) := by
  have hcp : 0 < 1 + c := by linarith
  have hd0 := splitMobius_den_pos hc.le hy
  have hd : 1 - y * c + c ≠ 0 := by
    convert hd0.ne' using 1 <;> ring
  dsimp [splitMobius, degreeMobius]
  simp only [inv_eq_one_div]
  field_simp [hc.ne', hcp.ne', hd]
  ring

private lemma concaveOn_splitMobius {c : ℝ} (hc : 0 ≤ c) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (splitMobius c) := by
  by_cases hc0 : c = 0
  · subst c
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy a b ha hb hab
    simp [splitMobius, smul_eq_mul]
    nlinarith [hab]
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hq : 0 < 1 / (1 + c) := by positivity
    have hq1 : 1 / (1 + c) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx' : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hy' : 1 - y ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hz : a * x + b * y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [smul_eq_mul] using convex_Icc 0 1 hx hy ha hb hab
    have hJ := (concaveOn_degreeMobius hq hq1).2 hx' hy' ha hb hab
    have hscale := mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hc)
    simp only [smul_eq_mul] at hscale ⊢
    rw [splitMobius_eq_inv_mul_degree hcpos hx,
      splitMobius_eq_inv_mul_degree hcpos hy]
    calc
      _ = c⁻¹ * (a * degreeMobius (1 / (1 + c)) (1 - x) +
          b * degreeMobius (1 / (1 + c)) (1 - y)) := by ring
      _ ≤ c⁻¹ * degreeMobius (1 / (1 + c)) (a * (1 - x) + b * (1 - y)) := hscale
      _ = splitMobius c (a * x + b * y) := by
        rw [splitMobius_eq_inv_mul_degree hcpos hz]
        congr 2
        nlinarith [hab]


private noncomputable def childOdds (l : ℝ) (T : Tree) : ℝ := Yt l T / (1 - Yt l T)

private noncomputable def childDef (l : ℝ) (c : ℝ) {k : ℕ} (ts : Fin k → Tree) : ℝ :=
  (1 + c + ∑ i, childOdds l (ts i))⁻¹

private lemma childOdds_nonneg_of_mem {l : ℝ} {T : Tree} (hT : Yt l T ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ childOdds l T := by
  unfold childOdds
  by_cases hy : 1 - Yt l T = 0
  · simp [hy]
  · exact div_nonneg hT.1 (sub_nonneg.mpr hT.2)

private lemma measurable_childDef (l c : ℝ) {k : ℕ} :
    Measurable (childDef l c (k := k)) := by
  apply Measurable.inv
  apply Measurable.add (measurable_const.add measurable_const)
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_Yt l).comp (measurable_pi_apply i)).div
    (measurable_const.sub ((measurable_Yt l).comp (measurable_pi_apply i)))

private lemma childDef_mem (l c : ℝ) {k : ℕ} (hc : 0 ≤ c) (ts : Fin k → Tree)
    (hts : ∀ i, Yt l (ts i) ∈ Set.Icc (0 : ℝ) 1) : childDef l c ts ∈ Set.Icc (0 : ℝ) 1 := by
  have hs : 0 ≤ ∑ i, childOdds l (ts i) :=
    Finset.sum_nonneg fun i _ => childOdds_nonneg_of_mem (hts i)
  have hd : 1 ≤ 1 + c + ∑ i, childOdds l (ts i) := by linarith
  exact ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ hd⟩

private lemma ae_Yt_pi (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (k : ℕ) : ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => GW μ),
      ∀ i, 0 < Yt l (ts i) ∧ Yt l (ts i) < 1 := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (μ := fun _ : Fin k => GW μ) i).quasiMeasurePreserving.ae (ae_Yt_mem_prov h hl hlm)

private lemma integrable_childDef (l c : ℝ) {k : ℕ} (hc : 0 ≤ c)
    (h : OffspringHyp μ) (hl : 1 < l) (hlm : l < mean μ) :
    Integrable (childDef l c (k := k)) (Measure.pi (fun _ : Fin k => GW μ)) := by
  have hm := measurable_childDef l c (k := k)
  apply integrable_of_ae_zero_le_le_one hm.aemeasurable
  · filter_upwards [ae_Yt_pi h hl hlm k] with ts hts
    exact (childDef_mem l c hc ts (fun i => ⟨(hts i).1.le, (hts i).2.le⟩)).1
  · filter_upwards [ae_Yt_pi h hl hlm k] with ts hts
    exact (childDef_mem l c hc ts (fun i => ⟨(hts i).1.le, (hts i).2.le⟩)).2

private lemma splitMobius_eq_inv {c s y : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    splitMobius (c + s) y = (1 + c + s + y / (1 - y))⁻¹ := by
  have hd : 0 < 1 - y := sub_pos.mpr hy1
  have hT : 1 + c + s + y / (1 - y) =
      (1 + (c + s) - (c + s) * y) / (1 - y) := by
    field_simp [hd.ne']
    ring
  dsimp [splitMobius]
  rw [hT, inv_div]

private lemma integral_splitMobius_Yt (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ T, splitMobius c (Yt l T) ∂GW μ ≤ splitMobius c (muY μ l) := by
  have hm : Measurable (fun T => splitMobius c (Yt l T)) := by
    exact (measurable_const.sub (measurable_Yt l)).div
      (measurable_const.sub (measurable_const.mul (measurable_Yt l)))
  have hmem : ∀ᵐ T ∂GW μ, splitMobius c (Yt l T) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [ae_Yt_mem_prov h hl hlm] with T hT
    exact splitMobius_mem hc ⟨hT.1.le, hT.2.le⟩
  have hi : Integrable (fun T => splitMobius c (Yt l T)) (GW μ) :=
    integrable_of_ae_zero_le_le_one hm.aemeasurable (hmem.mono fun _ h => h.1)
      (hmem.mono fun _ h => h.2)
  have hJ := (concaveOn_splitMobius hc).le_map_integral (continuousOn_splitMobius hc)
    isClosed_Icc ((ae_Yt_mem_prov h hl hlm).mono fun T hT => ⟨hT.1.le, hT.2.le⟩)
    (integrable_Yt_prov h hl hlm) hi
  simpa only [muY, Function.comp_def] using hJ

private lemma iid_child_bound (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ)
    (hm : 0 < muY μ l) (hm1 : muY μ l < 1) (k : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∫ ts, childDef l c ts ∂Measure.pi (fun _ : Fin k => GW μ) ≤
      (1 + c + (k : ℝ) * (muY μ l / (1 - muY μ l)))⁻¹ := by
  induction k generalizing c with
  | zero => simp [childDef]
  | succ k ih =>
      have hcons : Measurable (fun p : Tree × (Fin k → Tree) => Fin.cons (α := fun _ => Tree) p.1 p.2) := by
        rw [measurable_pi_iff]
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact measurable_fst
        · exact (measurable_pi_apply j).comp measurable_snd
      have hmeas := (measurable_childDef l c).comp hcons
      have hp : ∀ᵐ p ∂(GW μ).prod (Measure.pi (fun _ : Fin k => GW μ)),
          childDef l c (Fin.cons (α := fun _ => Tree) p.1 p.2) ∈ Set.Icc (0 : ℝ) 1 := by
        apply (Measure.ae_prod_iff_ae_ae (hmeas measurableSet_Icc)).2
        filter_upwards [ae_Yt_mem_prov h hl hlm] with head hhead
        filter_upwards [ae_Yt_pi h hl hlm k] with tail htail
        apply childDef_mem l c hc
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ⟨hhead.1.le, hhead.2.le⟩
        · exact ⟨(htail j).1.le, (htail j).2.le⟩
      have hF : Integrable (fun p : Tree × (Fin k → Tree) => childDef l c (Fin.cons (α := fun _ => Tree) p.1 p.2))
          ((GW μ).prod (Measure.pi (fun _ : Fin k => GW μ))) :=
        integrable_of_ae_zero_le_le_one hmeas.aemeasurable (hp.mono fun _ h => h.1)
          (hp.mono fun _ h => h.2)
      have hpi := integral_pi_succ μ (fun head tail => childDef l c (Fin.cons (α := fun _ => Tree) head tail)) hF
      have hodd : 0 ≤ muY μ l / (1 - muY μ l) := div_nonneg hm.le (sub_nonneg.mpr hm1.le)
      calc
        (∫ ts, childDef l c ts ∂Measure.pi (fun _ : Fin (k + 1) => GW μ)) =
            ∫ p : Tree × (Fin k → Tree), childDef l c (Fin.cons (α := fun _ => Tree) p.1 p.2)
              ∂(GW μ).prod (Measure.pi (fun _ : Fin k => GW μ)) := by
          simpa using hpi
        _ = ∫ tail, ∫ head, childDef l c (Fin.cons (α := fun _ => Tree) head tail) ∂GW μ
              ∂Measure.pi (fun _ : Fin k => GW μ) := integral_prod_symm _ hF
        _ ≤ ∫ tail, childDef l (c + muY μ l / (1 - muY μ l)) tail
              ∂Measure.pi (fun _ : Fin k => GW μ) := by
          apply integral_mono_ae hF.integral_prod_right
            (integrable_childDef l (c + muY μ l / (1 - muY μ l)) (add_nonneg hc hodd) h hl hlm)
          filter_upwards [ae_Yt_pi h hl hlm k] with tail htail
          have hs : 0 ≤ ∑ i, childOdds l (tail i) := Finset.sum_nonneg fun i _ =>
            childOdds_nonneg_of_mem ⟨(htail i).1.le, (htail i).2.le⟩
          calc
            _ = ∫ head, splitMobius (c + ∑ i, childOdds l (tail i)) (Yt l head) ∂GW μ := by
              apply integral_congr_ae
              filter_upwards [ae_Yt_mem_prov h hl hlm] with head hhead
              symm
              rw [splitMobius_eq_inv hc hs hhead.1.le hhead.2]
              simp [childDef, childOdds, Fin.sum_univ_succ]
              ring
            _ ≤ splitMobius (c + ∑ i, childOdds l (tail i)) (muY μ l) :=
              integral_splitMobius_Yt h hl hlm (add_nonneg hc hs)
            _ = childDef l (c + muY μ l / (1 - muY μ l)) tail := by
              rw [splitMobius_eq_inv hc hs hm.le hm1]
              simp only [childDef, childOdds]
              congr 1
              ring
        _ ≤ (1 + (c + muY μ l / (1 - muY μ l)) +
            (k : ℝ) * (muY μ l / (1 - muY μ l)))⁻¹ := ih _ (add_nonneg hc hodd)
        _ = (1 + c + ((k + 1 : ℕ) : ℝ) * (muY μ l / (1 - muY μ l)))⁻¹ := by
          push_cast
          congr 1
          ring


private lemma nat_inv_le_one (n : ℕ) : ((n : ℝ))⁻¹ ≤ 1 := by
  cases n with
  | zero => simp
  | succ n => exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_pos n)

private lemma wbar_pos (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    0 < wbar μ l := by
  letI := splitLaw_prob h
  have hi : Integrable (Wt l) (splitLaw μ) := by
    apply integrable_of_ae_zero_le_le_one (measurable_Wt l).aemeasurable
    · filter_upwards [ae_Wt_mem h hl hlm] with T hT; exact hT.1.le
    · filter_upwards [ae_Wt_mem h hl hlm] with T hT; exact hT.2.le
  have hn : 0 ≤ᵐ[splitLaw μ] Wt l := (ae_Wt_mem h hl hlm).mono fun _ hT => hT.1.le
  have hs : Function.support (Wt l) =ᵐ[splitLaw μ] Set.univ := by
    filter_upwards [ae_Wt_mem h hl hlm] with T hT
    simp [Function.support, hT.1.ne']
  simp only [wbar, etaW, pow_one]
  rw [integral_pos_iff_support_of_nonneg_ae hn hi, measure_congr hs]
  simp

private lemma muY_mem (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    0 < muY μ l ∧ muY μ l < 1 := by
  have hs : 0 < sS μ l := div_pos (by linarith) (pBr_pos h)
  have hw : 0 < wbar μ l := wbar_pos h hl hlm
  have hw1 : wbar μ l < 1 := by
    have := dW_pos h hl hlm
    unfold dW at this
    linarith
  have hw0 : 0 ≤ wbar μ l := hw.le
  have hm : muY μ l = wbar μ l / (1 + sS μ l) := muY_eq h hl hlm
  constructor
  · rw [hm]; positivity
  · calc
      muY μ l = wbar μ l / (1 + sS μ l) := hm
      _ ≤ wbar μ l := by
        apply (div_le_iff₀ (by linarith)).2
        nlinarith [mul_nonneg hw0 hs.le]
      _ < 1 := hw1

private noncomputable def splitWeight (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) : ℝ≥0∞ :=
  if 2 ≤ k then μ {k} / μ (Set.Ici 2) else 0

private lemma splitLaw_eq_sum_root (h : OffspringHyp μ) :
    splitLaw μ = Measure.sum fun k : ℕ =>
      splitWeight μ k • (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k) := by
  have hdisj : Pairwise (fun i j => Disjoint {T : Tree | degree T = i} {T | degree T = j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun T hi hj => hij (hi.symm.trans hj)
  calc
    splitLaw μ = (splitLaw μ).restrict Set.univ := by simp
    _ = (splitLaw μ).restrict (⋃ k : ℕ, {T | degree T = k}) := by
      congr 1
      ext T
      simp
    _ = Measure.sum fun k : ℕ => (splitLaw μ).restrict {T | degree T = k} :=
      Measure.restrict_iUnion hdisj fun k => continuous_degree.measurable (measurableSet_singleton k)
    _ = _ := by
      apply congrArg Measure.sum
      funext k
      by_cases hk : 2 ≤ k
      · simpa [splitWeight, hk] using splitLaw_restrict_degree h k hk
      · simp only [splitWeight, hk, ↓reduceIte, zero_smul]
        rw [splitLaw, Measure.restrict_smul]
        have he : {T : Tree | degree T = k} ∩ {T | 2 ≤ degree T} = ∅ := by
          ext T
          simp
          omega
        have hr : ((GW μ).restrict {T | 2 ≤ degree T}).restrict {T | degree T = k} = 0 := by
          apply Measure.restrict_eq_zero.2
          change (GW μ).restrict {T | 2 ≤ degree T} (degree ⁻¹' {k}) = 0
          rw [Measure.restrict_apply (continuous_degree.measurable (measurableSet_singleton k))]
          change GW μ ({T : Tree | degree T = k} ∩ {T | 2 ≤ degree T}) = 0
          rw [he, measure_empty]
        rw [hr, smul_zero]

private lemma integral_splitLaw_root (h : OffspringHyp μ) {G : Tree → ℝ}
    (hG : Integrable G (splitLaw μ)) :
    ∫ T, G T ∂splitLaw μ = ∑' k : ℕ, (splitWeight μ k).toReal *
      ∫ ts, G (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ) := by
  have hlaw := splitLaw_eq_sum_root (μ := μ) h
  have hsumint : Integrable G (Measure.sum fun k : ℕ =>
      splitWeight μ k • (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k)) := hlaw ▸ hG
  calc
    _ = ∫ T, G T ∂Measure.sum (fun k : ℕ =>
        splitWeight μ k • (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k)) := by rw [← hlaw]
    _ = ∑' k : ℕ, ∫ T, G T ∂(splitWeight μ k •
        (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k)) := integral_sum_measure hsumint
    _ = _ := by
      apply tsum_congr
      intro k
      by_cases hk : splitWeight μ k = 0
      · simp [hk]
      let ρ := (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k)
      have hs : AEStronglyMeasurable G (splitWeight μ k • ρ) :=
        hsumint.aestronglyMeasurable.mono_measure
          (show splitWeight μ k • ρ ≤ Measure.sum (fun k : ℕ =>
            splitWeight μ k • (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k)) from
            Measure.le_sum (fun k : ℕ => splitWeight μ k •
              (Measure.pi (fun _ : Fin k => GW μ)).map (nodeFin k)) k)
      have hmap : AEStronglyMeasurable G ρ := by
        exact ⟨hs.mk, hs.stronglyMeasurable_mk,
          by simpa only [Measure.ae_ennreal_smul_measure_eq hk] using hs.ae_eq_mk⟩
      calc
        _ = (splitWeight μ k).toReal * ∫ T, G T ∂ρ := by rw [integral_smul_measure]; rfl
        _ = _ := by
          apply congrArg (fun x : ℝ => (splitWeight μ k).toReal * x)
          exact integral_map (measurable_nodeFin k).aemeasurable hmap

private lemma summable_splitWeight (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Summable fun k => (splitWeight μ k).toReal := by
  have hs : Summable (fun k : ℕ => (μ.restrict (Set.Ici 2)).real {k}) :=
    summable_measure_toReal (fun k => measurableSet_singleton k)
      (by
        intro i j hij
        exact Set.disjoint_left.mpr fun x hi hj => hij ((Set.mem_singleton_iff.mp hi).symm.trans
          (Set.mem_singleton_iff.mp hj)))
  have heq (k : ℕ) : (splitWeight μ k).toReal =
      (μ.restrict (Set.Ici 2)).real {k} / pBr μ := by
    by_cases hk : 2 ≤ k
    · simp [splitWeight, hk, pBr, Measure.real, ENNReal.toReal_div,
        Measure.restrict_apply (measurableSet_singleton k)]
    · simp [splitWeight, hk, Measure.real, Measure.restrict_apply (measurableSet_singleton k)]
  simp_rw [heq]
  exact hs.div_const _

private lemma childSum_nodeFinProv (l : ℝ) (k : ℕ) (ts : Fin k → Tree) :
    childSum l (nodeFin k ts) = ∑ i, escape l (ts i) := by
  unfold childSum
  rw [degree_nodeFin]
  apply Finset.sum_congr rfl
  intro i _
  rw [children_nodeFin]

private lemma escape_eq_mul_childOddsProv {l : ℝ} (hl : 1 < l) (T : Tree)
    (hT : 0 < Yt l T ∧ Yt l T < 1) : escape l T = (l - 1) * childOdds l T := by
  have ha : 0 < l - 1 := by linarith
  have hβ : 0 ≤ escape l T := (escape_mem_Icc (by positivity) T).1
  have hd : 0 < l - 1 + escape l T := by positivity
  have hy : 1 - Yt l T ≠ 0 := by linarith [hT.2]
  unfold childOdds Yt at *
  field_simp [ha.ne', hd.ne', hy]
  ring

private lemma one_sub_Wt_nodeFin (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (k : ℕ) :
    ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => GW μ),
      1 - Wt l (nodeFin k ts) = childDef l 0 ts := by
  filter_upwards [ae_Yt_pi h hl hlm k] with ts hts
  have ha : 0 < l - 1 := by linarith
  have hsum : childSum l (nodeFin k ts) = (l - 1) * ∑ i, childOdds l (ts i) := by
    rw [childSum_nodeFinProv]
    calc
      _ = ∑ i, (l - 1) * childOdds l (ts i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact escape_eq_mul_childOddsProv hl (ts i) (hts i)
      _ = _ := by rw [Finset.mul_sum]
  have hs : 0 ≤ ∑ i, childOdds l (ts i) := Finset.sum_nonneg fun i _ =>
    childOdds_nonneg_of_mem ⟨(hts i).1.le, (hts i).2.le⟩
  have hd : 0 < l - 1 + childSum l (nodeFin k ts) := by rw [hsum]; positivity
  have ht : 0 < 1 + ∑ i, childOdds l (ts i) := by linarith
  dsimp [childDef]
  rw [inv_eq_one_div]
  simp only [add_zero]
  rw [eq_div_iff ht.ne']
  dsimp [Wt]
  rw [hsum]
  field_simp [hd.ne']
  ring

private lemma dW_eq_integral_prov (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) : dW μ l = ∫ T, (1 - Wt l T) ∂splitLaw μ := by
  letI := splitLaw_prob h
  have hW : Integrable (fun T => Wt l T) (splitLaw μ) := by
    apply integrable_of_ae_zero_le_le_one (measurable_Wt l).aemeasurable
    · filter_upwards [ae_Wt_mem h hl hlm] with T hT; exact hT.1.le
    · filter_upwards [ae_Wt_mem h hl hlm] with T hT; exact hT.2.le
  rw [integral_sub (integrable_const (1 : ℝ)) hW]
  simp [dW, wbar, etaW]

private lemma ae_split_degree_prov : ∀ᵐ T ∂splitLaw μ, 2 ≤ degree T := by
  exact (ae_restrict_mem (continuous_degree.measurable measurableSet_Ici)).filter_mono
    (Measure.ae_smul_measure_le _)

private lemma degree_Mobius_jensen (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    ∫ T, degreeMobius (muY μ l) ((degree T : ℝ)⁻¹) ∂splitLaw μ ≤
      degreeMobius (muY μ l) (eJ μ) := by
  letI := splitLaw_prob h
  obtain ⟨hm, hm1⟩ := muY_mem h hl hlm
  have hdeg : Measurable (fun T : Tree => (degree T : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp continuous_degree.measurable
  have hz : ∀ᵐ T ∂splitLaw μ, ((degree T : ℝ))⁻¹ ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards with T
    exact ⟨inv_nonneg.mpr (by positivity), nat_inv_le_one (degree T)⟩
  have hzi : Integrable (fun T => ((degree T : ℝ))⁻¹) (splitLaw μ) := by
    apply integrable_of_ae_zero_le_le_one
      ((measurable_of_countable (fun k : ℕ => ((k : ℝ))⁻¹)).comp
        continuous_degree.measurable).aemeasurable
    · exact hz.mono fun _ h => h.1
    · exact hz.mono fun _ h => h.2
  have hmeas : Measurable (fun T => degreeMobius (muY μ l) ((degree T : ℝ)⁻¹)) :=
    (measurable_const.mul hdeg.inv).div (measurable_const.add (measurable_const.mul hdeg.inv))
  have hgm : ∀ᵐ T ∂splitLaw μ,
      degreeMobius (muY μ l) ((degree T : ℝ)⁻¹) ∈ Set.Icc (0 : ℝ) 1 :=
    hz.mono fun _ h => degreeMobius_mem hm hm1 h
  have hgi := integrable_of_ae_zero_le_le_one hmeas.aemeasurable
    (hgm.mono fun _ h => h.1) (hgm.mono fun _ h => h.2)
  exact (concaveOn_degreeMobius hm hm1).le_map_integral
    (continuousOn_degreeMobius hm hm1.le) isClosed_Icc hz hzi hgi

/-- Lemma 4.1 (`lem:prefix-terminal`): the two deficit bounds, by conditional Jensen in
the children and then Jensen in the reciprocal split degree. -/
theorem dW_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    (1 - eJ μ) * dW μ l ≤ sS μ l * eJ μ ∧ dW μ l ≤ sS μ l := by
  letI := splitLaw_prob h
  obtain ⟨hm, hm1⟩ := muY_mem h hl hlm
  have hdint : Integrable (fun T => 1 - Wt l T) (splitLaw μ) := by
    apply integrable_of_ae_zero_le_le_one ((measurable_const.sub (measurable_Wt l)).aemeasurable)
    · filter_upwards [ae_Wt_mem h hl hlm] with T hT
      change 0 ≤ 1 - Wt l T
      linarith [hT.2]
    · filter_upwards [ae_Wt_mem h hl hlm] with T hT
      change 1 - Wt l T ≤ 1
      linarith [hT.1]
  have hdeg : Measurable (fun T : Tree => (degree T : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp continuous_degree.measurable
  have hgint : Integrable (fun T => degreeMobius (muY μ l) ((degree T : ℝ)⁻¹)) (splitLaw μ) := by
    apply integrable_of_ae_zero_le_le_one
      ((measurable_const.mul hdeg.inv).div
        (measurable_const.add (measurable_const.mul hdeg.inv))).aemeasurable
    · filter_upwards with T
      exact (degreeMobius_mem hm hm1 ⟨by positivity, nat_inv_le_one (degree T)⟩).1
    · filter_upwards with T
      exact (degreeMobius_mem hm hm1 ⟨by positivity, nat_inv_le_one (degree T)⟩).2
  have hcond (k : ℕ) (hk : 2 ≤ k) :
      (∫ ts, (1 - Wt l (nodeFin k ts)) ∂Measure.pi (fun _ : Fin k => GW μ)) ≤
        ∫ ts, degreeMobius (muY μ l) (((degree (nodeFin k ts) : ℕ) : ℝ)⁻¹)
          ∂Measure.pi (fun _ : Fin k => GW μ) := by
    calc
      _ = ∫ ts, childDef l 0 ts ∂Measure.pi (fun _ : Fin k => GW μ) :=
        integral_congr_ae (one_sub_Wt_nodeFin h hl hlm k)
      _ ≤ (1 + 0 + (k : ℝ) * (muY μ l / (1 - muY μ l)))⁻¹ :=
        iid_child_bound h hl hlm hm hm1 k 0 le_rfl
      _ = degreeMobius (muY μ l) ((k : ℝ)⁻¹) := by
        have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
        have hden : 0 < 1 + (k : ℝ) * (muY μ l / (1 - muY μ l)) := by
          have hq : 0 ≤ muY μ l / (1 - muY μ l) := div_nonneg hm.le (sub_nonneg.mpr hm1.le)
          positivity
        have hkd : (k : ℝ) + (1 - muY μ l) ≠ 0 := by positivity
        have hkmd : (k : ℝ) * muY μ l + (1 - muY μ l) ≠ 0 := by positivity
        dsimp [degreeMobius]
        simp only [inv_eq_one_div]
        field_simp [hk0.ne', (sub_pos.mpr hm1).ne', hden.ne', hkd, hkmd]
        ring
      _ = _ := by simp [degree_nodeFin]
  have hD0 (k : ℕ) : 0 ≤ᵐ[Measure.pi (fun _ : Fin k => GW μ)]
      (fun ts => 1 - Wt l (nodeFin k ts)) := by
    filter_upwards [one_sub_Wt_nodeFin h hl hlm k, ae_Yt_pi h hl hlm k] with ts hts hgood
    rw [hts]
    exact (childDef_mem l 0 le_rfl ts (fun i => ⟨(hgood i).1.le, (hgood i).2.le⟩)).1
  have hDle (k : ℕ) : (∫ ts, (1 - Wt l (nodeFin k ts))
      ∂Measure.pi (fun _ : Fin k => GW μ)) ≤ 1 := by
    have hi : Integrable (fun ts => 1 - Wt l (nodeFin k ts))
        (Measure.pi (fun _ : Fin k => GW μ)) :=
      (integrable_childDef l 0 le_rfl h hl hlm).congr (Filter.EventuallyEq.symm (one_sub_Wt_nodeFin h hl hlm k))
    calc
      _ ≤ ∫ _ts, (1 : ℝ) ∂Measure.pi (fun _ : Fin k => GW μ) := by
        apply integral_mono_ae hi (integrable_const (1 : ℝ))
        filter_upwards [one_sub_Wt_nodeFin h hl hlm k, ae_Yt_pi h hl hlm k] with ts hts hgood
        rw [hts]
        exact (childDef_mem l 0 le_rfl ts (fun i => ⟨(hgood i).1.le, (hgood i).2.le⟩)).2
      _ = 1 := by simp
  have hG0 (k : ℕ) : 0 ≤ᵐ[Measure.pi (fun _ : Fin k => GW μ)]
      (fun ts => degreeMobius (muY μ l) (((degree (nodeFin k ts) : ℕ) : ℝ)⁻¹)) := by
    filter_upwards with ts
    exact (degreeMobius_mem hm hm1 ⟨by positivity, nat_inv_le_one (degree (nodeFin k ts))⟩).1
  have hGle (k : ℕ) : (∫ ts, degreeMobius (muY μ l)
      (((degree (nodeFin k ts) : ℕ) : ℝ)⁻¹) ∂Measure.pi (fun _ : Fin k => GW μ)) ≤ 1 := by
    have hi : Integrable (fun ts => degreeMobius (muY μ l)
        (((degree (nodeFin k ts) : ℕ) : ℝ)⁻¹)) (Measure.pi (fun _ : Fin k => GW μ)) := by
      simp only [degree_nodeFin]
      exact integrable_const _
    calc
      _ ≤ ∫ _ts, (1 : ℝ) ∂Measure.pi (fun _ : Fin k => GW μ) := by
        apply integral_mono_ae hi (integrable_const (1 : ℝ))
        filter_upwards with ts
        exact (degreeMobius_mem hm hm1 ⟨by positivity, nat_inv_le_one (degree (nodeFin k ts))⟩).2
      _ = 1 := by simp
  have hsumD : Summable (fun k : ℕ => (splitWeight μ k).toReal *
      ∫ ts, (1 - Wt l (nodeFin k ts)) ∂Measure.pi (fun _ : Fin k => GW μ)) := by
    apply (summable_splitWeight μ).of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (integral_nonneg_of_ae (hD0 k)))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hDle k) ENNReal.toReal_nonneg
  have hsumG : Summable (fun k : ℕ => (splitWeight μ k).toReal *
      ∫ ts, degreeMobius (muY μ l) (((degree (nodeFin k ts) : ℕ) : ℝ)⁻¹)
        ∂Measure.pi (fun _ : Fin k => GW μ)) := by
    apply (summable_splitWeight μ).of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (integral_nonneg_of_ae (hG0 k)))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hGle k) ENNReal.toReal_nonneg
  have hmain : dW μ l ≤ degreeMobius (muY μ l) (eJ μ) := by
    calc
      dW μ l = ∑' k : ℕ, (splitWeight μ k).toReal *
          ∫ ts, (1 - Wt l (nodeFin k ts)) ∂Measure.pi (fun _ : Fin k => GW μ) := by
        rw [dW_eq_integral_prov h hl hlm, integral_splitLaw_root h hdint]
      _ ≤ ∑' k : ℕ, (splitWeight μ k).toReal *
          ∫ ts, degreeMobius (muY μ l) (((degree (nodeFin k ts) : ℕ) : ℝ)⁻¹)
            ∂Measure.pi (fun _ : Fin k => GW μ) := by
        apply Summable.tsum_le_tsum _ hsumD hsumG
        intro k
        by_cases hk : 2 ≤ k
        · exact mul_le_mul_of_nonneg_left (hcond k hk) ENNReal.toReal_nonneg
        · simp [splitWeight, hk]
      _ = ∫ T, degreeMobius (muY μ l) ((degree T : ℝ)⁻¹) ∂splitLaw μ :=
        (integral_splitLaw_root h hgint).symm
      _ ≤ degreeMobius (muY μ l) (eJ μ) := degree_Mobius_jensen h hl hlm
  have he := eJ_mem h
  have hs : 0 < sS μ l := div_pos (by linarith) (pBr_pos h)
  have hw : 0 < 1 - dW μ l := by
    dsimp [dW]
    simpa using wbar_pos h hl hlm
  have hdpos := dW_pos h hl hlm
  have hD : 0 < 1 - dW μ l + (sS μ l + dW μ l) * eJ μ :=
    add_pos_of_pos_of_nonneg hw (mul_nonneg (add_nonneg hs.le hdpos.le) he.1.le)
  have hs1 : 1 + sS μ l ≠ 0 := by linarith
  have hnum : 1 - (1 - dW μ l) / (1 + sS μ l) =
      (sS μ l + dW μ l) / (1 + sS μ l) := by
    field_simp [hs1]
    ring
  have hden : (1 - dW μ l) / (1 + sS μ l) +
      (1 - (1 - dW μ l) / (1 + sS μ l)) * eJ μ =
      (1 - dW μ l + (sS μ l + dW μ l) * eJ μ) / (1 + sS μ l) := by
    rw [hnum]
    field_simp [hs1]
  have hge : degreeMobius (muY μ l) (eJ μ) =
      (sS μ l + dW μ l) * eJ μ / (1 - dW μ l + (sS μ l + dW μ l) * eJ μ) := by
    rw [muY_eq h hl hlm]
    have hwd : wbar μ l = 1 - dW μ l := by unfold dW; ring
    rw [hwd]
    dsimp [degreeMobius]
    rw [hden, hnum]
    field_simp [hs1, hD.ne']
  rw [hge] at hmain
  have hmul := (le_div_iff₀ hD).mp hmain
  have hfactor : dW μ l * (1 - dW μ l + (sS μ l + dW μ l) * eJ μ) -
      (sS μ l + dW μ l) * eJ μ =
      (1 - dW μ l) * ((1 - eJ μ) * dW μ l - sS μ l * eJ μ) := by ring
  have hfirst : (1 - eJ μ) * dW μ l ≤ sS μ l * eJ μ := by
    have hz : (1 - dW μ l) * ((1 - eJ μ) * dW μ l - sS μ l * eJ μ) ≤ 0 := by
      nlinarith [hmul, hfactor]
    have hx := nonpos_of_mul_nonpos_right hz hw
    linarith
  refine ⟨hfirst, ?_⟩
  have he1 : eJ μ ≤ 1 - eJ μ := by linarith [he.2]
  have hsle : sS μ l * eJ μ ≤ sS μ l * (1 - eJ μ) :=
    mul_le_mul_of_nonneg_left he1 hs.le
  have hz : (1 - eJ μ) * (dW μ l - sS μ l) ≤ 0 := by nlinarith
  have hx := nonpos_of_mul_nonpos_right hz (show 0 < 1 - eJ μ by linarith [he.2])
  linarith

end LPPMonotonicityProof.Analytic
