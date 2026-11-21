module

public import LPPMonotonicityProof.Analytic.Interface
public import LPPMonotonicityProof.RTL.LocallyFinite.GenerationLaw
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Mean escape inequalities

This module proves the mean-escape bounds `b ≤ E[ν b/(λ + ν b)] ≤ m b/(λ + m b)`, with
`b = E β`, and
`E β ≤ (m - λ)/m`, obtained by conditional Jensen in the escape recursion in the proof
of Remark 2.3 (`rem:critical-bias`) and used again in the proof of Corollary 4.6
(`cor:small-terminal`). The two root-decomposition lemmas whose names end in `Prov`
are the real-valued (Bochner-integral) form of the decomposition of the Bienaymé law
along the root degree.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem integrable_natCastProv (h : OffspringHyp μ) :
    Integrable (fun k : ℕ => (k : ℝ)) μ := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun k => Nat.cast_nonneg k)).2
  simpa only [ENNReal.ofReal_natCast] using h.mean_lt_top

private theorem integral_natCast_eq_meanProv :
    (∫ k : ℕ, (k : ℝ) ∂μ) = mean μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun k => Nat.cast_nonneg k)
    (measurable_of_countable _).aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast, mean]

private theorem integrable_escapeProv {l : ℝ} (hl : 0 < l) :
    Integrable (escape l) (GW μ) := by
  apply Integrable.of_bound (measurable_escape l).aestronglyMeasurable 1
  filter_upwards with T
  rw [Real.norm_eq_abs, abs_of_nonneg (escape_mem_Icc hl T).1]
  exact (escape_mem_Icc hl T).2

private theorem integral_pi_evalProv {n : ℕ} (i : Fin n) (g : Tree → ℝ)
    (hg : AEStronglyMeasurable g (GW μ)) :
    (∫ ts, g (ts i) ∂Measure.pi (fun _ : Fin n => GW μ)) = ∫ T, g T ∂GW μ := by
  have hp := measurePreserving_eval (fun _ : Fin n => GW μ) i
  have hg' : AEStronglyMeasurable g ((Measure.pi (fun _ : Fin n => GW μ)).map (fun ts => ts i)) := by
    rwa [hp.map_eq]
  calc
    _ = ∫ T, g T ∂(Measure.pi (fun _ : Fin n => GW μ)).map (fun ts => ts i) :=
      (integral_map (μ := Measure.pi (fun _ : Fin n => GW μ))
        (φ := fun ts : Fin n → Tree => ts i) (f := g)
        (measurable_pi_apply i).aemeasurable hg').symm
    _ = _ := by rw [hp.map_eq]

/-- Root decomposition, real-valued form: the integral over the event that the root has
`k` children. -/
theorem integral_children_of_degreeProv (k : ℕ) {g : (Fin k → Tree) → ℝ}
    (hg : Measurable g) :
    ∫ T in {T | degree T = k}, g (fun i => child T (i.val + 1)) ∂GW μ =
      μ.real {k} * ∫ ts, g ts ∂Measure.pi (fun _ : Fin k => GW μ) := by
  have hd : GW μ {T | degree T = k} = μ {k} := by
    have h := congrArg (fun ν : Measure ℕ => ν {k}) (bienaymeLaw_map_degree μ)
    rwa [Measure.map_apply continuous_degree.measurable (measurableSet_singleton k)] at h
  by_cases hk : μ {k} = 0
  · rw [Measure.restrict_eq_zero.mpr (hd.trans hk), integral_zero_measure]
    simp [Measure.real, hk]
  · have hr : (GW μ).restrict {T | degree T = k} =
        μ {k} • (GW μ)[|{T | degree T = k}] := by
      rw [ProbabilityTheory.cond, hd, smul_smul,
        ENNReal.mul_inv_cancel hk (measure_ne_top _ _), one_smul]
    rw [hr, integral_smul_measure]
    rw [← (isBienayme_bienaymeLaw μ).2 k (by rwa [hd])]
    rw [integral_map (Measurable.of_eval fun i => (continuous_child (i.val + 1)).measurable).aemeasurable
      hg.aestronglyMeasurable]
    rfl

/-- Root decomposition, real-valued form: a real integral decomposed along root degrees. -/
theorem integral_bienayme_eq_tsum_degreeProv {f : Tree → ℝ} (hf : Integrable f (GW μ)) :
    (∫ T, f T ∂GW μ) = ∑' k : ℕ, ∫ T in {T | degree T = k}, f T ∂GW μ := by
  change (∫ T, f T ∂GW μ) = ∑' k : ℕ, ∫ T in degree ⁻¹' {k}, f T ∂GW μ
  have hu : ⋃ k : ℕ, (degree : Tree → ℕ) ⁻¹' {k} = Set.univ := by ext T; simp
  have hh := integral_iUnion (f := f) (μ := GW μ)
    (fun k => continuous_degree.measurable (measurableSet_singleton k))
    (fun i j hij => Set.disjoint_left.mpr fun T hi hj => hij (hi.symm.trans hj))
    (by rw [IntegrableOn, hu, Measure.restrict_univ]; exact hf)
  simpa only [hu, Measure.restrict_univ] using hh

private theorem ratio_concaveOnProv {l : ℝ} (hl : 0 < l) :
    ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x / (l + x)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hbval : b = 1 - a := by linarith
  subst b
  simp only [smul_eq_mul]
  have hlx : 0 < l + x := add_pos_of_pos_of_nonneg hl hx
  have hly : 0 < l + y := add_pos_of_pos_of_nonneg hl hy
  have hlc : 0 < l + (a * x + (1 - a) * y) :=
    add_pos_of_pos_of_nonneg hl (add_nonneg (mul_nonneg ha hx) (mul_nonneg (by linarith) hy))
  have hid : (a * x + (1 - a) * y) / (l + (a * x + (1 - a) * y)) -
      (a * (x / (l + x)) + (1 - a) * (y / (l + y))) =
      a * (1 - a) * l * (x - y) ^ 2 /
        ((l + x) * (l + y) * (l + (a * x + (1 - a) * y))) := by
    field_simp [hlx.ne', hly.ne', hlc.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity

private theorem ratio_continuousOnProv {l : ℝ} (hl : 0 < l) :
    ContinuousOn (fun x : ℝ => x / (l + x)) (Set.Ici 0) := by
  apply ContinuousOn.div continuousOn_id (continuousOn_const.add continuousOn_id)
  intro x hx
  exact (add_pos_of_pos_of_nonneg hl hx).ne'

private theorem ratio_mem_IciProv {l : ℝ} (hl : 0 < l) {x : ℝ} (hx : 0 ≤ x) :
    x / (l + x) ∈ Set.Ici 0 := div_nonneg hx (add_pos_of_pos_of_nonneg hl hx).le

private theorem ratio_le_oneProv {l : ℝ} (hl : 0 < l) {x : ℝ} (hx : 0 ≤ x) :
    x / (l + x) ≤ 1 := by
  apply (div_le_one (add_pos_of_pos_of_nonneg hl hx)).2
  exact le_add_of_nonneg_left hl.le

private theorem integrable_pi_sum_escapeProv {l : ℝ} (hl : 0 < l) (k : ℕ) :
    Integrable (fun ts : Fin k → Tree => ∑ i, escape l (ts i))
      (Measure.pi fun _ : Fin k => GW μ) := by
  apply integrable_finsetSum
  intro i _
  exact (measurePreserving_eval (fun _ : Fin k => GW μ) i).integrable_comp_of_integrable
    (integrable_escapeProv hl)

private theorem integral_pi_sum_escapeProv {l : ℝ} (hl : 0 < l) (k : ℕ) :
    (∫ ts : Fin k → Tree, (∑ i, escape l (ts i)) ∂Measure.pi (fun _ : Fin k => GW μ)) =
      k * ∫ T, escape l T ∂GW μ := by
  rw [integral_finsetSum]
  · calc
      _ = ∑ _i : Fin k, ∫ T, escape l T ∂GW μ := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_pi_evalProv i (escape l) (integrable_escapeProv hl).1
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  · intro i _
    exact (measurePreserving_eval (fun _ : Fin k => GW μ) i).integrable_comp_of_integrable
      (integrable_escapeProv hl)

private theorem conditional_ratio_boundProv {l : ℝ} (hl : 0 < l) (k : ℕ) :
    (∫ ts : Fin k → Tree,
      (∑ i, escape l (ts i)) / (l + ∑ i, escape l (ts i))
        ∂Measure.pi (fun _ : Fin k => GW μ)) ≤
      (k * ∫ T, escape l T ∂GW μ) /
        (l + k * ∫ T, escape l T ∂GW μ) := by
  let S : (Fin k → Tree) → ℝ := fun ts => ∑ i, escape l (ts i)
  have hSnonneg : ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => GW μ), S ts ∈ Set.Ici 0 :=
    ae_of_all _ fun ts => Finset.sum_nonneg fun i _ => (escape_mem_Icc hl _).1
  have hSint : Integrable S (Measure.pi fun _ : Fin k => GW μ) := integrable_pi_sum_escapeProv hl k
  have hratio : Integrable ((fun x : ℝ => x / (l + x)) ∘ S)
      (Measure.pi fun _ : Fin k => GW μ) := by
    apply Integrable.of_bound
      (((Finset.univ.measurable_sum fun i _ => (measurable_escape l).comp (measurable_pi_apply i)).div
        (measurable_const.add (Finset.univ.measurable_sum fun i _ =>
          (measurable_escape l).comp (measurable_pi_apply i)))).aestronglyMeasurable) 1
    filter_upwards with ts
    change |(∑ i, escape l (ts i)) / (l + ∑ i, escape l (ts i))| ≤ 1
    rw [abs_of_nonneg (ratio_mem_IciProv hl
      (Finset.sum_nonneg fun i _ => (escape_mem_Icc hl _).1))]
    exact ratio_le_oneProv hl (Finset.sum_nonneg fun i _ => (escape_mem_Icc hl _).1)
  have hj := (ratio_concaveOnProv hl).le_map_integral (ratio_continuousOnProv hl)
    isClosed_Ici hSnonneg hSint hratio
  rw [integral_pi_sum_escapeProv hl] at hj
  exact hj

private theorem integrable_ratio_natProv {l b : ℝ} (hl : 0 < l) (hb : 0 ≤ b) :
    Integrable (fun k : ℕ => (k * b) / (l + k * b)) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  filter_upwards with k
  rw [Real.norm_eq_abs, abs_of_nonneg (ratio_mem_IciProv hl (mul_nonneg (Nat.cast_nonneg k) hb))]
  exact ratio_le_oneProv hl (mul_nonneg (Nat.cast_nonneg k) hb)

private theorem probability_masses_summableProv : Summable (fun k : ℕ => μ.real {k}) := by
  have htop : (∑' k : ℕ, μ {k}) ≠ ∞ := by
    rw [← measure_iUnion]
    · simp
    · intro i j hij
      exact Set.disjoint_left.mpr fun x hi hj => hij (hi.symm.trans hj)
    · exact fun k => measurableSet_singleton k
  exact ENNReal.summable_toReal htop

/-- **Mean-escape bounds.** Positivity and the two Jensen bounds for the mean escape, with their
resulting upper bound `(m-l)/m`. -/
theorem mean_escape_bounds (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ) :
    let b := ∫ T, escape l T ∂GW μ
    0 < b ∧ b ≤ ∫ k, (k * b) / (l + k * b) ∂μ ∧
    (∫ k, (k * b) / (l + k * b) ∂μ) ≤ mean μ * b / (l + mean μ * b) ∧
      b ≤ (mean μ - l) / mean μ := by
  dsimp only
  let b : ℝ := ∫ T, escape l T ∂GW μ
  have hbint : Integrable (escape l) (GW μ) := integrable_escapeProv hl
  have hbnonneg : 0 ≤ b := integral_nonneg_of_ae (ae_of_all _ fun T => (escape_mem_Icc hl T).1)
  have hbpos : 0 < b := by
    by_contra hbnot
    have hb0 : b = 0 := le_antisymm (le_of_not_gt hbnot) hbnonneg
    have hzero : escape l =ᵐ[GW μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun T => (escape_mem_Icc hl T).1) hbint).mp hb0
    have hfalse : ∀ᵐ T ∂GW μ, False := by
      filter_upwards [ae_escape_pos h hl hlm, hzero] with T hT hTz
      exact hT.ne' hTz
    exact Measure.measure_univ_ne_zero.mpr (NeZero.ne (GW μ)) (by
      have hm : GW μ = 0 := by simpa using hfalse
      rw [hm]
      simp)
  have hcond (k : ℕ) :
      (∫ T in {T | degree T = k}, escape l T ∂GW μ) ≤
        μ.real {k} * ((k * b) / (l + k * b)) := by
    have he : (∫ T in {T | degree T = k}, escape l T ∂GW μ) =
        μ.real {k} * ∫ ts : Fin k → Tree,
          (∑ i, escape l (ts i)) / (l + ∑ i, escape l (ts i))
            ∂Measure.pi (fun _ : Fin k => GW μ) := by
      rw [← integral_children_of_degreeProv (μ := μ) k]
      · apply setIntegral_congr_fun (continuous_degree.measurable (measurableSet_singleton k))
        intro T hT
        change degree T = k at hT
        subst k
        rw [escape_eq hl T]
        rfl
      · exact (Finset.univ.measurable_sum fun i _ => (measurable_escape l).comp (measurable_pi_apply i)).div
          (measurable_const.add (Finset.univ.measurable_sum fun i _ =>
            (measurable_escape l).comp (measurable_pi_apply i)))
    rw [he]
    exact mul_le_mul_of_nonneg_left (conditional_ratio_boundProv hl k) measureReal_nonneg
  have hleftHas : HasSum (fun k : ℕ => ∫ T in {T | degree T = k}, escape l T ∂GW μ) b := by
    change HasSum (fun k : ℕ => ∫ T in degree ⁻¹' {k}, escape l T ∂GW μ) b
    have hu : ⋃ k : ℕ, (degree : Tree → ℕ) ⁻¹' {k} = Set.univ := by ext T; simp
    have hh := hasSum_integral_iUnion (f := escape l) (μ := GW μ)
      (fun k => continuous_degree.measurable (measurableSet_singleton k))
      (fun i j hij => Set.disjoint_left.mpr fun T hi hj => hij (hi.symm.trans hj))
      (by rw [IntegrableOn, hu, Measure.restrict_univ]; exact hbint)
    simpa only [hu, Measure.restrict_univ, b] using hh
  have hrightHas : HasSum (fun k : ℕ => μ.real {k} * ((k * b) / (l + k * b)))
      (∫ k, (k * b) / (l + k * b) ∂μ) := by
    have hsum : Summable (fun k : ℕ => μ.real {k} * ((k * b) / (l + k * b))) := by
      apply Summable.of_nonneg_of_le
        (fun k => mul_nonneg measureReal_nonneg (ratio_mem_IciProv hl (mul_nonneg (Nat.cast_nonneg k) hbnonneg)))
        (fun k => mul_le_of_le_one_right measureReal_nonneg (ratio_le_oneProv hl
          (mul_nonneg (Nat.cast_nonneg k) hbnonneg))) probability_masses_summableProv
    have heq := integral_countable (μ := μ) (integrable_ratio_natProv (μ := μ) hl hbnonneg)
    simp only [smul_eq_mul] at heq
    rw [heq]
    exact hsum.hasSum
  have hfirst : b ≤ ∫ k, (k * b) / (l + k * b) ∂μ := by
    calc
      b = ∑' k : ℕ, ∫ T in {T | degree T = k}, escape l T ∂GW μ := hleftHas.tsum_eq.symm
      _ ≤ ∑' k : ℕ, μ.real {k} * ((k * b) / (l + k * b)) :=
        hleftHas.summable.tsum_le_tsum hcond hrightHas.summable
      _ = _ := hrightHas.tsum_eq
  have hnat := integrable_natCastProv h
  have hinnerInt : Integrable (fun k : ℕ => (k : ℝ) * b) μ := hnat.mul_const b
  have houterInt : Integrable ((fun x : ℝ => x / (l + x)) ∘ (fun k : ℕ => (k : ℝ) * b)) μ := by
    simpa only [Function.comp_def, Nat.cast_mul] using integrable_ratio_natProv (μ := μ) hl hbnonneg
  have hsecond : (∫ k, (k * b) / (l + k * b) ∂μ) ≤ mean μ * b / (l + mean μ * b) := by
    have hj := (ratio_concaveOnProv hl).le_map_integral (ratio_continuousOnProv hl)
      isClosed_Ici (ae_of_all _ fun k => mul_nonneg (Nat.cast_nonneg k) hbnonneg)
      hinnerInt houterInt
    rw [integral_mul_const, integral_natCast_eq_meanProv] at hj
    simpa only [Function.comp_def, Nat.cast_mul] using hj
  have hmpos : 0 < mean μ := by
    have hm := h.one_lt_mean
    have hreal : 1 < mean μ :=
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top h.mean_lt_top.ne).2 hm
    exact zero_lt_one.trans hreal
  have hfinal : b ≤ (mean μ - l) / mean μ := by
    have hden : 0 < l + mean μ * b := add_pos_of_pos_of_nonneg hl (mul_nonneg hmpos.le hbnonneg)
    have hbsecond := hfirst.trans hsecond
    have hmul := (le_div_iff₀ hden).mp hbsecond
    have hprod : b * (l + mean μ * b) ≤ b * mean μ := by nlinarith [hmul]
    have hcancel : l + mean μ * b ≤ mean μ := le_of_mul_le_mul_right (by nlinarith [hprod] : (l + mean μ * b) * b ≤ mean μ * b) hbpos
    apply (le_div_iff₀ hmpos).2
    nlinarith
  exact ⟨hbpos, hfirst, hsecond, hfinal⟩

end LPPMonotonicityProof.Analytic
