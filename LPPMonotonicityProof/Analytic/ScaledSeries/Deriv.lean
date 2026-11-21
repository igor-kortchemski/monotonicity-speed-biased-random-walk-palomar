module

public import LPPMonotonicityProof.Analytic.ScaledSeries.Identities
public import LPPMonotonicityProof.Analytic.RegularityExport
public import LPPMonotonicityProof.Analytic.Interface2
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation of the split moments `ηₙ`

`∂_l W = ((l-1)Ṡ - S)/(l-1+S)²` on a regular split tree, with
`|Ṡ| ≤ Σᵢ K(childᵢ)` (Proposition 2.5 on the children). The children envelope is
integrable under `splitLaw` because `E Σ_{i ≤ ν} K(childᵢ) = E ν · E K` (root
decomposition of the Bienaymé law). Dominated differentiation then gives
`hasDerivAt_etaW`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-! ### The children envelope -/

/-- Sum over the root's children of the response envelopes on `[a, b]`. -/
noncomputable def childEnv (a b : ℝ) (T : Tree) : ℝ :=
  ∑ i : Fin (degree T), (envelope a b (child T (i.val + 1))).toReal

/-- The extended-valued children envelope. -/
noncomputable def childEnvE (a b : ℝ) (T : Tree) : ℝ≥0∞ :=
  ∑ i : Fin (degree T), envelope a b (child T (i.val + 1))

theorem childEnv_nonneg (a b : ℝ) (T : Tree) : 0 ≤ childEnv a b T :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

private theorem measurable_envChild (a b : ℝ) (j : ℕ) :
    Measurable (fun T : Tree => envelope a b (child T (j + 1))) :=
  (measurable_envelope a b).comp (continuous_child (j + 1)).measurable

theorem measurable_childEnvE (a b : ℝ) : Measurable (childEnvE a b) := by
  have h : Measurable (fun p : ℕ × Tree =>
      ∑ j ∈ Finset.range p.1, envelope a b (child p.2 (j + 1))) :=
    measurable_from_prod_countable_right fun k =>
      (Finset.range k).measurable_sum fun j _ => measurable_envChild a b j
  convert h.comp (continuous_degree.measurable.prodMk measurable_id) using 1
  ext T
  exact Fin.sum_univ_eq_sum_range (fun j => envelope a b (child T (j + 1))) (degree T)

theorem measurable_childEnv (a b : ℝ) : Measurable (childEnv a b) := by
  have h : Measurable (fun p : ℕ × Tree =>
      ∑ j ∈ Finset.range p.1, (envelope a b (child p.2 (j + 1))).toReal) :=
    measurable_from_prod_countable_right fun k =>
      (Finset.range k).measurable_sum fun j _ => (measurable_envChild a b j).ennreal_toReal
  convert h.comp (continuous_degree.measurable.prodMk measurable_id) using 1
  ext T
  exact Fin.sum_univ_eq_sum_range (fun j => (envelope a b (child T (j + 1))).toReal) (degree T)

/-- `E Σ_{i ≤ ν} K(childᵢ) = E ν · E K`. -/
theorem lintegral_childEnvE (a b : ℝ) :
    ∫⁻ T, childEnvE a b T ∂GW μ = (∫⁻ k, (k : ℝ≥0∞) ∂μ) * ∫⁻ T, envelope a b T ∂GW μ := by
  rw [lintegral_GW_eq_tsum _ (measurable_childEnvE a b)]
  have hk (k : ℕ) : ∫⁻ ts, childEnvE a b (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ) =
      k * ∫⁻ T, envelope a b T ∂GW μ := by
    have hnode (ts : Fin k → Tree) :
        childEnvE a b (nodeFin k ts) = ∑ i : Fin k, envelope a b (ts i) := by
      unfold childEnvE
      rw [degree_nodeFin]
      apply Finset.sum_congr rfl
      intro i _
      rw [children_nodeFin]
    simp_rw [hnode]
    rw [lintegral_finsetSum (f := fun i (ts : Fin k → Tree) => envelope a b (ts i)) _
      (fun i _ => (measurable_envelope a b).comp (measurable_pi_apply i))]
    have he (i : Fin k) : ∫⁻ ts, envelope a b (ts i) ∂Measure.pi (fun _ : Fin k => GW μ) =
        ∫⁻ T, envelope a b T ∂GW μ :=
      (measurePreserving_eval (fun _ : Fin k => GW μ) i).lintegral_comp (measurable_envelope a b)
    simp_rw [he]
    simp [Finset.sum_const, nsmul_eq_mul]
  simp_rw [hk]
  rw [lintegral_countable' (μ := μ) (fun k : ℕ => (k : ℝ≥0∞)), ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro k
  ring

theorem integrable_childEnv_GW (h : OffspringHyp μ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < mean μ) : Integrable (childEnv a b) (GW μ) := by
  have hm := measurable_childEnv a b
  rw [← lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun T => childEnv_nonneg a b T)]
  apply ne_of_lt
  calc ∫⁻ T, ENNReal.ofReal (childEnv a b T) ∂GW μ ≤ ∫⁻ T, childEnvE a b T ∂GW μ := by
        apply lintegral_mono
        intro T
        show ENNReal.ofReal (childEnv a b T) ≤ childEnvE a b T
        unfold childEnv childEnvE
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
        exact Finset.sum_le_sum fun i _ => ENNReal.ofReal_toReal_le
    _ = (∫⁻ k, (k : ℝ≥0∞) ∂μ) * ∫⁻ T, envelope a b T ∂GW μ := lintegral_childEnvE a b
    _ < ⊤ := ENNReal.mul_lt_top h.mean_lt_top (lintegral_envelope_lt_top h ha hab hb)

theorem integrable_childEnv_split (h : OffspringHyp μ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < mean μ) : Integrable (childEnv a b) (splitLaw μ) := by
  have hbranch : GW μ {T | 2 ≤ degree T} = μ (Set.Ici 2) := by
    have hmap := congrArg (fun ν : Measure ℕ => ν (Set.Ici 2)) (bienaymeLaw_map_degree μ)
    rwa [Measure.map_apply continuous_degree.measurable measurableSet_Ici] at hmap
  have hne : GW μ {T | 2 ≤ degree T} ≠ 0 := by
    rw [hbranch]
    intro hz
    have hp := pBr_pos h
    rw [pBr, hz, ENNReal.toReal_zero] at hp
    exact lt_irrefl 0 hp
  exact (integrable_childEnv_GW h ha hab hb).restrict.smul_measure (ENNReal.inv_ne_top.2 hne)

/-! ### Pathwise derivative of `W` -/

theorem Wt_mem_Icc' {l : ℝ} (hl : 1 < l) (T : Tree) : 0 ≤ Wt l T ∧ Wt l T ≤ 1 := by
  have hS : 0 ≤ childSum l T :=
    Finset.sum_nonneg fun i _ => (escape_mem_Icc (by linarith) _).1
  have hD : 0 < l - 1 + childSum l T := by linarith
  exact ⟨div_nonneg hS hD.le, (div_le_one hD).2 (by linarith)⟩

/-- The derivative of the child sum on a regular tree. -/
noncomputable def childSumDeriv (T : Tree) (x : ℝ) : ℝ :=
  ∑ i : Fin (degree T), deriv (fun l => escape l (child T (i.val + 1))) x

theorem hasDerivAt_childSum {T : Tree} (hT : RegTree μ T) {x : ℝ} (hx0 : 0 < x)
    (hxm : x < mean μ) : HasDerivAt (fun l => childSum l T) (childSumDeriv T x) x := by
  have hxI : x ∈ Set.Ioo 0 (mean μ) := ⟨hx0, hxm⟩
  apply HasDerivAt.fun_sum
  intro i _
  exact (((escape_contDiffOn (regTree_child hT i)).differentiableOn (by norm_num) x
    hxI).differentiableAt (isOpen_Ioo.mem_nhds hxI)).hasDerivAt

/-- `∂_l W = (Ṡ(l-1+S) - S(1+Ṡ))/(l-1+S)²` on a regular tree. -/
theorem hasDerivAt_Wt {T : Tree} (hT : RegTree μ T) {x : ℝ} (hx1 : 1 < x) (hxm : x < mean μ) :
    HasDerivAt (fun l => Wt l T)
      ((childSumDeriv T x * (x - 1 + childSum x T) - childSum x T * (1 + childSumDeriv T x)) /
        (x - 1 + childSum x T) ^ 2) x := by
  have hS := hasDerivAt_childSum hT (by linarith) hxm
  have hS0 : 0 ≤ childSum x T :=
    Finset.sum_nonneg fun i _ => (escape_mem_Icc (by linarith) _).1
  have hden : x - 1 + childSum x T ≠ 0 := ne_of_gt (by linarith)
  exact hS.fun_div (((hasDerivAt_id' (x := x)).sub_const 1).fun_add hS) hden

/-- Proposition 2.5 on the children: `|Ṡ| ≤ Σᵢ K(childᵢ)` on `[a, b]`. -/
theorem abs_childSumDeriv_le {T : Tree} (hT : RegTree μ T) {a b x : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < mean μ) (hx : x ∈ Set.Icc a b) :
    |childSumDeriv T x| ≤ childEnv a b T := by
  unfold childSumDeriv childEnv
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  obtain ⟨_, h0, h1⟩ := neg_deriv_escape_le (regTree_child hT i) ha hab hb hx
  have hβ := escape_mem_Icc (show 0 < x by linarith [hx.1]) (child T (i.val + 1))
  rw [abs_of_nonpos (by linarith)]
  calc -deriv (fun l => escape l (child T (i.val + 1))) x
      ≤ (envelope a b (child T (i.val + 1))).toReal * escape x (child T (i.val + 1)) := h1
    _ ≤ (envelope a b (child T (i.val + 1))).toReal * 1 :=
        mul_le_mul_of_nonneg_left hβ.2 ENNReal.toReal_nonneg
    _ = _ := mul_one _

/-- `|∂_l W| ≤ (Σᵢ K(childᵢ) + 1)/(a - 1)` on `[a, b] ⊂ (1, m)`. -/
theorem abs_deriv_Wt_le {T : Tree} (hT : RegTree μ T) {a b x : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hb : b < mean μ) (hx : x ∈ Set.Icc a b) :
    |deriv (fun l => Wt l T) x| ≤ (childEnv a b T + 1) / (a - 1) := by
  have hx1 : 1 < x := by linarith [hx.1]
  have hxm : x < mean μ := by linarith [hx.2]
  rw [(hasDerivAt_Wt hT hx1 hxm).deriv]
  have hS' := abs_childSumDeriv_le hT (by linarith) hab hb hx
  have hS0 : 0 ≤ childSum x T :=
    Finset.sum_nonneg fun i _ => (escape_mem_Icc (by linarith) _).1
  have hc : 0 < x - 1 := by linarith
  have hD : 0 < x - 1 + childSum x T := by linarith
  have hnum : childSumDeriv T x * (x - 1 + childSum x T) - childSum x T * (1 + childSumDeriv T x) =
      (x - 1) * childSumDeriv T x - childSum x T := by ring
  rw [hnum, abs_div, abs_of_pos (pow_pos hD 2)]
  have h1 : |(x - 1) * childSumDeriv T x - childSum x T| ≤
      (x - 1) * |childSumDeriv T x| + childSum x T := by
    calc |(x - 1) * childSumDeriv T x - childSum x T|
        ≤ |(x - 1) * childSumDeriv T x| + |childSum x T| := abs_sub _ _
      _ = (x - 1) * |childSumDeriv T x| + childSum x T := by
          rw [abs_mul, abs_of_pos hc, abs_of_nonneg hS0]
  have hA0 := abs_nonneg (childSumDeriv T x)
  have key : |(x - 1) * childSumDeriv T x - childSum x T| / (x - 1 + childSum x T) ^ 2 ≤
      (|childSumDeriv T x| + 1) / (x - 1) := by
    rw [div_le_div_iff₀ (pow_pos hD 2) hc]
    nlinarith [mul_le_mul_of_nonneg_right h1 hc.le, mul_nonneg (mul_nonneg hA0 hc.le) hS0,
      mul_nonneg hA0 (sq_nonneg (childSum x T)), sq_nonneg (x - 1), mul_nonneg hS0 hc.le,
      sq_nonneg (childSum x T)]
  have hE0 := childEnv_nonneg a b T
  calc _ ≤ (|childSumDeriv T x| + 1) / (x - 1) := key
    _ ≤ (childEnv a b T + 1) / (x - 1) := div_le_div_of_nonneg_right (by linarith) hc.le
    _ ≤ (childEnv a b T + 1) / (a - 1) :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith [hx.1])

/-- The pathwise response derivative is a.e. measurable under `splitLaw`. -/
theorem aemeasurable_deriv_Wt (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    AEMeasurable (fun T => deriv (fun l' => Wt l' T) l) (splitLaw μ) := by
  let t : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ))⁻¹
  have ht0 : Tendsto t atTop (𝓝 0) := by
    simpa only [t, Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht0, Filter.Eventually.of_forall fun n => ?_⟩
    change (((n + 1 : ℕ) : ℝ))⁻¹ ≠ 0
    exact inv_ne_zero (by positivity)
  let F : ℕ → Tree → ℝ := fun n T => slope (fun x => Wt x T) l (l + t n)
  have hmeas (n : ℕ) : AEMeasurable (F n) (splitLaw μ) := by
    simp only [F, slope_def_module, add_sub_cancel_left]
    exact ((measurable_Wt (l + t n)).sub (measurable_Wt l)).const_smul (t n)⁻¹ |>.aemeasurable
  apply aemeasurable_of_tendsto_metrizable_ae atTop hmeas
  filter_upwards [ae_regTree_split h] with T hT
  have hlim := (hasDerivAt_Wt hT hl hlm).differentiableAt.hasDerivAt.tendsto_slope_zero.comp ht
  simp only [F, slope_def_module, add_sub_cancel_left]
  exact hlim

/-- The dominating bound for the differentiated integrand of `ηₙ` on `[a, b]`. -/
theorem ae_norm_deriv_Wt_pow_le (h : OffspringHyp μ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hb : b < mean μ) (n : ℕ) :
    ∀ᵐ T ∂splitLaw μ, ∀ x ∈ Set.Icc a b,
      ‖(n : ℝ) * Wt x T ^ (n - 1) * deriv (fun l' => Wt l' T) x‖ ≤
        (n : ℝ) * ((childEnv a b T + 1) / (a - 1)) := by
  filter_upwards [ae_regTree_split h] with T hT x hx
  have hx1 : 1 < x := by linarith [hx.1]
  obtain ⟨hW0, hW1⟩ := Wt_mem_Icc' hx1 T
  have hW : |Wt x T ^ (n - 1)| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hW0 _)]
    exact pow_le_one₀ hW0 hW1
  have hd := abs_deriv_Wt_le hT ha hab hb hx
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  calc (n : ℝ) * |Wt x T ^ (n - 1)| * |deriv (fun l' => Wt l' T) x|
      ≤ (n : ℝ) * 1 * ((childEnv a b T + 1) / (a - 1)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg n)) hd (abs_nonneg _)
        positivity
    _ = _ := by ring

theorem integrable_deriv_bound (h : OffspringHyp μ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hb : b < mean μ) (n : ℕ) :
    Integrable (fun T => (n : ℝ) * ((childEnv a b T + 1) / (a - 1))) (splitLaw μ) := by
  letI := splitLaw_prob h
  exact (((integrable_childEnv_split h (by linarith) hab hb).add (integrable_const 1)).div_const
    (a - 1)).const_mul n

/-! ### `hasDerivAt_etaW` -/

/-- Differentiation of `ηₙ = E Wⁿ` under the integral (valid for every `n`). -/
theorem hasDerivAt_etaW (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) (n : ℕ) :
    HasDerivAt (fun l => etaW μ l n)
      (∫ T, n * Wt l T ^ (n - 1) * deriv (fun l' => Wt l' T) l ∂splitLaw μ) l := by
  letI := splitLaw_prob h
  have hm := one_lt_mean_of_hyp h
  set a := (1 + l) / 2 with ha_def
  set b := (l + mean μ) / 2 with hb_def
  have ha : 1 < a := by rw [ha_def]; linarith
  have hal : a < l := by rw [ha_def]; linarith
  have hlb : l < b := by rw [hb_def]; linarith
  have hb : b < mean μ := by rw [hb_def]; linarith
  have hab : a ≤ b := by linarith
  have hs : Set.Ioo a b ∈ 𝓝 l := isOpen_Ioo.mem_nhds ⟨hal, hlb⟩
  have hbound := ae_norm_deriv_Wt_pow_le h ha hab hb n
  obtain ⟨-, key⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := splitLaw μ)
    (F := fun x T => Wt x T ^ n)
    (F' := fun x T => (n : ℝ) * Wt x T ^ (n - 1) * deriv (fun l' => Wt l' T) x)
    (bound := fun T => (n : ℝ) * ((childEnv a b T + 1) / (a - 1))) hs
    (Filter.Eventually.of_forall fun x => ((measurable_Wt x).pow_const n).aestronglyMeasurable)
    (integrable_Wt_pow' h hl hlm n)
    ((aemeasurable_const.mul ((measurable_Wt l).pow_const _).aemeasurable).mul
      (aemeasurable_deriv_Wt h hl hlm)).aestronglyMeasurable
    (by
      filter_upwards [hbound] with T hT x hx
      exact hT x ⟨hx.1.le, hx.2.le⟩)
    (integrable_deriv_bound h ha hab hb n)
    (by
      filter_upwards [ae_regTree_split h] with T hT x hx
      exact (hasDerivAt_Wt hT (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.hasDerivAt.fun_pow n)
  exact key

/-- Uniform bound on `∂_l ηₙ` over a compact `[a, b] ⊂ (1, m)`. -/
theorem abs_deriv_etaW_le (h : OffspringHyp μ) {a b x : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hb : b < mean μ) (hx : x ∈ Set.Icc a b) (n : ℕ) :
    |deriv (fun l => etaW μ l n) x| ≤
      n * ∫ T, (childEnv a b T + 1) / (a - 1) ∂splitLaw μ := by
  rw [(hasDerivAt_etaW h (by linarith [hx.1]) (by linarith [hx.2]) n).deriv, ← Real.norm_eq_abs,
    ← integral_const_mul]
  apply norm_integral_le_of_norm_le (integrable_deriv_bound h ha hab hb n)
  filter_upwards [ae_norm_deriv_Wt_pow_le h ha hab hb n] with T hT
  exact hT x hx

end LPPMonotonicityProof.Analytic
