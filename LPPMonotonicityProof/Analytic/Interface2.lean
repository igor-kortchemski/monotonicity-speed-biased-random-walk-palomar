module

public import LPPMonotonicityProof.Analytic.Interface
public import LPPMonotonicityProof.Speed.Signed.TwoCopyBounds
public import LPPMonotonicityProof.Speed.Signed.TwoCopyProof

/-!
# Analytic interface lemmas: root decomposition, good event, Aïdékon quotient

This module decomposes integrals against the Bienaymé law over the root degree,
shows that the good event `GoodTree0` holds almost surely and is inherited by
subtrees, and writes the speed as the Aïdékon degree quotient, equation (2.1)
(`eq:aidekon`) of Theorem 2.2, in tree form.  The speed there is
`speedValueProv`, the copy of `Speed.speedValue` defined in
`LPPMonotonicityProof.Analytic.Defs`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-! ## Root decomposition -/

private lemma GW_eq_sum_root :
    GW μ = Measure.sum fun k : ℕ =>
      μ {k} • (Measure.pi fun _ : Fin k => GW μ).map (nodeFin k) := by
  have hdisj : Pairwise (fun i j =>
      Disjoint {T : Tree | degree T = i} {T : Tree | degree T = j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun T hi hj => hij (hi.symm.trans hj)
  calc
    GW μ = (GW μ).restrict Set.univ := by simp
    _ = (GW μ).restrict (⋃ k : ℕ, {T | degree T = k}) := by
      congr 1
      ext T
      simp
    _ = Measure.sum fun k : ℕ => (GW μ).restrict {T | degree T = k} :=
      Measure.restrict_iUnion hdisj
        (fun k => continuous_degree.measurable (measurableSet_singleton k))
    _ = _ := by
      apply congrArg Measure.sum
      funext k
      exact bienaymeLaw_restrict_degree k

/-- Extended integrals against the Bienaymé law decompose over the root degree. -/
theorem lintegral_GW_eq_tsum (f : Tree → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ T, f T ∂GW μ =
      ∑' k, μ {k} * ∫⁻ ts, f (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ) := by
  conv_lhs => rw [GW_eq_sum_root]
  rw [lintegral_sum_measure]
  apply tsum_congr
  intro k
  rw [lintegral_smul_measure, lintegral_map hf (measurable_nodeFin k)]
  simp only [smul_eq_mul]

/-- Real integrals against the Bienaymé law decompose over the root degree. -/
theorem integral_GW_eq_tsum (f : Tree → ℝ) (hf : Integrable f (GW μ)) :
    ∫ T, f T ∂GW μ =
      ∑' k, (μ {k}).toReal * ∫ ts, f (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ) := by
  exact integral_bienayme_root μ hf

/-- The child sum after root decomposition is the finite sum of child escapes. -/
theorem childSum_nodeFin (l : ℝ) (k : ℕ) (ts : Fin k → Tree) :
    childSum l (nodeFin k ts) = ∑ i, escape l (ts i) := by
  exact Speed.childSum_nodeFin l k ts

/-! ## The good event -/

/-- Almost every tree is leafless and has positive escape on every present subtree,
simultaneously at every transient bias. -/
theorem ae_goodTree0 (h : OffspringHyp μ) : ∀ᵐ T ∂GW μ, GoodTree0 μ T := by
  filter_upwards [LPPMonotonicityProof.RTL.Leafless.ae_present_offspring_pos μ h.zero,
    ae_escape_pos_all h] with T hleaf hesc
  exact ⟨fun v hv => hleaf v hv, fun l hl v hv => (hesc l hl v hv).1⟩

/-- The good event is inherited by every present subtree. -/
theorem GoodTree0.subtree {T : Tree} (hT : GoodTree0 μ T) {v : Address}
    (hv : Present T v) : GoodTree0 μ (Speed.subtree T v) := by
  constructor
  · intro u hu
    rw [Speed.subtree_val]
    exact hT.1 (v ++ u) ((present_subtree T v u hv).mp hu)
  · intro l hl u hu
    have hpos := hT.2 l hl (v ++ u) ((present_subtree T v u hv).mp hu)
    have hsub : Speed.subtree (Speed.subtree T v) u = Speed.subtree T (v ++ u) := by
      apply Subtype.ext
      funext w
      simp [Speed.subtree, List.append_assoc]
    rwa [hsub]

/-- The good event also holds almost surely under the root-conditioned split law. -/
theorem ae_goodTree0_split (h : OffspringHyp μ) : ∀ᵐ T ∂splitLaw μ, GoodTree0 μ T := by
  exact Measure.ae_smul_measure (ae_restrict_of_ae (ae_goodTree0 h)) _

/-! ## The Aïdékon quotient (2.1) in tree form -/

private lemma measurable_aidIntegrand (l : ℝ) (g : ℕ → ℝ) :
    Measurable (fun p : Tree × Tree =>
      g (degree p.1) * escape l p.2 / (l - 1 + escape l p.2 + childSum l p.1)) := by
  exact (((measurable_of_countable g).comp
    (continuous_degree.measurable.comp measurable_fst)).mul
    ((measurable_escape l).comp measurable_snd)).div
    (((measurable_const.sub measurable_const).add
      ((measurable_escape l).comp measurable_snd)).add
      ((measurable_childSum l).comp measurable_fst))

private lemma map_ref_fwd_bwd (l : ℝ) (hl : 0 < l) :
    (ref μ l hl).map (fun e => (e.fwd, e.bwd)) = (GW μ).prod (GW μ) := by
  let backLaw := (GW μ) ⊗ₘ harm l hl
  have hfst : backLaw.map Prod.fst = GW μ := Measure.fst_compProd _ _
  change (Measure.prod (GW μ) backLaw).map
    (fun e : Tree × (Tree × (ℕ → ℕ)) => (e.1, e.2.1)) = _
  rw [show (fun e : Tree × (Tree × (ℕ → ℕ)) => (e.1, e.2.1)) =
      Prod.map id Prod.fst by rfl,
    ← Measure.map_prod_map _ _ measurable_id measurable_fst, hfst]
  simp

/-- The forward/backward marginal reduces a reference-law integral to the two-tree
integral defining `aidE`; no integrability hypothesis is needed for the identity. -/
private lemma integral_ref_aid (l : ℝ) (hl : 0 < l) (g : ℕ → ℝ) :
    (∫ e, g (degree e.fwd) * escape l e.bwd /
      (l - 1 + escape l e.bwd + childSum l e.fwd) ∂ref μ l hl) = aidE μ l g := by
  rw [aidE, ← map_ref_fwd_bwd l hl]
  exact (integral_map
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).aemeasurable
    (measurable_aidIntegrand l g).aestronglyMeasurable).symm

private lemma integrable_pairAid_of_ref (l : ℝ) (hl : 0 < l) (g : ℕ → ℝ)
    (hint : Integrable (fun e => g (degree e.fwd) * escape l e.bwd /
      (l - 1 + escape l e.bwd + childSum l e.fwd)) (ref μ l hl)) :
    Integrable (fun p : Tree × Tree =>
      g (degree p.1) * escape l p.2 / (l - 1 + escape l p.2 + childSum l p.1))
      ((GW μ).prod (GW μ)) := by
  have hmap := (integrable_map_measure
    (measurable_aidIntegrand l g).aestronglyMeasurable
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).aemeasurable).2 hint
  change Integrable (fun p : Tree × Tree =>
    g (degree p.1) * escape l p.2 / (l - 1 + escape l p.2 + childSum l p.1))
    ((ref μ l hl).map (fun e => (e.fwd, e.bwd))) at hmap
  rwa [map_ref_fwd_bwd l hl] at hmap

private lemma integrable_aidRef (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) (g : ℕ → ℝ) (hg : ∃ C, ∀ k, |g k| ≤ C * (k + 1)) :
    Integrable (fun e => g (degree e.fwd) * escape l e.bwd /
      (l - 1 + escape l e.bwd + childSum l e.fwd)) (ref μ l hl) := by
  obtain ⟨C, hC⟩ := hg
  have hC0 : 0 ≤ C := by
    calc
      0 ≤ |g 0| := abs_nonneg _
      _ ≤ C := by simpa using hC 0
  let A : ℝ := (C + 1) * (1 + l⁻¹)
  have hCp : 0 ≤ C + 1 := by linarith
  have hA : 0 < A := mul_pos (by linarith) (by positivity)
  have hfac : 1 ≤ 1 + l⁻¹ := le_add_of_nonneg_right (inv_nonneg.mpr hl.le)
  have hAC : C ≤ A := by
    calc
      C ≤ C + 1 := by linarith
      _ = (C + 1) * 1 := (mul_one _).symm
      _ ≤ (C + 1) * (1 + l⁻¹) := mul_le_mul_of_nonneg_left hfac hCp
      _ = A := rfl
  have hlinv : (1 + l⁻¹) * l = l + 1 := by
    rw [add_mul, one_mul, inv_mul_cancel₀ (ne_of_gt hl)]
  have hAl : A * l = (C + 1) * (l + 1) := by
    calc
      A * l = (C + 1) * ((1 + l⁻¹) * l) := by ring
      _ = (C + 1) * (l + 1) := by rw [hlinv]
  have hACl : C ≤ A * l := by
    rw [hAl]
    have hl1 : 1 ≤ l + 1 := by linarith
    calc
      C ≤ C + 1 := by linarith
      _ = (C + 1) * 1 := (mul_one _).symm
      _ ≤ (C + 1) * (l + 1) := mul_le_mul_of_nonneg_left hl1 hCp
  let c : ℕ → ℝ := fun k => g k / A
  have hc : ∀ k, |c k| ≤ (k : ℝ) + l := by
    intro k
    change |g k / A| ≤ (k : ℝ) + l
    rw [abs_div, abs_of_pos hA]
    apply (div_le_iff₀ hA).2
    calc
      |g k| ≤ C * (k + 1) := hC k
      _ = C * (k : ℝ) + C := by ring
      _ ≤ A * (k : ℝ) + A * l :=
        add_le_add (mul_le_mul_of_nonneg_right hAC (Nat.cast_nonneg k)) hACl
      _ = A * ((k : ℝ) + l) := by ring
      _ = ((k : ℝ) + l) * A := mul_comm _ _
  refine ((integrable_C_ratio_ref μ hl h hlm c hc).const_mul A).congr
    (Filter.Eventually.of_forall fun e => ?_)
  simp only [c, Hfun, div_eq_mul_inv]
  calc
    _ = (A * A⁻¹) * (g (degree e.fwd) * escape l e.bwd *
      (l - 1 + escape l e.bwd + childSum l e.fwd)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hA.ne', one_mul]

/-- The tree-form Aïdékon integrand is integrable under the stated linear
 growth bound. -/
theorem integrable_aid (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ)
    (g : ℕ → ℝ) (hg : ∃ C, ∀ k, |g k| ≤ C * (k + 1)) :
    Integrable (fun p => g (degree p.1) * escape l p.2 /
      (l - 1 + escape l p.2 + childSum l p.1)) ((GW μ).prod (GW μ)) := by
  exact integrable_pairAid_of_ref l hl g (integrable_aidRef h hl hlm g hg)

/-- Equation (2.1) (`eq:aidekon`): the speed equals the normalized Aïdékon quotient. -/
theorem speedValue_eq_aid (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) :
    speedValueProv μ l = aidE μ l (fun k => k - l) / aidE μ l (fun k => k + l) := by
  have hspeed : speedValueProv μ l = Nval μ l / Zval μ l := by
    rw [speedValueProv, if_neg (ne_of_gt hl)]
    rfl
  rw [hspeed, ← degreeQuotient_eq μ hl h hlm]
  unfold degreeQuotient
  simp_rw [escapeSum_escape_eq_childSum]
  exact congrArg₂ (· / ·)
    (integral_ref_aid l hl (fun k : ℕ => (k : ℝ) - l))
    (integral_ref_aid l hl (fun k : ℕ => (k : ℝ) + l))

/-- The denominator of the Aïdékon quotient is strictly positive. -/
theorem aidE_pos (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ) :
    0 < aidE μ l (fun k => k + l) := by
  calc
    aidE μ l (fun k => k + l) =
        ∫ e, ((degree e.fwd : ℝ) + l) * escape l e.bwd /
          (l - 1 + escape l e.bwd + childSum l e.fwd) ∂ref μ l hl :=
      (integral_ref_aid l hl (fun k : ℕ => (k : ℝ) + l)).symm
    _ = ∫ e, (childSum l e.fwd + l * escape l e.bwd) /
          Hfun l (escape l e.bwd) (childSum l e.fwd) ∂ref μ l hl :=
      integral_ref_exchange_add μ hl h hlm l (by rw [abs_of_pos hl])
    _ = l * Zval μ l := integral_ref_plus_eq_Zval μ hl h hlm
    _ > 0 := mul_pos hl (Zval_pos μ hl h hlm)

end LPPMonotonicityProof.Analytic
