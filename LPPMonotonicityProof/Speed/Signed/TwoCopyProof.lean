module

public import LPPMonotonicityProof.Speed.Signed.ExchangeIntegrability

/-! # The two-copy identities and the degree quotient

The equality of the degree quotient and `N/Z` in equation (2.1) (`eq:aidekon`), from
the exchangeability argument in the proof of Theorem 2.2 (`thm:speed-formula`). -/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

lemma sum_C_ratio_norm_bound {l : ℝ} {k : ℕ} (hk : k ≠ 0) {b : ℝ} {bs : Fin k → ℝ}
    (hb : GoodEsc l b) (hbs : ∀ i, GoodEsc l (bs i)) (c : ℝ) :
    ‖((∑ i, bs i) + c * b) / Hfun l b (∑ i, bs i)‖ ≤ 1 + |c| := by
  have hH := Hfun_pos hk hb hbs
  have hS0 : 0 ≤ ∑ i, bs i := Finset.sum_nonneg fun i _ => (hbs i).1.le
  have hSH := Hfun_ge_sum hb hbs
  have hbH : |c| * b ≤ |c| * Hfun l b (∑ i, bs i) := by
    have hr := ratio_mono_bound hk hb hbs (C := |c|) (abs_nonneg _)
    rw [abs_div, abs_mul, abs_of_pos hH, abs_of_pos hb.1, abs_of_nonneg (abs_nonneg _)] at hr
    exact (div_le_iff₀ hH).1 hr
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hH]
  apply (div_le_iff₀ hH).2
  calc
    |(∑ i, bs i) + c * b| ≤ |(∑ i, bs i)| + |c * b| := abs_add_le _ _
    _ = (∑ i, bs i) + |c| * b := by rw [abs_of_nonneg hS0, abs_mul, abs_of_pos hb.1]
    _ ≤ (1 + |c|) * Hfun l b (∑ i, bs i) := by nlinarith

/-- Integrability of `(S+c*b)/H` on the reference environment. -/
lemma integrable_sum_C_ratio_ref (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) (c : ℝ) :
    Integrable (fun e => (childSum l e.fwd + c * escape l e.bwd) /
      Hfun l (escape l e.bwd) (childSum l e.fwd)) (ref μ l hl) := by
  let F : ℕ → ℝ → ℝ → ℝ := fun _ b S => (S + c * b) / Hfun l b S
  have hFb : ∀ k S, Measurable fun b => F k b S := by
    intro k S
    exact (measurable_const.add (measurable_const.mul measurable_id)).div
      ((measurable_const.sub measurable_const).add measurable_id |>.add measurable_const)
  have hFmeas : AEStronglyMeasurable
      (fun e => F (degree e.fwd) (escape l e.bwd) (childSum l e.fwd)) (ref μ l hl) := by
    apply Measurable.aestronglyMeasurable
    exact ((((measurable_childSum l).comp measurable_fst).add
      (measurable_const.mul ((measurable_escape l).comp (measurable_fst.comp measurable_snd)))).div
      (((measurable_const.sub measurable_const).add
        ((measurable_escape l).comp (measurable_fst.comp measurable_snd))).add
        ((measurable_childSum l).comp measurable_fst)))
  have hinner : ∀ᵐ T ∂bienaymeLaw μ, Integrable
      (fun q : Tree × (ℕ → ℕ) => F (degree T) (escape l q.1) (childSum l T))
      ((bienaymeLaw μ) ⊗ₘ harm l hl) := by
    let D := concreteEscapeData' μ l hl hμ hlm
    filter_upwards [D.ae_good] with T hT
    have hk : degree T ≠ 0 := Nat.ne_of_gt hT.1
    have hbs : ∀ i : Fin (degree T), GoodEsc l (escape l (child T (i.val + 1))) := by
      intro i
      have hi : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ degree T := by omega
      have hchild := hT.goodChild hi
      exact ⟨hchild.escape_pos, escape_lt_one hl _, hchild.escape_lower⟩
    have hB : Integrable (fun b => (childSum l T + c * b) / Hfun l b (childSum l T)) (escLaw μ l) := by
      apply (integrable_const (1 + |c|)).mono
        ((measurable_const.add (measurable_const.mul measurable_id)).div
          ((measurable_const.sub measurable_const).add measurable_id |>.add
            measurable_const)).aestronglyMeasurable
      filter_upwards [ae_goodEsc μ hl hμ hlm] with b hb
      rw [Real.norm_of_nonneg (show 0 ≤ 1 + |c| by positivity)]
      simpa [F, Hfun, childSum] using sum_C_ratio_norm_bound hk hb hbs c
    have hfst0 : ((bienaymeLaw μ) ⊗ₘ harm l hl).map Prod.fst = bienaymeLaw μ :=
      Measure.fst_compProd _ _
    have hfst : ((bienaymeLaw μ) ⊗ₘ harm l hl).map (escape l ∘ Prod.fst) = escLaw μ l := by
      rw [← Measure.map_map (measurable_escape l) measurable_fst, hfst0, escLaw]
    have hmap : Integrable (fun b => (childSum l T + c * b) / Hfun l b (childSum l T))
        (((bienaymeLaw μ) ⊗ₘ harm l hl).map (escape l ∘ Prod.fst)) := by
      rw [hfst]
      exact hB
    exact (integrable_map_measure hmap.aestronglyMeasurable
      ((measurable_escape l).comp measurable_fst).aemeasurable).1 hmap
  have hprod : ∀ k, μ {k} ≠ 0 → Integrable (fun q : ℝ × (Fin k → ℝ) =>
      F k q.1 (∑ i, q.2 i)) ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) := by
    intro k hk
    have hk0 : k ≠ 0 := by
      intro hk0
      subst k
      exact hk hμ.zero
    apply (integrable_const (1 + |c|)).mono
      (((Finset.univ.measurable_sum fun j _ => (measurable_pi_apply j).comp measurable_snd).add (measurable_const.mul measurable_fst)).div
        (((measurable_const.sub measurable_const).add measurable_fst).add
          (Finset.univ.measurable_sum fun j _ => (measurable_pi_apply j).comp measurable_snd))).aestronglyMeasurable
    filter_upwards [ae_iid_good μ hl hμ hlm k] with q hq
    rw [Real.norm_of_nonneg (show 0 ≤ 1 + |c| by positivity)]
    simpa [Hfun] using sum_C_ratio_norm_bound hk0 hq.1 hq.2 c
  have hsum : Summable fun k : ℕ => (μ {k}).toReal *
      ∫ q : ℝ × (Fin k → ℝ), ‖F k q.1 (∑ i, q.2 i)‖
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) := by
    have hmass : Summable fun k : ℕ => (μ {k}).toReal := by
      simpa only [Measure.real] using
        (summable_measure_toReal (μ := μ) (f := fun k : ℕ => {k})
          (fun _ => measurableSet_singleton _) (by
            intro i j hij
            simpa using hij))
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg ENNReal.toReal_nonneg (integral_nonneg fun _ => norm_nonneg _))
      (f := fun k : ℕ => (1 + |c|) * (μ {k}).toReal) ?_ (hmass.mul_left (1 + |c|))
    intro k
    by_cases hk : μ {k} = 0
    · simp [hk]
    have hk0 : k ≠ 0 := by
      intro hk0
      subst k
      exact hk hμ.zero
    have hb := integral_mono_ae (hprod k hk).norm (integrable_const (1 + |c|))
      (show (fun q : ℝ × (Fin k → ℝ) => ‖F k q.1 (∑ i, q.2 i)‖) ≤ᵐ[
        (escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)]
        (fun _ => 1 + |c|) by
          filter_upwards [ae_iid_good μ hl hμ hlm k] with q hq
          simpa only [norm_norm] using sum_C_ratio_norm_bound hk0 hq.1 hq.2 c)
    have hb' : (∫ q : ℝ × (Fin k → ℝ), ‖F k q.1 (∑ i, q.2 i)‖
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) ≤ 1 + |c| := by
      simpa using hb
    calc
      (μ {k}).toReal * ∫ q : ℝ × (Fin k → ℝ), ‖F k q.1 (∑ i, q.2 i)‖
          ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) ≤
          (μ {k}).toReal * (1 + |c|) := mul_le_mul_of_nonneg_left hb' ENNReal.toReal_nonneg
      _ = (1 + |c|) * (μ {k}).toReal := mul_comm _ _
  exact integrable_ref_of_fiber_summable μ l hl F hFb hFmeas hinner hprod hsum

/-- Exchangeability in each fixed-degree fiber, with a constant shift `c`. -/
lemma integral_fiber_add_exchange (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ)
    {k : ℕ} (hk : k ≠ 0) (c : ℝ) :
    (∫ q : ℝ × (Fin k → ℝ), ((k : ℝ) + c) * q.1 / Hfun l q.1 (∑ j, q.2 j)
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) =
      ∫ q : ℝ × (Fin k → ℝ), ((∑ j, q.2 j) + c * q.1) / Hfun l q.1 (∑ j, q.2 j)
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) := by
  have hkint := integrable_C_ratio μ hl hμ hlm hk (k : ℝ) (k : ℝ) (Nat.cast_nonneg k) (by simp)
  have hcint := integrable_C_ratio μ hl hμ hlm hk c |c| (abs_nonneg _) le_rfl
  have hleft : (fun q : ℝ × (Fin k → ℝ) => ((k : ℝ) + c) * q.1 / Hfun l q.1 (∑ j, q.2 j)) =
      fun q => (k : ℝ) * q.1 / Hfun l q.1 (∑ j, q.2 j) +
        c * q.1 / Hfun l q.1 (∑ j, q.2 j) := by
    funext q
    ring
  have hright : (fun q : ℝ × (Fin k → ℝ) => ((∑ j, q.2 j) + c * q.1) /
      Hfun l q.1 (∑ j, q.2 j)) = fun q =>
        (∑ j, q.2 j) / Hfun l q.1 (∑ j, q.2 j) + c * q.1 / Hfun l q.1 (∑ j, q.2 j) := by
    funext q
    ring
  rw [hleft, hright, integral_add hkint hcint, integral_degree_exchange μ hl hμ hlm hk,
    integral_add (integrable_sum_ratio μ hl hμ hlm hk) hcint]

/-- The signed exchange identity on the reference law. -/
theorem integral_ref_exchange_add (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ)
    (c : ℝ) (hc : |c| ≤ l) :
    (∫ e, ((degree e.fwd : ℝ) + c) * escape l e.bwd /
        Hfun l (escape l e.bwd) (childSum l e.fwd) ∂ref μ l hl) =
      ∫ e, (childSum l e.fwd + c * escape l e.bwd) /
        Hfun l (escape l e.bwd) (childSum l e.fwd) ∂ref μ l hl := by
  let F : ℕ → ℝ → ℝ → ℝ := fun k b S => ((k : ℝ) + c) * b / Hfun l b S
  let G : ℕ → ℝ → ℝ → ℝ := fun _ b S => (S + c * b) / Hfun l b S
  have hcoeff : ∀ k : ℕ, |((k : ℝ) + c)| ≤ (k : ℝ) + l := by
    intro k
    calc
      |((k : ℝ) + c)| ≤ |(k : ℝ)| + |c| := abs_add_le _ _
      _ ≤ (k : ℝ) + l := by rw [abs_of_nonneg (Nat.cast_nonneg k)]; linarith
  have hFint : Integrable (fun e => F (degree e.fwd) (escape l e.bwd) (childSum l e.fwd))
      (ref μ l hl) := integrable_C_ratio_ref μ hl hμ hlm (fun k => (k : ℝ) + c) hcoeff
  have hGint : Integrable (fun e => G (degree e.fwd) (escape l e.bwd) (childSum l e.fwd))
      (ref μ l hl) := by simpa only [G] using integrable_sum_C_ratio_ref μ hl hμ hlm c
  have hFm : ∀ k S, Measurable fun b => F k b S := by
    intro k S
    exact (measurable_const.mul measurable_id).div
      ((measurable_const.sub measurable_const).add measurable_id |>.add measurable_const)
  have hGm : ∀ k S, Measurable fun b => G k b S := by
    intro k S
    exact (measurable_const.add (measurable_const.mul measurable_id)).div
      ((measurable_const.sub measurable_const).add measurable_id |>.add measurable_const)
  have hFsF : ∀ k b, Measurable fun bs : Fin k → ℝ => F k b (∑ i, bs i) := by
    intro k b
    exact (measurable_const.mul measurable_const).div
      ((measurable_const.sub measurable_const).add measurable_const |>.add
        (Finset.univ.measurable_sum fun i _ => measurable_pi_apply i))
  have hFsG : ∀ k b, Measurable fun bs : Fin k → ℝ => G k b (∑ i, bs i) := by
    intro k b
    exact ((Finset.univ.measurable_sum fun i _ => measurable_pi_apply i).add measurable_const).div
      ((measurable_const.sub measurable_const).add measurable_const |>.add
        (Finset.univ.measurable_sum fun i _ => measurable_pi_apply i))
  have hpF : ∀ k, μ {k} ≠ 0 → Integrable (fun q : ℝ × (Fin k → ℝ) => F k q.1 (∑ i, q.2 i))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) := by
    intro k hk
    have hk0 : k ≠ 0 := by intro h; subst k; exact hk hμ.zero
    exact integrable_C_ratio μ hl hμ hlm hk0 ((k : ℝ) + c) |(k : ℝ) + c|
      (abs_nonneg _) le_rfl
  have hpG : ∀ k, μ {k} ≠ 0 → Integrable (fun q : ℝ × (Fin k → ℝ) => G k q.1 (∑ i, q.2 i))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) := by
    intro k hk
    have hk0 : k ≠ 0 := by intro h; subst k; exact hk hμ.zero
    change Integrable (fun q : ℝ × (Fin k → ℝ) =>
      ((∑ j, q.2 j) + c * q.1) / Hfun l q.1 (∑ j, q.2 j))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l))
    apply (integrable_const (1 + |c|)).mono
      ((((Finset.univ.measurable_sum fun j _ => (measurable_pi_apply j).comp measurable_snd).add (measurable_const.mul measurable_fst)).div
        (((measurable_const.sub measurable_const).add measurable_fst).add
          (Finset.univ.measurable_sum fun j _ => (measurable_pi_apply j).comp measurable_snd))).aestronglyMeasurable)
    filter_upwards [ae_iid_good μ hl hμ hlm k] with q hq
    rw [Real.norm_of_nonneg (show 0 ≤ 1 + |c| by positivity)]
    simpa [Hfun] using sum_C_ratio_norm_bound hk0 hq.1 hq.2 c
  rw [integral_ref_fwd_bwd μ l hl F hFm hFsF hFint hpF,
    integral_ref_fwd_bwd μ l hl G hGm hFsG hGint hpG]
  apply tsum_congr
  intro k
  by_cases hk : μ {k} = 0
  · simp [hk]
  have hk0 : k ≠ 0 := by intro h; subst k; exact hk hμ.zero
  congr 1
  exact integral_fiber_add_exchange μ hl hμ hlm hk0 c


lemma ae_twoCopy_algebra (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) :
    ∀ᵐ e ∂ref μ l hl, 0 ≤ childSum l e.fwd ∧
      escape l e.fwd = childSum l e.fwd / (l + childSum l e.fwd) ∧
      Dfun l (escape l e.fwd) (escape l e.bwd) ≠ 0 := by
  let D := concreteEscapeData' μ l hl hμ hlm
  filter_upwards [D.ae_good_ref] with e he
  have hS : 0 ≤ childSum l e.fwd := by
    rw [← escapeSum_escape_eq_childSum]
    exact he.1.escapeSum_pos.le
  have hr : escape l e.fwd = childSum l e.fwd / (l + childSum l e.fwd) := by
    simp only [escape_eq hl, escapeSum_escape_eq_childSum]
  have hf : GoodEsc l (escape l e.fwd) :=
    ⟨he.1.escape_pos, escape_lt_one hl _, he.1.escape_lower⟩
  have hb : GoodEsc l (escape l e.bwd) :=
    ⟨he.2.escape_pos, escape_lt_one hl _, he.2.escape_lower⟩
  exact ⟨hS, hr, ne_of_gt (Dfun_pos_of_good hl hf hb)⟩

/-- The positive signed numerator is `λ Z`. -/
theorem integral_ref_plus_eq_Zval (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) :
    (∫ e, (childSum l e.fwd + l * escape l e.bwd) /
        Hfun l (escape l e.bwd) (childSum l e.fwd) ∂ref μ l hl) = l * Zval μ l := by
  let g : ℝ × ℝ → ℝ := fun p => l * (p.1 + p.2 - p.1 * p.2) / Dfun l p.1 p.2
  have hgm : Measurable g :=
    ((measurable_const.mul ((measurable_fst.add measurable_snd).sub
      (measurable_fst.mul measurable_snd))).div (measurable_Dfun l))
  have hpoint : ∀ᵐ e ∂ref μ l hl,
      (childSum l e.fwd + l * escape l e.bwd) /
        Hfun l (escape l e.bwd) (childSum l e.fwd) =
      g (escape l e.fwd, escape l e.bwd) := by
    filter_upwards [ae_twoCopy_algebra μ hl hμ hlm] with e he
    exact plus_num_div_eq hl he.1 he.2.1 he.2.2
  calc
    _ = ∫ e, g (escape l e.fwd, escape l e.bwd) ∂ref μ l hl := integral_congr_ae hpoint
    _ = ∫ p, g p ∂(escLaw μ l).prod (escLaw μ l) :=
      integral_ref_escape_prod μ l hl g hgm.aestronglyMeasurable
    _ = l * Zval μ l := by
      dsimp only [g]
      rw [Zval]
      simp_rw [mul_div_assoc]
      exact integral_const_mul l _

/-- The negative signed numerator is `λ N`, by the two-copy swap symmetry. -/
theorem integral_ref_minus_eq_Nval (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) :
    (∫ e, (childSum l e.fwd - l * escape l e.bwd) /
        Hfun l (escape l e.bwd) (childSum l e.fwd) ∂ref μ l hl) = l * Nval μ l := by
  let g : ℝ × ℝ → ℝ := fun p => l * (p.1 - p.2 + p.1 * p.2) / Dfun l p.1 p.2
  have hgm : Measurable g :=
    ((measurable_const.mul ((measurable_fst.sub measurable_snd).add
      (measurable_fst.mul measurable_snd))).div (measurable_Dfun l))
  have hpoint : ∀ᵐ e ∂ref μ l hl,
      (childSum l e.fwd - l * escape l e.bwd) /
        Hfun l (escape l e.bwd) (childSum l e.fwd) =
      g (escape l e.fwd, escape l e.bwd) := by
    filter_upwards [ae_twoCopy_algebra μ hl hμ hlm] with e he
    exact minus_num_div_eq hl he.1 he.2.1 he.2.2
  have hGint : Integrable (fun e => (childSum l e.fwd - l * escape l e.bwd) /
      Hfun l (escape l e.bwd) (childSum l e.fwd)) (ref μ l hl) := by
    simpa only [sub_eq_add_neg, neg_mul] using integrable_sum_C_ratio_ref μ hl hμ hlm (-l)
  have hcomp : Integrable (fun e => g (escape l e.fwd, escape l e.bwd)) (ref μ l hl) :=
    hGint.congr hpoint
  have hint : Integrable g ((escLaw μ l).prod (escLaw μ l)) := by
    rw [← map_ref_escape μ l hl]
    exact (integrable_map_measure hgm.aestronglyMeasurable
      (((measurable_escape l).comp measurable_fst).prodMk
        ((measurable_escape l).comp (measurable_fst.comp measurable_snd))).aemeasurable).2 hcomp
  calc
    _ = ∫ e, g (escape l e.fwd, escape l e.bwd) ∂ref μ l hl := integral_congr_ae hpoint
    _ = ∫ p, g p ∂(escLaw μ l).prod (escLaw μ l) :=
      integral_ref_escape_prod μ l hl g hgm.aestronglyMeasurable
    _ = l * Nval μ l := integral_minusTwoCopy_eq_Nval μ l hint

/-- **Two-copy form:** the normalized degree quotient is the two-copy quotient `N/Z`
(the exchangeability argument in the proof of Theorem 2.2). -/
theorem degreeQuotient_eq (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) :
    degreeQuotient μ l hl = Nval μ l / Zval μ l := by
  have hminus := integral_ref_exchange_add μ hl hμ hlm (-l) (by rw [abs_neg, abs_of_pos hl])
  have hplus := integral_ref_exchange_add μ hl hμ hlm l (by rw [abs_of_pos hl])
  have hminus' :
      (∫ e, ((degree e.fwd : ℝ) - l) * escape l e.bwd /
          Hfun l (escape l e.bwd) (childSum l e.fwd) ∂ref μ l hl) = l * Nval μ l := by
    calc
      _ = ∫ e, (childSum l e.fwd + (-l) * escape l e.bwd) /
          Hfun l (escape l e.bwd) (childSum l e.fwd) ∂ref μ l hl := by
        simpa only [sub_eq_add_neg] using hminus
      _ = l * Nval μ l := by
        simpa only [sub_eq_add_neg, neg_mul] using integral_ref_minus_eq_Nval μ hl hμ hlm
  have hplus' :
      (∫ e, ((degree e.fwd : ℝ) + l) * escape l e.bwd /
          Hfun l (escape l e.bwd) (childSum l e.fwd) ∂ref μ l hl) = l * Zval μ l :=
    hplus.trans (integral_ref_plus_eq_Zval μ hl hμ hlm)
  unfold degreeQuotient
  simp_rw [escapeSum_escape_eq_childSum]
  change (∫ e, ((degree e.fwd : ℝ) - l) * escape l e.bwd /
      Hfun l (escape l e.bwd) (childSum l e.fwd) ∂ref μ l hl) /
    (∫ e, ((degree e.fwd : ℝ) + l) * escape l e.bwd /
      Hfun l (escape l e.bwd) (childSum l e.fwd) ∂ref μ l hl) = _
  rw [hminus', hplus', mul_div_mul_left _ _ (ne_of_gt hl)]

end LPPMonotonicityProof.Speed
