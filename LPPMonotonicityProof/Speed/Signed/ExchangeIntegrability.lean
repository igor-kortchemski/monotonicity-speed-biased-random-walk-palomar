module

public import LPPMonotonicityProof.Speed.Signed.TwoCopyBounds
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Integrability through root degree and exchangeable escape fibers -/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

lemma bienaymeLaw_eq_sum_root (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    bienaymeLaw μ = Measure.sum fun k : ℕ =>
      μ {k} • (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k) := by
  have hdisj : Pairwise (fun i j => Disjoint {T : Tree | degree T = i} {T : Tree | degree T = j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun T hi hj => hij (hi.symm.trans hj)
  calc
    bienaymeLaw μ = (bienaymeLaw μ).restrict Set.univ := by simp
    _ = (bienaymeLaw μ).restrict (⋃ k : ℕ, {T | degree T = k}) := by
      congr 1
      ext T
      simp
    _ = Measure.sum fun k : ℕ => (bienaymeLaw μ).restrict {T | degree T = k} :=
      Measure.restrict_iUnion hdisj fun k => continuous_degree.measurable (measurableSet_singleton k)
    _ = _ := by
      apply congrArg Measure.sum
      funext k
      exact bienaymeLaw_restrict_degree k

lemma integrable_bienayme_root_of_summable (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {G : Tree → ℝ} (hGmeas : AEStronglyMeasurable G (bienaymeLaw μ))
    (hnode : ∀ k, μ {k} ≠ 0 → Integrable (fun ts => G (nodeFin k ts))
      (Measure.pi fun _ : Fin k => bienaymeLaw μ))
    (hsum : Summable fun k : ℕ => (μ {k}).toReal *
      ∫ ts, ‖G (nodeFin k ts)‖ ∂Measure.pi (fun _ : Fin k => bienaymeLaw μ)) :
    Integrable G (bienaymeLaw μ) := by
  have hlaw := bienaymeLaw_eq_sum_root μ
  rw [hlaw] at hGmeas ⊢
  apply integrable_sum_measure
  · intro k
    by_cases hk : μ {k} = 0
    · simp [hk]
    let ρ := (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k)
    have hs : AEStronglyMeasurable G (μ {k} • ρ) := hGmeas.mono_measure
      (Measure.le_sum (fun k : ℕ => μ {k} •
        (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k)) k)
    have hGρ : AEStronglyMeasurable G ρ :=
      ⟨hs.mk, hs.stronglyMeasurable_mk,
        by simpa only [Measure.ae_ennreal_smul_measure_eq hk] using hs.ae_eq_mk⟩
    have hmap : Integrable G ρ := by
      apply (integrable_map_measure hGρ (measurable_nodeFin k).aemeasurable).2
      simpa only [Function.comp_def] using hnode k hk
    exact hmap.smul_measure (measure_ne_top μ {k})
  · have heq (k : ℕ) :
        (∫ T, ‖G T‖ ∂(μ {k} • (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k))) =
          (μ {k}).toReal * ∫ ts, ‖G (nodeFin k ts)‖
            ∂Measure.pi (fun _ : Fin k => bienaymeLaw μ) := by
      by_cases hk : μ {k} = 0
      · simp [hk]
      rw [integral_smul_measure]
      let ρ := (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k)
      have hs : AEStronglyMeasurable G (μ {k} • ρ) := hGmeas.mono_measure
        (Measure.le_sum (fun k : ℕ => μ {k} •
          (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k)) k)
      have hGρ : AEStronglyMeasurable G ρ :=
        ⟨hs.mk, hs.stronglyMeasurable_mk,
          by simpa only [Measure.ae_ennreal_smul_measure_eq hk] using hs.ae_eq_mk⟩
      congr 1
      exact integral_map (measurable_nodeFin k).aemeasurable hGρ.norm
    simpa only [heq] using hsum

/-- Integrability on the reference law from the independent-offspring fibers.
The summability hypothesis is on the full fiber norms, not on norms of their
inner integrals. -/
lemma integrable_ref_of_fiber_summable (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (F : ℕ → ℝ → ℝ → ℝ)
    (hFb : ∀ k S, Measurable fun b => F k b S)
    (hFmeas : AEStronglyMeasurable
      (fun e => F (degree e.fwd) (escape l e.bwd) (childSum l e.fwd)) (ref μ l hl))
    (hinner : ∀ᵐ T ∂bienaymeLaw μ, Integrable
      (fun q : Tree × (ℕ → ℕ) => F (degree T) (escape l q.1) (childSum l T))
      ((bienaymeLaw μ) ⊗ₘ harm l hl))
    (hprod : ∀ k, μ {k} ≠ 0 → Integrable (fun b : ℝ × (Fin k → ℝ) => F k b.1 (∑ i, b.2 i))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)))
    (hsum : Summable fun k : ℕ => (μ {k}).toReal *
      ∫ q : ℝ × (Fin k → ℝ), ‖F k q.1 (∑ i, q.2 i)‖
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) :
    Integrable (fun e => F (degree e.fwd) (escape l e.bwd) (childSum l e.fwd)) (ref μ l hl) := by
  let backLaw := (bienaymeLaw μ) ⊗ₘ harm l hl
  let G : Tree → ℝ := fun T =>
    ∫ q : Tree × (ℕ → ℕ), ‖F (degree T) (escape l q.1) (childSum l T)‖ ∂backLaw
  have hback (T : Tree) : G T = ∫ b, ‖F (degree T) b (childSum l T)‖ ∂escLaw μ l := by
    dsimp only [G]
    have hfst : backLaw.map Prod.fst = bienaymeLaw μ := Measure.fst_compProd _ _
    calc
      _ = ∫ B : Tree, ‖F (degree T) (escape l B) (childSum l T)‖ ∂bienaymeLaw μ := by
        rw [← hfst]
        exact (integral_map measurable_fst.aemeasurable
          ((hFb (degree T) (childSum l T)).norm.comp (measurable_escape l)).aestronglyMeasurable).symm
      _ = _ := by
        rw [escLaw, integral_map (measurable_escape l).aemeasurable
          (hFb (degree T) (childSum l T)).norm.aestronglyMeasurable]
  have hGmeas : AEStronglyMeasurable G (bienaymeLaw μ) := by
    exact hFmeas.norm.integral_prod_right'
  have hnode (k : ℕ) (hk : μ {k} ≠ 0) : Integrable (fun ts => G (nodeFin k ts))
        (Measure.pi fun _ : Fin k => bienaymeLaw μ) := by
      let piEsc := Measure.pi fun _ : Fin k => escLaw μ l
      let H : (Fin k → ℝ) → ℝ := fun bs => ∫ b, ‖F k b (∑ i, bs i)‖ ∂escLaw μ l
      have hvec : (Measure.pi fun _ : Fin k => bienaymeLaw μ).map
          (fun ts i => escape l (ts i)) = piEsc := Measure.pi_map_pi fun _ => (measurable_escape l).aemeasurable
      have hH : Integrable H piEsc := (hprod k hk).integral_norm_prod_right
      have hmap : Integrable (H ∘ fun ts i => escape l (ts i))
          (Measure.pi fun _ : Fin k => bienaymeLaw μ) := by
        rw [← hvec] at hH
        exact hH.comp_measurable
          (Measurable.of_eval fun i => (measurable_escape l).comp (measurable_pi_apply i))
      apply hmap.congr
      filter_upwards with ts
      dsimp only [Function.comp_def, H]
      rw [hback, degree_nodeFin, childSum_nodeFin]
  have hGint : Integrable G (bienaymeLaw μ) := by
    apply integrable_bienayme_root_of_summable μ hGmeas hnode
    apply hsum.congr
    intro k
    by_cases hk : μ {k} = 0
    · simp [hk]
    symm
    congr 1
    let piEsc := Measure.pi fun _ : Fin k => escLaw μ l
    let H : (Fin k → ℝ) → ℝ := fun bs => ∫ b, ‖F k b (∑ i, bs i)‖ ∂escLaw μ l
    have hvec : (Measure.pi fun _ : Fin k => bienaymeLaw μ).map
        (fun ts i => escape l (ts i)) = piEsc := Measure.pi_map_pi fun _ => (measurable_escape l).aemeasurable
    have hH : AEStronglyMeasurable H piEsc := (hprod k hk).integral_norm_prod_right.aestronglyMeasurable
    calc
      (∫ ts, ‖G (nodeFin k ts)‖ ∂Measure.pi fun _ : Fin k => bienaymeLaw μ) =
          ∫ ts, G (nodeFin k ts) ∂Measure.pi fun _ : Fin k => bienaymeLaw μ := by
        apply integral_congr_ae
        filter_upwards with ts
        rw [Real.norm_of_nonneg]
        exact integral_nonneg fun _ => norm_nonneg _
      _ = ∫ ts, H (fun i => escape l (ts i)) ∂Measure.pi (fun _ : Fin k => bienaymeLaw μ) := by
        apply integral_congr_ae
        filter_upwards with ts
        dsimp only [H]
        rw [hback, degree_nodeFin, childSum_nodeFin]
      _ = ∫ bs, H bs ∂piEsc := by
        rw [← hvec] at hH ⊢
        exact (integral_map
          (Measurable.of_eval fun i => (measurable_escape l).comp (measurable_pi_apply i)).aemeasurable hH).symm
      _ = ∫ q : (Fin k → ℝ) × ℝ, ‖F k q.2 (∑ i, q.1 i)‖ ∂piEsc.prod (escLaw μ l) := by
        exact (integral_prod _ (hprod k hk).norm.swap).symm
      _ = _ := by
        simpa only [Prod.swap, piEsc] using
          (integral_prod_swap (μ := escLaw μ l) (ν := piEsc)
            (fun q : ℝ × (Fin k → ℝ) => ‖F k q.1 (∑ i, q.2 i)‖))
  exact (integrable_prod_iff hFmeas).2 ⟨hinner, hGint⟩


lemma Hfun_ge_sum {l : ℝ} {k : ℕ} {b : ℝ} {bs : Fin k → ℝ}
    (hb : GoodEsc l b) (hbs : ∀ i, GoodEsc l (bs i)) :
    (∑ i, bs i) ≤ Hfun l b (∑ i, bs i) := by
  have hb0 : 0 ≤ l - 1 + b := by
    by_cases hl : l < 1
    · linarith [hb.2.2 hl]
    · linarith [hb.1]
  unfold Hfun
  linarith

lemma integrable_sum_ratio (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ)
    {k : ℕ} (hk : k ≠ 0) :
    Integrable (fun q : ℝ × (Fin k → ℝ) => (∑ j, q.2 j) / Hfun l q.1 (∑ j, q.2 j))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) := by
  have hHm : Measurable (fun q : ℝ × (Fin k → ℝ) => Hfun l q.1 (∑ j, q.2 j)) :=
    (((measurable_const.sub measurable_const).add measurable_fst).add
      (Finset.univ.measurable_sum fun j _ => (measurable_pi_apply j).comp measurable_snd))
  apply (integrable_const (1 : ℝ)).mono
    ((Finset.univ.measurable_sum fun j _ => (measurable_pi_apply j).comp measurable_snd).div
      hHm).aestronglyMeasurable
  filter_upwards [ae_iid_good μ hl hμ hlm k] with q hq
  have hH := Hfun_pos hk hq.1 hq.2
  have hS0 : 0 ≤ ∑ j, q.2 j := Finset.sum_nonneg fun j _ => (hq.2 j).1.le
  change ‖(∑ j, q.2 j) / Hfun l q.1 (∑ j, q.2 j)‖ ≤ ‖(1 : ℝ)‖
  rw [Real.norm_eq_abs, norm_one, abs_div, abs_of_pos hH, abs_of_nonneg hS0]
  apply (div_le_iff₀ hH).2
  simpa using Hfun_ge_sum hq.1 hq.2

set_option maxHeartbeats 800000 in
/-- The degree coefficient `c` is integrable against the reference law whenever
`|c k| ≤ k + l`. No second-moment condition is used. -/
lemma integrable_C_ratio_ref (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ)
    (c : ℕ → ℝ) (hc : ∀ k, |c k| ≤ (k : ℝ) + l) :
    Integrable (fun e => c (degree e.fwd) * escape l e.bwd /
      Hfun l (escape l e.bwd) (childSum l e.fwd)) (ref μ l hl) := by
  let F : ℕ → ℝ → ℝ → ℝ := fun k b S => c k * b / Hfun l b S
  have hFb : ∀ k S, Measurable fun b => F k b S := by
    intro k S
    exact (measurable_const.mul measurable_id).div
      ((measurable_const.sub measurable_const).add measurable_id |>.add measurable_const)
  have hFmeas : AEStronglyMeasurable
      (fun e => F (degree e.fwd) (escape l e.bwd) (childSum l e.fwd)) (ref μ l hl) := by
    apply Measurable.aestronglyMeasurable
    exact (((measurable_of_countable c).comp
      (continuous_degree.measurable.comp measurable_fst)).mul
      ((measurable_escape l).comp (measurable_fst.comp measurable_snd))).div
      (((measurable_const.sub measurable_const).add
        ((measurable_escape l).comp (measurable_fst.comp measurable_snd))).add
        ((measurable_childSum l).comp measurable_fst))
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
    have hB : Integrable (fun b => c (degree T) * b / Hfun l b (childSum l T)) (escLaw μ l) := by
      apply (integrable_const |c (degree T)|).mono
        ((measurable_const.mul measurable_id).div
          ((measurable_const.sub measurable_const).add measurable_id |>.add
            measurable_const)).aestronglyMeasurable
      filter_upwards [ae_goodEsc μ hl hμ hlm] with b hb
      simpa [F, Hfun, Real.norm_eq_abs, childSum, abs_div, abs_mul] using
        (ratio_mono_bound hk hb hbs (C := |c (degree T)|) (abs_nonneg _))
    have hfst0 : ((bienaymeLaw μ) ⊗ₘ harm l hl).map Prod.fst = bienaymeLaw μ :=
      Measure.fst_compProd _ _
    have hfst : ((bienaymeLaw μ) ⊗ₘ harm l hl).map (escape l ∘ Prod.fst) = escLaw μ l := by
      rw [← Measure.map_map (measurable_escape l) measurable_fst, hfst0, escLaw]
    have hmap : Integrable (fun b => c (degree T) * b / Hfun l b (childSum l T))
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
    exact integrable_C_ratio μ hl hμ hlm hk0 (c k) |c k| (abs_nonneg _) le_rfl
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
      (f := fun k : ℕ => (1 + l) * (μ {k}).toReal) ?_ (hmass.mul_left (1 + l))
    intro k
    by_cases hk : k = 0
    · subst k
      simp [hμ.zero]
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hSint := integrable_sum_ratio μ hl hμ hlm hk
    have hS0 : 0 ≤ ∫ q : ℝ × (Fin k → ℝ), (∑ j, q.2 j) / Hfun l q.1 (∑ j, q.2 j)
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_iid_good μ hl hμ hlm k] with q hq
      exact div_nonneg (Finset.sum_nonneg fun j _ => (hq.2 j).1.le)
        (Hfun_pos hk hq.1 hq.2).le
    have hS1 : (∫ q : ℝ × (Fin k → ℝ), (∑ j, q.2 j) / Hfun l q.1 (∑ j, q.2 j)
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) ≤ 1 := by
      have hmono := integral_mono_ae hSint (integrable_const (1 : ℝ))
        (show (fun q : ℝ × (Fin k → ℝ) => (∑ j, q.2 j) / Hfun l q.1 (∑ j, q.2 j)) ≤ᵐ[
          (escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)] (fun _ => 1) by
          filter_upwards [ae_iid_good μ hl hμ hlm k] with q hq
          exact (div_le_one (Hfun_pos hk hq.1 hq.2)).mpr (Hfun_ge_sum hq.1 hq.2))
      simpa using hmono
    have hnorm : (∫ q : ℝ × (Fin k → ℝ), ‖F k q.1 (∑ i, q.2 i)‖
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) =
        |c k| * ∫ q : ℝ × (Fin k → ℝ), q.1 / Hfun l q.1 (∑ j, q.2 j)
          ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_iid_good μ hl hμ hlm k] with q hq
      dsimp only [F]
      have hH := Hfun_pos hk hq.1 hq.2
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hH, abs_of_pos hq.1.1]
      ring
    have hdeg := integral_degree_exchange μ hl hμ hlm hk
    simp_rw [mul_div_assoc, integral_const_mul] at hdeg
    have hck : |c k| / (k : ℝ) ≤ 1 + l := by
      apply (div_le_iff₀ hkpos).2
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      nlinarith [hc k, hl]
    have hbound : (∫ q : ℝ × (Fin k → ℝ), ‖F k q.1 (∑ i, q.2 i)‖
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) ≤ 1 + l := by
      rw [hnorm]
      calc
        |c k| * ∫ q : ℝ × (Fin k → ℝ), q.1 / Hfun l q.1 (∑ j, q.2 j)
            ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) =
            |c k| / (k : ℝ) * ∫ q : ℝ × (Fin k → ℝ),
              (∑ j, q.2 j) / Hfun l q.1 (∑ j, q.2 j)
                ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) := by
          rw [← hdeg]
          field_simp [ne_of_gt hkpos]
        _ ≤ |c k| / (k : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hS1 (div_nonneg (abs_nonneg _) hkpos.le)
        _ = |c k| / (k : ℝ) := mul_one _
        _ ≤ 1 + l := hck
    calc
      (μ {k}).toReal * ∫ q : ℝ × (Fin k → ℝ), ‖F k q.1 (∑ i, q.2 i)‖
          ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) ≤
          (μ {k}).toReal * (1 + l) :=
        mul_le_mul_of_nonneg_left hbound ENNReal.toReal_nonneg
      _ = (1 + l) * (μ {k}).toReal := mul_comm _ _
  exact integrable_ref_of_fiber_summable μ l hl F hFb hFmeas hinner hprod hsum

end LPPMonotonicityProof.Speed
