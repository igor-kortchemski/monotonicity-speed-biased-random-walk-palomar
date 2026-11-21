module

public import LPPMonotonicityProof.Speed.Signed.TwoCopy
public import LPPMonotonicityProof.Speed.Env.Swap
public import LPPMonotonicityProof.RTL.LocallyFinite.GenerationLaw
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod

/-! # The degree quotient in i.i.d. form

The degree quotient under the reference law is written with independent escapes
`(βᵢ)` independent of `ν`, as in equation (2.1) (`eq:aidekon`). -/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Bochner integration against the root decomposition of the Bienaymé law. -/
theorem integral_bienayme_root (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {G : Tree → ℝ} (hG : Integrable G (bienaymeLaw μ)) :
    ∫ T, G T ∂bienaymeLaw μ = ∑' k : ℕ, (μ {k}).toReal *
      ∫ ts, G (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => bienaymeLaw μ) := by
  have hdisj : Pairwise (fun i j => Disjoint {T : Tree | degree T = i} {T : Tree | degree T = j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun T hi hj => hij (hi.symm.trans hj)
  have hlaw : bienaymeLaw μ = Measure.sum fun k : ℕ =>
      μ {k} • (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k) := by
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
  have hsumint : Integrable G (Measure.sum fun k : ℕ =>
      μ {k} • (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k)) := hlaw ▸ hG
  calc
    _ = ∫ T, G T ∂Measure.sum (fun k : ℕ =>
        μ {k} • (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k)) := by rw [← hlaw]
    _ = ∑' k : ℕ, ∫ T, G T ∂(μ {k} •
        (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k)) :=
      integral_sum_measure hsumint
    _ = _ := by
      apply tsum_congr
      intro k
      by_cases hk : μ {k} = 0
      · simp [hk]
      let ρ := (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k)
      have hs : AEStronglyMeasurable G (μ {k} • ρ) :=
        hsumint.aestronglyMeasurable.mono_measure
          (show μ {k} • ρ ≤ Measure.sum (fun k : ℕ =>
            μ {k} • (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k)) from
            Measure.le_sum (fun k : ℕ => μ {k} •
              (Measure.pi fun _ : Fin k => bienaymeLaw μ).map (nodeFin k)) k)
      have hmap : AEStronglyMeasurable G ρ := by
        exact ⟨hs.mk, hs.stronglyMeasurable_mk,
          by simpa only [Measure.ae_ennreal_smul_measure_eq hk] using hs.ae_eq_mk⟩
      calc
        _ = (μ {k}).toReal * ∫ T, G T ∂ρ := by
          rw [integral_smul_measure]
          rfl
        _ = _ := by
          apply congrArg (fun x : ℝ => (μ {k}).toReal * x)
          exact integral_map (measurable_nodeFin k).aemeasurable hmap

lemma childSum_nodeFin (l : ℝ) (k : ℕ) (ts : Fin k → Tree) :
    childSum l (nodeFin k ts) = ∑ i, escape l (ts i) := by
  unfold childSum
  rw [degree_nodeFin]
  apply Finset.sum_congr rfl
  intro i _
  rw [children_nodeFin]

/-- **Independent form:** functions of the forward degree, backward escape, and forward
escape sum have independent-offspring form. The two integrability hypotheses
are exactly those needed for Fubini and the countable Bochner interchange. -/
theorem integral_ref_fwd_bwd (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (F : ℕ → ℝ → ℝ → ℝ)
    (hFb : ∀ k S, Measurable fun b => F k b S)
    (hFs : ∀ k b, Measurable fun bs : Fin k → ℝ => F k b (∑ i, bs i))
    (hFint : Integrable (fun e => F (degree e.fwd) (escape l e.bwd) (childSum l e.fwd))
      (ref μ l hl))
    (hprod : ∀ k, μ {k} ≠ 0 → Integrable (fun b : ℝ × (Fin k → ℝ) => F k b.1 (∑ i, b.2 i))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l))) :
    ∫ e, F (degree e.fwd) (escape l e.bwd) (childSum l e.fwd) ∂ref μ l hl =
      ∑' k, (μ {k}).toReal * ∫ b, F k b.1 (∑ i : Fin k, b.2 i)
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) := by
  let backLaw := (bienaymeLaw μ) ⊗ₘ harm l hl
  let G : Tree → ℝ := fun T =>
    ∫ q : Tree × (ℕ → ℕ), F (degree T) (escape l q.1) (childSum l T) ∂backLaw
  have hback (T : Tree) : G T = ∫ b, F (degree T) b (childSum l T) ∂escLaw μ l := by
    dsimp only [G]
    have hfst : backLaw.map Prod.fst = bienaymeLaw μ := by
      exact Measure.fst_compProd (bienaymeLaw μ) (harm l hl)
    calc
      _ = ∫ B : Tree, F (degree T) (escape l B) (childSum l T) ∂bienaymeLaw μ := by
        rw [← hfst]
        exact (integral_map measurable_fst.aemeasurable
          ((hFb (degree T) (childSum l T)).comp (measurable_escape l)).aestronglyMeasurable).symm
      _ = _ := by
        rw [escLaw, integral_map (measurable_escape l).aemeasurable
          (hFb (degree T) (childSum l T)).aestronglyMeasurable]
  have hG : Integrable G (bienaymeLaw μ) := by
    change Integrable (fun T : Tree => ∫ q, F (degree T) (escape l q.1) (childSum l T) ∂backLaw)
      (bienaymeLaw μ)
    exact hFint.integral_prod_left
  calc
    _ = ∫ T, G T ∂bienaymeLaw μ := by
      exact integral_prod _ hFint
    _ = ∑' k : ℕ, (μ {k}).toReal *
        ∫ ts, G (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => bienaymeLaw μ) :=
      integral_bienayme_root μ hG
    _ = _ := by
      apply tsum_congr
      intro k
      by_cases hk : μ {k} = 0
      · simp [hk]
      congr 1
      let piEsc := Measure.pi fun _ : Fin k => escLaw μ l
      let H : (Fin k → ℝ) → ℝ := fun bs => ∫ b, F k b (∑ i, bs i) ∂escLaw μ l
      have hvec : (Measure.pi fun _ : Fin k => bienaymeLaw μ).map
          (fun ts i => escape l (ts i)) = piEsc := by
        exact Measure.pi_map_pi fun _ => (measurable_escape l).aemeasurable
      have hH : AEStronglyMeasurable H piEsc := by
        exact (hprod k hk).aestronglyMeasurable.prod_swap.integral_prod_right'
      calc
        _ = ∫ ts, ∫ b, F k b (∑ i, escape l (ts i)) ∂escLaw μ l
            ∂Measure.pi (fun _ : Fin k => bienaymeLaw μ) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ts => by dsimp only; rw [hback, degree_nodeFin, childSum_nodeFin]
        _ = ∫ bs, H bs ∂piEsc := by
          rw [← hvec] at hH ⊢
          exact (integral_map
            (Measurable.of_eval fun i => (measurable_escape l).comp (measurable_pi_apply i)).aemeasurable hH).symm
        _ = ∫ q : (Fin k → ℝ) × ℝ, F k q.2 (∑ i, q.1 i) ∂piEsc.prod (escLaw μ l) := by
          exact (integral_prod _ (hprod k hk).swap).symm
        _ = _ := by
          simpa only [Prod.swap, piEsc] using
            (integral_prod_swap (μ := escLaw μ l) (ν := piEsc)
              (fun p : ℝ × (Fin k → ℝ) => F k p.1 (∑ i, p.2 i)))

end LPPMonotonicityProof.Speed
