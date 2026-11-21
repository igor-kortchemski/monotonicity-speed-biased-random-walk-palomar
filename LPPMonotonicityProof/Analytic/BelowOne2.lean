module

public import LPPMonotonicityProof.Analytic.BelowOne
public import LPPMonotonicityProof.Analytic.Interface2
public import LPPMonotonicityProof.Speed.Signed.Exchange
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Aïdékon root-drift comparison

This module proves the comparison `v(λ) ≤ E[(ν - λ)/(ν + λ)]` for `0 < λ ≤ 1`, from
the root-drift comparison in the proof of Theorem 2.7 (`thm:below-one`).  It decomposes
the Aïdékon expectations by root degree before splitting i.i.d. escape coordinates.
The weight is written both as `(k + l) E[b/H]` and as
`1 + (1-l) E[(1-b)/H]`: the first formula supplies integrability, the second
monotonicity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private lemma one_lt_mean_real_B1 (h : OffspringHyp μ) : 1 < mean μ :=
  (ENNReal.toReal_lt_toReal ENNReal.one_ne_top h.mean_lt_top.ne).2 h.one_lt_mean

private lemma ae_nat_one_le_B1' (h : OffspringHyp μ) : ∀ᵐ k : ℕ ∂μ, 1 ≤ k := by
  rw [ae_iff]
  have hs : {k : ℕ | ¬1 ≤ k} = {0} := by ext k; simp
  rw [hs]
  exact h.zero

private noncomputable def escapeRatio (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (k : ℕ) : ℝ :=
  ∫ q : ℝ × (Fin k → ℝ), q.1 / Hfun l q.1 (∑ i, q.2 i)
    ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)

private noncomputable def complementRatio (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (k : ℕ) : ℝ :=
  ∫ q : ℝ × (Fin k → ℝ), (1 - q.1) / Hfun l q.1 (∑ i, q.2 i)
    ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)

private noncomputable def aidWeight (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (k : ℕ) : ℝ :=
  1 + (1 - l) * complementRatio μ l k

private noncomputable def rootDrift (l x : ℝ) : ℝ := (x - l) / (x + l)

private lemma integrable_ratio_fiber (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) {k : ℕ} (hk : k ≠ 0) (c : ℝ) :
    Integrable (fun q : ℝ × (Fin k → ℝ) => c * q.1 / Hfun l q.1 (∑ i, q.2 i))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) := by
  exact integrable_C_ratio μ hl h hlm hk c |c| (abs_nonneg _) le_rfl

/-- Root decomposition of an Aïdékon expectation, with null-degree fibers discarded. -/
private lemma aidE_eq_tsum_B1 (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) (g : ℕ → ℝ) (hg : ∃ C, ∀ k, |g k| ≤ C * (k + 1))
    (hprod : ∀ k, μ {k} ≠ 0 → Integrable (fun q : ℝ × (Fin k → ℝ) =>
      g k * q.1 / Hfun l q.1 (∑ i, q.2 i))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l))) :
    aidE μ l g = ∑' k, (μ {k}).toReal * (g k * escapeRatio μ l k) := by
  have hint := integrable_aid h hl hlm g hg
  let G : Tree → ℝ := fun T => ∫ U, g (degree T) * escape l U /
    (l - 1 + escape l U + childSum l T) ∂GW μ
  calc
    aidE μ l g = ∫ T, G T ∂GW μ := integral_prod _ hint
    _ = ∑' k, (μ {k}).toReal * ∫ ts, G (nodeFin k ts)
        ∂Measure.pi (fun _ : Fin k => GW μ) := integral_GW_eq_tsum G hint.integral_prod_left
    _ = _ := by
      apply tsum_congr
      intro k
      by_cases hk : μ {k} = 0
      · simp [hk]
      let piEsc := Measure.pi fun _ : Fin k => escLaw μ l
      let H : (Fin k → ℝ) → ℝ := fun bs =>
        ∫ b, g k * b / Hfun l b (∑ i, bs i) ∂escLaw μ l
      have hvec : (Measure.pi fun _ : Fin k => GW μ).map
          (fun ts i => escape l (ts i)) = piEsc :=
        Measure.pi_map_pi fun _ => (measurable_escape l).aemeasurable
      have hH : AEStronglyMeasurable H piEsc :=
        (hprod k hk).aestronglyMeasurable.prod_swap.integral_prod_right'
      calc
        (μ {k}).toReal * ∫ ts, G (nodeFin k ts) ∂Measure.pi (fun _ : Fin k => GW μ) =
            (μ {k}).toReal * ∫ ts, H (fun i => escape l (ts i))
              ∂Measure.pi (fun _ : Fin k => GW μ) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with ts
          dsimp only [G, H]
          rw [degree_nodeFin, childSum_nodeFin, escLaw,
            integral_map (measurable_escape l).aemeasurable]
          · rfl
          · exact ((measurable_const.mul measurable_id).div
              (((measurable_const.sub measurable_const).add measurable_id).add
                measurable_const)).aestronglyMeasurable
        _ = (μ {k}).toReal * ∫ bs, H bs ∂piEsc := by
          rw [← hvec] at hH ⊢
          congr 1
          exact (integral_map
            (Measurable.of_eval fun i => (measurable_escape l).comp
              (measurable_pi_apply i)).aemeasurable hH).symm
        _ = (μ {k}).toReal * ∫ q : (Fin k → ℝ) × ℝ,
            g k * q.2 / Hfun l q.2 (∑ i, q.1 i) ∂piEsc.prod (escLaw μ l) := by
          congr 1
          exact (integral_prod _ (hprod k hk).swap).symm
        _ = _ := by
          congr 1
          simpa only [escapeRatio, ← integral_const_mul, mul_div_assoc, Prod.swap, piEsc] using
            (integral_prod_swap (μ := escLaw μ l) (ν := piEsc)
              (fun q : ℝ × (Fin k → ℝ) => g k * q.1 / Hfun l q.1 (∑ i, q.2 i)))

private lemma aidE_eq_tsum_of_growth (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hlm : l < mean μ) (g : ℕ → ℝ) (hg : ∃ C, ∀ k, |g k| ≤ C * (k + 1)) :
    aidE μ l g = ∑' k, (μ {k}).toReal * (g k * escapeRatio μ l k) := by
  apply aidE_eq_tsum_B1 h hl hlm g hg
  intro k hk
  have hk0 : k ≠ 0 := by
    intro hk0
    subst k
    exact hk h.zero
  exact integrable_ratio_fiber h hl hlm hk0 (g k)

private lemma integrable_inv_escLaw (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hl1 : l ≤ 1) : Integrable (fun b : ℝ => b⁻¹) (escLaw μ l) := by
  have hUn : 0 ≤ invMean μ := by
    apply integral_nonneg_of_ae
    exact ae_of_all _ fun k => inv_nonneg.mpr (Nat.cast_nonneg k)
  have hU : l * invMean μ < 1 := by
    calc
      l * invMean μ ≤ 1 * invMean μ := mul_le_mul_of_nonneg_right hl1 hUn
      _ = invMean μ := one_mul _
      _ < 1 := (invMean_bounds h).2
  obtain ⟨_, hint⟩ := integrable_inv_escape h hl hU
  rw [escLaw]
  exact (integrable_map_measure measurable_id.inv.aestronglyMeasurable
    (measurable_escape l).aemeasurable).2 hint

private lemma integrable_complement_fiber (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hl1 : l ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    Integrable (fun q : ℝ × (Fin k → ℝ) => (1 - q.1) / Hfun l q.1 (∑ i, q.2 i))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) := by
  have hlm : l < mean μ := hl1.trans_lt (one_lt_mean_real_B1 h)
  have hHm : Measurable (fun q : ℝ × (Fin k → ℝ) => Hfun l q.1 (∑ i, q.2 i)) :=
    (((measurable_const.sub measurable_const).add measurable_fst).add
      (Finset.univ.measurable_sum fun i _ => (measurable_pi_apply i).comp measurable_snd))
  apply ((integrable_inv_escLaw h hl hl1).comp_fst
    (Measure.pi fun _ : Fin k => escLaw μ l)).mono
    ((measurable_const.sub measurable_fst).div hHm).aestronglyMeasurable
  filter_upwards [ae_iid_good μ hl h hlm k] with q hq
  have hH := Hfun_pos hk hq.1 hq.2
  have hbH := Hfun_ge_b hk hq.1 hq.2
  have hnum : 0 ≤ 1 - q.1 := sub_nonneg.mpr hq.1.2.1.le
  change |(1 - q.1) / Hfun l q.1 (∑ i, q.2 i)| ≤ |q.1⁻¹|
  rw [abs_div, abs_of_pos hH, abs_of_nonneg hnum,
    abs_of_pos (inv_pos.mpr hq.1.1)]
  apply (div_le_iff₀ hH).2
  calc
    1 - q.1 ≤ 1 := by linarith [hq.1.1]
    _ = q.1⁻¹ * q.1 := (inv_mul_cancel₀ hq.1.1.ne').symm
    _ ≤ q.1⁻¹ * Hfun l q.1 (∑ i, q.2 i) :=
      mul_le_mul_of_nonneg_left hbH (inv_nonneg.mpr hq.1.1.le)

private lemma weight_eq_ratio_B1 (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hl1 : l ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    aidWeight μ l k = ((k : ℝ) + l) * escapeRatio μ l k := by
  have hlm : l < mean μ := hl1.trans_lt (one_lt_mean_real_B1 h)
  let ρ := (escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)
  let R : (ℝ × (Fin k → ℝ)) → ℝ := fun q => q.1 / Hfun l q.1 (∑ i, q.2 i)
  let S : (ℝ × (Fin k → ℝ)) → ℝ := fun q => (∑ i, q.2 i) / Hfun l q.1 (∑ i, q.2 i)
  let C : (ℝ × (Fin k → ℝ)) → ℝ := fun q => (1 - q.1) / Hfun l q.1 (∑ i, q.2 i)
  have hRi : Integrable R ρ := integrable_ratio_fiber h hl hlm hk 1 |>.congr
    (ae_of_all _ fun q => by simp [R])
  have hSi : Integrable S ρ := integrable_sum_ratio μ hl h hlm hk
  have hCi : Integrable C ρ := integrable_complement_fiber h hl hl1 hk
  have hex : (k : ℝ) * escapeRatio μ l k = ∫ q, S q ∂ρ := by
    simpa only [escapeRatio, R, S, ρ, mul_div_assoc, integral_const_mul] using
      integral_degree_exchange μ hl h hlm hk
  change (k : ℝ) * (∫ q, R q ∂ρ) = ∫ q, S q ∂ρ at hex
  change 1 + (1 - l) * ∫ q, C q ∂ρ = ((k : ℝ) + l) * ∫ q, R q ∂ρ
  calc
    1 + (1 - l) * ∫ q, C q ∂ρ = ∫ q, (1 + (1 - l) * C q) ∂ρ := by
      rw [integral_add (integrable_const 1) (hCi.const_mul (1 - l)), integral_const_mul,
        integral_const, probReal_univ, one_smul]
    _ = ∫ q, (S q + l * R q) ∂ρ := by
      apply integral_congr_ae
      filter_upwards [ae_iid_good μ hl h hlm k] with q hq
      have hH := Hfun_pos hk hq.1 hq.2
      dsimp only [R, S, C]
      field_simp [hH.ne']
      dsimp only [Hfun]
      ring
    _ = (∫ q, S q ∂ρ) + l * ∫ q, R q ∂ρ := by
      rw [integral_add hSi (hRi.const_mul l), integral_const_mul]
    _ = (k : ℝ) * (∫ q, R q ∂ρ) + l * ∫ q, R q ∂ρ := by rw [← hex]
    _ = ((k : ℝ) + l) * ∫ q, R q ∂ρ := by ring

private lemma weight_mem_B1 (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hl1 : l ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    0 ≤ aidWeight μ l k ∧ aidWeight μ l k ≤ 1 + l := by
  have hlm : l < mean μ := hl1.trans_lt (one_lt_mean_real_B1 h)
  let ρ := (escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)
  let R : (ℝ × (Fin k → ℝ)) → ℝ := fun q => q.1 / Hfun l q.1 (∑ i, q.2 i)
  let S : (ℝ × (Fin k → ℝ)) → ℝ := fun q => (∑ i, q.2 i) / Hfun l q.1 (∑ i, q.2 i)
  have hRi : Integrable R ρ := integrable_ratio_fiber h hl hlm hk 1 |>.congr
    (ae_of_all _ fun q => by simp [R])
  have hSi : Integrable S ρ := integrable_sum_ratio μ hl h hlm hk
  have hSnonneg : 0 ≤ ∫ q, S q ∂ρ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_iid_good μ hl h hlm k] with q hq
    exact div_nonneg (Finset.sum_nonneg fun i _ => (hq.2 i).1.le)
      (Hfun_pos hk hq.1 hq.2).le
  have hSle : (∫ q, S q ∂ρ) ≤ 1 := by
    have hle := integral_mono_ae hSi (integrable_const 1)
      (show S ≤ᵐ[ρ] fun _ => 1 by
        filter_upwards [ae_iid_good μ hl h hlm k] with q hq
        exact (div_le_one (Hfun_pos hk hq.1 hq.2)).mpr (Hfun_ge_sum hq.1 hq.2))
    simpa using hle
  have hex : (k : ℝ) * escapeRatio μ l k = ∫ q, S q ∂ρ := by
    simpa only [escapeRatio, R, S, ρ, mul_div_assoc, integral_const_mul] using
      integral_degree_exchange μ hl h hlm hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hRnonneg : 0 ≤ escapeRatio μ l k := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_iid_good μ hl h hlm k] with q hq
    exact div_nonneg hq.1.1.le (Hfun_pos hk hq.1 hq.2).le
  have hRle : escapeRatio μ l k ≤ (k : ℝ)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hkpos).2
    rw [mul_comm]
    exact hex.le.trans hSle
  have hlR : l * escapeRatio μ l k ≤ l := by
    calc
      l * escapeRatio μ l k ≤ l * (k : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hRle hl.le
      _ ≤ l * 1 := mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hkone) hl.le
      _ = l := mul_one _
  rw [weight_eq_ratio_B1 h hl hl1 hk]
  constructor
  · exact mul_nonneg (by positivity) hRnonneg
  · calc
      ((k : ℝ) + l) * escapeRatio μ l k =
          (k : ℝ) * escapeRatio μ l k + l * escapeRatio μ l k := by ring
      _ = (∫ q, S q ∂ρ) + l * escapeRatio μ l k := by rw [hex]
      _ ≤ 1 + l := add_le_add hSle hlR

private lemma measurePreserving_dropLast_B1 {l : ℝ} (k : ℕ) :
    MeasurePreserving
      (fun q : ℝ × (Fin (k + 1) → ℝ) => (q.1, Fin.init q.2))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin (k + 1) => escLaw μ l))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) := by
  have hlast := measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => escLaw μ l) (Fin.last k)
  have hinit : MeasurePreserving (fun x : Fin (k + 1) → ℝ => Fin.init x)
      (Measure.pi fun _ : Fin (k + 1) => escLaw μ l)
      (Measure.pi fun _ : Fin k => escLaw μ l) := by
    have hcomp := (measurePreserving_snd (μ := escLaw μ l)
      (ν := Measure.pi fun _ : Fin k => escLaw μ l)).comp hlast
    have hfun : (fun x : Fin (k + 1) → ℝ => Fin.init x) =
        Prod.snd ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ)
          (Fin.last k)) := by
      funext x
      change Fin.init x = (Fin.last k).removeNth x
      exact (Fin.removeNth_last x).symm
    rw [hfun]
    exact hcomp
  have hfun : (fun q : ℝ × (Fin (k + 1) → ℝ) => (q.1, Fin.init q.2)) =
      Prod.map id (fun x : Fin (k + 1) → ℝ => Fin.init x) := by
    funext q
    rcases q with ⟨b, bs⟩
    rfl
  rw [hfun]
  exact (MeasurePreserving.id (escLaw μ l)).prod hinit

private lemma complementRatio_succ_le_B1 (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hl1 : l ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    complementRatio μ l (k + 1) ≤ complementRatio μ l k := by
  have hlm : l < mean μ := hl1.trans_lt (one_lt_mean_real_B1 h)
  let Cbig : (ℝ × (Fin (k + 1) → ℝ)) → ℝ := fun q =>
    (1 - q.1) / Hfun l q.1 (∑ i, q.2 i)
  let Csmall : (ℝ × (Fin k → ℝ)) → ℝ := fun q =>
    (1 - q.1) / Hfun l q.1 (∑ i, q.2 i)
  have hdrop := measurePreserving_dropLast_B1 (μ := μ) (l := l) k
  have hbig : Integrable Cbig
      ((escLaw μ l).prod (Measure.pi fun _ : Fin (k + 1) => escLaw μ l)) :=
    integrable_complement_fiber h hl hl1 (Nat.succ_ne_zero k)
  have hsmall : Integrable Csmall
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) :=
    integrable_complement_fiber h hl hl1 hk
  change (∫ q, Cbig q ∂(escLaw μ l).prod
      (Measure.pi fun _ : Fin (k + 1) => escLaw μ l)) ≤
    ∫ q, Csmall q ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)
  have hmeas : AEStronglyMeasurable Csmall
      (Measure.map (fun q : ℝ × (Fin (k + 1) → ℝ) => (q.1, Fin.init q.2))
        ((escLaw μ l).prod (Measure.pi fun _ : Fin (k + 1) => escLaw μ l))) := by
    rw [hdrop.map_eq]
    exact hsmall.aestronglyMeasurable
  have heq : (∫ q, Csmall (q.1, Fin.init q.2) ∂(escLaw μ l).prod
      (Measure.pi fun _ : Fin (k + 1) => escLaw μ l)) =
      ∫ q, Csmall q ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) := by
    calc
      _ = ∫ q, Csmall q ∂Measure.map (fun q : ℝ × (Fin (k + 1) → ℝ) =>
          (q.1, Fin.init q.2)) ((escLaw μ l).prod
            (Measure.pi fun _ : Fin (k + 1) => escLaw μ l)) :=
        (integral_map hdrop.measurable.aemeasurable hmeas).symm
      _ = _ := by rw [hdrop.map_eq]
  rw [← heq]
  apply integral_mono_ae hbig (hdrop.integrable_comp_of_integrable hsmall)
  filter_upwards [ae_iid_good μ hl h hlm (k + 1)] with q hq
  have hgoodSmall : GoodEsc l q.1 ∧ ∀ i : Fin k, GoodEsc l (q.2 i.castSucc) :=
    ⟨hq.1, fun i => hq.2 i.castSucc⟩
  have hHbig := Hfun_pos (Nat.succ_ne_zero k) hq.1 hq.2
  have hHsmall := Hfun_pos hk hgoodSmall.1 hgoodSmall.2
  have hsum : (∑ i : Fin (k + 1), q.2 i) =
      (∑ i : Fin k, q.2 i.castSucc) + q.2 (Fin.last k) := Fin.sum_univ_castSucc _
  have hden : Hfun l q.1 (∑ i : Fin k, q.2 i.castSucc) ≤
      Hfun l q.1 (∑ i : Fin (k + 1), q.2 i) := by
    rw [hsum]
    change l - 1 + q.1 + (∑ i : Fin k, q.2 i.castSucc) ≤
      l - 1 + q.1 + ((∑ i : Fin k, q.2 i.castSucc) + q.2 (Fin.last k))
    linarith [(hq.2 (Fin.last k)).1]
  change (1 - q.1) / Hfun l q.1 (∑ i : Fin (k + 1), q.2 i) ≤
    (1 - q.1) / Hfun l q.1 (∑ i : Fin k, q.2 i.castSucc)
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr hq.1.2.1.le) hHsmall hden

private lemma aidWeight_antitone_B1 (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hl1 : l ≤ 1) : AntitoneOn (aidWeight μ l) (Set.Ici 1) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro k hk
  have hk0 : k ≠ 0 := by omega
  have hc := complementRatio_succ_le_B1 h hl hl1 hk0
  have hcoef : 0 ≤ 1 - l := sub_nonneg.mpr hl1
  dsimp only [aidWeight]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hc hcoef) 1

private lemma rootDrift_monotone_B1 {l : ℝ} (hl : 0 < l) :
    MonotoneOn (rootDrift l) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx1 : (1 : ℝ) ≤ x := hx
  have hy1 : (1 : ℝ) ≤ y := hy
  have hxp : 0 < x + l := by linarith
  have hyp : 0 < y + l := by linarith
  apply (div_le_div_iff₀ hxp hyp).2
  nlinarith

private lemma integrable_rootDrift_B1 {l : ℝ} (hl : 0 < l) :
    Integrable (fun k : ℕ => rootDrift l k) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  filter_upwards with k
  have hp : 0 < (k : ℝ) + l := by positivity
  rw [Real.norm_eq_abs, rootDrift, abs_div, abs_of_pos hp]
  apply (div_le_one hp).2
  rw [abs_le]
  constructor <;> linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]

private lemma integrable_weight_B1 (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hl1 : l ≤ 1) : Integrable (aidWeight μ l) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (1 + l)
  filter_upwards [ae_nat_one_le_B1' h] with k hk
  have hk0 : k ≠ 0 := by omega
  obtain ⟨hw0, hw1⟩ := weight_mem_B1 h hl hl1 hk0
  rw [Real.norm_eq_abs, abs_of_nonneg hw0]
  exact hw1

private lemma integrable_drift_weight_B1 (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (hl1 : l ≤ 1) : Integrable (fun k : ℕ => rootDrift l k * aidWeight μ l k) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (1 + l)
  filter_upwards [ae_nat_one_le_B1' h] with k hk
  have hk0 : k ≠ 0 := by omega
  obtain ⟨hw0, hw1⟩ := weight_mem_B1 h hl hl1 hk0
  have hp : 0 < (k : ℝ) + l := by positivity
  have hd : |rootDrift l k| ≤ 1 := by
    rw [rootDrift, abs_div, abs_of_pos hp]
    apply (div_le_one hp).2
    rw [abs_le]
    constructor <;> linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |rootDrift l k| * |aidWeight μ l k| ≤ 1 * (1 + l) := by
      apply mul_le_mul hd (by simpa [abs_of_nonneg hw0] using hw1) (abs_nonneg _) (by linarith)
    _ = 1 + l := one_mul _

private lemma aidE_minus_eq_integral_B1 (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hl1 : l ≤ 1) :
    aidE μ l (fun k => (k : ℝ) - l) = ∫ k, rootDrift l k * aidWeight μ l k ∂μ := by
  have hlm : l < mean μ := hl1.trans_lt (one_lt_mean_real_B1 h)
  rw [aidE_eq_tsum_of_growth h hl hlm _ ⟨1, fun k => by
    rw [abs_le]
    constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]⟩,
    integral_countable (integrable_drift_weight_B1 h hl hl1)]
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · subst k
    simp [Measure.real, h.zero]
  have hden : (k : ℝ) + l ≠ 0 := by positivity
  rw [weight_eq_ratio_B1 h hl hl1 hk]
  simp only [Measure.real, rootDrift, smul_eq_mul]
  field_simp [hden]

private lemma aidE_plus_eq_integral_B1 (h : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hl1 : l ≤ 1) :
    aidE μ l (fun k => (k : ℝ) + l) = ∫ k, aidWeight μ l k ∂μ := by
  have hlm : l < mean μ := hl1.trans_lt (one_lt_mean_real_B1 h)
  rw [aidE_eq_tsum_of_growth h hl hlm _ ⟨2, fun k => by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + l)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]⟩,
    integral_countable (integrable_weight_B1 h hl hl1)]
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · subst k
    simp [Measure.real, h.zero]
  rw [weight_eq_ratio_B1 h hl hl1 hk]
  simp only [Measure.real, smul_eq_mul]

/-- **Root-drift comparison** (proof of Theorem 2.7). The speed is at most the expected
drift at the root for every `0 < l ≤ 1`. -/
theorem speed_le_mean_drift (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    Speed.speedValue μ l ≤ ∫ k, ((k : ℝ) - l) / (k + l) ∂μ := by
  have hlm : l < mean μ := hl1.trans_lt (one_lt_mean_real_B1 h)
  let Z : ℕ → ℝ := fun k => k
  let W : ℝ → ℝ := fun x => aidWeight μ l ⌊x⌋₊
  have hZ : ∀ᵐ k ∂μ, Z k ∈ Set.Ici (1 : ℝ) := by
    filter_upwards [ae_nat_one_le_B1' h] with k hk
    change (1 : ℝ) ≤ (k : ℝ)
    exact_mod_cast hk
  have hW : AntitoneOn W (Set.Ici 1) := by
    intro x hx y hy hxy
    have hx1 : (1 : ℝ) ≤ x := by change (1 : ℝ) ≤ x at hx; exact hx
    have hy1 : (1 : ℝ) ≤ y := by change (1 : ℝ) ≤ y at hy; exact hy
    have hx' : ((1 : ℕ) : ℝ) ≤ x := by simpa only [Nat.cast_one] using hx1
    have hy' : ((1 : ℕ) : ℝ) ≤ y := by simpa only [Nat.cast_one] using hy1
    apply aidWeight_antitone_B1 h hl hl1
    · exact Nat.le_floor hx'
    · exact Nat.le_floor hy'
    · exact Nat.floor_mono hxy
  have hcov := integral_mul_le_of_monotone_antitone (P := μ) (Z := Z)
    (Set.Ici (1 : ℝ)) hZ (rootDrift_monotone_B1 hl) hW
    (by simpa only [Function.comp_def, Z] using integrable_rootDrift_B1 (μ := μ) hl)
    (by simpa only [Function.comp_def, W, Z, Nat.floor_natCast] using integrable_weight_B1 h hl hl1)
    (by simpa only [rootDrift, Z, W, Nat.floor_natCast] using integrable_drift_weight_B1 h hl hl1)
  simp only [Z, W, Nat.floor_natCast] at hcov
  rw [← aidE_minus_eq_integral_B1 h hl hl1, ← aidE_plus_eq_integral_B1 h hl hl1] at hcov
  simp only [rootDrift] at hcov
  rw [show Speed.speedValue μ l = speedValueProv μ l from rfl,
    speedValue_eq_aid h hl hlm]
  apply (div_le_iff₀ (aidE_pos h hl hlm)).2
  simpa only [rootDrift] using hcov

end LPPMonotonicityProof.Analytic
