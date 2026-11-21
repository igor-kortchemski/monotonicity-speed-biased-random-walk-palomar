module

public import LPPMonotonicityProof.Speed.Escape.Energy
public import LPPMonotonicityProof.Speed.Interface.Leafless
public import LPPMonotonicityProof.Speed.Interface.Escape
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Tactic.Linarith

/-!
# Positive mean escape from capped-flow energy

This module proves that the mean escape is positive, a step of the direct proof of
Lemma 2.1(iv) (`lem:escape`).  The finite-horizon estimate uses the capped second
moment only.  A bounded dominated-convergence argument passes to `escapeRaw`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- Nonnegativity of finite escape, exposed for expectation and limit arguments. -/
theorem escapeN_nonneg' (ω : Offspring) {l : ℝ} (hl : 0 < l) :
    ∀ (N : ℕ) (v : Address), 0 ≤ escapeN ω l N v := by
  intro N
  induction N with
  | zero => intro v; simp [escapeN]
  | succ N ih =>
      intro v
      rw [escapeN]
      apply div_nonneg
      · exact Finset.sum_nonneg fun i _ => ih (offChild ω v i)
      · have hS : 0 ≤ ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i) :=
          Finset.sum_nonneg fun i _ => ih (offChild ω v i)
        positivity

/-- Finite escape at a fixed address depends measurably on the raw field. -/
theorem measurable_escapeN (l : ℝ) : ∀ (N : ℕ) (v : Address),
    Measurable (fun ω => escapeN ω l N v) := by
  intro N
  induction N with
  | zero => intro v; simp [escapeN]
  | succ N ih =>
      intro v
      have h : Measurable (fun p : ℕ × Offspring =>
          ∑ j ∈ Finset.range p.1, escapeN p.2 l N (v ++ [j + 1])) :=
        measurable_from_prod_countable_right fun k =>
          (Finset.range k).measurable_sum fun j _ => ih (v ++ [j + 1])
      have hc : Measurable (fun ω => ∑ j ∈ Finset.range (ω v),
          escapeN ω l N (v ++ [j + 1])) := by
        simpa only [Function.comp_def] using
          h.comp (f := fun ω => (ω v, ω)) ((measurable_pi_apply v).prodMk measurable_id)
      have hS : Measurable (fun ω => ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i)) := by
        convert hc using 1
        ext ω
        simpa only [offChild] using
          (Fin.sum_univ_eq_sum_range (fun j => escapeN ω l N (v ++ [j + 1])) (ω v))
      change Measurable (fun ω => (∑ i : Fin (ω v), escapeN ω l N (offChild ω v i)) /
        (l + ∑ i : Fin (ω v), escapeN ω l N (offChild ω v i)))
      exact hS.div (measurable_const.add hS)

/-- Finite escape is integrable because it is bounded between zero and one. -/
theorem integrable_escapeN {l : ℝ} (hl : 0 < l) (N : ℕ) (v : Address) :
    Integrable (fun ω => escapeN ω l N v) (offspringFieldLaw μ) := by
  refine ⟨(measurable_escapeN l N v).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 1) ?_⟩
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (escapeN_nonneg' ω hl N v)]
  exact escapeN_le_one ω hl N v

/-- Every capped generation size has real first moment `b ^ j`. -/
theorem integral_capZ (B : ℕ) (j : ℕ) :
    (∫ ω, (capZ B ω [] j : ℝ) ∂offspringFieldLaw μ) = cappedMeanReal μ B ^ j := by
  have hm : Measurable (fun ω => (capZ B ω [] j : ℝ≥0∞)) :=
    (show Measurable (fun n : ℕ => (n : ℝ≥0∞)) by fun_prop).comp (measurable_capZ B [] j)
  change (∫ ω, (capZ B ω [] j : ℝ≥0∞).toReal ∂offspringFieldLaw μ) = cappedMeanReal μ B ^ j
  rw [integral_toReal hm.aemeasurable (by simp), lintegral_capZ,
    cappedMeanReal, ENNReal.toReal_pow]

/-- The capped flow at the root has unit expectation whenever `0 < b`. -/
theorem integral_capFlow_root (B : ℕ) {b : ℝ} (hb : b = cappedMeanReal μ B)
    (hb0 : 0 < b) (N : ℕ) :
    (∫ ω, capFlow B b ω N [] ∂offspringFieldLaw μ) = 1 := by
  subst b
  have hroot (ω : Offspring) : capFlow B (cappedMeanReal μ B) ω N [] = (cappedMeanReal μ B)⁻¹ ^ N * capZ B ω [] N := by
    have hz : ([] : Address) ∈ capGen B ω [] 0 := by
      apply (mem_capGen_root B ω [] 0).2
      exact ⟨present_nil _, by simp⟩
    rw [capFlow, List.length_nil, Nat.sub_zero, ite_eq_left hz]
  simp_rw [hroot]
  rw [integral_const_mul, integral_capZ, inv_pow, inv_mul_cancel₀ (pow_ne_zero N hb0.ne')]

/-- The capped root flow is uniformly bounded, hence integrable for `0 < b`. -/
theorem integrable_capFlow_root (B : ℕ) {b : ℝ} (hb : 0 < b) (N : ℕ) :
    Integrable (fun ω => capFlow B b ω N []) (offspringFieldLaw μ) := by
  have hroot (ω : Offspring) : capFlow B b ω N [] = b⁻¹ ^ N * capZ B ω [] N := by
    have hz : ([] : Address) ∈ capGen B ω [] 0 := by
      apply (mem_capGen_root B ω [] 0).2
      exact ⟨present_nil _, by simp⟩
    rw [capFlow, List.length_nil, Nat.sub_zero, ite_eq_left hz]
  refine ⟨(measurable_capFlow B b N []).aestronglyMeasurable, HasFiniteIntegral.of_bounded
    (C := b⁻¹ ^ N * (B ^ N : ℝ)) ?_⟩
  filter_upwards with ω
  rw [hroot, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))]
  gcongr
  exact_mod_cast capZ_le B ω [] N

/-- Finiteness supplied by `lintegral_energy` gives integrability of the real energy. -/
theorem integrable_energy (B : ℕ) {b l : ℝ} (hb : b = cappedMeanReal μ B)
    (hb1 : 1 < b) (hl : 0 < l) (hlb : l < b) (N : ℕ) :
    Integrable (fun ω => energy B b l ω N) (offspringFieldLaw μ) := by
  have hbound := lintegral_energy (μ := μ) B hb hb1 hl hlb N
  apply (lintegral_ofReal_ne_top_iff_integrable (measurable_energy B b l N).aestronglyMeasurable
    (ae_of_all _ fun ω => energy_nonneg B b hl.le ω N)).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound

/-- Real-integral form of the expected energy bound `lintegral_energy`. -/
theorem integral_energy_le (B : ℕ) {b l : ℝ} (hb : b = cappedMeanReal μ B)
    (hb1 : 1 < b) (hl : 0 < l) (hlb : l < b) (N : ℕ) :
    (∫ ω, energy B b l ω N ∂offspringFieldLaw μ) ≤ cappedMomentBound μ B / (1 - l / b) := by
  have hbound := lintegral_energy (μ := μ) B hb hb1 hl hlb N
  have hi := integrable_energy (μ := μ) B hb hb1 hl hlb N
  have hnonneg : 0 ≤ᵐ[offspringFieldLaw μ] fun ω => energy B b l ω N :=
    ae_of_all _ fun ω => energy_nonneg B b hl.le ω N
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg] at hbound
  apply (ENNReal.ofReal_le_ofReal_iff ?_).mp hbound
  have hC : 0 ≤ cappedMomentBound μ B := zero_le_one.trans
    (one_le_cappedMomentBound (μ := μ) (by rwa [← hb]))
  exact div_nonneg hC (sub_pos.mpr (div_lt_one (zero_lt_one.trans hb1) |>.2 hlb) |>.le)

private theorem le_amgm_of_sq_le {F β E t : ℝ} (hF : 0 ≤ F) (hβ : 0 ≤ β)
    (hE : 0 ≤ E) (ht : 0 < t) (hsq : F ^ 2 ≤ β * E) :
    F ≤ (t * β + E / t) / 2 := by
  have hsum : 0 ≤ t * β + E / t := by positivity
  apply (sq_le_sq₀ hF (by positivity : 0 ≤ (t * β + E / t) / 2)).mp
  have htE : t * (E / t) = E := by field_simp [ht.ne']
  nlinarith [sq_nonneg (t * β - E / t)]

/-- **Finite horizon.** The capped finite-flow inequality and the expected
energy bound give a uniform lower bound on mean finite escape. -/
theorem integral_escapeN_ge (hμ : OffspringHyp μ) (B : ℕ) {b l : ℝ}
    (hb : b = cappedMeanReal μ B) (hb1 : 1 < b) (hl : 0 < l) (hlb : l < b) (N : ℕ) :
    (1 - l / b) / cappedMomentBound μ B ≤
      ∫ ω, escapeN ω l N [] ∂offspringFieldLaw μ := by
  subst b
  let C : ℝ := cappedMomentBound μ B
  let d : ℝ := 1 - l / cappedMeanReal μ B
  let t : ℝ := C / d
  let A : ℝ := ∫ ω, escapeN ω l N [] ∂offspringFieldLaw μ
  let I : ℝ := ∫ ω, energy B (cappedMeanReal μ B) l ω N ∂offspringFieldLaw μ
  have hb0 : 0 < cappedMeanReal μ B := zero_lt_one.trans hb1
  have hd : 0 < d := sub_pos.mpr ((div_lt_one hb0).2 hlb)
  have hC : 1 ≤ C := one_le_cappedMomentBound (μ := μ) hb1
  have ht : 0 < t := div_pos (zero_lt_one.trans_le hC) hd
  have hAint : Integrable (fun ω => escapeN ω l N []) (offspringFieldLaw μ) :=
    integrable_escapeN hl N []
  have hIint : Integrable (fun ω => energy B (cappedMeanReal μ B) l ω N)
      (offspringFieldLaw μ) := integrable_energy B rfl hb1 hl hlb N
  have hFIint : Integrable (fun ω => capFlow B (cappedMeanReal μ B) ω N [])
      (offspringFieldLaw μ) := integrable_capFlow_root B hb0 N
  have htAint : Integrable (fun ω => t * escapeN ω l N []) (offspringFieldLaw μ) :=
    hAint.const_mul t
  have hItint : Integrable (fun ω => energy B (cappedMeanReal μ B) l ω N / t)
      (offspringFieldLaw μ) := by
    simpa [div_eq_mul_inv] using hIint.mul_const t⁻¹
  have hRHSint : Integrable (fun ω =>
      (t * escapeN ω l N [] + energy B (cappedMeanReal μ B) l ω N / t) / 2)
      (offspringFieldLaw μ) := by
    simpa [div_eq_mul_inv] using (htAint.add hItint).mul_const (2 : ℝ)⁻¹
  have hpoint : ∀ᵐ ω ∂offspringFieldLaw μ,
      capFlow B (cappedMeanReal μ B) ω N [] ≤
        (t * escapeN ω l N [] + energy B (cappedMeanReal μ B) l ω N / t) / 2 := by
    filter_upwards [ae_offspring_pos μ hμ.zero] with ω hω
    apply le_amgm_of_sq_le
      (mul_nonneg (by positivity) (Nat.cast_nonneg _))
      (escapeN_nonneg' ω hl N [])
      (energy_nonneg B (cappedMeanReal μ B) hl.le ω N) ht
    exact finite_flow_iterated ω hl N [] (leaflessBelow_of hω N [])
      (fun w => capFlow B (cappedMeanReal μ B) ω N w) (flow_conservation B (cappedMeanReal μ B) ω N)
  have hAM : 1 ≤ (t * A + I / t) / 2 := by
    calc
      1 = ∫ ω, capFlow B (cappedMeanReal μ B) ω N [] ∂offspringFieldLaw μ :=
        (integral_capFlow_root B rfl hb0 N).symm
      _ ≤ ∫ ω, (t * escapeN ω l N [] + energy B (cappedMeanReal μ B) l ω N / t) / 2
          ∂offspringFieldLaw μ := integral_mono_ae hFIint hRHSint hpoint
      _ = (t * A + I / t) / 2 := by
        rw [integral_div, integral_add htAint hItint]
        simp only [integral_div, integral_const_mul, A, I]
  have hI : I ≤ t := by
    dsimp only [I, t, d, C]
    exact integral_energy_le B rfl hb1 hl hlb N
  have hIt : I / t ≤ 1 := (div_le_one ht).2 hI
  have hrec : 1 / t ≤ A := by
    apply (div_le_iff₀ ht).2
    nlinarith
  change d / C ≤ A
  simpa only [t, one_div_div] using hrec

/-- **Limiting mean escape.** Passing the uniform lower bound through the
bounded decreasing finite-horizon escapes makes mean non-return positive. -/
theorem integral_escapeRaw_pos (hμ : OffspringHyp μ) {l : ℝ}
    (hl : 0 < l) (hlm : l < mean μ) :
    0 < ∫ ω, escapeRaw ω l [] ∂offspringFieldLaw μ := by
  obtain ⟨B, hmax⟩ := exists_cap hμ hlm
  let b : ℝ := cappedMeanReal μ B
  let C : ℝ := cappedMomentBound μ B
  let d : ℝ := 1 - l / b
  have hb1 : 1 < b := lt_of_le_of_lt (le_max_left _ _) hmax
  have hlb : l < b := lt_of_le_of_lt (le_max_right _ _) hmax
  have hd : 0 < d := sub_pos.mpr ((div_lt_one (zero_lt_one.trans hb1)).2 hlb)
  have hC : 0 < C := zero_lt_one.trans_le (one_le_cappedMomentBound (μ := μ) hb1)
  have hlim : Tendsto (fun N => ∫ ω, escapeN ω l N [] ∂offspringFieldLaw μ) atTop
      (𝓝 (∫ ω, escapeRaw ω l [] ∂offspringFieldLaw μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) ?_
      (integrable_const 1) ?_ ?_
    · intro N
      exact (measurable_escapeN l N []).aestronglyMeasurable
    · intro N
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (escapeN_nonneg' ω hl N [])]
      exact escapeN_le_one ω hl N []
    · filter_upwards with ω
      unfold escapeRaw
      apply tendsto_atTop_ciInf
      · exact antitone_nat_of_succ_le fun N => escapeN_anti_height ω hl N []
      · apply bddBelow_def.mpr
        refine ⟨0, ?_⟩
        rintro x ⟨N, rfl⟩
        exact escapeN_nonneg' ω hl N []
  have hbound : ∀ N : ℕ, d / C ≤ ∫ ω, escapeN ω l N [] ∂offspringFieldLaw μ := by
    intro N
    exact integral_escapeN_ge hμ B rfl hb1 hl hlb N
  exact (div_pos hd hC).trans_le (ge_of_tendsto hlim (Eventually.of_forall hbound))

end LPPMonotonicityProof.Speed
