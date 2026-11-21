module

public import LPPMonotonicityProof.Speed.Ergodic.G012
public import LPPMonotonicityProof.Speed.Env.Ball
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The invariant future probability factors through the forward tree

The harmonic outward chain is used to average finite-ball approximants.  The
resulting averages depend only on the forward tree and converge to the
invariant future probability in `L¹`.  The forward-tree conditional
expectation therefore agrees with that future probability almost surely.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

/-- Every fixed-time state of the harmonic outward chain has law `muU`. -/
theorem qPathLaw_map_outIter (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    (n : ℕ) :
    (qPathLaw μ l hl hμ hEscapePos).map
      (fun x => outIter l hl x.1 x.2 n) = muU μ l hl hμ hEscapePos := by
  apply Markov.LabelSpec.map_state_compProd
  rw [qSpec_stateKernel μ l hl hμ hEscapePos]
  exact (concreteEscapeData μ l hl hμ hEscapePos).muU_invariant

private def neighbourInvariant (f : Env → ℝ) (e : Env) : Prop :=
  ∀ j ≤ degree e.fwd, f (move e j) = f e

private def stableLayer (f : Env → ℝ) (G : Set Env) : Set Env :=
  {e | neighbourInvariant f e ∧ ∀ j ≤ degree e.fwd, move e j ∈ G}

private def stableChain (f : Env → ℝ) : ℕ → Set Env
  | 0 => Set.univ
  | n + 1 => stableLayer f (stableChain f n)

private def stableSet (f : Env → ℝ) : Set Env := ⋂ n, stableChain f n

private lemma mem_stableSet {f : Env → ℝ} {e : Env} :
    e ∈ stableSet f ↔ ∀ n, e ∈ stableChain f n := by
  simp only [stableSet, Set.mem_iInter]

private lemma ae_stableChain (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A)
    (hinv : walkShift l hl ⁻¹' A = A) (n : ℕ) :
    ∀ᵐ e ∂muW μ l hl hμ hEscapePos,
      e ∈ stableChain (hInv l hl A) n := by
  induction n with
  | zero => simp [stableChain]
  | succ n ih =>
      have hnull : muW μ l hl hμ hEscapePos (stableChain (hInv l hl A) n)ᶜ = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        simpa only [Set.mem_compl_iff, not_not] using ih
      filter_upwards [hInv_move μ l hl hμ hEscapePos hA hinv,
        ae_move_avoids_null μ l hl hμ hEscapePos hnull] with e he havoid
      exact ⟨he, fun j hj => not_not.mp (havoid j hj)⟩

private lemma ae_stableSet (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A)
    (hinv : walkShift l hl ⁻¹' A = A) :
    ∀ᵐ e ∂muW μ l hl hμ hEscapePos, e ∈ stableSet (hInv l hl A) := by
  simp only [mem_stableSet]
  rw [ae_all_iff]
  exact ae_stableChain μ l hl hμ hEscapePos hA hinv

private lemma stableSet_neighbour {f : Env → ℝ} {e : Env}
    (he : e ∈ stableSet f) : neighbourInvariant f e := by
  exact (mem_stableSet.mp he 1).1

private lemma stableSet_move {f : Env → ℝ} {e : Env}
    (he : e ∈ stableSet f) {j : ℕ} (hj : j ≤ degree e.fwd) :
    move e j ∈ stableSet f := by
  apply mem_stableSet.mpr
  intro n
  exact (mem_stableSet.mp he (n + 1)).2 j hj

private lemma hInv_outIter_of_stable {l : ℝ} (hl : 0 < l) {A : Set PathSpace} {e : Env}
    (he : e ∈ stableSet (hInv l hl A)) {c : ℕ → ℕ} (hc : rayValid e.fwd c) (n : ℕ) :
    outIter l hl e c n ∈ stableSet (hInv l hl A) ∧
      hInv l hl A (outIter l hl e c n) = hInv l hl A e := by
  induction n with
  | zero => exact ⟨he, rfl⟩
  | succ n ih =>
      have hv : 1 ≤ c n ∧ c n ≤ degree (outIter l hl e c n).fwd := by
        rw [outIter_fwd]
        exact hc n
      have hmove : move (outIter l hl e c n) (c n) =
          outIter l hl e c (n + 1) := by
        change move (outIter l hl e c n) (c n) = outward (outIter l hl e c n) (c n)
        rw [move, if_neg (by omega : c n ≠ 0)]
      constructor
      · rw [← hmove]
        exact stableSet_move ih.1 hv.2
      · rw [← hmove, stableSet_neighbour ih.1 (c n) hv.2]
        exact ih.2

/-- Along `Q`, the future probability is almost surely unchanged by any
number of outward moves. -/
theorem ae_hInv_outIter (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A)
    (hinv : walkShift l hl ⁻¹' A = A) :
    ∀ᵐ x ∂qPathLaw μ l hl hμ hEscapePos, ∀ n,
      hInv l hl A (outIter l hl x.1 x.2 n) = hInv l hl A x.1 := by
  let D := concreteEscapeData μ l hl hμ hEscapePos
  have hstable : ∀ᵐ e ∂muU μ l hl hμ hEscapePos, e ∈ stableSet (hInv l hl A) := by
    exact (D.muU_absolutelyContinuous_ref.trans (D.ref_absolutelyContinuous_muW hμ)).ae_le
      (ae_stableSet μ l hl hμ hEscapePos hA hinv)
  have hgood : ∀ᵐ e ∂muU μ l hl hμ hEscapePos, GoodTree D.β l e.fwd :=
    D.muU_absolutelyContinuous_ref.ae_le (D.ae_good_ref.mono fun _ he => he.1)
  have hsections : ∀ᵐ e ∂muU μ l hl hμ hEscapePos,
      ∀ᵐ c ∂(qSpec l hl).law e, rayValid e.fwd c := by
    filter_upwards [hgood] with e he
    rw [qSpec_law]
    exact D.ae_rayValid_harm e.fwd he
  have hmap : Measurable (fun x : PathSpace => (x.1.fwd, x.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hvalid : ∀ᵐ x ∂qPathLaw μ l hl hμ hEscapePos, rayValid x.1.fwd x.2 := by
    exact Measure.ae_compProd_of_ae_ae (measurableSet_rayValid.preimage hmap) hsections
  have hfst : MeasurePreserving (fun x : PathSpace => x.1)
      (qPathLaw μ l hl hμ hEscapePos) (muU μ l hl hμ hEscapePos) :=
    ⟨measurable_fst, Measure.fst_compProd _ _⟩
  filter_upwards [hvalid, hfst.quasiMeasurePreserving.ae hstable] with x hxvalid hxstable
  intro n
  exact (hInv_outIter_of_stable hl hxstable hxvalid n).2

private def unitClamp (x : ℝ) : ℝ := max 0 (min 1 x)

private lemma measurable_unitClamp : Measurable unitClamp := by
  unfold unitClamp
  fun_prop

private lemma unitClamp_nonneg (x : ℝ) : 0 ≤ unitClamp x := le_max_left _ _

private lemma unitClamp_le_one (x : ℝ) : unitClamp x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

private lemma unitClamp_sub_abs_le {x y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |unitClamp x - y| ≤ |x - y| := by
  by_cases hx0 : x ≤ 0
  · have hc : unitClamp x = 0 := by
      simp [unitClamp, min_eq_right (hx0.trans zero_le_one), max_eq_left hx0]
    rw [hc, abs_le]
    constructor <;> nlinarith [neg_abs_le (x - y), le_abs_self (x - y)]
  · have hx0' : 0 ≤ x := le_of_not_ge hx0
    by_cases hx1 : 1 ≤ x
    · have hc : unitClamp x = 1 := by simp [unitClamp, min_eq_left hx1]
      have h1y : 0 ≤ 1 - y := sub_nonneg.mpr hy1
      have hxy : 0 ≤ x - y := sub_nonneg.mpr (hy1.trans hx1)
      rw [hc, abs_of_nonneg h1y, abs_of_nonneg hxy]
      linarith
    · have hc : unitClamp x = x := by
        simp [unitClamp, min_eq_right (le_of_not_ge hx1), max_eq_right hx0']
      rw [hc]

private lemma integrable_hInv_muU (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A) :
    Integrable (hInv l hl A) (muU μ l hl hμ hEscapePos) := by
  apply Integrable.of_bound (measurable_hInv l hl hA).aestronglyMeasurable 1
  filter_upwards [] with e
  rw [Real.norm_eq_abs, abs_of_nonneg (hInv_nonneg l hl A e)]
  exact hInv_le_one l hl A e

/-- The finite-ball approximation `exists_measurable_comp_ballMap_approx` with a bounded
ball observable, specialized to the future probability. -/
private lemma exists_unit_comp_ballMap_approx_hInv
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A) {ε : ENNReal} (hε : 0 < ε) :
    ∃ (r : ℕ) (φ : BallData r → ℝ), Measurable φ ∧
      (∀ b, 0 ≤ φ b ∧ φ b ≤ 1) ∧
      eLpNorm ((φ ∘ ballMap r) - hInv l hl A) 1 (muU μ l hl hμ hEscapePos) < ε := by
  obtain ⟨r, φ, hφ, -, hφε⟩ := exists_measurable_comp_ballMap_approx
    (muU μ l hl hμ hEscapePos) (integrable_hInv_muU μ l hl hμ hEscapePos hA) hε
  refine ⟨r, unitClamp ∘ φ, measurable_unitClamp.comp hφ,
    fun b => ⟨unitClamp_nonneg _, unitClamp_le_one _⟩, ?_⟩
  apply (eLpNorm_mono_ae
    (((measurable_unitClamp.comp hφ).comp (measurable_ballMap r)).sub
      (measurable_hInv l hl hA)).aestronglyMeasurable ?_).trans_lt hφε
  filter_upwards [] with e
  change |unitClamp (φ (ballMap r e)) - hInv l hl A e| ≤ |φ (ballMap r e) - hInv l hl A e|
  exact unitClamp_sub_abs_le (hInv_nonneg l hl A e) (hInv_le_one l hl A e)

private def forwardOnly (T : Tree) : Env := (T, leaf, fun _ => 0)

private noncomputable def ballAverage (l : ℝ) (hl : 0 < l) {r : ℕ}
    (φ : BallData r → ℝ) (T : Tree) : ℝ :=
  ∫ c, φ (ballMap r (outIter l hl (forwardOnly T) c r)) ∂harm l hl T

private lemma measurable_forwardOnly : Measurable forwardOnly :=
  measurable_id.prodMk (measurable_const.prodMk measurable_const)

private lemma measurable_ballAverage (l : ℝ) (hl : 0 < l) {r : ℕ}
    {φ : BallData r → ℝ} (hφ : Measurable φ) : Measurable (ballAverage l hl φ) := by
  have hmap : Measurable (fun x : Tree × (ℕ → ℕ) =>
      outIter l hl (forwardOnly x.1) x.2 r) :=
    ((qSpec l hl).measurable_state r).comp
      ((measurable_forwardOnly.comp measurable_fst).prodMk measurable_snd)
  have hi : StronglyMeasurable (Function.uncurry (fun (T : Tree) (c : ℕ → ℕ) =>
      φ (ballMap r (outIter l hl (forwardOnly T) c r)))) :=
    (hφ.comp ((measurable_ballMap r).comp hmap)).stronglyMeasurable
  exact hi.integral_kernel_prod_right.measurable

private lemma ballAverage_fwd (l : ℝ) (hl : 0 < l) {r : ℕ}
    (φ : BallData r → ℝ) (e : Env) :
    ballAverage l hl φ e.fwd =
      ∫ c, φ (ballMap r (outIter l hl e c r)) ∂(qSpec l hl).law e := by
  rw [qSpec_law]
  apply integral_congr_ae
  filter_upwards [] with c
  exact congrArg φ (ballMap_outIter l hl (r := r) (n := r) le_rfl
    (forwardOnly e.fwd) e rfl c)

private lemma integrable_unit_ballAverage_comp (μ : Measure Env) [IsFiniteMeasure μ]
    (l : ℝ) (hl : 0 < l) {r : ℕ} {φ : BallData r → ℝ}
    (hφ : Measurable φ) (hφ0 : ∀ b, 0 ≤ φ b) (hφ1 : ∀ b, φ b ≤ 1) :
    Integrable (ballAverage l hl φ ∘ Env.fwd) μ := by
  apply Integrable.of_bound ((measurable_ballAverage l hl hφ).comp measurable_fst).aestronglyMeasurable 1
  filter_upwards [] with T
  change ‖ballAverage l hl φ (Env.fwd T)‖ ≤ 1
  unfold ballAverage
  apply (norm_integral_le_of_norm_le_const (C := 1) ?_).trans
  · simp
  · filter_upwards [] with c
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]
    exact hφ1 _

/-- Harmonic averaging of a bounded ball observable contracts its `L¹` error. -/
private lemma eLpNorm_ballAverage_sub_hInv_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A)
    (hinv : walkShift l hl ⁻¹' A = A) {r : ℕ} {φ : BallData r → ℝ}
    (hφ : Measurable φ) (hφ0 : ∀ b, 0 ≤ φ b) (hφ1 : ∀ b, φ b ≤ 1) :
    eLpNorm ((ballAverage l hl φ ∘ Env.fwd) - hInv l hl A) 1
        (muU μ l hl hμ hEscapePos) ≤
      eLpNorm ((φ ∘ ballMap r) - hInv l hl A) 1 (muU μ l hl hμ hEscapePos) := by
  let U := muU μ l hl hμ hEscapePos
  let Q := qPathLaw μ l hl hμ hEscapePos
  let S : PathSpace → Env := fun x => outIter l hl x.1 x.2 r
  let F : Env → ℝ := (φ ∘ ballMap r) - hInv l hl A
  have hF : Measurable F := (hφ.comp (measurable_ballMap r)).sub (measurable_hInv l hl hA)
  have hS : Measurable S := (qSpec l hl).measurable_state r
  have hSP : MeasurePreserving S Q U := ⟨hS, qPathLaw_map_outIter μ l hl hμ hEscapePos r⟩
  have hleft : Measurable ((ballAverage l hl φ ∘ Env.fwd) - hInv l hl A) :=
    ((measurable_ballAverage l hl hφ).comp measurable_fst).sub (measurable_hInv l hl hA)
  have hright : Measurable (F ∘ S) := hF.comp hS
  calc
    eLpNorm ((ballAverage l hl φ ∘ Env.fwd) - hInv l hl A) 1 U ≤ eLpNorm (F ∘ S) 1 Q := by
      rw [eLpNorm_one_eq_lintegral_enorm hleft.aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm hright.aestronglyMeasurable]
      change (∫⁻ e, ‖(ballAverage l hl φ e.fwd - hInv l hl A e)‖ₑ ∂U) ≤
        ∫⁻ x, ‖F (S x)‖ₑ ∂(U ⊗ₘ (qSpec l hl).law)
      have hcomp : (∫⁻ x, ‖F (S x)‖ₑ ∂(U ⊗ₘ (qSpec l hl).law)) =
          ∫⁻ e, ∫⁻ c, ‖F (outIter l hl e c r)‖ₑ ∂(qSpec l hl).law e ∂U :=
        Measure.lintegral_compProd (hF.enorm.comp hS)
      rw [hcomp]
      apply lintegral_mono_ae
      have hsections := Measure.ae_ae_of_ae_compProd
        (ae_hInv_outIter μ l hl hμ hEscapePos hA hinv)
      filter_upwards [hsections] with e he
      have he' : ∀ᵐ c ∂(qSpec l hl).law e,
          hInv l hl A (outIter l hl e c r) = hInv l hl A e := by
        filter_upwards [he] with c hc
        exact hc r
      have hmap : Measurable (fun c => outIter l hl e c r) :=
        ((qSpec l hl).measurable_state r).comp (measurable_const.prodMk measurable_id)
      have hint : Integrable (fun c => φ (ballMap r (outIter l hl e c r)))
          ((qSpec l hl).law e) := by
        apply Integrable.of_bound
          (hφ.comp ((measurable_ballMap r).comp hmap)).aestronglyMeasurable 1
        filter_upwards [] with c
        change |φ (ballMap r (outIter l hl e c r))| ≤ 1
        rw [abs_of_nonneg (hφ0 _)]
        exact hφ1 _
      have hdiff : ballAverage l hl φ e.fwd - hInv l hl A e =
          ∫ c, (φ (ballMap r (outIter l hl e c r)) -
            hInv l hl A (outIter l hl e c r)) ∂(qSpec l hl).law e := by
        rw [ballAverage_fwd]
        calc
          (∫ c, φ (ballMap r (outIter l hl e c r)) ∂(qSpec l hl).law e) - hInv l hl A e =
              (∫ c, φ (ballMap r (outIter l hl e c r)) ∂(qSpec l hl).law e) -
                ∫ _c, hInv l hl A e ∂(qSpec l hl).law e := by simp
          _ = ∫ c, (φ (ballMap r (outIter l hl e c r)) - hInv l hl A e)
              ∂(qSpec l hl).law e := (integral_sub hint (integrable_const _)).symm
          _ = _ := by
            apply integral_congr_ae
            filter_upwards [he'] with c hc
            rw [hc]
      rw [hdiff]
      exact enorm_integral_le_lintegral_enorm _
    _ = eLpNorm F 1 U := eLpNorm_comp_measurePreserving hF.aestronglyMeasurable hSP

private def fwdFiltration : MeasurableSpace Env :=
  MeasurableSpace.comap Env.fwd inferInstance

/-- **Factorization.**  The invariant future probability is almost surely a measurable
function of the initial forward tree under the normalized `Q`-law. -/
theorem hInv_factor_fwd (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A)
    (hinv : walkShift l hl ⁻¹' A = A) :
    ∃ g : Tree → ℝ, Measurable g ∧
      hInv l hl A =ᵐ[muU μ l hl hμ hEscapePos] g ∘ Env.fwd := by
  let U := muU μ l hl hμ hEscapePos
  have hfwd : @Measurable Env Tree (inferInstance : MeasurableSpace Env) inferInstance Env.fwd := by
    change Measurable (fun e : Env => e.1)
    exact measurable_fst
  have hfwd_comap : Measurable[fwdFiltration] Env.fwd := fun _s hs => ⟨_s, hs, rfl⟩
  have hfwdFiltration : fwdFiltration ≤ (inferInstance : MeasurableSpace Env) := hfwd.comap_le
  have hfint : Integrable (hInv l hl A) U := integrable_hInv_muU μ l hl hμ hEscapePos hA
  have hzero : eLpNorm (hInv l hl A - U[hInv l hl A | fwdFiltration]) 1 U = 0 := by
    apply le_antisymm ?_ (by simp)
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε htop
    have hε0 : (0 : NNReal) < ε := hε
    have hdiv : (0 : ENNReal) < (((ε / 4 : NNReal) : ENNReal)) := by
      rw [ENNReal.coe_pos]
      positivity
    obtain ⟨r, φ, hφ, hφ01, hφε⟩ := exists_unit_comp_ballMap_approx_hInv
      μ l hl hμ hEscapePos hA (ε := ((ε / 4 : NNReal) : ENNReal)) hdiv
    let ψ : Env → ℝ := ballAverage l hl φ ∘ Env.fwd
    have hψmeas : Measurable[fwdFiltration] ψ := (measurable_ballAverage l hl hφ).comp hfwd_comap
    have hψint : Integrable ψ U := integrable_unit_ballAverage_comp U l hl hφ
      (fun b => (hφ01 b).1) (fun b => (hφ01 b).2)
    have hψcond : U[ψ | fwdFiltration] =ᵐ[U] ψ :=
      condExp_of_aestronglyMeasurable' (μ := U) hfwdFiltration hψmeas.stronglyMeasurable.aestronglyMeasurable hψint
    have hsplit : hInv l hl A - U[hInv l hl A | fwdFiltration] =ᵐ[U]
        (hInv l hl A - ψ) - U[hInv l hl A - ψ | fwdFiltration] := by
      have hsub := condExp_sub hfint hψint fwdFiltration
      filter_upwards [hsub, hψcond] with e he heψ
      change hInv l hl A e - U[hInv l hl A | fwdFiltration] e =
        (hInv l hl A e - ψ e) - U[hInv l hl A - ψ | fwdFiltration] e
      rw [he]
      simp only [Pi.sub_apply]
      rw [heψ]
      ring
    rw [eLpNorm_congr_ae hsplit]
    have htri := eLpNorm_add_le (μ := U) (p := (1 : ENNReal))
      (f := hInv l hl A - ψ) (g := -U[hInv l hl A - ψ | fwdFiltration]) le_rfl
    rw [eLpNorm_neg] at htri
    have hcondexp := eLpNorm_condExp_le_eLpNorm (μ := U) (m := fwdFiltration) (hInv l hl A - ψ)
      (show 1 ≤ (1 : ENNReal) from le_rfl)
    have hbound : eLpNorm ((hInv l hl A - ψ) - U[hInv l hl A - ψ | fwdFiltration]) 1 U ≤
        2 * eLpNorm (hInv l hl A - ψ) 1 U := by
      calc
        eLpNorm ((hInv l hl A - ψ) - U[hInv l hl A - ψ | fwdFiltration]) 1 U =
            eLpNorm ((hInv l hl A - ψ) + (-U[hInv l hl A - ψ | fwdFiltration])) 1 U := by
              congr 2
        _ ≤ eLpNorm (hInv l hl A - ψ) 1 U + eLpNorm (U[hInv l hl A - ψ | fwdFiltration]) 1 U := htri
        _ ≤ eLpNorm (hInv l hl A - ψ) 1 U + eLpNorm (hInv l hl A - ψ) 1 U :=
          add_le_add_right hcondexp _
        _ = 2 * eLpNorm (hInv l hl A - ψ) 1 U := by ring
    have havg : eLpNorm (ψ - hInv l hl A) 1 U ≤
        eLpNorm ((φ ∘ ballMap r) - hInv l hl A) 1 U :=
      eLpNorm_ballAverage_sub_hInv_le μ l hl hμ hEscapePos hA hinv hφ
        (fun b => (hφ01 b).1) (fun b => (hφ01 b).2)
    have hnorm : eLpNorm (hInv l hl A - ψ) 1 U =
        eLpNorm (ψ - hInv l hl A) 1 U := by
      have hfun : hInv l hl A - ψ = -(ψ - hInv l hl A) := by
        funext e
        simp only [Pi.sub_apply, Pi.neg_apply]
        ring
      rw [hfun, eLpNorm_neg]
    have htwo : (2 : ENNReal) * (((ε / 4 : NNReal) : ENNReal)) ≤ (ε : ENNReal) := by
      exact_mod_cast (show (2 : NNReal) * (ε / 4) ≤ ε by
        calc
          (2 : NNReal) * (ε / 4) ≤ 4 * (ε / 4) := by gcongr; norm_num
          _ = ε := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (4 : NNReal) ≠ 0)])
    calc
      eLpNorm ((hInv l hl A - ψ) - U[hInv l hl A - ψ | fwdFiltration]) 1 U ≤
          2 * eLpNorm (hInv l hl A - ψ) 1 U := hbound
      _ = 2 * eLpNorm (ψ - hInv l hl A) 1 U := by rw [hnorm]
      _ ≤ 2 * eLpNorm ((φ ∘ ballMap r) - hInv l hl A) 1 U := by gcongr
      _ ≤ 2 * (((ε / 4 : NNReal) : ENNReal)) := by gcongr
      _ ≤ 0 + (ε : ENNReal) := by simpa using htwo
  have hcond : U[hInv l hl A | fwdFiltration] =ᵐ[U] hInv l hl A := by
    rw [eLpNorm_eq_zero_iff one_ne_zero] at hzero
    filter_upwards [hzero] with e he
    exact (sub_eq_zero.mp he).symm
  have hfactor : Measurable[fwdFiltration] (U[hInv l hl A | fwdFiltration]) := stronglyMeasurable_condExp.measurable
  obtain ⟨g, hg, hcomp⟩ := hfactor.exists_eq_measurable_comp
  refine ⟨g, hg, ?_⟩
  rw [← hcomp]
  exact hcond.symm

end LPPMonotonicityProof.Speed
