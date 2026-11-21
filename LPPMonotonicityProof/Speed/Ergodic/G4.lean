module

public import LPPMonotonicityProof.Speed.Ergodic.G3
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Ergodicity of the labelled walk

The invariant future probability factors through the forward tree
(`Ergodic/G3.lean`).
Neighbour invariance makes that factor constant on siblings.  Two children of
a branching vertex are independent, so the factor is constant almost surely.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace Markov.LabelSpec

variable {S : Type*} [MeasurableSpace S]

/-- Invariance of the initial law gives stationarity of the full labelled
shift, not merely of the state path. -/
theorem measurePreserving_shift_compProd (G : LabelSpec S) (π : Measure S) [SFinite π]
    (hπ : G.stateKernel ∘ₘ π = π) :
    MeasurePreserving G.shift (π ⊗ₘ G.law) (π ⊗ₘ G.law) := by
  refine ⟨G.measurable_shift, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf G.measurable_shift]
  let F : S → ℝ≥0∞ := fun s => ∫⁻ c, f (s, c) ∂G.law s
  have hF : Measurable F := hf.lintegral_kernel_prod_right'
  have hfirst (s : S) :
      (∫⁻ c, f (G.shift (s, c)) ∂G.law s) =
        ∑' j, G.weight s j * F (G.next s j) := by
    rw [G.law_firstStep]
    simp only [lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul]
    apply tsum_congr
    intro j
    have hm : Measurable (fun c => f (G.shift (s, c))) :=
      (hf.comp G.measurable_shift).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_map hm (measurable_seqCons j)]
    rfl
  calc
    (∫⁻ x, f (G.shift x) ∂(π ⊗ₘ G.law)) =
        ∫⁻ s, ∑' j, G.weight s j * F (G.next s j) ∂π := by
      change (∫⁻ x, (f ∘ G.shift) x ∂(π ⊗ₘ G.law)) = _
      rw [Measure.lintegral_compProd (hf.comp G.measurable_shift)]
      apply lintegral_congr
      exact hfirst
    _ = ∑' j, ∫⁻ s, G.weight s j * F (G.next s j) ∂π := by
      rw [lintegral_tsum]
      intro j
      exact ((G.measurable_weight j).mul (hF.comp (G.measurable_next j))).aemeasurable
    _ = ∫⁻ s, ∫⁻ t, F t ∂G.stateKernel s ∂π := by
      symm
      calc
        (∫⁻ s, ∫⁻ t, F t ∂G.stateKernel s ∂π) =
            ∫⁻ s, ∑' j, G.weight s j * F (G.next s j) ∂π :=
          lintegral_congr (μ := π) (f := fun s => ∫⁻ t, F t ∂G.stateKernel s)
            (g := fun s => ∑' j, G.weight s j * F (G.next s j)) (fun s => by
              rw [G.stateKernel_apply, lintegral_sum_measure]
              simp only [lintegral_smul_measure, smul_eq_mul]
              apply tsum_congr
              intro j
              rw [lintegral_dirac' _ hF])
        _ = ∑' j, ∫⁻ s, G.weight s j * F (G.next s j) ∂π := by
          rw [lintegral_tsum]
          intro j
          exact ((G.measurable_weight j).mul (hF.comp (G.measurable_next j))).aemeasurable
    _ = ∫⁻ t, F t ∂(G.stateKernel ∘ₘ π) := by
      rw [Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable]
    _ = ∫⁻ t, F t ∂π := by rw [hπ]
    _ = ∫⁻ x, f x ∂(π ⊗ₘ G.law) := (Measure.lintegral_compProd hf).symm

end Markov.LabelSpec

/-- If two independent copies of a real observable agree almost surely, the
observable is almost surely constant. -/
lemma exists_const_ae_of_ae_eq_prod {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (h : (fun x : Ω × Ω => f x.1) =ᵐ[ν.prod ν] fun x => f x.2) :
    ∃ c : ℝ, f =ᵐ[ν] fun _ => c := by
  have hs := Measure.ae_ae_of_ae_prod h
  obtain ⟨x, hx⟩ := hs.exists
  refine ⟨f x, ?_⟩
  filter_upwards [hs] with y hy
  obtain ⟨z, hyz, hxz⟩ := (hy.and hx).exists
  exact hyz.trans hxz.symm

/-- The forward-tree factorization (`hInv_factor_fwd`) and neighbour invariance make
the forward factor almost surely constant. -/
theorem hInv_ae_const (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    {A : Set PathSpace} (hA : MeasurableSet A)
    (hinv : walkShift l hl ⁻¹' A = A) :
    ∃ c : ℝ, hInv l hl A =ᵐ[muW μ l hl hμ hEscapePos] fun _ => c := by
  let D := concreteEscapeData μ l hl hμ hEscapePos
  obtain ⟨g, hg, hfacU⟩ := hInv_factor_fwd μ l hl hμ hEscapePos hA hinv
  have hfacR : hInv l hl A =ᵐ[ref μ l hl] g ∘ Env.fwd :=
    D.ref_absolutelyContinuous_muU.ae_le hfacU
  have hfacW : hInv l hl A =ᵐ[muW μ l hl hμ hEscapePos] g ∘ Env.fwd :=
    D.muW_absolutelyContinuous_ref.ae_le hfacR
  let N : Set Env := {e | hInv l hl A e ≠ (g ∘ Env.fwd) e}
  have hNW : muW μ l hl hμ hEscapePos N = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hfacW] with e he hn
    exact hn he
  have hmR := (D.ref_absolutelyContinuous_muW hμ).ae_le
    (hInv_move μ l hl hμ hEscapePos hA hinv)
  have haR := (D.ref_absolutelyContinuous_muW hμ).ae_le
    (ae_move_avoids_null μ l hl hμ hEscapePos hNW)
  have hchildR : ∀ᵐ e ∂ref μ l hl, ∀ j, 1 ≤ j → j ≤ degree e.fwd →
      g (child e.fwd j) = g e.fwd := by
    filter_upwards [hmR, haR, hfacR] with e hm ha he
    intro j hj0 hj
    have hf : hInv l hl A (move e j) = g (move e j).fwd := by
      by_contra hn
      exact ha j hj hn
    calc
      g (child e.fwd j) = g (move e j).fwd := by
        congr 2
        simp [move, show j ≠ 0 by omega, outward, Env.fwd]
      _ = hInv l hl A (move e j) := hf.symm
      _ = hInv l hl A e := hm j hj
      _ = g e.fwd := he
  obtain ⟨k, hk, hμk⟩ := exists_degree_ge_two hμ
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  let children : Tree → (Fin k → Tree) := fun T i => child T (i.val + 1)
  let B : Set (Fin k → Tree) := {ts | g (ts i0) ≠ g (ts i1)}
  have hi01 : i0 ≠ i1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i0, i1] at hv
  have hdeg : MeasurableSet {T : Tree | degree T = k} :=
    continuous_degree.measurable (measurableSet_singleton k)
  have hpair_meas : MeasurableSet {T : Tree | g (children T i0) = g (children T i1)} :=
    measurableSet_eq_fun (hg.comp (continuous_child (i0.val + 1)).measurable)
      (hg.comp (continuous_child (i1.val + 1)).measurable)
  have hpair : ∀ᵐ T ∂bienaymeLaw μ, degree T = k →
      g (children T i0) = g (children T i1) := by
    have hP : MeasurableSet {T : Tree | degree T = k →
        g (children T i0) = g (children T i1)} := hdeg.imp hpair_meas
    have hfst : MeasurePreserving (fun e : Env => e.fwd) (ref μ l hl) (bienaymeLaw μ) := by
      simpa only [ref, Env.fwd] using
        (measurePreserving_fst (μ := bienaymeLaw μ) (ν := (bienaymeLaw μ) ⊗ₘ harm l hl))
    rw [← hfst.map_eq]
    exact (ae_map_iff measurable_fst.aemeasurable hP).2 (by
      filter_upwards [hchildR] with e he hkdeg
      have ha := he (i0.val + 1) (by omega) (by dsimp [i0]; change 1 ≤ degree e.1; rw [hkdeg]; omega)
      have hb := he (i1.val + 1) (by omega) (by dsimp [i1]; change 2 ≤ degree e.1; rw [hkdeg]; omega)
      exact ha.trans hb.symm)
  have hB : MeasurableSet B := by
    exact (measurableSet_eq_fun (hg.comp (measurable_pi_apply i0))
      (hg.comp (measurable_pi_apply i1))).compl
  have hBpre : MeasurableSet (children ⁻¹' B) := hB.preimage (by
    exact Measurable.of_eval fun i => (continuous_child _).measurable)
  have hroot0 : (bienaymeLaw μ).restrict {T | degree T = k} (children ⁻¹' B) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hpair.filter_mono ae_restrict_le, ae_restrict_mem hdeg] with T hT hTk hn
    exact hn (hT hTk)
  have hpi0 : Measure.pi (fun _ : Fin k => bienaymeLaw μ) B = 0 := by
    have hrootint : ∫⁻ T in {T | degree T = k}, B.indicator 1 (children T) ∂bienaymeLaw μ = 0 := by
      calc
        (∫⁻ T in {T | degree T = k}, B.indicator 1 (children T) ∂bienaymeLaw μ) =
            ∫⁻ T in {T | degree T = k}, (children ⁻¹' B).indicator 1 T ∂bienaymeLaw μ := by
          apply lintegral_congr
          intro T
          simp only [Set.indicator, Set.mem_preimage, Pi.one_apply]
        _ = 0 := by rw [lintegral_indicator_one hBpre, hroot0]
    simp only [children] at hrootint
    have hbranch := lintegral_children_of_degree μ k
      (g := B.indicator (fun _ => (1 : ENNReal))) (measurable_const.indicator hB)
    have hmul : μ {k} * Measure.pi (fun _ : Fin k => bienaymeLaw μ) B = 0 := by
      calc
        μ {k} * Measure.pi (fun _ : Fin k => bienaymeLaw μ) B =
            μ {k} * ∫⁻ ts, B.indicator 1 ts ∂Measure.pi (fun _ : Fin k => bienaymeLaw μ) := by
          rw [lintegral_indicator_one hB]
        _ = ∫⁻ T in {T | degree T = k}, B.indicator 1 (fun i => child T (i.val + 1))
            ∂bienaymeLaw μ := hbranch.symm
        _ = 0 := hrootint
    exact (mul_eq_zero.mp hmul).resolve_left hμk
  have hpi : ∀ᵐ ts ∂Measure.pi (fun _ : Fin k => bienaymeLaw μ), g (ts i0) = g (ts i1) := by
    rw [measure_eq_zero_iff_ae_notMem] at hpi0
    filter_upwards [hpi0] with ts hts
    exact not_not.mp hts
  have hind : IndepFun (fun ts : Fin k → Tree => ts i0) (fun ts => ts i1)
      (Measure.pi (fun _ : Fin k => bienaymeLaw μ)) :=
    (iIndepFun_pi (fun _ => measurable_id.aemeasurable)).indepFun hi01
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply i0).aemeasurable (measurable_pi_apply i1).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin k => bienaymeLaw μ) i0).map_eq,
    (measurePreserving_eval (fun _ : Fin k => bienaymeLaw μ) i1).map_eq] at hmap
  have hpairPi : ∀ᵐ z ∂(Measure.pi (fun _ : Fin k => bienaymeLaw μ)).map
      (fun ts => (ts i0, ts i1)), g z.1 = g z.2 := by
    exact (ae_map_iff ((measurable_pi_apply i0).prodMk
      (measurable_pi_apply i1)).aemeasurable
      (measurableSet_eq_fun (hg.comp measurable_fst) (hg.comp measurable_snd))).2 hpi
  rw [hmap] at hpairPi
  obtain ⟨c, hc⟩ := exists_const_ae_of_ae_eq_prod (bienaymeLaw μ) hpairPi
  have hfst : MeasurePreserving (fun e : Env => e.fwd) (ref μ l hl) (bienaymeLaw μ) := by
    simpa only [ref, Env.fwd] using
      (measurePreserving_fst (μ := bienaymeLaw μ) (ν := (bienaymeLaw μ) ⊗ₘ harm l hl))
  have hcR : g ∘ Env.fwd =ᵐ[ref μ l hl] fun _ => c :=
    hfst.quasiMeasurePreserving.ae hc
  exact ⟨c, hfacW.trans (D.muW_absolutelyContinuous_ref.ae_le hcR)⟩

/-- **Ergodicity.**  The labelled physical walk is ergodic under its normalized
stationary path law. -/
theorem ergodic_walkShift (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    (hlm : l < mean μ) :
    Ergodic (walkShift l hl) (walkPathLaw μ l hl hμ hEscapePos) := by
  let D := concreteEscapeData μ l hl hμ hEscapePos
  have hstat : MeasurePreserving (walkShift l hl)
      (walkPathLaw μ l hl hμ hEscapePos) (walkPathLaw μ l hl hμ hEscapePos) := by
    apply (walkSpec l hl).measurePreserving_shift_compProd
    rw [walkSpec_stateKernel μ l hl hμ hEscapePos]
    exact D.muW_invariant
  apply Ergodic.of_preimage_eq hstat
  intro A hA hinv
  obtain ⟨c, hc⟩ := hInv_ae_const μ l hl hμ hEscapePos hA hinv
  have hfst : MeasurePreserving (fun x : PathSpace => x.1)
      (walkPathLaw μ l hl hμ hEscapePos) (muW μ l hl hμ hEscapePos) :=
    ⟨measurable_fst, Measure.fst_compProd _ _⟩
  have hcP : (fun x : PathSpace => hInv l hl A x.1) =ᵐ[walkPathLaw μ l hl hμ hEscapePos]
      fun _ => c := hfst.quasiMeasurePreserving.ae hc
  have hiP : A.indicator 1 =ᵐ[walkPathLaw μ l hl hμ hEscapePos] fun _ => c :=
    (indicator_ae_eq_hInv μ l hl hμ hEscapePos hA hinv).trans hcP
  have hc01 : c = 0 ∨ c = 1 := by
    obtain ⟨x, hx⟩ := hiP.exists
    by_cases hxA : x ∈ A
    · exact Or.inr (by simpa [Set.indicator_of_mem hxA] using hx.symm)
    · exact Or.inl (by simpa [Set.indicator_of_notMem hxA] using hx.symm)
  apply eventuallyEmptyOrUniv_iff.mpr
  rcases hc01 with rfl | rfl
  · right
    filter_upwards [hiP] with x hx hxA
    rw [Set.indicator_of_mem hxA] at hx
    exact one_ne_zero hx
  · left
    filter_upwards [hiP] with x hx
    by_contra hxA
    rw [Set.indicator_of_notMem hxA] at hx
    exact zero_ne_one hx

end LPPMonotonicityProof.Speed
