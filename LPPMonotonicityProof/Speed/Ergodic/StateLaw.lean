module

public import LPPMonotonicityProof.Speed.Env.Concrete
public import LPPMonotonicityProof.Speed.Env.Stationary

/-!
# Stationary state laws for labelled chains

A helper for `Ergodic/Initial.lean`.  Forgetting the recorded labels
identifies the state path with the ordinary Markov path, so invariance of the
initial law makes every fixed-time state have that same law.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Markov.LabelSpec

variable {S : Type*} [MeasurableSpace S]

/-- The joint initial-state/label law has the stationary state law at every
fixed time when the state kernel preserves the initial measure. -/
theorem map_state_compProd (G : LabelSpec S) (π : Measure S) [SFinite π]
    (hπ : G.stateKernel ∘ₘ π = π) (n : ℕ) :
    (π ⊗ₘ G.law).map (fun x => G.state x.1 x.2 n) = π := by
  have hstate : (π ⊗ₘ G.law).map (fun x => G.state x.1 x.2) =
      pathMeasure G.stateKernel π := by
    rw [pathMeasure_eq_bind]
    ext B hB
    rw [Measure.map_apply G.measurable_state_uncurry hB,
      Measure.compProd_apply (hB.preimage G.measurable_state_uncurry),
      Measure.bind_apply hB (Kernel.aemeasurable _)]
    apply lintegral_congr
    intro e
    change (G.law e) (G.state e ⁻¹' B) = (path G.stateKernel e) B
    rw [← Measure.map_apply (G.measurable_state_apply e) hB, ← G.path_stateKernel]
  have hzero : (pathMeasure G.stateKernel π).map (fun ω => ω 0) = π := by
    rw [pathMeasure_eq_bind,
      Measure.map_bind (Kernel.aemeasurable _) (measurable_pi_apply 0).aemeasurable]
    simp_rw [map_eval_zero_path]
    exact Measure.bind_dirac
  have hiter (ω : ℕ → S) : shiftPath^[n] ω 0 = ω n := by
    induction n generalizing ω with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply, ih]
        rfl
  have heval : (pathMeasure G.stateKernel π).map (fun ω => ω n) =
      (pathMeasure G.stateKernel π).map (fun ω => ω 0) := by
    calc
      (pathMeasure G.stateKernel π).map (fun ω => ω n) =
          ((pathMeasure G.stateKernel π).map shiftPath^[n]).map (fun ω => ω 0) := by
        rw [Measure.map_map (measurable_pi_apply 0) (measurable_shiftPath.iterate n)]
        congr 1
        funext ω
        exact (hiter ω).symm
      _ = (pathMeasure G.stateKernel π).map (fun ω => ω 0) := by
        rw [(measurePreserving_shiftPath G.stateKernel π hπ).iterate n |>.map_eq]
  calc
    (π ⊗ₘ G.law).map (fun x => G.state x.1 x.2 n) =
        ((π ⊗ₘ G.law).map (fun x => G.state x.1 x.2)).map (fun ω => ω n) := by
      rw [Measure.map_map (measurable_pi_apply n) G.measurable_state_uncurry]
      rfl
    _ = (pathMeasure G.stateKernel π).map (fun ω => ω n) := by rw [hstate]
    _ = (pathMeasure G.stateKernel π).map (fun ω => ω 0) := heval
    _ = π := hzero

end Markov.LabelSpec

/-- The concrete walk has initial law `muW` at every fixed time. -/
theorem walkPathLaw_map_state (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hEscapePos : EscapePosOnSubtrees μ l)
    (n : ℕ) :
    (walkPathLaw μ l hl hμ hEscapePos).map
      (fun x => (walkSpec l hl).state x.1 x.2 n) = muW μ l hl hμ hEscapePos := by
  let D := concreteEscapeData μ l hl hμ hEscapePos
  apply Markov.LabelSpec.map_state_compProd
  rw [walkSpec_stateKernel μ l hl hμ hEscapePos]
  exact D.muW_invariant

end LPPMonotonicityProof.Speed
