module

public import LPPMonotonicityProof.Speed.Interface.Model
public import LPPMonotonicityProof.Speed.Interface.Leafless
public import LPPMonotonicityProof.Speed.Markov.Path

/-!
# Zero-bias speed on the public model

This is proved directly for `LPPMonotonicity.walkLaw`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState

/-- The public path law is the point-started homogeneous Markov path. -/
theorem walkLaw_eq_path (ω : List ℕ → ℕ) (l : ℝ≥0) :
    walkLaw ω l = path (stepKernel l ω) (.vtx []) := by
  change pathMeasure (stepKernel l ω) (Measure.dirac (.vtx [])) = _
  exact trajMeasure_dirac (stepKernel l ω) (.vtx [])

/-- The public path starts at the root almost surely. -/
theorem ae_public_walk_zero (ω : List ℕ → ℕ) (l : ℝ≥0) :
    ∀ᵐ X ∂walkLaw ω l, X 0 = .vtx [] := by
  rw [walkLaw_eq_path]
  exact path_zero (stepKernel l ω) (.vtx [])

/-- At zero bias on a positive field, every one-step mass increases height by one. -/
lemma ae_public_stepKernel_zero_height (ω : List ℕ → ℕ) (hω : ∀ v, 1 ≤ ω v)
    (x : WalkState) :
    ∀ᵐ y ∂stepKernel 0 ω x, height y = height x + 1 := by
  cases x with
  | rootParent =>
      simp [stepKernel, Kernel.ofFunOfCountable, stepMeasure, height]
  | vtx v =>
      have hk0 : ω v ≠ 0 := Nat.ne_of_gt (hω v)
      simp only [stepKernel, Kernel.ofFunOfCountable, Kernel.coe_mk, stepMeasure, hk0,
        and_false, ↓reduceIte]
      simp [height]
      intro i
      exact Measure.ae_smul_measure (by simp) _

/-- Every step increases height by one at zero bias on a positive field. -/
theorem ae_public_zero_bias_heightIncrement (ω : List ℕ → ℕ) (hω : ∀ v, 1 ≤ ω v)
    (n : ℕ) :
    ∀ᵐ X ∂walkLaw ω 0, height (X (n + 1)) = height (X n) + 1 := by
  let μ := walkLaw ω 0
  let J : (ℕ → WalkState) → ((Π _ : Finset.Iic n, WalkState) × WalkState) :=
    fun X => (Preorder.frestrictLe n X, X (n + 1))
  have hJ : Measurable J := by fun_prop
  have hjoint : μ.map J = (μ.map (Preorder.frestrictLe n)) ⊗ₘ walkKernel 0 ω n :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm
  have hp : ∀ᵐ p ∂μ.map (Preorder.frestrictLe n),
      ∀ᵐ y ∂walkKernel 0 ω n p, height y = height (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩) + 1 := by
    exact ae_of_all _ fun p => by
      simpa [walkKernel] using ae_public_stepKernel_zero_height ω hω
        (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  have hprod : ∀ᵐ z ∂(μ.map (Preorder.frestrictLe n)) ⊗ₘ walkKernel 0 ω n,
      height z.2 = height (z.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) + 1 :=
    Measure.ae_compProd_of_ae_ae ((Set.to_countable _).measurableSet) hp
  rw [← hjoint] at hprod
  exact (ae_map_iff hJ.aemeasurable ((Set.to_countable _).measurableSet)).mp hprod

/-- On a field with positive offspring everywhere, zero-bias height equals time. -/
theorem ae_public_zero_bias_height_of_pos (ω : List ℕ → ℕ) (hω : ∀ v, 1 ≤ ω v) :
    ∀ᵐ X ∂walkLaw ω 0, ∀ n : ℕ, height (X n) = (n : ℤ) := by
  have hsteps : ∀ᵐ X ∂walkLaw ω 0, ∀ n,
      height (X (n + 1)) = height (X n) + 1 :=
    ae_all_iff.2 fun n => ae_public_zero_bias_heightIncrement ω hω n
  filter_upwards [ae_public_walk_zero ω 0, hsteps] with X h0 hstep
  intro n
  induction n with
  | zero => simp [h0, height]
  | succ n ih =>
      have hr := hstep n
      rw [ih] at hr
      simpa using hr

/-- **The model lemma `v(0) = 1`.** Under the leaflessness hypothesis `μ' 0 = 0`,
`treeLaw`-almost every field is positive everywhere and its zero-bias walk has
height exactly `n` at time `n`, almost surely simultaneously for all `n`. -/
theorem ae_treeWalk_zero_bias_height (μ' : PMF ℕ) (hμ0 : μ' 0 = 0) :
    ∀ᵐ ω ∂treeLaw μ', ∀ᵐ X ∂walkLaw ω 0, ∀ n : ℕ, height (X n) = (n : ℤ) := by
  have h0 : μ'.toMeasure {0} = 0 := by
    rw [μ'.toMeasure_apply_singleton _ (measurableSet_singleton _)]
    exact hμ0
  rw [treeLaw_eq]
  filter_upwards [ae_offspring_pos μ'.toMeasure h0] with ω hω
  exact ae_public_zero_bias_height_of_pos ω hω

/-- Normalized height therefore has the almost-sure zero-bias limit one. -/
theorem ae_treeWalk_zero_bias_speed (μ' : PMF ℕ) (hμ0 : μ' 0 = 0) :
    ∀ᵐ ω ∂treeLaw μ', ∀ᵐ X ∂walkLaw ω 0,
      Tendsto (fun n : ℕ => (height (X n) : ℝ) / n) atTop (𝓝 1) := by
  filter_upwards [ae_treeWalk_zero_bias_height μ' hμ0] with ω hω
  filter_upwards [hω] with X hX
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hX n]
  simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]

end LPPMonotonicityProof.Speed
