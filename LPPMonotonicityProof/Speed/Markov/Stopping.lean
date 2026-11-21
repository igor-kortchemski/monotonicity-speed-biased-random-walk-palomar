module

public import LPPMonotonicityProof.Speed.Markov.Path
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Summation over a finite random time

The strong-Markov calculation needed by the proof of the speed formula, obtained by
summing the fixed-time Markov property over the finite values of a stopping
time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Preorder Filtration
open scoped ENNReal BigOperators Function

namespace LPPMonotonicityProof.Speed

variable {S : Type*} [MeasurableSpace S]

/-- The Markov property summed over the finite values of a stopping time. -/
theorem path_markov_stopping (K : Kernel S S) [IsMarkovKernel K] (x : S)
    {τ : (ℕ → S) → ℕ∞}
    (hτ : ∀ t : ℕ, MeasurableSet[Filtration.piLE t] {ω | τ ω = t})
    {A : Set (ℕ → S)} (hA : MeasurableSet A) :
    path K x {ω | ∃ t : ℕ, τ ω = t ∧ shiftN t ω ∈ A} =
      ∫⁻ ω in {ω | τ ω ≠ ⊤}, path K (ω (τ ω).toNat) A ∂path K x := by
  let B : ℕ → Set (ℕ → S) := fun t => {ω | τ ω = t}
  have hB : ∀ t, MeasurableSet (B t) := fun t => (Filtration.piLE.le t) _ (hτ t)
  have hdisjB : Pairwise (Disjoint on B) := by
    intro s t hst
    change Disjoint (B s) (B t)
    rw [Set.disjoint_left]
    intro ω hωs hωt
    apply hst
    exact_mod_cast hωs.symm.trans hωt
  have hfinite : {ω | τ ω ≠ ⊤} = ⋃ t, B t := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, B]
    exact ENat.ne_top_iff_exists.trans (by constructor <;> rintro ⟨t, ht⟩ <;> exact ⟨t, ht.symm⟩)
  have hevent : {ω | ∃ t : ℕ, τ ω = t ∧ shiftN t ω ∈ A} =
      ⋃ t, B t ∩ shiftN t ⁻¹' A := by
    ext ω
    simp [B]
  have hdisj : Pairwise (Disjoint on fun t => B t ∩ shiftN t ⁻¹' A) :=
    fun s t hst => (hdisjB hst).mono Set.inter_subset_left Set.inter_subset_left
  have hmeas : ∀ t, MeasurableSet (B t ∩ shiftN t ⁻¹' A) := fun t =>
    (hB t).inter (hA.preimage (measurable_shiftN t))
  rw [hevent, measure_iUnion hdisj hmeas]
  have hMarkov : ∀ t, path K x (B t ∩ shiftN t ⁻¹' A) =
      ∫⁻ ω in B t, path K (ω t) A ∂path K x := by
    intro t
    exact path_markov K t x (by simpa [B] using hτ t) hA
  simp_rw [hMarkov]
  rw [hfinite, lintegral_iUnion hB hdisjB]
  apply tsum_congr
  intro t
  apply setLIntegral_congr_fun (hB t)
  intro ω hω
  simp only [B, Set.mem_setOf_eq] at hω
  change path K (ω t) A = path K (ω (τ ω).toNat) A
  rw [hω, ENat.toNat_natCast]

end LPPMonotonicityProof.Speed
