module

public import LPPMonotonicityProof.Analytic.Regularity.Domination
public import LPPMonotonicityProof.Analytic.Regularity.EnvelopeMoments
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.UniformSpace.Dini

/-!
# `C¹` regularity of escape probabilities: the regular event

This module shows that almost every Bienaymé tree satisfies `RegTree`: it is
leafless, its present subtrees have positive escape at every transient bias, and
their response envelopes are finite on every rational bias interval.  The `C¹`
argument of Proposition 2.5 (`prop:regularity`) runs on this event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem subtree_subtree (T : Tree) (v u : Address) :
    subtree (subtree T v) u = subtree T (v ++ u) := by
  apply Subtype.ext
  funext w
  simp [Speed.subtree, List.append_assoc]

/-- Every present subtree of a regular tree is regular. -/
theorem RegTree.subtree {T : Tree} (hT : RegTree μ T) {v : Address}
    (hv : Present T v) : RegTree μ (Speed.subtree T v) := by
  refine ⟨hT.1.subtree hv, ?_⟩
  intro qNeg qPos hq0 hqle hqm u hu
  have hp : Present T (v ++ u) := (present_subtree T v u hv).mp hu
  rw [subtree_subtree]
  exact hT.2 qNeg qPos hq0 hqle hqm (v ++ u) hp

private theorem ae_regTree_aux (h : OffspringHyp μ) :
    ∀ᵐ T ∂GW μ, ∀ qNeg qPos : ℚ, 0 < qNeg → qNeg ≤ qPos → (qPos : ℝ) < mean μ →
      ∀ v, Present T v → envelopeProv (qNeg : ℝ) (qPos : ℝ) (subtree T v) < ⊤ := by
  rw [ae_all_iff]
  intro qNeg
  rw [ae_all_iff]
  intro qPos
  rw [ae_all_iff]
  intro hq0
  rw [ae_all_iff]
  intro hqle
  rw [ae_all_iff]
  intro hqm
  have hl0 : 0 < (qNeg : ℝ) := by exact_mod_cast hq0
  have hlle : (qNeg : ℝ) ≤ (qPos : ℝ) := by exact_mod_cast hqle
  have hInt := lintegral_envelope_lt_top h hl0 hlle hqm
  have hfin : ∀ᵐ T ∂GW μ, envelope (qNeg : ℝ) (qPos : ℝ) T < ⊤ :=
    ae_lt_top' (measurable_envelope (qNeg : ℝ) (qPos : ℝ)).aemeasurable hInt.ne
  have hmeas : MeasurableSet {T : Tree | envelope (qNeg : ℝ) (qPos : ℝ) T < ⊤} :=
    measurableSet_lt (measurable_envelope (qNeg : ℝ) (qPos : ℝ)) measurable_const
  have hsub := ae_all_subtrees μ hmeas hfin
  filter_upwards [hsub] with T hT
  intro v hv
  rw [← envelope_eq_prov]
  exact hT v hv

/-- Almost every Galton--Watson tree is regular for the analytic response argument. -/
theorem ae_regTree (h : OffspringHyp μ) : ∀ᵐ T ∂GW μ, RegTree μ T := by
  filter_upwards [ae_goodTree0 h, ae_regTree_aux h] with T hgood hfin
  exact ⟨hgood, hfin⟩

/-- Regularity also holds almost surely under the root-conditioned split law. -/
theorem ae_regTree_split (h : OffspringHyp μ) : ∀ᵐ T ∂splitLaw μ, RegTree μ T := by
  exact Measure.ae_smul_measure (ae_restrict_of_ae (ae_regTree h)) _

end LPPMonotonicityProof.Analytic
