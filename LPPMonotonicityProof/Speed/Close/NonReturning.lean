module

public import LPPMonotonicityProof.Speed.Close.S4
public import LPPMonotonicityProof.Speed.Transfer.SignedLimit
public import LPPMonotonicityProof.Speed.Transfer.Laws

/-!
# The speed on paths which never cross the joining edge
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

open LPPMonotonicity
open LPPMonotonicity.WalkState
open LPPMonotonicityProof.RTL.LocallyFinite

/-- The paths whose normalized height does not converge to `v`. -/
def Bad (v : ℝ) : Set (ℕ → WalkState) :=
  {X | ¬ Tendsto (fun n : ℕ => (height (X n) : ℝ) / n) atTop (𝓝 v)}

lemma measurableSet_bad (v : ℝ) : MeasurableSet (Bad v) := by
  apply MeasurableSet.compl
  apply measurableSet_tendsto
  intro n
  exact ((measurable_of_countable fun x : WalkState => (height x : ℝ)).comp
    (measurable_pi_apply n)).div_const n

private lemma measure_bad_neverHits_eq_label (T : Tree) (l : ℝ≥0) (v : ℝ) :
    walkLaw T.val l (Bad v ∩ neverHits .rootParent) =
      ((publicSpec T.val l).law (.vtx []))
        (noHit T.val l ∩ (pubState T.val l) ⁻¹' Bad v) := by
  have hB : MeasurableSet (Bad v ∩ neverHits .rootParent) :=
    (measurableSet_bad v).inter (measurableSet_neverHits _)
  rw [walkLaw_eq_walkFrom, walkFrom_eq_publicLabel,
    Measure.map_apply ((publicSpec T.val l).measurable_state_apply _) hB]
  congr 1
  ext c
  constructor <;> intro h <;> exact ⟨h.2, h.1⟩

private lemma label_bad_noHit_null (e : Env) {l : ℝ} (hl : 0 < l) {v : ℝ}
    (hlim : ∀ᵐ c ∂moveLaw l hl e,
      Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, sgn (c j)) / n) atTop (𝓝 v)) :
    ((publicSpec e.fwd.val l.toNNReal).law (.vtx []))
      (noHit e.fwd.val l.toNNReal ∩ (pubState e.fwd.val l.toNNReal) ⁻¹' Bad v) = 0 := by
  let B : Set (ℕ → ℕ) :=
    noHit e.fwd.val l.toNNReal ∩ (pubState e.fwd.val l.toNNReal) ⁻¹' Bad v
  have hB : MeasurableSet B :=
    (measurableSet_noHit _ _).inter
      ((measurableSet_bad v).preimage
        ((publicSpec e.fwd.val l.toNNReal).measurable_state_apply _))
  have hzero : (moveLaw l hl e) B = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hlim] with c hc hBc
    apply hBc.2
    change Tendsto (fun n : ℕ => (height (pubState e.fwd.val l.toNNReal c n) : ℝ) / n)
      atTop (𝓝 v)
    convert hc using 1
    ext n
    rw [height_eq_signed hBc.1]
  have hrestricted : ((publicSpec e.fwd.val l.toNNReal).law (.vtx [])).restrict
      (noHit e.fwd.val l.toNNReal) B = 0 := by
    rw [← moveLaw_restrict_noHit l hl e, Measure.restrict_apply hB,
      Set.inter_eq_left.mpr Set.inter_subset_left]
    exact hzero
  rw [Measure.restrict_apply hB, Set.inter_eq_left.mpr Set.inter_subset_left] at hrestricted
  exact hrestricted

/-- **Non-returning paths.**  Under the reference environment law, every non-returning
public path has the speed identified in `walk_signed_limit`. -/
theorem ae_bad_neverHits (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) :
    ∀ᵐ T ∂bienaymeLaw μ,
      walkLaw T.val l.toNNReal (Bad (speedValue μ l) ∩ neverHits .rootParent) = 0 := by
  have href := ref_ae_walk_signed_limit μ hl hμ hlm
  have hpub : ∀ᵐ e ∂ref μ l hl,
      ((publicSpec e.fwd.val l.toNNReal).law (.vtx []))
        (noHit e.fwd.val l.toNNReal ∩
          (pubState e.fwd.val l.toNNReal) ⁻¹' Bad (speedValue μ l)) = 0 := by
    filter_upwards [href] with e he
    exact label_bad_noHit_null e hl he
  have href' : ∀ᵐ e ∂(bienaymeLaw μ).prod ((bienaymeLaw μ) ⊗ₘ harm l hl),
      ((publicSpec (Env.fwd e).val l.toNNReal).law (.vtx []))
        (noHit (Env.fwd e).val l.toNNReal ∩
          (pubState (Env.fwd e).val l.toNNReal) ⁻¹' Bad (speedValue μ l)) = 0 := by
    simpa only [ref] using hpub
  have hfst := Measure.ae_ae_of_ae_prod href'
  filter_upwards [hfst] with T hT
  obtain ⟨b, hb⟩ := hT.exists
  rw [measure_bad_neverHits_eq_label]
  exact hb

end LPPMonotonicityProof.Speed
