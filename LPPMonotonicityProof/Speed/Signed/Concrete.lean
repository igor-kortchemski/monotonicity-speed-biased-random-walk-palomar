module

public import LPPMonotonicityProof.Speed.Env.Concrete
public import LPPMonotonicityProof.Speed.Escape.Positive

/-!
# The concrete escape instance without an extra positivity hypothesis
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory

variable {μ : Measure ℕ} [IsProbabilityMeasure μ] {l : ℝ}

/-- Positivity of escape (Lemma 2.1(iv), `ae_escape_pos_subtrees`) discharges the
positivity input of the concrete escape package. -/
theorem escapePosOnSubtrees (hμ : OffspringHyp μ) (hl : 0 < l) (hlm : l < mean μ) :
    EscapePosOnSubtrees μ l :=
  ae_escape_pos_subtrees hμ hl hlm

/-- The concrete escape package, with its positivity hypothesis proved from the
standing offspring and bias hypotheses. -/
noncomputable def concreteEscapeData' (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ) : EscapeData μ l :=
  concreteEscapeData μ l hl hμ (escapePosOnSubtrees hμ hl hlm)

end LPPMonotonicityProof.Speed
