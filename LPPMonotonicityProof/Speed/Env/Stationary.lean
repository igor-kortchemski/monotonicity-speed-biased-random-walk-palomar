module

public import LPPMonotonicityProof.Speed.Env.Masses
public import LPPMonotonicityProof.Speed.Markov.Path

/-!
# Stationarity of the environment path laws

Lin's one-step invariance and the general trajectory-shift
theorem give stationary walk and harmonic-outward path laws.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open MeasureTheory ProbabilityTheory

namespace EscapeData

variable {μ : Measure ℕ} [IsProbabilityMeasure μ] {l : ℝ}

/-- **Stationarity for the walk:** the normalized environment path law is
shift-stationary. -/
theorem measurePreserving_shiftPath_walk (D : EscapeData μ l) :
    MeasurePreserving shiftPath (pathMeasure D.walkKernel D.muW)
      (pathMeasure D.walkKernel D.muW) :=
  measurePreserving_shiftPath D.walkKernel D.muW D.muW_invariant

/-- **Stationarity for `Q`:** the normalized harmonic-outward path law is
shift-stationary. -/
theorem measurePreserving_shiftPath_q (D : EscapeData μ l) :
    MeasurePreserving shiftPath (pathMeasure D.qKernel D.muU)
      (pathMeasure D.qKernel D.muU) :=
  measurePreserving_shiftPath D.qKernel D.muU D.muU_invariant

end EscapeData

end LPPMonotonicityProof.Speed
