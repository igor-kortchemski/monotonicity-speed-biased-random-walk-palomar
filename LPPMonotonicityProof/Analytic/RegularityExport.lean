module

public import LPPMonotonicityProof.Analytic.Response
public import LPPMonotonicityProof.Analytic.Regularity

/-!
# Proposition 2.5 (`prop:regularity`): the export bundle

Downstream analytic modules import this module only. It collects, for the
`λ`-biased escapes of a Bienaymé tree with `P(ν = 0) = 0` and `1 < m < ∞`
(Proposition 2.5, `prop:regularity`):

* almost surely, the escape of every subtree is `C¹` on `(0, m)`
  (`ae_contDiffOn_escape_subtrees`);
* on each compact `[a, b] ⊂ (0, m)`, the integrable envelope `K = envelope a b`
  bounds `0 ≤ -∂β ≤ K β` (`lintegral_envelope_lt_top`, `neg_deriv_escape_le`);
* the response recursion and its two lower bounds (`resp_eq`, `resp_ge`,
  `two_resp_ge`), the upper bound `resp_le`, measurability and integrability
  of the response in `(0, m)` (`aemeasurable_resp_of_mem`, `integrable_resp`);
* `|∂β| ≤ 2` for `0 < λ ≤ 1/2` (`abs_deriv_escape_le_two`), as in the proof of
  Proposition 2.6 near zero bias.

Measurability of the response is proved only for biases in `(0, m)`
(`aemeasurable_resp_of_mem`), the only range where it is used.
`abs_deriv_escape_le_two` takes the offspring hypotheses, which give `1/2 < 1 < m`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- Under the offspring hypotheses the real mean exceeds one. -/
theorem one_lt_mean_of_hyp (h : OffspringHyp μ) : 1 < mean μ := by
  have := ENNReal.toReal_strict_mono h.mean_lt_top.ne h.one_lt_mean
  simpa [mean] using this

/-- `|∂β| ≤ 2` for `0 < λ ≤ 1/2`, on a regular tree (proof of Proposition 2.6,
near zero bias). -/
theorem abs_deriv_escape_le_two (h : OffspringHyp μ) {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : 0 < l) (hl2 : l ≤ 1 / 2) :
    |deriv (fun l' => escape l' T) l| ≤ 2 :=
  abs_deriv_escape_le_two_of_mem hT ⟨hl, by linarith [one_lt_mean_of_hyp h]⟩ hl2

/-- `prop:regularity`, first sentence: almost surely the escape of every subtree
is `C¹` on `(0, m)`. -/
theorem ae_contDiffOn_escape_subtrees (h : OffspringHyp μ) :
    ∀ᵐ T ∂GW μ, ∀ v, Present T v →
      ContDiffOn ℝ 1 (fun l => escape l (Speed.subtree T v)) (Set.Ioo 0 (mean μ)) := by
  filter_upwards [ae_regTree h] with T hT v hv
  exact escape_contDiffOn (hT.subtree hv)

/-- `prop:regularity`, second sentence: on a compact `[a, b] ⊂ (0, m)` the envelope
`K = envelope a b` is integrable and almost surely `0 ≤ -∂β ≤ K β` throughout. -/
theorem envelope_bound_regularity (h : OffspringHyp μ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) :
    ∫⁻ T, envelope a b T ∂GW μ < ⊤ ∧
      ∀ᵐ T ∂GW μ, ∀ l ∈ Set.Icc a b,
        0 ≤ -deriv (fun l' => escape l' T) l ∧
          -deriv (fun l' => escape l' T) l ≤ (envelope a b T).toReal * escape l T := by
  refine ⟨lintegral_envelope_lt_top h ha hab hb, ?_⟩
  filter_upwards [ae_regTree h] with T hT l hl
  exact (neg_deriv_escape_le hT ha hab hb hl).2

end LPPMonotonicityProof.Analytic
