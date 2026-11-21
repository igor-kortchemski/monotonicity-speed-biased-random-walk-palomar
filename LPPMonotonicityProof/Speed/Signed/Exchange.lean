module

public import LPPMonotonicityProof.Speed.Signed.Joint
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Conditional exchangeability of the escape coordinates

Given `ν`, the `ν + 1` escapes are exchangeable; this is the exchangeability step in
the proof of the two-copy form in Theorem 2.2 (`thm:speed-formula`). -/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The symmetric denominator in `k+1` i.i.d. escape coordinates. -/
def Kden (l : ℝ) {k : ℕ} (x : Fin (k + 1) → ℝ) : ℝ := l - 1 + ∑ i, x i

lemma Hfun_eq_Kden (l : ℝ) {k : ℕ} (q : ℝ × (Fin k → ℝ)) :
    Hfun l q.1 (∑ i, q.2 i) =
      Kden l ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm q) := by
  simp [Hfun, Kden, Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, add_assoc]


lemma Kden_comp_piCongrLeft (l : ℝ) {k : ℕ} (e : Fin (k + 1) ≃ Fin (k + 1))
    (x : Fin (k + 1) → ℝ) :
    Kden l (x ∘ e) = Kden l x := by
  unfold Kden
  simpa [Function.comp_def] using congrArg (fun t => l - 1 + t) (Equiv.sum_comp e x)

/-- Every escape coordinate has the same `b/H` integral. -/
lemma integral_iid_child_ratio (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ)
    {k : ℕ} (i : Fin k) :
    (∫ q : ℝ × (Fin k → ℝ), q.2 i / Hfun l q.1 (∑ j, q.2 j)
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) =
      ∫ q : ℝ × (Fin k → ℝ), q.1 / Hfun l q.1 (∑ j, q.2 j)
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) := by
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  let π : Measure (Fin (k + 1) → ℝ) := Measure.pi fun _ => escLaw μ l
  let ρ : Measure (ℝ × (Fin k → ℝ)) :=
    (escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)
  have hE : MeasurePreserving E π ρ := measurePreserving_piFinSuccAbove (fun _ => escLaw μ l) 0
  have hfull (j : Fin (k + 1)) :
      (∫ x, x j / Kden l x ∂π) = ∫ x, x 0 / Kden l x ∂π := by
    let e : Fin (k + 1) ≃ Fin (k + 1) := Equiv.swap 0 j
    let P := MeasurableEquiv.piCongrLeft (fun _ : Fin (k + 1) => ℝ) e
    have hP : MeasurePreserving P π π := measurePreserving_piCongrLeft (fun _ => escLaw μ l) e
    have h := hP.integral_comp' (fun x => x 0 / Kden l x)
    have he : (fun x => (P x) 0 / Kden l (P x)) = (fun x => x j / Kden l x) := by
      funext x
      have hPx : P x = x ∘ e.symm := by
        funext a
        simp [P, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      rw [hPx, Kden_comp_piCongrLeft]
      change x (e.symm 0) / Kden l x = x j / Kden l x
      simp [e]
    rw [he] at h
    exact h
  have hE0 (q : ℝ × (Fin k → ℝ)) : E.symm q 0 = q.1 := by
    simp [E, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hEs (q : ℝ × (Fin k → ℝ)) (j : Fin k) : E.symm q (Fin.succ j) = q.2 j := by
    simp [E, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hEK (q : ℝ × (Fin k → ℝ)) : Kden l (E.symm q) = Hfun l q.1 (∑ j, q.2 j) := by
    simpa [E] using (Hfun_eq_Kden l q).symm
  calc
    _ = ∫ x, x (Fin.succ i) / Kden l x ∂π := by
      rw [← hE.symm.integral_comp']
      apply integral_congr_ae
      filter_upwards with q
      symm
      change E.symm q (Fin.succ i) / Kden l (E.symm q) = _
      rw [hEs, hEK]
    _ = ∫ x, x 0 / Kden l x ∂π := hfull _
    _ = _ := by
      rw [← hE.symm.integral_comp']
      apply integral_congr_ae
      filter_upwards with q
      change E.symm q 0 / Kden l (E.symm q) = _
      rw [hE0, hEK]

lemma Hfun_ge_child {l : ℝ} {k : ℕ} (hk : k ≠ 0) {b : ℝ} {bs : Fin k → ℝ}
    (hb : GoodEsc l b) (hbs : ∀ i, GoodEsc l (bs i)) (i : Fin k) :
    bs i ≤ Hfun l b (∑ j, bs j) := by
  have hb0 : 0 ≤ l - 1 + b := by
    by_cases hl : l < 1
    · linarith [hb.2.2 hl]
    · linarith [hb.1]
  have hi : bs i ≤ ∑ j, bs j :=
    Finset.single_le_sum (fun j _ => (hbs j).1.le) (Finset.mem_univ i)
  unfold Hfun
  linarith

lemma integrable_child_ratio (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ)
    {k : ℕ} (hk : k ≠ 0) (i : Fin k) :
    Integrable (fun q : ℝ × (Fin k → ℝ) => q.2 i / Hfun l q.1 (∑ j, q.2 j))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) := by
  have hHm : Measurable (fun q : ℝ × (Fin k → ℝ) => Hfun l q.1 (∑ j, q.2 j)) :=
    (((measurable_const.sub measurable_const).add measurable_fst).add
      (Finset.univ.measurable_sum fun j _ => (measurable_pi_apply j).comp measurable_snd))
  apply (integrable_const (1 : ℝ)).mono
    (((measurable_pi_apply i).comp measurable_snd).div hHm).aestronglyMeasurable
  filter_upwards [ae_iid_good μ hl hμ hlm k] with q hq
  have hH := Hfun_pos hk hq.1 hq.2
  have hle := Hfun_ge_child hk hq.1 hq.2 i
  change ‖q.2 i / Hfun l q.1 (∑ j, q.2 j)‖ ≤ ‖(1 : ℝ)‖
  rw [Real.norm_eq_abs, norm_one, abs_div, abs_of_pos hH, abs_of_pos (hq.2 i).1]
  apply (div_le_iff₀ hH).2
  simpa using hle

/-- The fixed-degree exchange identity `E[k*b/H] = E[S/H]`. -/
theorem integral_degree_exchange (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {l : ℝ} (hl : 0 < l) (hμ : OffspringHyp μ) (hlm : l < mean μ)
    {k : ℕ} (hk : k ≠ 0) :
    (∫ q : ℝ × (Fin k → ℝ), (k : ℝ) * q.1 / Hfun l q.1 (∑ j, q.2 j)
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) =
      ∫ q : ℝ × (Fin k → ℝ), (∑ j, q.2 j) / Hfun l q.1 (∑ j, q.2 j)
        ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l) := by
  have hsum : (fun q : ℝ × (Fin k → ℝ) => (∑ j, q.2 j) / Hfun l q.1 (∑ j, q.2 j)) =
      fun q => ∑ j, q.2 j / Hfun l q.1 (∑ j, q.2 j) := by
    funext q
    rw [Finset.sum_div]
  rw [hsum, integral_finset_sum]
  · simp_rw [integral_iid_child_ratio μ l hl hμ hlm]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simpa only [mul_div_assoc] using integral_const_mul (k : ℝ)
      (fun q : ℝ × (Fin k → ℝ) => q.1 / Hfun l q.1 (∑ j, q.2 j))
  · intro i _
    exact integrable_child_ratio μ hl hμ hlm hk i

end LPPMonotonicityProof.Speed
