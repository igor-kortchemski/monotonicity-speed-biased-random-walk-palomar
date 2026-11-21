module

public import LPPMonotonicityProof.Speed.Env.CaseII
public import Mathlib.Probability.Kernel.WithDensity

/-!
# Invariance from Lin's ordered Cases I and II

The walk-density reference measure, with density `(ν+λ)β₀/(a+β₀+S)` as in the proof
of Theorem 2.2 (`thm:speed-formula`), is invariant for the environment seen by the
walk, and the `u`-density reference measure is invariant for the harmonic outward
kernel.  The reference measures are left unnormalised; invariance
therefore needs no moment or integrability assumption beyond `EscapeData`.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace EscapeData

variable {μ : Measure ℕ} [IsProbabilityMeasure μ] {l : ℝ}

/-- A countable weighted sum of deterministic environment moves. -/
noncomputable def weightedMoves (next : Env → ℕ → Env)
    (hnext : ∀ j, Measurable fun e => next e j) (weight : Env → ℕ → ℝ≥0∞) : Kernel Env Env :=
  Kernel.sum fun j => (Kernel.deterministic (fun e => next e j) (hnext j)).withDensity
    (fun e _ => weight e j)

theorem lintegral_weightedMoves (next : Env → ℕ → Env)
    (hnext : ∀ j, Measurable fun e => next e j) (weight : Env → ℕ → ℝ≥0∞)
    (hweight : ∀ j, Measurable (fun p : Env × Env => weight p.1 j))
    (e : Env) {f : Env → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ e', f e' ∂weightedMoves next hnext weight e = ∑' j, weight e j * f (next e j) := by
  rw [weightedMoves, Kernel.sum_apply, lintegral_sum_measure]
  apply tsum_congr
  intro j
  rw [Kernel.lintegral_withDensity _ (hweight j) _ hf]
  exact Kernel.lintegral_deterministic' (hnext j)
    (f := fun b : Env => weight e j * f b) (measurable_const.mul hf)

/-- Physical walk weights, with move zero inward and positive moves outward. -/
noncomputable def walkWeight (D : EscapeData μ l) (e : Env) (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then ENNReal.ofReal (l / (l + degree e.fwd))
  else if j ≤ degree e.fwd then ENNReal.ofReal (1 / (l + degree e.fwd)) else 0

theorem measurable_walkWeight (D : EscapeData μ l) (j : ℕ) :
    Measurable (fun p : Env × Env => walkWeight D p.1 j) := by
  apply Measurable.ite (measurableSet_eq_fun measurable_const measurable_const)
  · exact ENNReal.measurable_ofReal.comp
      (measurable_const.div (measurable_const.add
        (Nat.cast_continuous.measurable.comp (continuous_degree.measurable.comp measurable_fst.fst))))
  · apply Measurable.ite
      ((MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | p.1 ≤ p.2}).preimage
        (measurable_const.prodMk (continuous_degree.measurable.comp measurable_fst.fst)))
    · exact ENNReal.measurable_ofReal.comp
        (measurable_const.div (measurable_const.add
          (Nat.cast_continuous.measurable.comp (continuous_degree.measurable.comp measurable_fst.fst))))
    · exact measurable_const

/-- Harmonic outward weights, with a delta at slot one off the good set. -/
noncomputable def qWeight (D : EscapeData μ l) (e : Env) (j : ℕ) : ℝ≥0∞ :=
  if 0 < escapeSum D.β e.fwd then
    ENNReal.ofReal (escapeWeight D.β e.fwd j / escapeSum D.β e.fwd)
  else if j = 1 then 1 else 0

theorem measurable_qWeight (D : EscapeData μ l) (j : ℕ) :
    Measurable (fun p : Env × Env => qWeight D p.1 j) := by
  apply Measurable.ite
    (measurableSet_lt measurable_const (D.measurable_escapeSum.comp measurable_fst.fst))
  · exact ENNReal.measurable_ofReal.comp (((D.measurable_escapeWeight j).comp measurable_fst.fst).div
      (D.measurable_escapeSum.comp measurable_fst.fst))
  · exact measurable_const

/-- The weighted walk moves as an inward term plus the finite outward sum. -/
theorem walk_moveSum (D : EscapeData μ l) (e : Env) {f : Env → ℝ≥0∞} :
    ∑' j, walkWeight D e j * f (move e j) =
      ENNReal.ofReal (l / (l + degree e.fwd)) * f (inward e) +
        ∑ i : Fin (degree e.fwd),
          ENNReal.ofReal (1 / (l + degree e.fwd)) * f (outward e (i.val + 1)) := by
  classical
  rw [ENNReal.tsum_eq_add_tsum_ite 0]
  simp only [walkWeight, ↓reduceIte, move]
  congr 1
  calc
    _ = ∑' j : ℕ, if 1 ≤ j ∧ j ≤ degree e.fwd then
        ENNReal.ofReal (1 / (l + degree e.fwd)) * f (outward e j) else 0 := by
      apply tsum_congr
      intro j
      by_cases hj : j = 0
      · simp [hj]
      · have hj1 : 1 ≤ j := by omega
        simp [hj, hj1]
    _ = _ := slots_degree e.fwd
      (fun j => ENNReal.ofReal (1 / (l + degree e.fwd)) * f (outward e j))

/-- On a good forward tree, the harmonic outward sum has no fallback term. -/
theorem q_moveSum (D : EscapeData μ l) {e : Env} (he : GoodTree D.β l e.fwd)
    {f : Env → ℝ≥0∞} :
    ∑' j, qWeight D e j * f (outward e j) =
      ∑ i : Fin (degree e.fwd),
        ENNReal.ofReal (D.β (child e.fwd (i.val + 1)) / escapeSum D.β e.fwd) *
          f (outward e (i.val + 1)) := by
  classical
  have hS : 0 < escapeSum D.β e.fwd := he.escapeSum_pos
  calc
    _ = ∑' j : ℕ, ENNReal.ofReal (escapeWeight D.β e.fwd j / escapeSum D.β e.fwd) *
        f (outward e j) := by
      apply tsum_congr
      intro j
      simp [qWeight, hS]
    _ = ∑' j : ℕ, if 1 ≤ j ∧ j ≤ degree e.fwd then
        ENNReal.ofReal (D.β (child e.fwd j) / escapeSum D.β e.fwd) *
          f (outward e j) else 0 := by
      apply tsum_congr
      intro j
      by_cases hj : 1 ≤ j ∧ j ≤ degree e.fwd <;> simp [escapeWeight, hj]
    _ = _ := slots_degree e.fwd (fun j =>
      ENNReal.ofReal (D.β (child e.fwd j) / escapeSum D.β e.fwd) * f (outward e j))

/-- The unnormalised walk-invariant and `Q`-invariant reference measures. -/
noncomputable def wRef (D : EscapeData μ l) : Measure Env :=
  D.ref.withDensity fun e => ENNReal.ofReal (wDens D e)

noncomputable def uRef (D : EscapeData μ l) : Measure Env :=
  D.ref.withDensity fun e => ENNReal.ofReal (uDens D e)

/-- The walk's one-step environment kernel. -/
noncomputable def walkKernel (D : EscapeData μ l) : Kernel Env Env :=
  weightedMoves move measurable_move (walkWeight D)

/-- The harmonic outward (`Q`) one-step environment kernel. -/
noncomputable def qKernel (D : EscapeData μ l) : Kernel Env Env :=
  weightedMoves outward measurable_outward (qWeight D)

/-- The walk density times its move sum is the sum of the Case-II and
Case-I left integrands. -/
theorem wDens_walk_moveSum (D : EscapeData μ l) {e : Env}
    (he : GoodTree D.β l e.fwd ∧ GoodTree D.β l e.bwd) (f : Env → ℝ≥0∞) :
    ENNReal.ofReal (wDens D e) * ∑' j, walkWeight D e j * f (move e j) =
      ENNReal.ofReal (l * beta0 D e / Hden D e) * f (inward e) +
        ENNReal.ofReal (beta0 D e / Hden D e) *
          ∑ i : Fin (degree e.fwd), f (outward e (i.val + 1)) := by
  classical
  have hH : 0 < Hden D e := Hden_pos he.1 he.2
  have hlk : 0 < l + degree e.fwd :=
    add_pos_of_pos_of_nonneg D.hl (Nat.cast_nonneg _)
  have hW : 0 ≤ wDens D e := by
    exact div_nonneg (mul_nonneg (add_nonneg (Nat.cast_nonneg _) D.hl.le)
      (D.β_nonneg _)) hH.le
  have hscalar0 : wDens D e * (l / (l + degree e.fwd)) = l * beta0 D e / Hden D e := by
    unfold wDens beta0 Hden fwdSum
    field_simp [ne_of_gt hH, ne_of_gt hlk]
    <;> ring
  have hscalar1 : wDens D e * (1 / (l + degree e.fwd)) = beta0 D e / Hden D e := by
    unfold wDens beta0 Hden fwdSum
    field_simp [ne_of_gt hH, ne_of_gt hlk]
    <;> ring
  rw [walk_moveSum, mul_add, Finset.mul_sum, Finset.mul_sum]
  simp only [← mul_assoc]
  congr 1
  · rw [← ENNReal.ofReal_mul hW, hscalar0]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [← ENNReal.ofReal_mul hW, hscalar1]

/-- The `Q` move sum weighted by `u` is the Case-I left integrand with test
`e ↦ β(e.fwd) • f(e)`. -/
theorem uDens_q_moveSum (D : EscapeData μ l) {e : Env}
    (he : GoodTree D.β l e.fwd ∧ GoodTree D.β l e.bwd) (f : Env → ℝ≥0∞) :
    ENNReal.ofReal (uDens D e) * ∑' j, qWeight D e j * f (outward e j) =
      ENNReal.ofReal (beta0 D e / Hden D e) *
        ∑ i : Fin (degree e.fwd), ENNReal.ofReal (D.β (child e.fwd (i.val + 1))) *
          f (outward e (i.val + 1)) := by
  classical
  have hH : 0 < Hden D e := Hden_pos he.1 he.2
  have hS : 0 < escapeSum D.β e.fwd := he.1.escapeSum_pos
  have hU : 0 ≤ uDens D e := by
    exact div_nonneg (mul_nonneg (D.β_nonneg _) (escapeSum_nonneg D.β_nonneg _)) hH.le
  rw [q_moveSum D he.1, Finset.mul_sum, Finset.mul_sum]
  simp only [← mul_assoc]
  apply Finset.sum_congr rfl
  intro i hi
  have hB : 0 ≤ beta0 D e / Hden D e := div_nonneg (D.β_nonneg _) hH.le
  have hscalar : uDens D e * (D.β (child e.fwd (i.val + 1)) / escapeSum D.β e.fwd) =
      (beta0 D e / Hden D e) * D.β (child e.fwd (i.val + 1)) := by
    unfold uDens beta0 Hden fwdSum
    field_simp [ne_of_gt hH, ne_of_gt hS]
    <;> ring
  rw [← ENNReal.ofReal_mul hU, hscalar, ENNReal.ofReal_mul hB]

/-- Unnormalised invariance for the walk, in integral form. -/
theorem walk_invariant_lintegral (D : EscapeData μ l) {f : Env → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ e, ENNReal.ofReal (wDens D e) * ∑' j, walkWeight D e j * f (move e j) ∂D.ref =
      ∫⁻ e, ENNReal.ofReal (wDens D e) * f e ∂D.ref := by
  have hI : Measurable (fun e : Env => ENNReal.ofReal (l * beta0 D e / Hden D e) *
      f (inward e)) :=
    (ENNReal.measurable_ofReal.comp ((measurable_const.mul D.measurable_beta0).div
      D.measurable_Hden)).mul (hf.comp measurable_inward)
  have hO : Measurable (fun e : Env => ENNReal.ofReal (beta0 D e / Hden D e) *
      ∑ i : Fin (degree e.fwd), f (outward e (i.val + 1))) := by
    apply Measurable.mul (ENNReal.measurable_ofReal.comp
      (D.measurable_beta0.div D.measurable_Hden))
    have hm : Measurable (fun e : Env => ∑' j : ℕ,
        if 1 ≤ j ∧ j ≤ degree e.fwd then f (outward e j) else 0) := by
      apply Measurable.tsum
      intro j
      apply Measurable.ite
        ((MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | 1 ≤ p.1 ∧ p.1 ≤ p.2}).preimage
          (measurable_const.prodMk (continuous_degree.measurable.comp measurable_fst)))
      · exact hf.comp (measurable_outward j)
      · exact measurable_const
    have heq : (fun e : Env => ∑ i : Fin (degree e.fwd), f (outward e (i.val + 1))) =
        (fun e : Env => ∑' j : ℕ,
          if 1 ≤ j ∧ j ≤ degree e.fwd then f (outward e j) else 0) := by
      funext e
      exact (slots_degree e.fwd (fun j => f (outward e j))).symm
    rw [heq]
    exact hm
  calc
    _ = ∫⁻ e, ENNReal.ofReal (l * beta0 D e / Hden D e) * f (inward e) +
        ENNReal.ofReal (beta0 D e / Hden D e) *
          ∑ i : Fin (degree e.fwd), f (outward e (i.val + 1)) ∂D.ref := by
      apply lintegral_congr_ae
      filter_upwards [D.ae_good_ref] with e he
      exact wDens_walk_moveSum D he f
    _ = (∫⁻ e, ENNReal.ofReal (l * beta0 D e / Hden D e) * f (inward e) ∂D.ref) +
        ∫⁻ e, ENNReal.ofReal (beta0 D e / Hden D e) *
          ∑ i : Fin (degree e.fwd), f (outward e (i.val + 1)) ∂D.ref :=
      lintegral_add_left hI _
    _ = (∫⁻ e, ENNReal.ofReal (caseIIDens D e) * f e ∂D.ref) +
        ∫⁻ e, ENNReal.ofReal (caseIDens D e) * f e ∂D.ref := by
      rw [D.caseII hf, D.caseI hf]
    _ = _ := by
      rw [← lintegral_add_left (μ := D.ref)
        (f := fun e => ENNReal.ofReal (caseIIDens D e) * f e)
        (g := fun e => ENNReal.ofReal (caseIDens D e) * f e)
        ((ENNReal.measurable_ofReal.comp D.measurable_caseIIDens).mul hf)]
      apply lintegral_congr_ae
      filter_upwards [D.ae_good_ref] with e he
      have hII : 0 ≤ caseIIDens D e := by
        apply div_nonneg (mul_nonneg (D.β_nonneg _) _) (Hden_pos he.1 he.2).le
        have hsum : escapeSum D.β e.fwd ≤ degree e.fwd := by
          rw [escapeSum_eq_sum_fin]
          calc
            _ ≤ ∑ _i : Fin (degree e.fwd), (1 : ℝ) :=
              Finset.sum_le_sum fun i _ => D.β_le_one _
            _ = _ := by simp
        exact sub_nonneg.mpr hsum
      have hI : 0 ≤ caseIDens D e := by
        exact div_nonneg (mul_nonneg (D.β_nonneg _) (add_nonneg D.hl.le
          (escapeSum_nonneg D.β_nonneg _))) (Hden_pos he.1 he.2).le
      rw [← add_mul, ← ENNReal.ofReal_add hII hI]
      congr 2
      unfold caseIIDens caseIDens wDens
      ring

/-- Unnormalised invariance for `Q`, in integral form. -/
theorem q_invariant_lintegral (D : EscapeData μ l) {f : Env → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ e, ENNReal.ofReal (uDens D e) * ∑' j, qWeight D e j * f (outward e j) ∂D.ref =
      ∫⁻ e, ENNReal.ofReal (uDens D e) * f e ∂D.ref := by
  let g : Env → ℝ≥0∞ := fun e => ENNReal.ofReal (D.β e.fwd) * f e
  have hg : Measurable g :=
    (ENNReal.measurable_ofReal.comp (D.measurable_β.comp measurable_fst)).mul hf
  have hcase := D.caseI hg
  calc
    _ = ∫⁻ e, ENNReal.ofReal (beta0 D e / Hden D e) *
        ∑ i : Fin (degree e.fwd), g (outward e (i.val + 1)) ∂D.ref := by
      apply lintegral_congr_ae
      filter_upwards [D.ae_good_ref] with e he
      exact uDens_q_moveSum D he f
    _ = ∫⁻ e, ENNReal.ofReal (caseIDens D e) * g e ∂D.ref := hcase
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [D.ae_good_ref] with e he
      have hI : 0 ≤ caseIDens D e := by
        exact div_nonneg (mul_nonneg (D.β_nonneg _) (add_nonneg D.hl.le
          (escapeSum_nonneg D.β_nonneg _))) (Hden_pos he.1 he.2).le
      change ENNReal.ofReal (caseIDens D e) * (ENNReal.ofReal (D.β e.fwd) * f e) =
        ENNReal.ofReal (uDens D e) * f e
      rw [← mul_assoc, ← ENNReal.ofReal_mul hI]
      congr 2
      have hS : 0 < l + escapeSum D.β e.fwd :=
        add_pos_of_pos_of_nonneg D.hl (escapeSum_nonneg D.β_nonneg _)
      unfold caseIDens uDens beta0 fwdSum Hden
      rw [D.escape_rec e.fwd]
      field_simp [ne_of_gt hS]
      <;> ring

/-- **Walk invariance, unnormalised:** the walk-density reference measure is invariant
for the ordered environment walk. -/
theorem wRef_invariant (D : EscapeData μ l) : D.walkKernel ∘ₘ D.wRef = D.wRef := by
  have hW : Measurable (fun e : Env => ENNReal.ofReal (wDens D e)) := by
    apply ENNReal.measurable_ofReal.comp
    exact (((Nat.cast_continuous.measurable.comp
      (continuous_degree.measurable.comp measurable_fst)).add measurable_const).mul
        D.measurable_beta0).div D.measurable_Hden
  apply Measure.ext_of_lintegral
  intro f hf
  change (∫⁻ x, f x ∂Measure.bind D.wRef D.walkKernel) = _
  rw [Measure.lintegral_bind (Kernel.measurable _).aemeasurable hf.aemeasurable]
  simp_rw [walkKernel, lintegral_weightedMoves move measurable_move (walkWeight D)
    (measurable_walkWeight D) _ hf]
  have hm : Measurable (fun e : Env => ∑' j, walkWeight D e j * f (move e j)) := by
    apply Measurable.tsum
    intro j
    exact ((D.measurable_walkWeight j).comp (measurable_id.prodMk measurable_id)).mul
      (hf.comp (measurable_move j))
  rw [wRef, lintegral_withDensity_eq_lintegral_mul _ hW hm,
    lintegral_withDensity_eq_lintegral_mul _ hW hf]
  exact D.walk_invariant_lintegral hf

/-- **`Q` invariance, unnormalised:** the `u`-density reference measure is invariant for
the ordered harmonic outward kernel. -/
theorem uRef_invariant (D : EscapeData μ l) : D.qKernel ∘ₘ D.uRef = D.uRef := by
  have hU : Measurable (fun e : Env => ENNReal.ofReal (uDens D e)) := by
    exact ENNReal.measurable_ofReal.comp
      ((D.measurable_beta0.mul D.measurable_fwdSum).div D.measurable_Hden)
  apply Measure.ext_of_lintegral
  intro f hf
  change (∫⁻ x, f x ∂Measure.bind D.uRef D.qKernel) = _
  rw [Measure.lintegral_bind (Kernel.measurable _).aemeasurable hf.aemeasurable]
  simp_rw [qKernel, lintegral_weightedMoves outward measurable_outward (qWeight D)
    (measurable_qWeight D) _ hf]
  have hm : Measurable (fun e : Env => ∑' j, qWeight D e j * f (outward e j)) := by
    apply Measurable.tsum
    intro j
    exact ((D.measurable_qWeight j).comp (measurable_id.prodMk measurable_id)).mul
      (hf.comp (measurable_outward j))
  rw [uRef, lintegral_withDensity_eq_lintegral_mul _ hU hm,
    lintegral_withDensity_eq_lintegral_mul _ hU hf]
  exact D.q_invariant_lintegral hf

/-- Normalisation by the total mass; no probability claim is made when that
mass is zero or infinite. -/
noncomputable def muW (D : EscapeData μ l) : Measure Env := (D.wRef Set.univ)⁻¹ • D.wRef
noncomputable def muU (D : EscapeData μ l) : Measure Env := (D.uRef Set.univ)⁻¹ • D.uRef

/-- Normalised invariance for the walk. -/
theorem muW_invariant (D : EscapeData μ l) : D.walkKernel ∘ₘ D.muW = D.muW := by
  rw [muW, Measure.comp_smul, D.wRef_invariant]

/-- Normalised invariance for `Q`. -/
theorem muU_invariant (D : EscapeData μ l) : D.qKernel ∘ₘ D.muU = D.muU := by
  rw [muU, Measure.comp_smul, D.uRef_invariant]

/-- The normalised walk law is a probability measure exactly when its total
unnormalised mass is finite and nonzero. -/
theorem isProbabilityMeasure_muW (D : EscapeData μ l)
    (h0 : D.wRef Set.univ ≠ 0) (htop : D.wRef Set.univ ≠ ∞) :
    IsProbabilityMeasure D.muW := by
  refine ⟨?_⟩
  rw [muW, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

/-- The normalised `Q` law is a probability measure under the same mass
conditions. -/
theorem isProbabilityMeasure_muU (D : EscapeData μ l)
    (h0 : D.uRef Set.univ ≠ 0) (htop : D.uRef Set.univ ≠ ∞) :
    IsProbabilityMeasure D.muU := by
  refine ⟨?_⟩
  rw [muU, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

end EscapeData

end LPPMonotonicityProof.Speed
