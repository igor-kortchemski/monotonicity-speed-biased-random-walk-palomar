module

public import LPPMonotonicityProof.Speed.Env.CaseI

/-!
# Lin's ordered Case II

This is the ordered form of Case II (inward moves) of Lin's Proposition 4, used in
the occupation argument in the proof of Theorem 2.2 (`thm:speed-formula`).
The harmonic ray is split by its first slot with an
arbitrary environment test; the ordered swap then turns every inward test into
a test at the same resummed environment.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace EscapeData

variable {μ : Measure ℕ} [IsProbabilityMeasure μ] {l : ℝ}

/-- The `i`-th component of the normalized harmonic decomposition of the
inward-move test.  The pair is `(forward, backward)`. -/
noncomputable def caseIIPreSlot (D : EscapeData μ l) (f : Env → ℝ≥0∞) (i : ℕ)
    (p : Tree × Tree) : ℝ≥0∞ :=
  ENNReal.ofReal (l * D.β p.2 / (l - 1 + D.β p.2 + escapeSum D.β p.1)) *
    ENNReal.ofReal (escapeWeight D.β p.2 i / escapeSum D.β p.2) *
      ∫⁻ r, f (inward (p.1, p.2, seqCons i r)) ∂D.harm (child p.2 i)

/-- One ordered Case-II slot after exchanging the backward child with the
forward tree.  The pair is `(new forward, new backward)`. -/
noncomputable def caseIISlot (D : EscapeData μ l) (f : Env → ℝ≥0∞) (i : ℕ)
    (p : Tree × Tree) : ℝ≥0∞ :=
  ENNReal.ofReal (l * D.β (replaceChild p.1 i p.2) /
    (l - 1 + D.β (replaceChild p.1 i p.2) + escapeSum D.β (child p.1 i))) *
    ENNReal.ofReal (escapeWeight D.β (replaceChild p.1 i p.2) i /
      escapeSum D.β (replaceChild p.1 i p.2)) *
      ∫⁻ r, f (p.1, p.2, r) ∂D.harm p.2

theorem measurable_caseIIPreSlot (D : EscapeData μ l) {f : Env → ℝ≥0∞}
    (hf : Measurable f) (i : ℕ) : Measurable (caseIIPreSlot D f i) := by
  have hc : Measurable (fun p : Tree × Tree => child p.2 i) :=
    (continuous_child i).measurable.comp measurable_snd
  have hcons : Measurable (fun x : (Tree × Tree) × (ℕ → ℕ) => seqCons i x.2) := by
    apply measurable_pi_iff.mpr
    intro n
    cases n with
    | zero => exact measurable_const
    | succ n => exact (measurable_pi_apply n).comp measurable_snd
  have henv : Measurable (fun x : (Tree × Tree) × (ℕ → ℕ) =>
      (x.1.1, x.1.2, seqCons i x.2)) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk hcons)
  have htest : Measurable (fun x : (Tree × Tree) × (ℕ → ℕ) =>
      f (inward (x.1.1, x.1.2, seqCons i x.2))) :=
    hf.comp (measurable_inward.comp henv)
  have hray : Measurable (fun p : Tree × Tree =>
      ∫⁻ r, f (inward (p.1, p.2, seqCons i r)) ∂D.harm (child p.2 i)) := by
    exact Measurable.lintegral_kernel_prod_right'
      (κ := D.harm.comap (fun p : Tree × Tree => child p.2 i) hc) htest
  refine (Measurable.mul ?_ ?_).mul hray
  · apply ENNReal.measurable_ofReal.comp
    exact (measurable_const.mul (D.measurable_β.comp measurable_snd)).div
      ((measurable_const.sub measurable_const).add
        (D.measurable_β.comp measurable_snd) |>.add
          (D.measurable_escapeSum.comp measurable_fst))
  · apply ENNReal.measurable_ofReal.comp
    exact ((D.measurable_escapeWeight i).comp measurable_snd).div
      (D.measurable_escapeSum.comp measurable_snd)

theorem measurable_caseIISlot (D : EscapeData μ l) {f : Env → ℝ≥0∞}
    (hf : Measurable f) (i : ℕ) : Measurable (caseIISlot D f i) := by
  have hrep : Measurable (fun p : Tree × Tree => replaceChild p.1 i p.2) :=
    measurable_replaceChild.comp (measurable_const.prodMk measurable_id)
  have hchild : Measurable (fun p : Tree × Tree => child p.1 i) :=
    (continuous_child i).measurable.comp measurable_fst
  have htest : Measurable (fun x : (Tree × Tree) × (ℕ → ℕ) => f (x.1.1, x.1.2, x.2)) :=
    hf.comp MeasurableEquiv.prodAssoc.measurable
  have hray : Measurable (fun p : Tree × Tree => ∫⁻ r, f (p.1, p.2, r) ∂D.harm p.2) := by
    exact Measurable.lintegral_kernel_prod_right'
      (κ := D.harm.comap Prod.snd measurable_snd) htest
  refine (Measurable.mul ?_ ?_).mul hray
  · apply ENNReal.measurable_ofReal.comp
    exact (measurable_const.mul (D.measurable_β.comp hrep)).div
      ((measurable_const.sub measurable_const).add
        (D.measurable_β.comp hrep) |>.add (D.measurable_escapeSum.comp hchild))
  · apply ENNReal.measurable_ofReal.comp
    exact ((D.measurable_escapeWeight i).comp hrep).div
      (D.measurable_escapeSum.comp hrep)

/-- Restricting a pre-slot to backward-valid environments costs nothing:
the harmonic weight is zero outside that set. -/
theorem lintegral_caseIIPreSlot_restrict (D : EscapeData μ l) {f : Env → ℝ≥0∞}
    (_hf : Measurable f) (i : ℕ) :
    ∫⁻ e, caseIIPreSlot D f i (e.fwd, e.bwd) ∂D.ref =
      ∫⁻ e in {e | i ≤ degree e.bwd}, caseIIPreSlot D f i (e.fwd, e.bwd) ∂D.ref := by
  have hs : MeasurableSet {e : Env | i ≤ degree e.bwd} :=
    (MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | p.1 ≤ p.2}).preimage
      (measurable_const.prodMk (continuous_degree.measurable.comp measurable_snd.fst))
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro e
  by_cases hi : i ≤ degree e.bwd
  · simp [hi]
  · simp [hi, caseIIPreSlot, escapeWeight]

/-- The ordered swap identifies one backward-valid Case-II slot with the
resummed environment test. -/
theorem caseII_slot_swap (D : EscapeData μ l) {f : Env → ℝ≥0∞}
    (hf : Measurable f) {i : ℕ} (hi : 1 ≤ i) :
    ∫⁻ e in {e | i ≤ degree e.bwd}, caseIIPreSlot D f i (e.fwd, e.bwd) ∂D.ref =
      ∫⁻ p : Tree × Tree, caseIISlot D f i p
        ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ) := by
  have hpair : Measurable (fun e : Env => (e.fwd, e.bwd)) := measurable_fst.prodMk measurable_snd.fst
  have hpre : Measurable (fun e : Env => caseIIPreSlot D f i (e.fwd, e.bwd)) :=
    (D.measurable_caseIIPreSlot hf i).comp hpair
  rw [lintegral_refBwd D i hpre]
  let H : Tree × Tree → ℝ≥0∞ := fun p =>
    ∫⁻ _r, caseIIPreSlot D f i (p.2, p.1) ∂D.harm p.1
  have hH : Measurable H := by
    exact Measurable.lintegral_kernel_prod_right'
      (κ := D.harm.comap Prod.fst measurable_fst)
      (f := fun x : (Tree × Tree) × (ℕ → ℕ) => caseIIPreSlot D f i (x.1.2, x.1.1))
      ((D.measurable_caseIIPreSlot hf i).comp
        (measurable_fst.snd.prodMk measurable_fst.fst))
  change (∫⁻ p, H p
      ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ)) = _
  calc
    _ = ∫⁻ p, H (swapChild i p)
        ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ) :=
      (lintegral_refFwdProd_swap D i hi hH).symm
    _ = _ := by
      have hs : MeasurableSet {T : Tree | i ≤ degree T} :=
        (MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | p.1 ≤ p.2}).preimage
          (measurable_const.prodMk continuous_degree.measurable)
      have hp : ∀ᵐ p : Tree × Tree
          ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ),
          i ≤ degree p.1 := Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hs)
      apply lintegral_congr_ae
      filter_upwards [hp] with p hp
      have hvi : 1 ≤ i ∧ i ≤ degree p.1 := ⟨hi, hp⟩
      dsimp [H, caseIIPreSlot, caseIISlot, swapChild, inward, Env.fwd, Env.bwd, Env.ray]
      rw [child_replaceChild_same _ hvi, replaceChild_replaceChild_original _ hvi]
      simp only [seqTail_cons, lintegral_const, measure_univ, mul_one]

/-- Invalid post-swap slots likewise integrate to zero outside the restricted
independent pair. -/
theorem lintegral_caseIISlot_restrict (D : EscapeData μ l) {f : Env → ℝ≥0∞}
    (_hf : Measurable f) (i : ℕ) :
    ∫⁻ p : Tree × Tree, caseIISlot D f i p
        ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ) =
      ∫⁻ p : Tree × Tree, caseIISlot D f i p ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
  have hs : MeasurableSet {p : Tree × Tree | i ≤ degree p.1} :=
    (MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | p.1 ≤ p.2}).preimage
      (measurable_const.prodMk (continuous_degree.measurable.comp measurable_fst))
  rw [← Measure.restrict_univ (μ := bienaymeLaw μ), Measure.prod_restrict,
    Measure.restrict_univ]
  rw [show {T : Tree | i ≤ degree T} ×ˢ (Set.univ : Set Tree) =
    {p : Tree × Tree | i ≤ degree p.1} by ext p; simp]
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro p
  by_cases hp : i ≤ degree p.1
  · simp [hp]
  · simp [hp, caseIISlot, escapeWeight]

/-- Contribution of one valid post-swap slot, in the form that can be summed
over the children of the new forward tree. -/
theorem caseIISlot_eq_contrib (D : EscapeData μ l) {F B : Tree}
    (hF : GoodTree D.β l F) (hB : GoodTree D.β l B) {i : ℕ}
    (hi : 1 ≤ i ∧ i ≤ degree F) {f : Env → ℝ≥0∞} (_hf : Measurable f) :
    caseIISlot D f i (F, B) =
      ENNReal.ofReal (D.β B * (1 - D.β (child F i)) /
        (l - 1 + D.β B + escapeSum D.β F)) * ∫⁻ r, f (F, B, r) ∂D.harm B := by
  let σ : ℝ := escapeSum D.β (child F i)
  let b : ℝ := D.β B
  let S : ℝ := escapeSum D.β F
  let X : ℝ := escapeSum D.β (replaceChild F i B)
  have hC : GoodTree D.β l (child F i) := hF.goodChild hi
  have hR : GoodTree D.β l (replaceChild F i B) := D.good_replaceChild hF hi hB
  have hXeq : X = S - σ / (l + σ) + b := by
    dsimp [X, S, σ, b]
    rw [escapeSum_replaceChild hi B, D.escape_rec (child F i)]
  have hX : 0 < X := hR.escapeSum_pos
  have hDrep : 0 < l - 1 + D.β (replaceChild F i B) + escapeSum D.β (child F i) :=
    Hden_pos hC hR
  have hD : 0 < l - 1 + X / (l + X) + σ := by
    have h := hDrep
    rw [D.escape_rec (replaceChild F i B)] at h
    exact h
  have hD' : 0 < l - 1 + b + S := Hden_pos hF hB
  have halg := caseII_slot D.hl (show 0 ≤ σ from escapeSum_nonneg D.β_nonneg _)
    (show 0 < S - σ / (l + σ) + b by rwa [← hXeq])
    (by rw [← hXeq]; exact hD) hD'
  have hA : 0 ≤ l * D.β (replaceChild F i B) /
      (l - 1 + D.β (replaceChild F i B) + escapeSum D.β (child F i)) := by
    exact div_nonneg (mul_nonneg D.hl.le (D.β_nonneg _)) hDrep.le
  have hfactor : l * D.β (replaceChild F i B) /
        (l - 1 + D.β (replaceChild F i B) + escapeSum D.β (child F i)) *
      (escapeWeight D.β (replaceChild F i B) i / escapeSum D.β (replaceChild F i B)) =
      D.β B * (1 - D.β (child F i)) / (l - 1 + D.β B + escapeSum D.β F) := by
    simp only [escapeWeight, degree_replaceChild, if_pos hi, child_replaceChild_same _ hi]
    rw [D.escape_rec (replaceChild F i B), D.escape_rec (child F i)]
    change l * (X / (l + X)) / (l - 1 + X / (l + X) + σ) * (b / X) =
      b * (1 - σ / (l + σ)) / (l - 1 + b + S)
    rw [hXeq]
    exact halg
  rw [caseIISlot, ← ENNReal.ofReal_mul hA, hfactor]

/-- Finite real sum of the one-slot Case-II contributions. -/
theorem caseII_real_sum (D : EscapeData μ l) (F B : Tree) :
    ∑ i : Fin (degree F), D.β B * (1 - D.β (child F (i.val + 1))) /
      (l - 1 + D.β B + escapeSum D.β F) =
    D.β B * ((degree F : ℝ) - escapeSum D.β F) /
      (l - 1 + D.β B + escapeSum D.β F) := by
  classical
  calc
    _ = ∑ i : Fin (degree F), (D.β B / (l - 1 + D.β B + escapeSum D.β F)) *
        (1 - D.β (child F (i.val + 1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (D.β B / (l - 1 + D.β B + escapeSum D.β F)) *
        ∑ i : Fin (degree F), (1 - D.β (child F (i.val + 1))) := by
      rw [Finset.mul_sum]
    _ = (D.β B / (l - 1 + D.β B + escapeSum D.β F)) *
        ((degree F : ℝ) - ∑ i : Fin (degree F), D.β (child F (i.val + 1))) := by
      rw [Finset.sum_sub_distrib]
      simp
    _ = _ := by rw [← escapeSum_eq_sum_fin]; ring

/-- Resummation of all post-swap Case-II slots. -/
theorem caseII_ray (D : EscapeData μ l) {F B : Tree}
    (hF : GoodTree D.β l F) (hB : GoodTree D.β l B)
    {f : Env → ℝ≥0∞} (hf : Measurable f) :
    ∑' i : ℕ, caseIISlot D f i (F, B) =
      ENNReal.ofReal (D.β B * ((degree F : ℝ) - escapeSum D.β F) /
        (l - 1 + D.β B + escapeSum D.β F)) * ∫⁻ r, f (F, B, r) ∂D.harm B := by
  classical
  have hH : 0 < l - 1 + D.β B + escapeSum D.β F := Hden_pos hF hB
  calc
    _ = ∑' i : ℕ, if 1 ≤ i ∧ i ≤ degree F then
        ENNReal.ofReal (D.β B * (1 - D.β (child F i)) /
          (l - 1 + D.β B + escapeSum D.β F)) * ∫⁻ r, f (F, B, r) ∂D.harm B else 0 := by
      apply tsum_congr
      intro i
      by_cases hi : 1 ≤ i ∧ i ≤ degree F
      · rw [caseIISlot_eq_contrib D hF hB hi hf]
        simp [hi]
      · simp [caseIISlot, escapeWeight, hi]
    _ = ∑ i : Fin (degree F), ENNReal.ofReal (D.β B *
          (1 - D.β (child F (i.val + 1))) / (l - 1 + D.β B + escapeSum D.β F)) *
        ∫⁻ r, f (F, B, r) ∂D.harm B := by
      exact slots_degree F (fun i => ENNReal.ofReal (D.β B * (1 - D.β (child F i)) /
        (l - 1 + D.β B + escapeSum D.β F)) * ∫⁻ r, f (F, B, r) ∂D.harm B)
    _ = (∑ i : Fin (degree F), ENNReal.ofReal (D.β B *
          (1 - D.β (child F (i.val + 1))) / (l - 1 + D.β B + escapeSum D.β F))) *
        ∫⁻ r, f (F, B, r) ∂D.harm B := by rw [Finset.sum_mul]
    _ = ENNReal.ofReal (∑ i : Fin (degree F), D.β B *
          (1 - D.β (child F (i.val + 1))) / (l - 1 + D.β B + escapeSum D.β F)) *
        ∫⁻ r, f (F, B, r) ∂D.harm B := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact div_nonneg (mul_nonneg (D.β_nonneg B)
        (sub_nonneg.mpr (D.β_le_one _))) hH.le
    _ = _ := by rw [caseII_real_sum]

/-- Split the inward test by the first harmonic-ray slot, retaining the same
arbitrary measurable test in every summand. -/
theorem caseII_ray_split (D : EscapeData μ l) (F B : Tree)
    (hF : GoodTree D.β l F) (hB : GoodTree D.β l B)
    {f : Env → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ r, ENNReal.ofReal (l * D.β B / (l - 1 + D.β B + escapeSum D.β F)) *
        f (inward (F, B, r)) ∂D.harm B =
      ∑' i : ℕ, caseIIPreSlot D f i (F, B) := by
  have hA : 0 ≤ l * D.β B / (l - 1 + D.β B + escapeSum D.β F) := by
    have hpos : 0 < l - 1 + D.β B + escapeSum D.β F := Hden_pos hF hB
    exact div_nonneg (mul_nonneg D.hl.le (D.β_nonneg B)) hpos.le
  have htest : Measurable (fun r : ℕ → ℕ => f (inward (F, B, r))) := by
    apply hf.comp
    apply measurable_inward.comp
    exact measurable_const.prodMk (measurable_const.prodMk measurable_id)
  calc
    _ = ENNReal.ofReal (l * D.β B / (l - 1 + D.β B + escapeSum D.β F)) *
        ∫⁻ r, f (inward (F, B, r)) ∂D.harm B :=
      lintegral_const_mul _ htest
    _ = ENNReal.ofReal (l * D.β B / (l - 1 + D.β B + escapeSum D.β F)) *
        ∑' i : ℕ, ENNReal.ofReal (escapeWeight D.β B i / escapeSum D.β B) *
          ∫⁻ r, f (inward (F, B, seqCons i r)) ∂D.harm (child B i) := by
      rw [D.harm_firstStep_normalized B hB htest]
    _ = _ := by
      simp only [caseIIPreSlot, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro i
      ac_rfl

/-- Full iterated-reference formula, with the forward tree first. -/
theorem lintegral_ref_forward (D : EscapeData μ l) {g : Env → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ e, g e ∂D.ref = ∫⁻ p : Tree × Tree,
      ∫⁻ r, g (p.1, p.2, r) ∂D.harm p.2 ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
  simpa [EscapeData.ref, refFwdProd] using D.lintegral_refFwdProd 0 hg

/-- **Lin's ordered Case II.**  Inward moves, for every nonnegative
measurable environment test. -/
theorem caseII (D : EscapeData μ l) {f : Env → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ e, ENNReal.ofReal (l * beta0 D e / Hden D e) * f (inward e) ∂D.ref =
      ∫⁻ e, ENNReal.ofReal (caseIIDens D e) * f e ∂D.ref := by
  classical
  have hpair : Measurable (fun e : Env => (e.fwd, e.bwd)) := measurable_fst.prodMk measurable_snd.fst
  calc
    _ = ∫⁻ p : Tree × Tree, ∫⁻ r,
        ENNReal.ofReal (l * D.β p.2 / (l - 1 + D.β p.2 + escapeSum D.β p.1)) *
          f (inward (p.1, p.2, r)) ∂D.harm p.2
        ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
      exact lintegral_ref_forward D
        ((ENNReal.measurable_ofReal.comp ((measurable_const.mul D.measurable_beta0).div
          D.measurable_Hden)).mul (hf.comp measurable_inward))
    _ = ∫⁻ p : Tree × Tree, ∑' i : ℕ, caseIIPreSlot D f i p
        ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
      apply lintegral_congr_ae
      filter_upwards [D.ae_good_pair] with p hp
      exact caseII_ray_split D p.1 p.2 hp.2 hp.1 hf
    _ = ∑' i : ℕ, ∫⁻ p : Tree × Tree, caseIIPreSlot D f i p
        ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
      rw [lintegral_tsum]
      intro i
      exact (D.measurable_caseIIPreSlot hf i).aemeasurable
    _ = ∑' i : ℕ, ∫⁻ e, caseIIPreSlot D f i (e.fwd, e.bwd) ∂D.ref := by
      apply tsum_congr
      intro i
      rw [lintegral_ref_forward D (g := fun e => caseIIPreSlot D f i (e.fwd, e.bwd))
        ((D.measurable_caseIIPreSlot hf i).comp hpair)]
      simp only [Env.fwd, Env.bwd, lintegral_const, measure_univ, mul_one]
    _ = ∑' i : ℕ, ∫⁻ e in {e | i ≤ degree e.bwd},
        caseIIPreSlot D f i (e.fwd, e.bwd) ∂D.ref := by
      apply tsum_congr
      intro i
      exact lintegral_caseIIPreSlot_restrict D hf i
    _ = ∑' i : ℕ, ∫⁻ p : Tree × Tree, caseIISlot D f i p
        ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ) := by
      apply tsum_congr
      intro i
      by_cases hi : 1 ≤ i
      · exact caseII_slot_swap D hf hi
      · have hi0 : i = 0 := by omega
        subst i
        simp [caseIIPreSlot, caseIISlot, escapeWeight]
    _ = ∑' i : ℕ, ∫⁻ p : Tree × Tree, caseIISlot D f i p
        ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
      apply tsum_congr
      intro i
      exact lintegral_caseIISlot_restrict D hf i
    _ = ∫⁻ p : Tree × Tree, ∑' i : ℕ, caseIISlot D f i p
        ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
      rw [lintegral_tsum]
      intro i
      exact (D.measurable_caseIISlot hf i).aemeasurable
    _ = ∫⁻ p : Tree × Tree,
        ENNReal.ofReal (D.β p.2 * ((degree p.1 : ℝ) - escapeSum D.β p.1) /
          (l - 1 + D.β p.2 + escapeSum D.β p.1)) * ∫⁻ r, f (p.1, p.2, r) ∂D.harm p.2
        ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
      apply lintegral_congr_ae
      filter_upwards [D.ae_good_pair] with p hp
      exact caseII_ray D hp.2 hp.1 hf
    _ = _ := by
      rw [lintegral_ref_forward D (g := fun e => ENNReal.ofReal (caseIIDens D e) * f e)
        ((ENNReal.measurable_ofReal.comp D.measurable_caseIIDens).mul hf)]
      apply lintegral_congr
      intro p
      change _ = ∫⁻ r, ENNReal.ofReal (D.β p.2 * ((degree p.1 : ℝ) - escapeSum D.β p.1) /
        (l - 1 + D.β p.2 + escapeSum D.β p.1)) * f (p.1, p.2, r) ∂D.harm p.2
      exact (lintegral_const_mul _ (hf.comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)))).symm

end EscapeData

end LPPMonotonicityProof.Speed
