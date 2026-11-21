module

public import LPPMonotonicityProof.Speed.Env.Lin

/-!
# Lin's ordered Case I

This is the ordered form of Case I (outward moves) of Lin's Proposition 4, used in
the occupation argument in the proof of Theorem 2.2 (`thm:speed-formula`).
The harmonic first-step identity is used with an arbitrary
environment test at the already resummed forward/backward pair.  This avoids
changing the shape of the test after the ordered child swap.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace EscapeData

variable {μ : Measure ℕ} [IsProbabilityMeasure μ] {l : ℝ}

/-- One ordered slot after the Case-I child swap.  The first component of `p`
is the backward tree and the second is the forward tree. -/
noncomputable def caseISlot (D : EscapeData μ l) (f : Env → ℝ≥0∞) (i : ℕ)
    (p : Tree × Tree) : ℝ≥0∞ :=
  ENNReal.ofReal (escapeWeight D.β p.1 i /
      (l - 1 + D.β p.2 + escapeSum D.β p.1)) *
    ∫⁻ r, f (p.2, p.1, seqCons i r) ∂D.harm (child p.1 i)

theorem measurable_caseISlot (D : EscapeData μ l) {f : Env → ℝ≥0∞}
    (hf : Measurable f) (i : ℕ) : Measurable (caseISlot D f i) := by
  have hc : Measurable (fun p : Tree × Tree => child p.1 i) :=
    (continuous_child i).measurable.comp measurable_fst
  have hcons : Measurable (fun x : (Tree × Tree) × (ℕ → ℕ) => seqCons i x.2) := by
    apply measurable_pi_iff.mpr
    intro n
    cases n with
    | zero => exact measurable_const
    | succ n => exact (measurable_pi_apply n).comp measurable_snd
  have htest : Measurable (fun x : (Tree × Tree) × (ℕ → ℕ) =>
      f (x.1.2, x.1.1, seqCons i x.2)) :=
    hf.comp (measurable_fst.snd.prodMk (measurable_fst.fst.prodMk hcons))
  have hray : Measurable (fun p : Tree × Tree =>
      ∫⁻ r, f (p.2, p.1, seqCons i r) ∂D.harm (child p.1 i)) := by
    exact Measurable.lintegral_kernel_prod_right'
      (κ := D.harm.comap (fun p : Tree × Tree => child p.1 i) hc) htest
  apply Measurable.mul _ hray
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.div
  · exact (D.measurable_escapeWeight i).comp measurable_fst
  · exact (measurable_const.sub measurable_const).add
      (D.measurable_β.comp measurable_snd) |>.add
        (D.measurable_escapeSum.comp measurable_fst)

/-- The unnormalized harmonic first-step identity for an arbitrary test at the
same resummed environment. -/
theorem harm_firstStep_env (D : EscapeData μ l) (F B : Tree)
    {G : Env → ℝ≥0∞} (hG : Measurable G) :
    ∑' i : ℕ, ENNReal.ofReal (escapeWeight D.β B i) *
        ∫⁻ r, G (F, B, seqCons i r) ∂D.harm (child B i) =
      ENNReal.ofReal (escapeSum D.β B) * ∫⁻ r, G (F, B, r) ∂D.harm B := by
  have hg : Measurable (fun r => G (F, B, r)) :=
    hG.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  exact (D.harm_firstStep B hg).symm

/-- Case-I ray resummation.  Every slot on the left tests the same `(F, B)`;
only the ray is extended by `seqCons`. -/
theorem caseI_ray (D : EscapeData μ l) {F B : Tree}
    (hF : GoodTree D.β l F) (hB : GoodTree D.β l B)
    {f : Env → ℝ≥0∞} (hf : Measurable f) :
    ∑' i : ℕ, caseISlot D f i (B, F) =
      ENNReal.ofReal (escapeSum D.β B / (l - 1 + D.β F + escapeSum D.β B)) *
        ∫⁻ r, f (F, B, r) ∂D.harm B := by
  have hH : 0 < l - 1 + D.β F + escapeSum D.β B := Hden_pos hB hF
  have hray : Measurable (fun r : ℕ → ℕ => f (F, B, r)) :=
    hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  calc
    _ = ∑' i : ℕ, (ENNReal.ofReal (escapeWeight D.β B i) *
          ∫⁻ r, f (F, B, seqCons i r) ∂D.harm (child B i)) /
        ENNReal.ofReal (l - 1 + D.β F + escapeSum D.β B) := by
      apply tsum_congr
      intro i
      simp only [caseISlot, ENNReal.ofReal_div_of_pos hH, ENNReal.div_eq_inv_mul]
      ac_rfl
    _ = (∑' i : ℕ, ENNReal.ofReal (escapeWeight D.β B i) *
          ∫⁻ r, f (F, B, seqCons i r) ∂D.harm (child B i)) /
        ENNReal.ofReal (l - 1 + D.β F + escapeSum D.β B) := by
      simp only [ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left]
    _ = (ENNReal.ofReal (escapeSum D.β B) * ∫⁻ r, f (F, B, r) ∂D.harm B) /
        ENNReal.ofReal (l - 1 + D.β F + escapeSum D.β B) := by
      rw [harm_firstStep_env D F B hf]
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos hH]
      simp only [ENNReal.div_eq_inv_mul]
      ac_rfl

/-- The ordered child swap identifies one forward-valid Case-I slot with the
resummed slot test. -/
theorem caseI_slot_swap (D : EscapeData μ l) {f : Env → ℝ≥0∞}
    (hf : Measurable f) {i : ℕ} (hi : 1 ≤ i) :
    ∫⁻ e, ENNReal.ofReal (beta0 D e / Hden D e) * f (outward e i)
        ∂D.refFwdProd i =
      ∫⁻ p : Tree × Tree, caseISlot D f i p
        ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ) := by
  have hout : Measurable (fun e : Env =>
      ENNReal.ofReal (beta0 D e / Hden D e) * f (outward e i)) :=
    (ENNReal.measurable_ofReal.comp (D.measurable_beta0.div D.measurable_Hden)).mul
      (hf.comp (measurable_outward i))
  let H : Tree × Tree → ℝ≥0∞ := fun p => ∫⁻ r,
    ENNReal.ofReal (beta0 D (p.1, p.2, r) / Hden D (p.1, p.2, r)) *
      f (outward (p.1, p.2, r) i) ∂D.harm p.2
  have hH : Measurable H := by
    exact Measurable.lintegral_kernel_prod_right'
      (κ := D.harm.comap Prod.snd measurable_snd)
      (f := (fun e : Env => ENNReal.ofReal (beta0 D e / Hden D e) * f (outward e i)) ∘
        MeasurableEquiv.prodAssoc) (hout.comp MeasurableEquiv.prodAssoc.measurable)
  rw [lintegral_refFwdProd D i hout]
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
      have htest : Measurable (fun r : ℕ → ℕ => f (p.2, p.1, seqCons i r)) := by
        apply hf.comp
        exact measurable_const.prodMk (measurable_const.prodMk
          (measurable_seqCons.comp (measurable_const.prodMk measurable_id)))
      dsimp [H, caseISlot, swapChild, outward, beta0, Hden, fwdSum, Env.fwd, Env.bwd,
        Env.ray]
      rw [child_replaceChild_same _ hvi, replaceChild_replaceChild_original _ hvi]
      simp only [escapeWeight, if_pos hvi]
      rw [escapeSum_replaceChild hvi p.2]
      have hden : l - 1 + D.β (child p.1 i) +
          (escapeSum D.β p.1 - D.β (child p.1 i) + D.β p.2) =
        l - 1 + D.β p.2 + escapeSum D.β p.1 := by ring
      rw [hden, lintegral_const_mul _ htest]

/-- Invalid slots vanish, so their restricted pair integral can be replaced by
the full independent pair integral. -/
theorem lintegral_caseISlot_restrict (D : EscapeData μ l) {f : Env → ℝ≥0∞}
    (_hf : Measurable f) (i : ℕ) :
    ∫⁻ p : Tree × Tree, caseISlot D f i p
        ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ) =
      ∫⁻ p : Tree × Tree, caseISlot D f i p ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
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
  · simp [hp, caseISlot, escapeWeight]

/-- Goodness of the backward/forward independent pair (in that order). -/
theorem ae_good_pair (D : EscapeData μ l) : ∀ᵐ p : Tree × Tree
    ∂(bienaymeLaw μ).prod (bienaymeLaw μ),
    GoodTree D.β l p.2 ∧ GoodTree D.β l p.1 := by
  have hb : ∀ᵐ p : Tree × Tree ∂(bienaymeLaw μ).prod (bienaymeLaw μ),
      GoodTree D.β l p.1 := Measure.quasiMeasurePreserving_fst.ae D.ae_good
  have hf : ∀ᵐ p : Tree × Tree ∂(bienaymeLaw μ).prod (bienaymeLaw μ),
      GoodTree D.β l p.2 := Measure.quasiMeasurePreserving_snd.ae D.ae_good
  filter_upwards [hf, hb] with p hpF hpB
  exact ⟨hpF, hpB⟩

/-- The scalar identity after the Case-I ray resummation. -/
theorem caseI_density (D : EscapeData μ l) {F B : Tree}
    (hF : GoodTree D.β l F) (hB : GoodTree D.β l B) :
    escapeSum D.β B / (l - 1 + D.β F + escapeSum D.β B) =
      D.β B * (l + escapeSum D.β F) / (l - 1 + D.β B + escapeSum D.β F) := by
  rw [D.escape_rec B, D.escape_rec F]
  exact caseI_algebra D.hl (escapeSum_nonneg D.β_nonneg B)
    (escapeSum_nonneg D.β_nonneg F) (by rw [← D.escape_rec F]; exact Hden_pos hB hF)
    (by rw [← D.escape_rec B]; exact Hden_pos hF hB)

/-- Full iterated-reference formula, with the backward tree first. -/
theorem lintegral_ref_backward (D : EscapeData μ l) {g : Env → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ e, g e ∂D.ref = ∫⁻ p : Tree × Tree,
      ∫⁻ r, g (p.2, p.1, r) ∂D.harm p.1 ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
  simpa using D.lintegral_refBwd 0 hg

/-- **Lin's ordered Case I.**  Outward moves, for every nonnegative
measurable environment test. -/
theorem caseI (D : EscapeData μ l) {f : Env → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ e, ENNReal.ofReal (beta0 D e / Hden D e) *
        ∑ i : Fin (degree e.fwd), f (outward e (i.val + 1)) ∂D.ref =
      ∫⁻ e, ENNReal.ofReal (caseIDens D e) * f e ∂D.ref := by
  classical
  calc
    _ = ∫⁻ e, ∑' i : ℕ, if 1 ≤ i ∧ i ≤ degree e.fwd then
          ENNReal.ofReal (beta0 D e / Hden D e) * f (outward e i) else 0 ∂D.ref := by
      apply lintegral_congr
      intro e
      rw [← slots_degree e.fwd (fun i => f (outward e i)), slots, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro i
      by_cases hi : 1 ≤ i ∧ i ≤ degree e.fwd <;> simp [hi]
    _ = ∑' i : ℕ, ∫⁻ e, if 1 ≤ i ∧ i ≤ degree e.fwd then
          ENNReal.ofReal (beta0 D e / Hden D e) * f (outward e i) else 0 ∂D.ref := by
      rw [lintegral_tsum]
      intro i
      have hs : MeasurableSet {e : Env | 1 ≤ i ∧ i ≤ degree e.fwd} :=
        (MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | 1 ≤ p.1 ∧ p.1 ≤ p.2}).preimage
          (measurable_const.prodMk (continuous_degree.measurable.comp measurable_fst))
      have hout : Measurable (fun e : Env =>
          ENNReal.ofReal (beta0 D e / Hden D e) * f (outward e i)) :=
        (ENNReal.measurable_ofReal.comp (D.measurable_beta0.div D.measurable_Hden)).mul
          (hf.comp (measurable_outward i))
      exact (Measurable.ite hs hout measurable_const).aemeasurable
    _ = ∑' i : ℕ, ∫⁻ p : Tree × Tree, caseISlot D f i p
        ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ) := by
      apply tsum_congr
      intro i
      by_cases hi : 1 ≤ i
      · have hs : MeasurableSet {e : Env | i ≤ degree e.fwd} :=
          (MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | p.1 ≤ p.2}).preimage
            (measurable_const.prodMk (continuous_degree.measurable.comp measurable_fst))
        have hind : (fun e : Env => if 1 ≤ i ∧ i ≤ degree e.fwd then
              ENNReal.ofReal (beta0 D e / Hden D e) * f (outward e i) else 0) =
            {e : Env | i ≤ degree e.fwd}.indicator (fun e =>
              ENNReal.ofReal (beta0 D e / Hden D e) * f (outward e i)) := by
          funext e
          by_cases hdeg : i ≤ degree e.fwd <;> simp [hi, hdeg]
        rw [hind, lintegral_indicator hs]
        change (∫⁻ e, ENNReal.ofReal (beta0 D e / Hden D e) * f (outward e i)
            ∂D.refFwd i) = _
        rw [← refFwdProd_eq_refFwd]
        exact caseI_slot_swap D hf hi
      · have hi0 : i = 0 := by omega
        subst i
        simp [caseISlot, escapeWeight]
    _ = ∑' i : ℕ, ∫⁻ p : Tree × Tree, caseISlot D f i p
        ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
      apply tsum_congr
      intro i
      exact lintegral_caseISlot_restrict D hf i
    _ = ∫⁻ p : Tree × Tree, ∑' i : ℕ, caseISlot D f i p
        ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
      rw [lintegral_tsum]
      intro i
      exact (D.measurable_caseISlot hf i).aemeasurable
    _ = ∫⁻ p : Tree × Tree,
        ENNReal.ofReal (escapeSum D.β p.1 / (l - 1 + D.β p.2 + escapeSum D.β p.1)) *
          ∫⁻ r, f (p.2, p.1, r) ∂D.harm p.1
        ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
      apply lintegral_congr_ae
      filter_upwards [D.ae_good_pair] with p hp
      exact caseI_ray D hp.1 hp.2 hf
    _ = ∫⁻ p : Tree × Tree, ∫⁻ r, ENNReal.ofReal (caseIDens D (p.2, p.1, r)) *
          f (p.2, p.1, r) ∂D.harm p.1 ∂(bienaymeLaw μ).prod (bienaymeLaw μ) := by
      apply lintegral_congr_ae
      filter_upwards [D.ae_good_pair] with p hp
      rw [caseI_density D hp.1 hp.2]
      change _ = ∫⁻ r, ENNReal.ofReal (D.β p.1 * (l + escapeSum D.β p.2) /
        (l - 1 + D.β p.1 + escapeSum D.β p.2)) * f (p.2, p.1, r) ∂D.harm p.1
      exact (lintegral_const_mul _ (hf.comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)))).symm
    _ = _ := by
      symm
      exact lintegral_ref_backward D
        ((ENNReal.measurable_ofReal.comp (D.measurable_caseIDens)).mul hf)

end EscapeData

end LPPMonotonicityProof.Speed
