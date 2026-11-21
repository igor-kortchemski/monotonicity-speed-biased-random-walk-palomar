module

public import LPPMonotonicityProof.Speed.Env.Swap
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Kernel algebra for Lin's ordered Cases I and II

These identities contain no probabilistic assertion; they
are the algebraic part of the vacated-slot calculation.
-/

@[expose] public section

namespace LPPMonotonicityProof.Speed

/-- The escape-recursion identity used after the outward child swap. -/
theorem caseI_algebra {l x y : ℝ} (hl : 0 < l) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hD : 0 < l - 1 + y / (l + y) + x)
    (hD' : 0 < l - 1 + x / (l + x) + y) :
    x / (l - 1 + y / (l + y) + x) =
      x / (l + x) * (l + y) / (l - 1 + x / (l + x) + y) := by
  have hlx : l + x ≠ 0 := by positivity
  have hly : l + y ≠ 0 := by positivity
  have hD0 : l - 1 + y / (l + y) + x ≠ 0 := ne_of_gt hD
  have hD'0 : l - 1 + x / (l + x) + y ≠ 0 := ne_of_gt hD'
  field_simp
  ring

/-- The contribution of one vacated slot in Lin's Case II. -/
theorem caseII_slot {l σ b' S' : ℝ} (hl : 0 < l) (hσ : 0 ≤ σ)
    (hX : 0 < S' - σ / (l + σ) + b')
    (hD : 0 < l - 1 + (S' - σ / (l + σ) + b') /
        (l + (S' - σ / (l + σ) + b')) + σ)
    (hD' : 0 < l - 1 + b' + S') :
    l * ((S' - σ / (l + σ) + b') / (l + (S' - σ / (l + σ) + b'))) /
        (l - 1 + (S' - σ / (l + σ) + b') /
          (l + (S' - σ / (l + σ) + b')) + σ) * (b' / (S' - σ / (l + σ) + b')) =
      b' * (1 - σ / (l + σ)) / (l - 1 + b' + S') := by
  let s := σ / (l + σ)
  let X := S' - s + b'
  change l * (X / (l + X)) / (l - 1 + X / (l + X) + σ) * (b' / X) =
    b' * (1 - s) / (l - 1 + b' + S')
  have hlσ : l + σ ≠ 0 := by positivity
  have hX' : 0 < X := hX
  have hD'' : 0 < l - 1 + X / (l + X) + σ := hD
  have hX0 : X ≠ 0 := ne_of_gt hX'
  have hlX : l + X ≠ 0 := by positivity
  have hD0 : l - 1 + X / (l + X) + σ ≠ 0 := ne_of_gt hD''
  have hD'0 : l - 1 + b' + S' ≠ 0 := ne_of_gt hD'
  have hS : S' = X + s - b' := by
    dsimp [X, s]
    ring
  rw [hS] at hD' hD'0 ⊢
  have hC : -l + l * X + l * σ + l ^ 2 + X * σ ≠ 0 := by
    intro hC
    apply hD0
    apply (mul_eq_zero.mp ?_).resolve_right hlX
    calc
      (l - 1 + X / (l + X) + σ) * (l + X) =
          -l + l * X + l * σ + l ^ 2 + X * σ := by
            field_simp [hlX]
            ring
      _ = 0 := hC
  field_simp [hC, hX0, hlX, hD0, hD'0]
  have hC2 : (l + X) * (l - 1) + X + (l + X) * σ ≠ 0 := by
    convert hC using 1 <;> ring
  rw [div_eq_iff hC2]
  have hsrel : σ = s * (l + σ) := by
    dsimp [s]
    field_simp [hlσ]
  linear_combination (-b' * (X + l)) * hsrel


open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The descendant tree at an address. -/
def subtree (T : Tree) (v : Address) : Tree :=
  ⟨fun u => T.val (v ++ u), by
    intro u j hj
    simpa only [List.append_assoc] using T.property (v ++ u) j hj⟩

@[simp] theorem subtree_offspring (T : Tree) (v u : Address) :
    (subtree T v).val u = T.val (v ++ u) := rfl

theorem degree_subtree (T : Tree) (v : Address) : degree (subtree T v) = T.val v := by
  change T.val (v ++ []) = T.val v
  rw [List.append_nil]

@[simp] theorem subtree_nil (T : Tree) : subtree T [] = T := by
  apply Subtype.ext
  funext u
  simp [subtree]

theorem child_subtree (T : Tree) (v : Address) (j : ℕ) :
    child (subtree T v) j = subtree T (v ++ [j]) := by
  apply Subtype.ext
  funext u
  simp [subtree, List.append_assoc]

theorem subtree_cons (T : Tree) (j : ℕ) (v : Address) :
    subtree T (j :: v) = subtree (child T j) v := by
  apply Subtype.ext
  funext u
  simp [subtree]

theorem present_valid_of_append (T : Tree) (v : Address) (j : ℕ) (u : Address)
    (h : Present T (v ++ j :: u)) : 1 ≤ j ∧ j ≤ T.val v := by
  induction v generalizing T with
  | nil => exact ⟨h.1, h.2.1⟩
  | cons a v ih => exact ih (child T a) h.2.2

theorem present_append_singleton (T : Tree) (v : Address) (j : ℕ)
    (hv : Present T v) : Present T (v ++ [j]) ↔ 1 ≤ j ∧ j ≤ T.val v := by
  induction v generalizing T with
  | nil =>
      simp only [List.nil_append]
      simp only [present_cons, present_nil, and_true, degree]
  | cons a v ih =>
      have hv' : Present (child T a) v := hv.2.2
      simp only [List.cons_append, present_cons, child_offspring]
      rw [ih (child T a) hv']
      constructor
      · intro h
        exact h.2.2
      · intro h
        exact ⟨hv.1, hv.2.1, h⟩

theorem present_subtree (T : Tree) (v u : Address) (hv : Present T v) :
    Present (subtree T v) u ↔ Present T (v ++ u) := by
  induction u generalizing T v with
  | nil => simp [hv]
  | cons j u ih =>
      rw [present_cons, child_subtree]
      constructor
      · intro h
        have hvj : Present T (v ++ [j]) := (present_append_singleton T v j hv).2 ⟨h.1, by
          have hh := h.2.1
          rw [degree_subtree] at hh
          exact hh⟩
        have hu := (ih T (v ++ [j]) hvj).1 h.2.2
        simpa [List.append_assoc] using hu
      · intro h
        have hvj : 1 ≤ j ∧ j ≤ T.val v := present_valid_of_append T v j u h
        have hp : Present T (v ++ [j]) := (present_append_singleton T v j hv).2 hvj
        refine ⟨hvj.1, by rw [degree_subtree]; exact hvj.2, ?_⟩
        exact (ih T (v ++ [j]) hp).2 (by simpa [List.append_assoc] using h)

/-- Nonnegative escape weights on the valid ordered child slots. -/
def escapeWeight (β : Tree → ℝ) (T : Tree) (i : ℕ) : ℝ :=
  if 1 ≤ i ∧ i ≤ degree T then β (child T i) else 0

/-- The finite child sum, written as a countable sum for slotwise integration. -/
noncomputable def escapeSum (β : Tree → ℝ) (T : Tree) : ℝ :=
  ∑' i : ℕ, escapeWeight β T i

theorem escapeSum_eq_sum_Icc (β : Tree → ℝ) (T : Tree) :
    escapeSum β T = ∑ i ∈ Finset.Icc 1 (degree T), β (child T i) := by
  unfold escapeSum
  rw [tsum_eq_sum (s := Finset.Icc 1 (degree T))]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Icc] at hi
    simp [escapeWeight, hi]
  · intro i hi
    simp only [Finset.mem_Icc, not_and, not_le] at hi
    simp [escapeWeight]
    omega

theorem escapeWeight_nonneg {β : Tree → ℝ} (hβ : ∀ T, 0 ≤ β T) (T : Tree) (i : ℕ) :
    0 ≤ escapeWeight β T i := by
  simp only [escapeWeight]
  split <;> simp [hβ]

theorem escapeSum_nonneg {β : Tree → ℝ} (hβ : ∀ T, 0 ≤ β T) (T : Tree) :
    0 ≤ escapeSum β T :=
  tsum_nonneg (escapeWeight_nonneg hβ T)

theorem escapeSum_pos {β : Tree → ℝ} {T : Tree}
    (hdeg : 0 < degree T) (hpos : ∀ i, 1 ≤ i → i ≤ degree T → 0 < β (child T i)) :
    0 < escapeSum β T := by
  rw [escapeSum_eq_sum_Icc]
  apply Finset.sum_pos
  · intro i hi
    have hv : 1 ≤ i ∧ i ≤ degree T := by simpa [Finset.mem_Icc] using hi
    exact hpos i hv.1 hv.2
  · exact ⟨1, by simp only [Finset.mem_Icc, le_refl, true_and]; exact hdeg⟩

/-- The escape-sum change caused by replacing one ordered child. -/
theorem escapeSum_replaceChild {β : Tree → ℝ} {T : Tree} {i : ℕ}
    (hi : 1 ≤ i ∧ i ≤ degree T) (R : Tree) :
    escapeSum β (replaceChild T i R) =
      escapeSum β T - β (child T i) + β R := by
  rw [escapeSum_eq_sum_Icc, escapeSum_eq_sum_Icc, degree_replaceChild]
  have hm : i ∈ Finset.Icc 1 (degree T) := by simpa [Finset.mem_Icc] using hi
  have he : ∀ j ∈ Finset.Icc 1 (degree T),
      β (child (replaceChild T i R) j) = Function.update (β ∘ child T) i (β R) j := by
    intro j hj
    have hv : 1 ≤ j ∧ j ≤ degree T := by simpa [Finset.mem_Icc] using hj
    by_cases hji : j = i
    · subst j
      simp [child_replaceChild_same, hi]
    · rw [child_replaceChild_of_ne R hji, Function.update_of_ne hji]
      rfl
  calc
    _ = ∑ j ∈ Finset.Icc 1 (degree T), Function.update (β ∘ child T) i (β R) j :=
      Finset.sum_congr rfl he
    _ = _ := by
      rw [Finset.sum_update_of_mem hm, ← Finset.sum_erase_add _ _ hm]
      simp only [Finset.sdiff_singleton_eq_erase, Function.comp_apply]
      ring

/-- A tree on which every present subtree has the positivity needed by Lin's densities. -/
def GoodTree (β : Tree → ℝ) (l : ℝ) (T : Tree) : Prop :=
  0 < degree T ∧ ∀ v, Present T v →
    0 < T.val v ∧ 0 < β (subtree T v) ∧ (l < 1 → 1 - l ≤ β (subtree T v))

theorem GoodTree.escape_pos {β : Tree → ℝ} {l : ℝ} {T : Tree}
    (hT : GoodTree β l T) : 0 < β T := by
  simpa using (hT.2 [] (present_nil T)).2.1

theorem GoodTree.escape_lower {β : Tree → ℝ} {l : ℝ} {T : Tree}
    (hT : GoodTree β l T) (hl : l < 1) : 1 - l ≤ β T := by
  simpa using (hT.2 [] (present_nil T)).2.2 hl

theorem GoodTree.goodChild {β : Tree → ℝ} {l : ℝ} {T : Tree}
    (hT : GoodTree β l T) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ degree T) :
    GoodTree β l (child T i) := by
  constructor
  · have hp : Present T [i] := by simp [hi]
    exact hT.2 [i] hp |>.1
  · intro v hv
    have hp : Present T (i :: v) := by simpa [hi] using hv
    simpa [← subtree_cons] using hT.2 (i :: v) hp

theorem GoodTree.child_escape_pos {β : Tree → ℝ} {l : ℝ} {T : Tree}
    (hT : GoodTree β l T) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ degree T) :
    0 < β (child T i) := by
  have hp : Present T [i] := by simp [hi]
  have hst : subtree T [i] = child T i := by rw [subtree_cons, subtree_nil]
  have hβ := (hT.2 [i] hp).2.1
  rwa [hst] at hβ

theorem GoodTree.child_escape_lower {β : Tree → ℝ} {l : ℝ} {T : Tree}
    (hT : GoodTree β l T) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ degree T) (hl : l < 1) :
    1 - l ≤ β (child T i) := by
  have hp : Present T [i] := by simp [hi]
  have hst : subtree T [i] = child T i := by rw [subtree_cons, subtree_nil]
  have hβ := (hT.2 [i] hp).2.2 hl
  rwa [hst] at hβ

theorem GoodTree.escapeSum_pos {β : Tree → ℝ} {l : ℝ} {T : Tree}
    (hT : GoodTree β l T) : 0 < escapeSum β T :=
  LPPMonotonicityProof.Speed.escapeSum_pos hT.1 fun i hi hik =>
    hT.child_escape_pos ⟨hi, hik⟩

theorem GoodTree.escapeSum_sub_child_nonneg {β : Tree → ℝ} {l : ℝ} {T : Tree}
    (hT : GoodTree β l T) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ degree T) :
    0 ≤ escapeSum β T - β (child T i) := by
  rw [escapeSum_eq_sum_Icc]
  have hm : i ∈ Finset.Icc 1 (degree T) := by simpa [Finset.mem_Icc] using hi
  rw [← Finset.sum_erase_add _ _ hm]
  have hother : 0 ≤ ∑ j ∈ (Finset.Icc 1 (degree T)).erase i, β (child T j) :=
    Finset.sum_nonneg fun j hj => by
      have hv : 1 ≤ j ∧ j ≤ degree T := by
        simpa [Finset.mem_Icc] using (Finset.mem_erase.mp hj).2
      exact (hT.child_escape_pos hv).le
  linarith

theorem GoodTree.escapeSum_lower {β : Tree → ℝ} {l : ℝ} {T : Tree}
    (hT : GoodTree β l T) (hl : l < 1) : 1 - l ≤ escapeSum β T := by
  rw [escapeSum_eq_sum_Icc]
  have hm : 1 ∈ Finset.Icc 1 (degree T) := by simp only [Finset.mem_Icc, le_refl, true_and]; exact hT.1
  have hfirst := hT.child_escape_lower (show 1 ≤ 1 ∧ 1 ≤ degree T by simp only [le_refl, true_and]; exact hT.1) hl
  have hother : 0 ≤ ∑ j ∈ (Finset.Icc 1 (degree T)).erase 1, β (child T j) :=
    Finset.sum_nonneg fun j hj => by
      have hv : 1 ≤ j ∧ j ≤ degree T := by
        simpa [Finset.mem_Icc] using (Finset.mem_erase.mp hj).2
      exact (hT.child_escape_pos hv).le
  rw [← Finset.sum_erase_add _ _ hm]
  simpa only [zero_add] using add_le_add hother hfirst

/-- Abstract escape and harmonic-ray data required for the two ordered Lin identities. -/
structure EscapeData (μ : Measure ℕ) [IsProbabilityMeasure μ] (l : ℝ) where
  hl : 0 < l
  β : Tree → ℝ
  harm : Kernel Tree (ℕ → ℕ)
  measurable_β : Measurable β
  β_nonneg : ∀ T, 0 ≤ β T
  β_le_one : ∀ T, β T ≤ 1
  escape_rec : ∀ T, β T = escapeSum β T / (l + escapeSum β T)
  harm_probability : ∀ T, IsProbabilityMeasure (harm T)
  harm_firstStep : ∀ (T : Tree) {g : (ℕ → ℕ) → ℝ≥0∞}, Measurable g →
    ENNReal.ofReal (escapeSum β T) * ∫⁻ r, g r ∂harm T =
      ∑' i : ℕ, ENNReal.ofReal (escapeWeight β T i) *
        ∫⁻ r, g (seqCons i r) ∂harm (child T i)
  ae_good : ∀ᵐ T ∂bienaymeLaw μ, GoodTree β l T

namespace EscapeData

variable {μ : Measure ℕ} [IsProbabilityMeasure μ] {l : ℝ}

instance (D : EscapeData μ l) : IsMarkovKernel D.harm := ⟨D.harm_probability⟩

/-- Goodness is stable under insertion of a good tree in a vacated slot. -/
theorem good_replaceChild (D : EscapeData μ l) {T : Tree}
    (hT : GoodTree D.β l T) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ degree T)
    {R : Tree} (hR : GoodTree D.β l R) : GoodTree D.β l (replaceChild T i R) := by
  constructor
  · simpa using hT.1
  · intro v hv
    cases v with
    | nil =>
        have hsub := hT.escapeSum_sub_child_nonneg hi
        have hpos : 0 < escapeSum D.β (replaceChild T i R) := by
          rw [escapeSum_replaceChild hi R]
          linarith [hR.escape_pos]
        refine ⟨?_, ?_⟩
        · change 0 < degree (replaceChild T i R)
          rw [degree_replaceChild]
          exact hT.1
        · rw [subtree_nil, D.escape_rec]
          constructor
          · exact div_pos hpos (by linarith [D.hl])
          · intro hl
            have hsum : 1 - l ≤ escapeSum D.β (replaceChild T i R) := by
              rw [escapeSum_replaceChild hi R]
              linarith [hR.escape_lower hl]
            have hmul := mul_le_mul_of_nonneg_left hsum D.hl.le
            exact (le_div_iff₀ (by linarith [D.hl])).2 (by nlinarith)
    | cons j v =>
        by_cases hji : j = i
        · subst j
          have hc : child (replaceChild T i R) i = R := child_replaceChild_same R hi
          have hp : Present R v := by
            have hp : Present (child (replaceChild T i R) i) v := hv.2.2
            rwa [hc] at hp
          have hst : subtree (replaceChild T i R) (i :: v) = subtree R v := by
            rw [subtree_cons, hc]
          have hval : (replaceChild T i R).val (i :: v) = R.val v := by
            change (child (replaceChild T i R) i).val v = R.val v
            rw [hc]
          rw [hst, hval]
          exact hR.2 v hp
        · have hc : child (replaceChild T i R) j = child T j := child_replaceChild_of_ne R hji
          have hp : Present T (j :: v) := by
            have hp : 1 ≤ j ∧ j ≤ degree (replaceChild T i R) ∧
                Present (child (replaceChild T i R) j) v := hv
            rw [hc, degree_replaceChild] at hp
            exact hp
          have hst : subtree (replaceChild T i R) (j :: v) = subtree T (j :: v) := by
            rw [subtree_cons, hc]
            exact (subtree_cons T j v).symm
          have hval : (replaceChild T i R).val (j :: v) = T.val (j :: v) := by
            change (child (replaceChild T i R) j).val v = T.val (j :: v)
            rw [hc]
            rfl
          rw [hst, hval]
          exact hT.2 (j :: v) hp

/-- The reference environment law: independent forward/backward trees and a harmonic ray. -/
noncomputable def ref (D : EscapeData μ l) : Measure Env :=
  (bienaymeLaw μ).prod ((bienaymeLaw μ) ⊗ₘ D.harm)

noncomputable def beta0 (D : EscapeData μ l) (e : Env) : ℝ := D.β e.bwd
noncomputable def fwdSum (D : EscapeData μ l) (e : Env) : ℝ := escapeSum D.β e.fwd
noncomputable def Hden (D : EscapeData μ l) (e : Env) : ℝ := l - 1 + beta0 D e + fwdSum D e
noncomputable def wDens (D : EscapeData μ l) (e : Env) : ℝ :=
  (degree e.fwd + l) * beta0 D e / Hden D e
noncomputable def uDens (D : EscapeData μ l) (e : Env) : ℝ :=
  beta0 D e * fwdSum D e / Hden D e
noncomputable def caseIDens (D : EscapeData μ l) (e : Env) : ℝ :=
  beta0 D e * (l + fwdSum D e) / Hden D e
noncomputable def caseIIDens (D : EscapeData μ l) (e : Env) : ℝ :=
  beta0 D e * (degree e.fwd - fwdSum D e) / Hden D e

/-- On good trees the denominator is at least the positive backward escape. -/
theorem Hden_ge_beta {D : EscapeData μ l} {F B : Tree}
    (hF : GoodTree D.β l F) (hB : GoodTree D.β l B) :
    D.β B ≤ l - 1 + D.β B + escapeSum D.β F := by
  by_cases hl : l < 1
  · have hsum := hF.escapeSum_lower hl
    linarith [hB.escape_pos]
  · have hsum := escapeSum_nonneg D.β_nonneg F
    linarith

theorem Hden_pos {D : EscapeData μ l} {F B : Tree}
    (hF : GoodTree D.β l F) (hB : GoodTree D.β l B) :
    0 < l - 1 + D.β B + escapeSum D.β F :=
  hB.escape_pos.trans_le (Hden_ge_beta hF hB)

/-- Normalized harmonic first-step decomposition on a good tree. -/
theorem harm_firstStep_normalized (D : EscapeData μ l) (T : Tree)
    (hT : GoodTree D.β l T) {g : (ℕ → ℕ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ r, g r ∂D.harm T =
      ∑' i : ℕ, ENNReal.ofReal (escapeWeight D.β T i / escapeSum D.β T) *
        ∫⁻ r, g (seqCons i r) ∂D.harm (child T i) := by
  have hS : 0 < escapeSum D.β T := hT.escapeSum_pos
  calc
    _ = (∑' i : ℕ, ENNReal.ofReal (escapeWeight D.β T i) *
        ∫⁻ r, g (seqCons i r) ∂D.harm (child T i)) / ENNReal.ofReal (escapeSum D.β T) :=
      (ENNReal.eq_div_iff (ENNReal.ofReal_pos.mpr hS).ne' ENNReal.ofReal_ne_top).2
        (D.harm_firstStep T hg)
    _ = _ := by
      rw [ENNReal.div_eq_inv_mul, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro i
      rw [ENNReal.ofReal_div_of_pos hS, ENNReal.div_eq_inv_mul]
      ac_rfl

/-- The joint forward/backward good set has full reference measure. -/
theorem ae_good_ref (D : EscapeData μ l) :
    ∀ᵐ e ∂D.ref, GoodTree D.β l e.fwd ∧ GoodTree D.β l e.bwd := by
  have hsnd : @MeasurePreserving (Tree × (ℕ → ℕ)) Tree _ _
      (fun p => p.1) ((bienaymeLaw μ) ⊗ₘ D.harm) (bienaymeLaw μ) := by
    refine ⟨measurable_fst, Measure.fst_compProd (bienaymeLaw μ) D.harm⟩
  have hf : ∀ᵐ e ∂D.ref, GoodTree D.β l e.fwd :=
    Measure.quasiMeasurePreserving_fst.ae D.ae_good
  have hb : ∀ᵐ e ∂D.ref, GoodTree D.β l e.bwd := by
    exact (hsnd.quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_snd (μ := bienaymeLaw μ)
        (ν := (bienaymeLaw μ) ⊗ₘ D.harm))).ae D.ae_good
  filter_upwards [hf, hb] with e hfe hbe
  exact ⟨hfe, hbe⟩


theorem measurable_escapeWeight (D : EscapeData μ l) (i : ℕ) :
    Measurable (fun T => escapeWeight D.β T i) := by
  apply Measurable.ite
  · exact (MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | 1 ≤ p.1 ∧ p.1 ≤ p.2}).preimage
      (measurable_const.prodMk ((continuous_degree.measurable).comp measurable_id))
  · exact D.measurable_β.comp (continuous_child i).measurable
  · exact measurable_const

theorem measurable_escapeSum (D : EscapeData μ l) : Measurable (escapeSum D.β) :=
  Measurable.tsum D.measurable_escapeWeight

theorem measurable_beta0 (D : EscapeData μ l) : Measurable (beta0 D) :=
  D.measurable_β.comp measurable_snd.fst

theorem measurable_fwdSum (D : EscapeData μ l) : Measurable (fwdSum D) :=
  D.measurable_escapeSum.comp measurable_fst

theorem measurable_Hden (D : EscapeData μ l) : Measurable (Hden D) :=
  (measurable_const.sub measurable_const).add D.measurable_beta0 |>.add D.measurable_fwdSum

theorem measurable_caseIDens (D : EscapeData μ l) : Measurable (caseIDens D) :=
  (D.measurable_beta0.mul (measurable_const.add D.measurable_fwdSum)).div D.measurable_Hden

theorem measurable_caseIIDens (D : EscapeData μ l) : Measurable (caseIIDens D) :=
  (D.measurable_beta0.mul
    ((Nat.cast_continuous.measurable.comp
      (continuous_degree.measurable.comp measurable_fst) : Measurable (fun e : Env => (degree e.fwd : ℝ))).sub
      D.measurable_fwdSum)).div D.measurable_Hden

/-- Restriction of the reference law to a forward-valid slot. -/
noncomputable def refFwd (D : EscapeData μ l) (i : ℕ) : Measure Env :=
  D.ref.restrict {e | i ≤ degree e.fwd}

/-- The forward-restricted law as an explicit iterated product. -/
noncomputable def refFwdProd (D : EscapeData μ l) (i : ℕ) : Measure Env :=
  ((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod ((bienaymeLaw μ) ⊗ₘ D.harm)

theorem refFwdProd_eq_refFwd (D : EscapeData μ l) (i : ℕ) :
    D.refFwdProd i = D.refFwd i := by
  unfold refFwdProd refFwd ref
  rw [← Measure.restrict_univ (μ := (bienaymeLaw μ) ⊗ₘ D.harm), Measure.prod_restrict,
    Measure.restrict_univ]
  congr 1
  ext e
  simp [Env.fwd]

/-- Iterated-integral formula on a forward-valid slot. -/
theorem lintegral_refFwdProd (D : EscapeData μ l) (i : ℕ)
    {g : Env → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ e, g e ∂D.refFwdProd i =
      ∫⁻ p : Tree × Tree, ∫⁻ r, g (p.1, p.2, r) ∂D.harm p.2
        ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ) := by
  unfold refFwdProd
  have hs : MeasurableSet {T : Tree | i ≤ degree T} :=
    (MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | p.1 ≤ p.2}).preimage
      (measurable_const.prodMk continuous_degree.measurable)
  rw [lintegral_prod (μ := (bienaymeLaw μ).restrict {T | i ≤ degree T})
    (ν := (bienaymeLaw μ) ⊗ₘ D.harm) _ hg.aemeasurable]
  have hm : AEMeasurable (fun p : Tree × Tree => ∫⁻ r, g (p.1, p.2, r) ∂D.harm p.2)
      (((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ)) := by
    have hm : Measurable (fun p : Tree × Tree => ∫⁻ r, g (p.1, p.2, r) ∂D.harm p.2) := by
      exact Measurable.lintegral_kernel_prod_right'
        (κ := D.harm.comap Prod.snd measurable_snd)
        (f := g ∘ MeasurableEquiv.prodAssoc) (hg.comp MeasurableEquiv.prodAssoc.measurable)
    exact hm.aemeasurable
  conv_rhs =>
    rw [← lintegral_lintegral (μ := (bienaymeLaw μ).restrict {T | i ≤ degree T})
      (ν := bienaymeLaw μ) (f := fun T B => ∫⁻ r, g (T, B, r) ∂D.harm B) hm]
  apply setLIntegral_congr_fun hs
  intro T hT
  simpa only [Function.comp_apply, id_eq] using
    (Measure.lintegral_compProd (μ := bienaymeLaw μ) (κ := D.harm)
      (hg.comp (measurable_const.prodMk measurable_id)))

/-- Iterated-integral formula on a backward-valid slot, with the backward tree first. -/
theorem lintegral_refBwd (D : EscapeData μ l) (i : ℕ)
    {g : Env → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ e in {e | i ≤ degree e.bwd}, g e ∂D.ref =
      ∫⁻ p : Tree × Tree, ∫⁻ r, g (p.2, p.1, r) ∂D.harm p.1
        ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ) := by
  have hs : MeasurableSet {T : Tree | i ≤ degree T} :=
    (MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | p.1 ≤ p.2}).preimage
      (measurable_const.prodMk continuous_degree.measurable)
  have hse : MeasurableSet {e : Env | i ≤ degree e.bwd} :=
    (MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | p.1 ≤ p.2}).preimage
      (measurable_const.prodMk (continuous_degree.measurable.comp measurable_snd.fst))
  have hgi : Measurable ({e : Env | i ≤ degree e.bwd}.indicator g) :=
    hg.indicator hse
  let H : Tree × Tree → ℝ≥0∞ := fun p => ∫⁻ r, g (p.1, p.2, r) ∂D.harm p.2
  have hH : Measurable H := by
    exact Measurable.lintegral_kernel_prod_right'
      (κ := D.harm.comap Prod.snd measurable_snd)
      (f := g ∘ MeasurableEquiv.prodAssoc) (hg.comp MeasurableEquiv.prodAssoc.measurable)
  dsimp [H] at hH
  have hH' : AEMeasurable (fun p : Tree × Tree => ∫⁻ r, g (p.1, p.2, r) ∂D.harm p.2)
      (((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ)) := hH.aemeasurable
  have hsP : MeasurableSet {p : Tree × (ℕ → ℕ) | i ≤ degree p.1} :=
    (MeasurableSet.of_discrete : MeasurableSet {p : ℕ × ℕ | p.1 ≤ p.2}).preimage
      (measurable_const.prodMk (continuous_degree.measurable.comp measurable_fst))
  have hrestr : ((bienaymeLaw μ) ⊗ₘ D.harm).restrict {p : Tree × (ℕ → ℕ) | i ≤ degree p.1} =
      (bienaymeLaw μ).restrict {T | i ≤ degree T} ⊗ₘ D.harm := by
    ext A hA
    rw [Measure.restrict_apply hA,
      Measure.compProd_apply (μ := (bienaymeLaw μ).restrict {T | i ≤ degree T}) hA,
      Measure.compProd_apply (μ := bienaymeLaw μ) (hA.inter hsP)]
    calc
      _ = ∫⁻ a, {a : Tree | i ≤ degree a}.indicator
          (fun _ => (D.harm a) (Prod.mk a ⁻¹' A)) a ∂bienaymeLaw μ := by
        apply lintegral_congr
        intro a
        congr 1
        by_cases hi : i ≤ degree a <;> simp [hi, Set.indicator_apply]
      _ = _ := lintegral_indicator hs _
  have hR : D.ref.restrict {e | i ≤ degree e.bwd} =
      (bienaymeLaw μ).prod ((bienaymeLaw μ).restrict {T | i ≤ degree T} ⊗ₘ D.harm) := by
    unfold EscapeData.ref
    have hsets : {e : Env | i ≤ degree e.bwd} =
        Set.univ ×ˢ {p : Tree × (ℕ → ℕ) | i ≤ degree p.1} := by
      ext e
      simp [Env.bwd]
    rw [hsets, ← Measure.prod_restrict, Measure.restrict_univ, hrestr]
  rw [hR, lintegral_prod (μ := bienaymeLaw μ)
    (ν := (bienaymeLaw μ).restrict {T | i ≤ degree T} ⊗ₘ D.harm) _ hg.aemeasurable]
  have hc := lintegral_congr (μ := bienaymeLaw μ) (fun x =>
    (Measure.lintegral_compProd (μ := (bienaymeLaw μ).restrict {T | i ≤ degree T})
      (κ := D.harm) (f := fun p : Tree × (ℕ → ℕ) => g (x, p))
      (hg.comp (measurable_const.prodMk measurable_id))))
  rw [hc]
  conv_lhs =>
    rw [lintegral_lintegral (μ := bienaymeLaw μ)
      (ν := (bienaymeLaw μ).restrict {T | i ≤ degree T})
      (f := fun F B => ∫⁻ r, g (F, B, r) ∂D.harm B) hH.aemeasurable]
  rw [← Measure.measurePreserving_swap.lintegral_comp hH]
  simp only [Prod.swap]

/-- Ordered child exchange on the forward slot in iterated-integral form. -/
theorem lintegral_refFwdProd_swap (D : EscapeData μ l) (i : ℕ) (hi : 1 ≤ i)
    {H : Tree × Tree → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ p : Tree × Tree, H (swapChild i p)
      ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ)) =
      ∫⁻ p : Tree × Tree, H p
        ∂((bienaymeLaw μ).restrict {T | i ≤ degree T}).prod (bienaymeLaw μ) :=
  (measurePreserving_swapChild hi).lintegral_comp hH

end EscapeData


/-- Valid ordered slots as a countable sum, convenient for Tonelli arguments. -/
noncomputable def slots {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    (T : Tree) (g : ℕ → α) : α :=
  ∑' i : ℕ, if 1 ≤ i ∧ i ≤ degree T then g i else 0

theorem slots_eq_sum_fin {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    (k : ℕ) (g : ℕ → α) :
    slots (node k (fun _ => leaf)) g = ∑ i : Fin k, g (i.val + 1) := by
  have hdeg : degree (node k (fun _ : ℕ => leaf)) = k := degree_node k _
  unfold slots
  rw [tsum_eq_sum (s := Finset.Icc 1 k)]
  · simp_rw [hdeg]
    calc
      _ = ∑ i ∈ Finset.Icc 1 k, g i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hv : 1 ≤ i ∧ i ≤ k := by simpa [Finset.mem_Icc] using hi
        simp [hv]
      _ = _ := by
        apply Finset.sum_bij (fun a ha => (⟨a - 1, by
          have hv : 1 ≤ a ∧ a ≤ k := by simpa [Finset.mem_Icc] using ha
          omega⟩ : Fin k))
        · intro a ha
          simp
        · intro a ha b hb hab
          have hva : 1 ≤ a ∧ a ≤ k := by simpa [Finset.mem_Icc] using ha
          have hvb : 1 ≤ b ∧ b ≤ k := by simpa [Finset.mem_Icc] using hb
          have hv := congrArg Fin.val hab
          dsimp at hv
          omega
        · intro b hb
          refine ⟨b.val + 1, ?_, ?_⟩
          · simp only [Finset.mem_Icc]
            omega
          · apply Fin.ext
            simp only
            omega
        · intro a ha
          have hv : 1 ≤ a ∧ a ≤ k := by simpa [Finset.mem_Icc] using ha
          simp only
          congr 1
          omega
  · intro i hi
    have hnot : ¬(1 ≤ i ∧ i ≤ degree (node k (fun _ : ℕ => leaf))) := by
      intro hv
      apply hi
      apply Finset.mem_Icc.mpr
      simpa only [hdeg] using hv
    have hnotK : ¬(1 ≤ i ∧ i ≤ k) := by
      intro hv
      apply hnot
      simpa only [hdeg] using hv
    simp [hnotK]

/-- The slots of a tree reconstructed from its own children. -/
theorem slots_degree {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    (T : Tree) (g : ℕ → α) :
    slots T g = ∑ i : Fin (degree T), g (i.val + 1) := by
  rw [← node_degree_child T]
  exact slots_eq_sum_fin (degree T) g


theorem escapeSum_eq_sum_fin (β : Tree → ℝ) (T : Tree) :
    escapeSum β T = ∑ i : Fin (degree T), β (child T (i.val + 1)) := by
  rw [← slots_degree T (fun i => β (child T i))]
  rfl

namespace EscapeData

variable {μ : Measure ℕ} [IsProbabilityMeasure μ] {l : ℝ}

end EscapeData

end LPPMonotonicityProof.Speed
