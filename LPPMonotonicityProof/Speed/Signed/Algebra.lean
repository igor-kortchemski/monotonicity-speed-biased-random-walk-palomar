module

public import LPPMonotonicityProof.Speed.Signed.Iid

/-! # Algebraic helpers for the two-copy form -/

@[expose] public section

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The reference denominator in i.i.d. coordinates. -/
def Hfun (l b S : ℝ) : ℝ := l - 1 + b + S

/-- Numerical content of a good backward escape. -/
def GoodEsc (l b : ℝ) : Prop := 0 < b ∧ b < 1 ∧ (l < 1 → 1 - l ≤ b)

lemma one_sub_le_sum {l : ℝ} {k : ℕ} (hk : k ≠ 0) {bs : Fin k → ℝ}
    (hbs : ∀ i, GoodEsc l (bs i)) (hl : l < 1) : 1 - l ≤ ∑ i, bs i := by
  let i : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
  calc
    1 - l ≤ bs i := (hbs i).2.2 hl
    _ ≤ ∑ j, bs j := Finset.single_le_sum (fun j _ => (hbs j).1.le) (Finset.mem_univ i)

lemma Hfun_ge_b {l : ℝ} {k : ℕ} (hk : k ≠ 0) {b : ℝ} {bs : Fin k → ℝ}
    (hb : GoodEsc l b) (hbs : ∀ i, GoodEsc l (bs i)) : b ≤ Hfun l b (∑ i, bs i) := by
  unfold Hfun
  by_cases hl : l < 1
  · have h := one_sub_le_sum hk hbs hl
    linarith
  · have hS : 0 ≤ ∑ i, bs i := Finset.sum_nonneg fun i _ => (hbs i).1.le
    linarith

lemma Hfun_pos {l : ℝ} {k : ℕ} (hk : k ≠ 0) {b : ℝ} {bs : Fin k → ℝ}
    (hb : GoodEsc l b) (hbs : ∀ i, GoodEsc l (bs i)) : 0 < Hfun l b (∑ i, bs i) :=
  hb.1.trans_le (Hfun_ge_b hk hb hbs)

lemma ratio_mono_bound {l : ℝ} {k : ℕ} (hk : k ≠ 0) {b : ℝ} {bs : Fin k → ℝ}
    (hb : GoodEsc l b) (hbs : ∀ i, GoodEsc l (bs i)) {C : ℝ}
    (hC : 0 ≤ C) : |C * b / Hfun l b (∑ i, bs i)| ≤ C := by
  have hH := Hfun_pos hk hb hbs
  have hbH := Hfun_ge_b hk hb hbs
  rw [abs_div, abs_mul, abs_of_pos hH, abs_of_nonneg hC, abs_of_pos hb.1]
  apply (div_le_iff₀ hH).2
  exact mul_le_mul_of_nonneg_left hbH hC

lemma ae_goodEsc (μ : Measure ℕ) [IsProbabilityMeasure μ] {l : ℝ} (hl : 0 < l)
    (hμ : OffspringHyp μ) (hlm : l < mean μ) : ∀ᵐ b ∂escLaw μ l, GoodEsc l b := by
  let D := concreteEscapeData' μ l hl hμ hlm
  have hg : ∀ᵐ T ∂bienaymeLaw μ, GoodEsc l (D.β T) := by
    filter_upwards [D.ae_good] with T hT
    exact ⟨hT.escape_pos, escape_lt_one hl T, hT.escape_lower⟩
  have hgoodset : MeasurableSet {b | GoodEsc l b} := by
    by_cases hl1 : l < 1
    · rw [show {b | GoodEsc l b} = {b | 0 < b} ∩ {b | b < 1} ∩ {b | 1 - l ≤ b} by
        ext b; simp only [GoodEsc, hl1, true_implies, Set.mem_inter_iff, Set.mem_setOf_eq]; tauto]
      exact ((measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_lt measurable_id measurable_const)).inter
        (measurableSet_le measurable_const measurable_id)
    · rw [show {b | GoodEsc l b} = {b | 0 < b} ∩ {b | b < 1} by
        ext b; simp only [GoodEsc, hl1, true_implies, Set.mem_inter_iff, Set.mem_setOf_eq]; tauto]
      exact (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_lt measurable_id measurable_const)
  rw [escLaw, ae_map_iff (measurable_escape l).aemeasurable hgoodset]
  dsimp only [D, concreteEscapeData', concreteEscapeData] at hg
  exact hg

lemma ae_iid_good (μ : Measure ℕ) [IsProbabilityMeasure μ] {l : ℝ} (hl : 0 < l)
    (hμ : OffspringHyp μ) (hlm : l < mean μ) (k : ℕ) :
    ∀ᵐ q : ℝ × (Fin k → ℝ) ∂(escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l),
      GoodEsc l q.1 ∧ ∀ i, GoodEsc l (q.2 i) := by
  have hg : ∀ᵐ b ∂escLaw μ l, GoodEsc l b := ae_goodEsc μ hl hμ hlm
  have hp : ∀ᵐ bs : Fin k → ℝ ∂Measure.pi (fun _ : Fin k => escLaw μ l),
      ∀ i, GoodEsc l (bs i) := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin k => escLaw μ l) i).quasiMeasurePreserving.ae hg
  filter_upwards [(measurePreserving_fst (μ := escLaw μ l)
    (ν := Measure.pi fun _ : Fin k => escLaw μ l)).quasiMeasurePreserving.ae hg,
    (measurePreserving_snd (μ := escLaw μ l)
    (ν := Measure.pi fun _ : Fin k => escLaw μ l)).quasiMeasurePreserving.ae hp] with q hq hqs
  exact ⟨hq, hqs⟩

/-- Integrability of `c·b/H` under the i.i.d. escape fibers. -/
lemma integrable_C_ratio (μ : Measure ℕ) [IsProbabilityMeasure μ] {l : ℝ} (hl : 0 < l)
    (hμ : OffspringHyp μ) (hlm : l < mean μ) {k : ℕ} (hk : k ≠ 0) (c B : ℝ)
    (hB : 0 ≤ B) (hc : |c| ≤ B) :
    Integrable (fun q : ℝ × (Fin k → ℝ) => c * q.1 / Hfun l q.1 (∑ i, q.2 i))
      ((escLaw μ l).prod (Measure.pi fun _ : Fin k => escLaw μ l)) := by
  let H : ℝ × (Fin k → ℝ) → ℝ := fun q => Hfun l q.1 (∑ i, q.2 i)
  have hHm : Measurable H := by
    exact (((measurable_const.sub measurable_const).add measurable_fst).add
      (Finset.univ.measurable_sum fun i _ => (measurable_pi_apply i).comp measurable_snd))
  apply (integrable_const B).mono ((measurable_const.mul measurable_fst).div hHm).aestronglyMeasurable
  filter_upwards [ae_iid_good μ hl hμ hlm k] with q hq
  have hfrac : |q.1 / Hfun l q.1 (∑ i, q.2 i)| ≤ 1 := by
    simpa using ratio_mono_bound hk hq.1 hq.2 (C := (1 : ℝ)) zero_le_one
  calc
    |c * q.1 / Hfun l q.1 (∑ i, q.2 i)| = |c| * |q.1 / Hfun l q.1 (∑ i, q.2 i)| := by
      simp only [abs_div, abs_mul]
      ring
    _ ≤ B * 1 := mul_le_mul hc hfrac (abs_nonneg _) hB
    _ = B := mul_one B
  all_goals simp [Real.norm_eq_abs, abs_of_nonneg hB]

end LPPMonotonicityProof.Speed
