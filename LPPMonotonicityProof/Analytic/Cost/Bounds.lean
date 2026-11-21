module

public import LPPMonotonicityProof.Analytic.Kernel
public import LPPMonotonicityProof.Analytic.Kernel2
public import LPPMonotonicityProof.Analytic.RegularityExport

/-! # Domination of the two-copy derivative kernels

These are the domination bounds that justify differentiating `N` and `Z` under the
expectation in the proof of Proposition 2.6 (`prop:cost`), on compact bias intervals
either with `λ₊ E[1/ν] < 1` or above bias one.  They use the denominator `DfunProv`,
which is definitionally equal to `Speed.Dfun`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ}

/-- The explicit bias partial of the numerator kernel (`hasDerivAt_F_l` with `c = 0`). -/
noncomputable def kNl (l b b' : ℝ) : ℝ := -(b * b') / DfunProv l b b' ^ 2

/-- The first escape partial of the numerator kernel (`hasDerivAt_F_b` with `c = 0`). -/
noncomputable def kNb (l b b' : ℝ) : ℝ := Pol l 0 b' / DfunProv l b b' ^ 2

/-- The explicit bias partial of the denominator kernel (`hasDerivAt_F_l` at `c = 0` minus
`c = 1`). -/
noncomputable def kZl (l b b' : ℝ) : ℝ := -tau b b' / DfunProv l b b' ^ 2

/-- The first escape partial of the denominator kernel (`hasDerivAt_F_b` at `c = 0` minus
`c = 1`). -/
noncomputable def kZb (l b b' : ℝ) : ℝ := (Pol l 0 b' - Pol l 1 b') / DfunProv l b b' ^ 2

/-- Every regular tree has its root escape in `(0, 1]` at transient bias. -/
theorem escape_mem_Ioc_of_regTree {T : Tree} (hT : RegTree μ T) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) : escape l T ∈ Set.Ioc 0 1 := by
  exact ⟨by simpa only [subtree_nil] using hT.1.2 l hl [] (present_nil T),
    (escape_mem_Icc hl.1 T).2⟩

private theorem escape_lower_of_regTree {T : Tree} (hT : RegTree μ T)
    {l : ℝ} (hl : 0 < l) (hl1 : l < 1) : 1 - l ≤ escape l T :=
  escape_ge hl hl1 T fun v hv => hT.1.1 v hv

theorem DfunProv_pos_of_regTrees {T T' : Tree} (hT : RegTree μ T) (hT' : RegTree μ T')
    {l : ℝ} (hl : l ∈ Set.Ioo 0 (mean μ)) :
    0 < DfunProv l (escape l T) (escape l T') := by
  have h := (Dfun_bounds hl.1 (escape_mem_Ioc_of_regTree hT hl)
    (escape_mem_Ioc_of_regTree hT' hl)
    (fun hl1 => ⟨escape_lower_of_regTree hT hl.1 hl1, escape_lower_of_regTree hT' hl.1 hl1⟩)).1
  exact (mul_pos (lt_min zero_lt_one hl.1)
    ((escape_mem_Ioc_of_regTree hT hl).1.trans_le (le_max_left _ _))).trans_le h

/-- Every interior bias admits a compact neighborhood in one of the two domination regimes. -/
theorem regime_cover [IsProbabilityMeasure μ] (h : OffspringHyp μ) {l₀ : ℝ} (hl₀ : l₀ ∈ Set.Ioo 0 (mean μ)) :
    ∃ a b, 0 < a ∧ a < l₀ ∧ l₀ < b ∧ b < mean μ ∧ (b * invMean μ < 1 ∨ 1 < a) := by
  rcases le_or_gt l₀ 1 with hl₁ | hl₁
  · have hU := invMean_bounds h
    have hpos : 0 < invMean μ :=
      (div_pos zero_lt_one (zero_lt_one.trans (one_lt_mean_of_hyp h))).trans_le hU.1
    have hupper : l₀ < min (mean μ) (1 / invMean μ) := by
      refine lt_min hl₀.2 (hl₁.trans_lt ?_)
      exact (lt_div_iff₀ hpos).2 (by simpa using hU.2)
    obtain ⟨b, hb₀, hb⟩ := exists_between hupper
    refine ⟨l₀ / 2, b, by linarith [hl₀.1], by linarith [hl₀.1], hb₀,
      hb.trans_le (min_le_left _ _), Or.inl ?_⟩
    exact (lt_div_iff₀ hpos).1 (hb.trans_le (min_le_right _ _))
  · obtain ⟨a, ha₁, ha₀⟩ := exists_between hl₁
    obtain ⟨b, hb₀, hb⟩ := exists_between hl₀.2
    exact ⟨a, b, zero_lt_one.trans ha₁, ha₀, hb₀, hb, Or.inr ha₁⟩

section ScalarBounds

variable {a l x y : ℝ}

/-- The lower endpoint gives a common coefficient in the denominator bound (2.2). -/
private theorem denominator_lower (ha : 0 < a) (hal : a ≤ l)
    (hx : x ∈ Set.Ioc 0 1) (hy : y ∈ Set.Ioc 0 1)
    (hlow : l < 1 → 1 - l ≤ x ∧ 1 - l ≤ y) :
    min 1 a * max x y ≤ DfunProv l x y :=
  (mul_le_mul_of_nonneg_right (min_le_min_left 1 hal) (hx.1.le.trans (le_max_left _ _))).trans
    (Dfun_bounds (ha.trans_le hal) hx hy hlow).1

private theorem numerators_nonneg_le {B : ℝ} (hx : x ∈ Set.Ioc 0 1)
    (hy : y ∈ Set.Ioc 0 1) (hxB : x ≤ B) (hyB : y ≤ B) :
    0 ≤ x * y ∧ x * y ≤ tau x y ∧ tau x y ≤ 2 * B := by
  have hxy := mul_nonneg hx.1.le hy.1.le
  have hx' : x * y ≤ x := mul_le_of_le_one_right hx.1.le hy.2
  have hy' : x * y ≤ y := mul_le_of_le_one_left hy.1.le hx.2
  exact ⟨hxy, by unfold tau; linarith, by unfold tau; linarith⟩

/-- In regime A the explicit partials are dominated by a reciprocal escape bound.
Here `e` can be the first escape at the upper bias endpoint. -/
theorem explicit_partials_le_inv {e : ℝ} (ha : 0 < a) (hal : a ≤ l)
    (hx : x ∈ Set.Ioc 0 1) (hy : y ∈ Set.Ioc 0 1)
    (hlow : l < 1 → 1 - l ≤ x ∧ 1 - l ≤ y) (he : 0 < e) (hex : e ≤ x) :
    |kNl l x y| ≤ 2 / ((min 1 a)^2 * e) ∧
      |kZl l x y| ≤ 2 / ((min 1 a)^2 * e) := by
  let B := max x y
  let s := min (1 : ℝ) a
  have hs : 0 < s := lt_min zero_lt_one ha
  have heB : e ≤ B := hex.trans (le_max_left _ _)
  have hB : 0 < B := he.trans_le heB
  have hD : s * B ≤ DfunProv l x y := denominator_lower ha hal hx hy hlow
  rcases numerators_nonneg_le hx hy (le_max_left x y) (le_max_right x y) with ⟨hN, hNZ, hZ⟩
  have hdiv : (2 * B) / (s * B)^2 ≤ 2 / (s^2 * e) := by
    calc
      (2 * B) / (s * B)^2 = 2 / (s^2 * B) := by field_simp
      _ ≤ 2 / (s^2 * e) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left heB (sq_nonneg s))
  have hz := (div_le_div₀ (by positivity : 0 ≤ 2 * B) hZ
    (by positivity : 0 < (s * B)^2)
    (pow_le_pow_left₀ (mul_nonneg hs.le hB.le) hD 2)).trans hdiv
  simp only [kNl, kZl, abs_div, abs_neg, abs_of_nonneg hN,
    abs_of_nonneg (hN.trans hNZ), abs_of_nonneg (sq_nonneg (DfunProv l x y))]
  exact ⟨(div_le_div_of_nonneg_right hNZ (sq_nonneg _)).trans hz, hz⟩

/-- In regime B both explicit partials admit a constant bound. -/
theorem explicit_partials_le_const (ha : 1 < a) (hal : a ≤ l)
    (hx : x ∈ Set.Ioc 0 1) (hy : y ∈ Set.Ioc 0 1) :
    |kNl l x y| ≤ 2 / (a - 1)^2 ∧ |kZl l x y| ≤ 2 / (a - 1)^2 := by
  rcases numerators_nonneg_le hx hy hx.2 hy.2 with ⟨hN, hNZ, hZ⟩
  have ha0 : 0 < a - 1 := sub_pos.mpr ha
  have hD : a - 1 ≤ DfunProv l x y := by
    have hτ := hN.trans hNZ
    change 0 ≤ x + y - x * y at hτ
    unfold DfunProv
    linarith
  have hz := div_le_div₀ (by norm_num : 0 ≤ (2 : ℝ)) (by simpa using hZ)
    (by positivity : 0 < (a - 1)^2) (pow_le_pow_left₀ ha0.le hD 2)
  simp only [kNl, kZl, abs_div, abs_neg, abs_of_nonneg hN,
    abs_of_nonneg (hN.trans hNZ), abs_of_nonneg (sq_nonneg (DfunProv l x y))]
  exact ⟨(div_le_div_of_nonneg_right hNZ (sq_nonneg _)).trans hz, hz⟩

/-- Multiplication by the differentiated escape makes both escape partials uniformly bounded. -/
theorem escape_partials_mul_le (ha : 0 < a) (hal : a ≤ l)
    (hx : x ∈ Set.Ioc 0 1) (hy : y ∈ Set.Ioc 0 1)
    (hlow : l < 1 → 1 - l ≤ x ∧ 1 - l ≤ y) :
    |kNb l x y| * x ≤ ((min 1 a)^2)⁻¹ ∧ |kZb l x y| * x ≤ ((min 1 a)^2)⁻¹ := by
  let s := min (1 : ℝ) a
  let D := DfunProv l x y
  have hs : 0 < s := lt_min zero_lt_one ha
  have hs1 : s ≤ 1 := min_le_left _ _
  have hB := denominator_lower ha hal hx hy hlow
  have hD : 0 < D := (mul_pos hs (hx.1.trans_le (le_max_left _ _))).trans_le hB
  have hxD : x ≤ D / s := (le_div_iff₀ hs).2
    ((mul_comm x s ▸ mul_le_mul_of_nonneg_left (le_max_left x y) hs.le).trans hB)
  have hτ0 : 0 ≤ tau x y := by
    have hn := numerators_nonneg_le hx hy hx.2 hy.2
    exact hn.1.trans hn.2.1
  have hDdiv : D ≤ D / s := (le_div_iff₀ hs).2 (mul_le_of_le_one_right hD.le hs1)
  have haD : |l - 1| ≤ D / s := by
    rcases le_or_gt 1 l with hl1 | hl1
    · rw [abs_of_nonneg (sub_nonneg.mpr hl1)]
      exact (show l - 1 ≤ D by
        change l - 1 ≤ l - 1 + x + y - x * y
        unfold tau at hτ0
        linarith).trans hDdiv
    · rw [abs_of_neg (sub_neg.mpr hl1), neg_sub]
      exact (hlow hl1).1.trans hxD
  have hyadd : 0 ≤ l - 1 + y := by
    rcases le_or_gt 1 l with hl1 | hl1
    · linarith [hy.1]
    · linarith [(hlow hl1).2]
  have hyD : l - 1 + y ≤ D := by
    change l - 1 + y ≤ l - 1 + x + y - x * y
    linarith [show x * y ≤ x from mul_le_of_le_one_right hx.1.le hy.2]
  have hN : |Pol l 0 y| ≤ D / s := by
    rw [show Pol l 0 y = (l - 1 + y) * y by unfold Pol; ring, abs_mul,
      abs_of_nonneg hyadd, abs_of_nonneg hy.1.le]
    exact (mul_le_of_le_one_right hyadd hy.2).trans (hyD.trans hDdiv)
  have hZ : |Pol l 0 y - Pol l 1 y| ≤ D / s := by
    rw [show Pol l 0 y - Pol l 1 y = (l - 1) * (1 - y) by unfold Pol; ring, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr hy.2)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (by linarith [hy.1])).trans haD
  have finish (z : ℝ) (hz : |z| ≤ D / s) : |z / D^2| * x ≤ (s^2)⁻¹ := by
    rw [abs_div, abs_of_nonneg (sq_nonneg D), div_mul_eq_mul_div₀]
    apply (div_le_iff₀ (sq_pos_of_pos hD)).2
    calc
      |z| * x ≤ (D / s) * (D / s) := mul_le_mul hz hxD hx.1.le (by positivity)
      _ = (s^2)⁻¹ * D^2 := by simp only [div_eq_mul_inv, ← inv_pow]; ring
  exact ⟨finish _ hN, finish _ hZ⟩

end ScalarBounds

/-- Each escape-chain-rule term is dominated by its tree's response envelope. -/
theorem escape_terms_le_envelope [IsProbabilityMeasure μ] {T T' : Tree} (hT : RegTree μ T) (hT' : RegTree μ T')
    {a b l : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < mean μ) (hl : l ∈ Set.Icc a b) :
    |kNb l (escape l T) (escape l T') * deriv (fun t => escape t T) l| ≤
        ((min 1 a)^2)⁻¹ * (envelope a b T).toReal ∧
      |kZb l (escape l T) (escape l T') * deriv (fun t => escape t T) l| ≤
        ((min 1 a)^2)⁻¹ * (envelope a b T).toReal := by
  have hl' : l ∈ Set.Ioo 0 (mean μ) := ⟨ha.trans_le hl.1, hl.2.trans_lt hb⟩
  have hder := (neg_deriv_escape_le hT ha hab hb hl).2
  have hbounds := escape_partials_mul_le ha hl.1 (escape_mem_Ioc_of_regTree hT hl')
    (escape_mem_Ioc_of_regTree hT' hl')
    (fun hl1 => ⟨escape_lower_of_regTree hT hl'.1 hl1, escape_lower_of_regTree hT' hl'.1 hl1⟩)
  have finish (k : ℝ) (hk : |k| * escape l T ≤ ((min 1 a)^2)⁻¹) :
      |k * deriv (fun t => escape t T) l| ≤ ((min 1 a)^2)⁻¹ * (envelope a b T).toReal := by
    rw [abs_mul, abs_of_nonpos (neg_nonneg.mp hder.1)]
    calc
      |k| * (-deriv (fun t => escape t T) l) ≤ |k| * ((envelope a b T).toReal * escape l T) :=
        mul_le_mul_of_nonneg_left hder.2 (abs_nonneg k)
      _ = (|k| * escape l T) * (envelope a b T).toReal := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hk ENNReal.toReal_nonneg
  exact ⟨finish _ hbounds.1, finish _ hbounds.2⟩

/-- The reciprocal at the upper endpoint dominates both explicit partials in regime A. -/
theorem explicit_terms_le_inv_escape {T T' : Tree} (hT : RegTree μ T) (hT' : RegTree μ T')
    {a b l : ℝ} (ha : 0 < a) (hb : b < mean μ) (hl : l ∈ Set.Icc a b) :
    |kNl l (escape l T) (escape l T')| ≤ 2 / ((min 1 a)^2 * escape b T) ∧
      |kZl l (escape l T) (escape l T')| ≤ 2 / ((min 1 a)^2 * escape b T) := by
  have hl' : l ∈ Set.Ioo 0 (mean μ) := ⟨ha.trans_le hl.1, hl.2.trans_lt hb⟩
  have hb0 := hl'.1.trans_le hl.2
  exact explicit_partials_le_inv ha hl.1 (escape_mem_Ioc_of_regTree hT hl')
    (escape_mem_Ioc_of_regTree hT' hl')
    (fun hl1 => ⟨escape_lower_of_regTree hT hl'.1 hl1, escape_lower_of_regTree hT' hl'.1 hl1⟩)
    (escape_mem_Ioc_of_regTree hT ⟨hb0, hb⟩).1 (escape_antitoneOn T hl'.1 hb0 hl.2)

end LPPMonotonicityProof.Analytic
