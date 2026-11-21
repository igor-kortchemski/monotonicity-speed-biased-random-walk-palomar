module

public import LPPMonotonicityProof.Analytic.RegularityExport
public import LPPMonotonicityProof.Analytic.Comparison
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Logarithmic response bound

This module proves Lemma 4.2 (`lem:log-response`): the lower bound `u ≥ φ_λ(β) ≥ 0` on
the response, with the integral `φ_λ` of (4.1) (`phiResp`), its closed form, and the
identity `(1-Y)² φ_λ(β) = Y[-d₀ log Y - λ(1-Y)]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem logResponse_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hb1 : b < 1) :
    (∫ t in (0 : ℝ)..1,
      (1 - t) / ((1 + a * t) * (1 + a * t / b))) =
      b / (a ^ 2 * (1 - b)) *
        ((a + b) * Real.log (1 + a / b) - (a + 1) * Real.log (a + 1)) := by
  let A : ℝ := -(b * (a + 1) / (a ^ 2 * (1 - b)))
  let B : ℝ := b * (a + b) / (a ^ 2 * (1 - b))
  let F : ℝ → ℝ := fun t => A * Real.log (1 + a * t) +
    B * Real.log (1 + a * t / b)
  have hb0 : b ≠ 0 := ne_of_gt hb
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb1' : 1 - b ≠ 0 := ne_of_gt (sub_pos.mpr hb1)
  have hdenA (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 1 + a * t ≠ 0 := by
    have : 0 < 1 + a * t := by nlinarith [ht.1, ha]
    exact ne_of_gt this
  have hdenB (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 1 + a * t / b ≠ 0 := by
    have : 0 < 1 + a * t / b := by
      have ht0 : 0 ≤ t := ht.1
      positivity
    exact ne_of_gt this
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt F
        (A * (a / (1 + a * t)) + B * ((a / b) / (1 + a * t / b))) t := by
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
    have hlinA : HasDerivAt (fun x : ℝ => 1 + a * x) a t := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul a).const_add 1
    have hlinB : HasDerivAt (fun x : ℝ => 1 + a * x / b) (a / b) t := by
      convert ((hasDerivAt_id t).const_mul (a / b)).const_add 1 using 1
      · funext x
        change 1 + a * x / b = 1 + (a / b) * x
        field_simp
        <;> ring
      · ring
    have hlogA := hlinA.log (hdenA t ht')
    have hlogB := hlinB.log (hdenB t ht')
    change HasDerivAt (fun x => A * Real.log (1 + a * x) +
      B * Real.log (1 + a * x / b)) _ t
    exact (hlogA.const_mul A).add (hlogB.const_mul B)
  have hlineA : ContinuousOn (fun t : ℝ => 1 + a * t) (Set.uIcc 0 1) :=
    continuousOn_const.add (continuousOn_const.mul continuousOn_id)
  have hlineB : ContinuousOn (fun t : ℝ => 1 + a * t / b) (Set.uIcc 0 1) :=
    continuousOn_const.add
      ((continuousOn_const.mul continuousOn_id).div_const b)
  have hcont : ContinuousOn
      (fun t : ℝ => A * (a / (1 + a * t)) + B * ((a / b) / (1 + a * t / b)))
      (Set.uIcc (0 : ℝ) 1) := by
    apply ContinuousOn.add
    · exact continuousOn_const.mul (continuousOn_const.div hlineA (by
        intro t ht
        exact hdenA t (by simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht)))
    · exact continuousOn_const.mul (continuousOn_const.div hlineB (by
        intro t ht
        exact hdenB t (by simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht)))
  have hint : IntervalIntegrable
      (fun t : ℝ => A * (a / (1 + a * t)) + B * ((a / b) / (1 + a * t / b)))
      volume 0 1 := hcont.intervalIntegrable
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hfractions (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (1 - t) / ((1 + a * t) * (1 + a * t / b)) =
        A * (a / (1 + a * t)) + B * ((a / b) / (1 + a * t / b)) := by
    dsimp [A, B]
    have hdenA' : 1 + a * t ≠ 0 := hdenA t ht
    have hdenB' : b + a * t ≠ 0 := by
      have ht0 : 0 ≤ t := ht.1
      have hta : 0 ≤ t * a := mul_nonneg ht0 ha.le
      linarith [hb]
    have hdenC : (1 + a * t) * (b + a * t) ≠ 0 := mul_ne_zero hdenA' hdenB'
    have hfrac : (1 - t) / ((1 + a * t) * (1 + a * t / b)) =
        b * (1 - t) / ((1 + a * t) * (b + a * t)) := by
      have hB : 1 + a * t / b = (b + a * t) / b := by
        field_simp [hb0]
        <;> ring
      rw [hB]
      field_simp [hb0, hdenA', hdenB']
      <;> ring
    rw [hfrac]
    have hterm : (a / b) / (1 + a * t / b) = a / (b + a * t) := by
      field_simp [hb0, hdenB']
      <;> ring
    rw [hterm]
    apply (div_eq_iff hdenC).2
    have hdenA'' : 1 + t * a ≠ 0 := by simpa [mul_comm] using hdenA'
    have hdenB'' : t * a + b ≠ 0 := by simpa [add_comm, mul_comm] using hdenB'
    field_simp [hdenA'', hdenB'', ha0, hb1']
    apply mul_right_cancel₀ hdenB''
    simp [mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel₀ hdenB'']
    field_simp [hdenB'']
    <;> ring_nf
  have hInt' :
      (∫ t in (0 : ℝ)..1, (1 - t) / ((1 + a * t) * (1 + a * t / b))) =
        F 1 - F 0 := by
    calc
      (∫ t in (0 : ℝ)..1, (1 - t) / ((1 + a * t) * (1 + a * t / b))) =
          ∫ t in (0 : ℝ)..1,
            A * (a / (1 + a * t)) + B * ((a / b) / (1 + a * t / b)) :=
        intervalIntegral.integral_congr fun t ht =>
          hfractions t (by simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht)
      _ = F 1 - F 0 := hInt
  rw [hInt']
  simp only [F, A, B, mul_zero, zero_div, add_zero, Real.log_one, mul_one]
  field_simp [ha0, hb0, hb1']
  <;> ring_nf

/-- Closed form for the logarithmic response integral. -/
theorem phiResp_closed {l b : ℝ} (hl : 1 < l) (hb : 0 < b) (hb1 : b ≤ 1) :
    phiResp l b = b / (l - 1) *
      ((l - 1 + b) * Real.log (1 + (l - 1) / b) / Real.log l - l) := by
  have ha : 0 < l - 1 := by linarith
  have hlog : Real.log l ≠ 0 := ne_of_gt (Real.log_pos hl)
  by_cases hbEq : b = 1
  · subst b
    simp [phiResp, hlog]
  · have hb1' : b < 1 := lt_of_le_of_ne hb1 hbEq
    have hInt := logResponse_integral (a := l - 1) ha hb hb1'
    rw [phiResp, hInt]
    have hden : (l - 1) ^ 2 * (1 - b) ≠ 0 := mul_ne_zero (pow_ne_zero 2 (ne_of_gt ha))
      (ne_of_gt (sub_pos.mpr hb1'))
    have hlog' : Real.log (l - 1 + 1) = Real.log l := by congr 1 <;> ring
    rw [hlog']
    field_simp [hden, hlog, ne_of_gt ha]
    <;> ring

private noncomputable def logQuot (y : ℝ) : ℝ := -Real.log y / (1 - y)

private theorem hasDerivAt_logQuot {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    HasDerivAt logQuot
      ((-y⁻¹ * (1 - y) - Real.log y) / (1 - y) ^ 2) y := by
  have hlog := (Real.hasDerivAt_log (ne_of_gt hy)).neg
  have hden : HasDerivAt (fun x : ℝ => 1 - x) (-1) y := by
    convert (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y) using 1
    · funext x
      simp
    · ring_nf
  have hd := hlog.div hden (ne_of_gt (sub_pos.mpr hy1))
  convert hd using 1
  · funext x
    simp [logQuot]
  · simp only [Pi.neg_apply]
    ring_nf

private theorem logQuot_antitone : AntitoneOn logQuot (Set.Ioo (0 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo (0 : ℝ) 1)
  · intro y hy
    have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ioo] using hy
    exact (hasDerivAt_logQuot hy'.1 hy'.2).continuousAt.continuousWithinAt
  · intro y hy
    have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ioo] using hy
    exact (hasDerivAt_logQuot hy'.1 hy'.2).differentiableAt.differentiableWithinAt
  · intro y hy
    have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ioo] using hy
    have hd := hasDerivAt_logQuot hy'.1 hy'.2
    have hloginv := Real.log_le_sub_one_of_pos (inv_pos.mpr hy'.1)
    rw [Real.log_inv] at hloginv
    have hmul := mul_le_mul_of_nonneg_left hloginv hy'.1.le
    have hyinv : y * y⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hy'.1)
    have hnum : y - 1 - y * Real.log y ≤ 0 := by nlinarith [hmul, hyinv]
    have hderiv : deriv logQuot y =
        (y - 1 - y * Real.log y) / (y * (1 - y) ^ 2) := by
      rw [hd.deriv]
      field_simp [ne_of_gt hy'.1, ne_of_gt (sub_pos.mpr hy'.2)]
      <;> ring_nf
    rw [hderiv]
    exact div_nonpos_of_nonpos_of_nonneg hnum (mul_nonneg hy'.1.le (sq_nonneg (1 - y)))

/-- The identity converting the integral response potential to transformed escape. -/
theorem phiResp_identity {l b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioo 0 1) :
    let y := b / (l - 1 + b)
    (1 - y) ^ 2 * phiResp l b =
      y * (-((l - 1) / Real.log l) * Real.log y - l * (1 - y)) := by
  dsimp
  have ha : 0 < l - 1 := by linarith
  have hden : 0 < l - 1 + b := by linarith [ha, hb.1]
  have hy : 0 < b / (l - 1 + b) ∧ b / (l - 1 + b) < 1 := by
    constructor
    · exact div_pos hb.1 hden
    · rw [div_lt_one hden]
      linarith [hb.1]
  have hlog := phiResp_closed hl hb.1 hb.2.le
  rw [hlog]
  have hratio : b / (l - 1 + b) = (1 + (l - 1) / b)⁻¹ := by
    field_simp [ne_of_gt hb.1, ne_of_gt hden]
    have hne : -1 + l + b ≠ 0 := by linarith [hden]
    calc
      1 = (-1 + l + b) * (-1 + l + b)⁻¹ := (mul_inv_cancel₀ hne).symm
      _ = l * (-1 + l + b)⁻¹ + b * (-1 + l + b)⁻¹ -
          (-1 + l + b)⁻¹ := by ring
      _ = (l - 1 + b) / (b + (l - 1)) := by
        have hnum : l - 1 + b = -1 + l + b := by ring
        have hdenEq : -1 + l + b = b + (l - 1) := by ring
        rw [hnum, ← hdenEq]
        field_simp [hne]
        <;> ring
  have hlogy : Real.log (b / (l - 1 + b)) =
      -Real.log (1 + (l - 1) / b) := by rw [hratio, Real.log_inv]
  rw [hlogy]
  have hden' : 0 < l + b - 1 := by linarith [hden]
  have hden'' : 0 < -1 + l + b := by linarith [hden]
  field_simp [ne_of_gt ha, ne_of_gt hden, ne_of_gt hden',
    ne_of_gt hden'', ne_of_gt (Real.log_pos hl), ne_of_gt hb.1]
  ring_nf

/-- The response potential is nonnegative on its full stated range. -/
theorem phiResp_nonneg {l b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioc 0 1) :
    0 ≤ phiResp l b := by
  rw [phiResp]
  have hfactor : 0 ≤ (1 - b) * ((l - 1) / Real.log l) := by
    apply mul_nonneg (sub_nonneg.mpr hb.2)
    exact div_nonneg (by linarith) (Real.log_pos hl).le
  apply mul_nonneg hfactor
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have ha : 0 < l - 1 := by linarith
  have hb0 : 0 < b := hb.1
  have hden1 : 0 < 1 + (l - 1) * t := by positivity
  have hden2 : 0 < 1 + (l - 1) * t / b := by
    have hmul : 0 ≤ (l - 1) * t := mul_nonneg ha.le ht0
    have hdiv : 0 ≤ (l - 1) * t / b := div_nonneg hmul hb0.le
    linarith
  apply div_nonneg
  · exact sub_nonneg.mpr ht1
  · exact mul_nonneg hden1.le hden2.le

private theorem entropy_odds_sum {ι : Type*} (s : Finset ι) {t : ℝ} {y : ι → ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hy0 : ∀ i ∈ s, 0 < y i) (hy1 : ∀ i ∈ s, y i < 1)
    (hyt : ∀ i ∈ s, y i ≤ t)
    (hodds : t / (1 - t) = ∑ i ∈ s, y i / (1 - y i)) :
    -t * Real.log t ≤ (1 - t) ^ 2 *
      ∑ i ∈ s, y i / (1 - y i) * logQuot (y i) := by
  have htmem : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hsum : (∑ i ∈ s, y i / (1 - y i) * logQuot t) ≤
      ∑ i ∈ s, y i / (1 - y i) * logQuot (y i) := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left
    · exact logQuot_antitone ⟨hy0 i hi, hy1 i hi⟩ htmem (hyt i hi)
    · exact div_nonneg (hy0 i hi).le (sub_nonneg.mpr (hy1 i hi).le)
  have hfactor : 0 ≤ (1 - t) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum hfactor
  have halg : (1 - t) ^ 2 * (∑ i ∈ s, y i / (1 - y i)) * logQuot t =
      -t * Real.log t := by
    rw [← hodds]
    simp [logQuot]
    field_simp [ne_of_gt (sub_pos.mpr ht1)]
  calc
    -t * Real.log t = (1 - t) ^ 2 *
        (∑ i ∈ s, y i / (1 - y i)) * logQuot t := halg.symm
    _ = (1 - t) ^ 2 *
        ((∑ i ∈ s, y i / (1 - y i)) * logQuot t) := by ring
    _ = (1 - t) ^ 2 *
        ∑ i ∈ s, y i / (1 - y i) * logQuot t := by rw [Finset.sum_mul]
    _ ≤ (1 - t) ^ 2 *
        ∑ i ∈ s, y i / (1 - y i) * logQuot (y i) := hmul

private noncomputable def finiteY (ω : List ℕ → ℕ) (N : ℕ) (v : List ℕ)
    (x : ℝ) : ℝ := escapeN ω x N v / (x - 1 + escapeN ω x N v)

private theorem finiteY_mem {ω : List ℕ → ℕ} {x : ℝ} (hx : 1 < x)
    (N : ℕ) (v : List ℕ) (hω : LeaflessBelow ω N v) :
    finiteY ω N v x ∈ Set.Ioo 0 1 := by
  have hx0 : 0 < x := by linarith
  have he : 0 < escapeN ω x N v := escapeN_pos ω hx0 N v hω
  have hden : 0 < x - 1 + escapeN ω x N v := by linarith
  constructor
  · exact div_pos he hden
  · dsimp [finiteY]
    rw [div_lt_one hden]
    linarith

private theorem hasDerivAt_finiteY {ω : List ℕ → ℕ} {x : ℝ} (hx : 1 < x)
    (N : ℕ) (v : List ℕ) (hω : LeaflessBelow ω N v) :
    HasDerivAt (fun z => finiteY ω N v z)
      (-(((x - 1) * escapeN ω x N v * wN ω x N v +
          x * escapeN ω x N v) /
        (x * (x - 1 + escapeN ω x N v) ^ 2))) x := by
  have hx0 : 0 < x := by linarith
  have he := hasDerivAt_escapeN ω hx0 N v hω
  have hepos : 0 < escapeN ω x N v := escapeN_pos ω hx0 N v hω
  have hdenpos : 0 < x - 1 + escapeN ω x N v := by linarith
  have hlin : HasDerivAt (fun z : ℝ => z - 1) 1 x := by
    convert (hasDerivAt_id x).sub_const (1 : ℝ) using 1 <;> simp
  have hden := hlin.add he
  have hquot := he.div hden hdenpos.ne'
  convert hquot using 1
  · ext z
    rfl
  · simp only [Pi.add_apply, Pi.sub_apply, id_eq]
    field_simp [hx0.ne', hdenpos.ne']
    ring

private theorem finite_odds {ω : List ℕ → ℕ} {x : ℝ} (hx : 1 < x)
    (N : ℕ) (v : List ℕ) (hω : LeaflessBelow ω (N + 1) v) :
    x * finiteY ω (N + 1) v x / (1 - x * finiteY ω (N + 1) v x) =
      ∑ i : Fin (ω v), finiteY ω N (offChild ω v i) x /
        (1 - finiteY ω N (offChild ω v i) x) := by
  let a := x - 1
  let S := ∑ i : Fin (ω v), escapeN ω x N (offChild ω v i)
  have hx0 : 0 < x := by linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have hS : 0 < S := by
    apply Finset.sum_pos
    · intro i _
      exact escapeN_pos ω (by linarith) N _ (hω.2 i)
    · have hdegree : 1 ≤ ω v := hω.1
      let i0 : Fin (ω v) := ⟨0, Nat.zero_lt_one.trans_le hdegree⟩
      exact ⟨i0, Finset.mem_univ i0⟩
  have hb (i : Fin (ω v)) : 0 < escapeN ω x N (offChild ω v i) :=
    escapeN_pos ω (by linarith) N _ (hω.2 i)
  have hchild (i : Fin (ω v)) :
      finiteY ω N (offChild ω v i) x /
        (1 - finiteY ω N (offChild ω v i) x) =
        escapeN ω x N (offChild ω v i) / a := by
    let β := escapeN ω x N (offChild ω v i)
    have hsum : a + β ≠ 0 := ne_of_gt (add_pos ha (hb i))
    change (β / (a + β)) / (1 - β / (a + β)) = β / a
    have hcomp : 1 - β / (a + β) = a / (a + β) := by
      field_simp [hsum]
      <;> ring
    rw [hcomp]
    field_simp [hsum, ha.ne']
    <;> ring
  have hroot : finiteY ω (N + 1) v x = S / (x * (a + S)) := by
    change (escapeN ω x (N + 1) v) /
        (x - 1 + escapeN ω x (N + 1) v) = _
    have hrec : escapeN ω x (N + 1) v = S / (x + S) := rfl
    rw [hrec]
    have hxs : 0 < x + S := by linarith
    have hden : 0 < x - 1 + S / (x + S) := by positivity
    field_simp [ne_of_gt hxs, ne_of_gt hden, ne_of_gt (by linarith : 0 < x),
      ne_of_gt (add_pos ha hS)]
    <;> ring
  rw [hroot]
  have hrootId : x * (S / (x * (a + S))) /
      (1 - x * (S / (x * (a + S)))) = S / a := by
    have hden : 1 - x * (S / (x * (a + S))) ≠ 0 := by
      have hval : 1 - x * (S / (x * (a + S))) = a / (a + S) := by
        field_simp [ne_of_gt (by linarith : 0 < x), ne_of_gt (add_pos ha hS)]
        <;> ring
      rw [hval]
      positivity
    field_simp [ne_of_gt (by linarith : 0 < x), ha.ne',
      ne_of_gt (add_pos ha hS), hden]
    <;> ring
  rw [hrootId]
  unfold S
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  exact (hchild i).symm

private theorem finite_children_below_root {ω : List ℕ → ℕ} {x : ℝ}
    (hx : 1 < x) (N : ℕ) (v : List ℕ)
    (hω : LeaflessBelow ω (N + 1) v) :
    0 < x * finiteY ω (N + 1) v x ∧
      x * finiteY ω (N + 1) v x < 1 ∧
      ∀ i : Fin (ω v),
        finiteY ω N (offChild ω v i) x ≤ x * finiteY ω (N + 1) v x := by
  let a := x - 1
  let S := ∑ i : Fin (ω v), escapeN ω x N (offChild ω v i)
  have hx0 : 0 < x := by linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have hS : 0 < S := by
    apply Finset.sum_pos
    · intro i _
      exact escapeN_pos ω (by linarith) N _ (hω.2 i)
    · have hd : 1 ≤ ω v := hω.1
      let i0 : Fin (ω v) := ⟨0, Nat.zero_lt_one.trans_le hd⟩
      exact ⟨i0, Finset.mem_univ i0⟩
  have hroot : x * finiteY ω (N + 1) v x = S / (a + S) := by
    change x * (escapeN ω x (N + 1) v /
      (x - 1 + escapeN ω x (N + 1) v)) = _
    have hrec : escapeN ω x (N + 1) v = S / (x + S) := rfl
    rw [hrec]
    have hxs : 0 < x + S := by linarith
    have hden : 0 < x - 1 + S / (x + S) := by positivity
    field_simp [ne_of_gt hxs, ne_of_gt hden, ne_of_gt hx0,
      ne_of_gt (add_pos ha hS)]
    <;> ring
  constructor
  · rw [hroot]
    exact div_pos hS (add_pos ha hS)
  constructor
  · rw [hroot, div_lt_one (add_pos ha hS)]
    linarith
  · intro i
    let e := escapeN ω x N (offChild ω v i)
    have he : 0 < e := by dsimp [e]; exact escapeN_pos ω (by linarith) N _ (hω.2 i)
    have heS : e ≤ S := by
      dsimp [S, e]
      exact Finset.single_le_sum (fun j _ =>
        (escapeN_pos ω (by linarith) N (offChild ω v j) (hω.2 j)).le)
        (Finset.mem_univ i)
    have hdenE : 0 < a + e := add_pos ha he
    have hdenS : 0 < a + S := add_pos ha hS
    have hratio : e / (a + e) ≤ S / (a + S) := by
      rw [div_le_div_iff₀ hdenE hdenS]
      nlinarith [mul_le_mul_of_nonneg_left heS ha.le]
    calc
      finiteY ω N (offChild ω v i) x = e / (a + e) := by
        dsimp [finiteY, e, a]
      _ ≤ S / (a + S) := hratio
      _ = x * finiteY ω (N + 1) v x := hroot.symm

/-- Differentiating the additive-odds identity gives the exact parent response
of `t = x Y`, without expanding the finite-depth escape recursion. -/
private theorem finite_Qt_identity {ω : List ℕ → ℕ} {x : ℝ} (hx : 1 < x)
    (N : ℕ) (v : List ℕ) (hω : LeaflessBelow ω (N + 1) v) :
    -x * Real.log x *
        (finiteY ω (N + 1) v x +
          x * deriv (fun z => finiteY ω (N + 1) v z) x) =
      (1 - x * finiteY ω (N + 1) v x) ^ 2 *
        ∑ i : Fin (ω v),
          (-x * Real.log x * deriv (fun z => finiteY ω N (offChild ω v i) z) x) /
            (1 - finiteY ω N (offChild ω v i) x) ^ 2 := by
  have htmem := finite_children_below_root hx N v hω
  have ht : HasDerivAt (fun z => z * finiteY ω (N + 1) v z)
      (finiteY ω (N + 1) v x +
        x * deriv (fun z => finiteY ω (N + 1) v z) x) x := by
    have hy := hasDerivAt_finiteY hx (N + 1) v hω
    rw [← hy.deriv] at hy
    convert (hasDerivAt_id x).mul hy using 1
    · ext z
      rfl
    · simp only [id_eq]
      ring
  have hleft : HasDerivAt
      (fun z => z * finiteY ω (N + 1) v z / (1 - z * finiteY ω (N + 1) v z))
      ((finiteY ω (N + 1) v x +
        x * deriv (fun z => finiteY ω (N + 1) v z) x) /
          (1 - x * finiteY ω (N + 1) v x) ^ 2) x := by
    convert ht.div ((hasDerivAt_const x (1 : ℝ)).sub ht)
      (ne_of_gt (sub_pos.mpr htmem.2.1)) using 1 <;>
      simp only [Pi.sub_apply, Pi.one_apply, id_eq] <;> ring_nf
  have hright : HasDerivAt
      (fun z => ∑ i : Fin (ω v), finiteY ω N (offChild ω v i) z /
        (1 - finiteY ω N (offChild ω v i) z))
      (∑ i : Fin (ω v), deriv (fun z => finiteY ω N (offChild ω v i) z) x /
        (1 - finiteY ω N (offChild ω v i) x) ^ 2) x := by
    apply HasDerivAt.fun_sum
    intro i _
    have hi := finiteY_mem hx N (offChild ω v i) (hω.2 i)
    have hy := hasDerivAt_finiteY hx N (offChild ω v i) (hω.2 i)
    rw [← hy.deriv] at hy
    convert hy.div ((hasDerivAt_const x (1 : ℝ)).sub hy)
      (ne_of_gt (sub_pos.mpr hi.2)) using 1 <;>
      simp only [Pi.sub_apply, Pi.one_apply, id_eq] <;> ring_nf
  have heq : (fun z => z * finiteY ω (N + 1) v z /
      (1 - z * finiteY ω (N + 1) v z)) =ᶠ[𝓝 x]
      (fun z => ∑ i : Fin (ω v), finiteY ω N (offChild ω v i) z /
        (1 - finiteY ω N (offChild ω v i) z)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
    exact finite_odds hz N v hω
  have hd := hleft.unique (hright.congr_of_eventuallyEq heq)
  calc
    -x * Real.log x * (finiteY ω (N + 1) v x +
        x * deriv (fun z => finiteY ω (N + 1) v z) x) =
        (1 - x * finiteY ω (N + 1) v x) ^ 2 *
          (-x * Real.log x * ((finiteY ω (N + 1) v x +
            x * deriv (fun z => finiteY ω (N + 1) v z) x) /
              (1 - x * finiteY ω (N + 1) v x) ^ 2)) := by
          field_simp [ne_of_gt (sub_pos.mpr htmem.2.1)]
          <;> ring
    _ = (1 - x * finiteY ω (N + 1) v x) ^ 2 *
        (-x * Real.log x * ∑ i : Fin (ω v),
          deriv (fun z => finiteY ω N (offChild ω v i) z) x /
            (1 - finiteY ω N (offChild ω v i) x) ^ 2) := by rw [hd]
    _ = _ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The finite-depth transformed escape satisfies the logarithmic response
inequality.  The induction boundary is `Y = 1 / x`. -/
private theorem finiteY_log_bound {ω : List ℕ → ℕ} {x : ℝ} (hx : 1 < x) :
    ∀ (N : ℕ) (v : List ℕ), LeaflessBelow ω N v →
      -finiteY ω N v x * Real.log (finiteY ω N v x) ≤
        -x * Real.log x * deriv (fun z => finiteY ω N v z) x := by
  intro N
  induction N with
  | zero =>
      intro v hω
      rw [(hasDerivAt_finiteY hx 0 v hω).deriv]
      have hy : finiteY ω 0 v x = x⁻¹ := by
        simp only [finiteY, escapeN]
        congr 1
        ring
      rw [hy, Real.log_inv]
      simp only [escapeN, wN, mul_zero, zero_mul, zero_add, neg_zero, mul_one]
      field_simp [ne_of_gt (by linarith : 0 < x)]
      nlinarith
  | succ N ih =>
      intro v hω
      have hy := finiteY_mem hx (N + 1) v hω
      have hchild (i : Fin (ω v)) := finiteY_mem hx N (offChild ω v i) (hω.2 i)
      have hsum : (∑ i : Fin (ω v),
          finiteY ω N (offChild ω v i) x / (1 - finiteY ω N (offChild ω v i) x) *
            logQuot (finiteY ω N (offChild ω v i) x)) ≤
          ∑ i : Fin (ω v),
            (-x * Real.log x * deriv (fun z => finiteY ω N (offChild ω v i) z) x) /
              (1 - finiteY ω N (offChild ω v i) x) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        calc
          finiteY ω N (offChild ω v i) x / (1 - finiteY ω N (offChild ω v i) x) *
              logQuot (finiteY ω N (offChild ω v i) x) =
              (-finiteY ω N (offChild ω v i) x *
                Real.log (finiteY ω N (offChild ω v i) x)) /
                  (1 - finiteY ω N (offChild ω v i) x) ^ 2 := by
              simp only [logQuot]
              field_simp [ne_of_gt (sub_pos.mpr (hchild i).2)]
              <;> ring
          _ ≤ (-x * Real.log x * deriv (fun z => finiteY ω N (offChild ω v i) z) x) /
              (1 - finiteY ω N (offChild ω v i) x) ^ 2 :=
            (div_le_div_iff_of_pos_right (sq_pos_of_pos (sub_pos.mpr (hchild i).2))).2
              (ih (offChild ω v i) (hω.2 i))
      have hentropy := entropy_odds_sum Finset.univ
        (finite_children_below_root hx N v hω).1
        (finite_children_below_root hx N v hω).2.1
        (fun i _ => (hchild i).1) (fun i _ => (hchild i).2)
        (fun i _ => (finite_children_below_root hx N v hω).2.2 i)
        (finite_odds hx N v hω)
      have hmul := mul_le_mul_of_nonneg_left hsum
        (sq_nonneg (1 - x * finiteY ω (N + 1) v x))
      have hQt : -(x * finiteY ω (N + 1) v x) *
          Real.log (x * finiteY ω (N + 1) v x) ≤
          -x * Real.log x * (finiteY ω (N + 1) v x +
            x * deriv (fun z => finiteY ω (N + 1) v z) x) := by
        calc
          _ ≤ (1 - x * finiteY ω (N + 1) v x) ^ 2 *
              ∑ i : Fin (ω v),
                finiteY ω N (offChild ω v i) x / (1 - finiteY ω N (offChild ω v i) x) *
                  logQuot (finiteY ω N (offChild ω v i) x) := hentropy
          _ ≤ (1 - x * finiteY ω (N + 1) v x) ^ 2 *
              ∑ i : Fin (ω v),
                (-x * Real.log x * deriv (fun z => finiteY ω N (offChild ω v i) z) x) /
                  (1 - finiteY ω N (offChild ω v i) x) ^ 2 := hmul
          _ = _ := (finite_Qt_identity hx N v hω).symm
      rw [Real.log_mul (ne_of_gt (by linarith : 0 < x)) (ne_of_gt hy.1)] at hQt
      apply (mul_le_mul_iff_of_pos_left (by linarith : 0 < x)).mp
      nlinarith

private noncomputable def limitY (T : Tree) (x : ℝ) : ℝ :=
  escape x T / (x - 1 + escape x T)

private theorem limitY_mem {T : Tree} (hT : RegTree μ T) {x : ℝ}
    (hx : 1 < x) (hxm : x < mean μ) : limitY T x ∈ Set.Ioo 0 1 := by
  have he : 0 < escape x T := hT.1.2 x ⟨by linarith, hxm⟩ [] (present_nil T)
  have hden : 0 < x - 1 + escape x T := by linarith
  constructor
  · exact div_pos he hden
  · dsimp [limitY]
    rw [div_lt_one hden]
    linarith

private theorem hasDerivAt_limitY {T : Tree} (hT : RegTree μ T) {x : ℝ}
    (hx : 1 < x) (hxm : x < mean μ) :
    HasDerivAt (fun z => limitY T z)
      (((x - 1) * deriv (fun z => escape z T) x - escape x T) /
        (x - 1 + escape x T) ^ 2) x := by
  have hxmem : x ∈ Set.Ioo 0 (mean μ) := ⟨by linarith, hxm⟩
  have he : HasDerivAt (fun z => escape z T)
      (deriv (fun z => escape z T) x) x :=
    (((escape_contDiffOn hT).differentiableOn (by norm_num) x hxmem).differentiableAt
      (isOpen_Ioo.mem_nhds hxmem)).hasDerivAt
  have hlin : HasDerivAt (fun z : ℝ => z - 1) 1 x := by
    convert (hasDerivAt_id x).sub_const (1 : ℝ) using 1 <;> simp
  have hepos : 0 < escape x T := hT.1.2 x hxmem [] (present_nil T)
  have hden : 0 < x - 1 + escape x T := by linarith
  have hq := he.div (hlin.add he) hden.ne'
  convert hq using 1
  · ext z
    rfl
  · simp only [Pi.add_apply, Pi.sub_apply, id_eq]
    ring

private theorem hasDerivAt_finiteY_simple {ω : List ℕ → ℕ} {x : ℝ} (hx : 1 < x)
    (N : ℕ) (v : List ℕ) (hω : LeaflessBelow ω N v) :
    HasDerivAt (fun z => finiteY ω N v z)
      (((x - 1) * deriv (fun z => escapeN ω z N v) x - escapeN ω x N v) /
        (x - 1 + escapeN ω x N v) ^ 2) x := by
  have he := hasDerivAt_escapeN ω (by linarith : 0 < x) N v hω
  rw [← he.deriv] at he
  have hlin : HasDerivAt (fun z : ℝ => z - 1) 1 x := by
    convert (hasDerivAt_id x).sub_const (1 : ℝ) using 1 <;> simp
  have hpos : 0 < escapeN ω x N v := escapeN_pos ω (by linarith) N v hω
  have hden : 0 < x - 1 + escapeN ω x N v := by linarith
  have hq := he.div (hlin.add he) hden.ne'
  convert hq using 1
  · ext z
    rfl
  · simp only [Pi.add_apply, Pi.sub_apply, id_eq]
    ring

/-- The finite-depth logarithmic response bound passes to the escape, through the
convergence of the finite-depth escapes and their derivatives on regular trees. -/
private theorem limitY_log_bound {T : Tree} (hT : RegTree μ T) {x : ℝ}
    (hx : 1 < x) (hxm : x < mean μ) :
    -limitY T x * Real.log (limitY T x) ≤
      -x * Real.log x * deriv (fun z => limitY T z) x := by
  have hx0 : 0 < x := by linarith
  have hxmem : x ∈ Set.Ioo 0 (mean μ) := ⟨hx0, hxm⟩
  have hymem := limitY_mem hT hx hxm
  have hβ : Tendsto (fun N => escapeN T.val x N []) atTop (𝓝 (escape x T)) :=
    tendsto_escapeN_root hx0
  have hdβ : Tendsto (fun N => deriv (fun z => escapeN T.val z N []) x) atTop
      (𝓝 (deriv (fun z => escape z T) x)) := tendsto_deriv_escapeN hT hxmem
  have hden : Tendsto (fun N => x - 1 + escapeN T.val x N []) atTop
      (𝓝 (x - 1 + escape x T)) := tendsto_const_nhds.add hβ
  have hdenpos : 0 < x - 1 + escape x T := by
    have he : 0 < escape x T := by
      simpa only [subtree_nil] using hT.1.2 x hxmem [] (present_nil T)
    linarith
  have hY : Tendsto (fun N => finiteY T.val N [] x) atTop (𝓝 (limitY T x)) := by
    have hY0 := hβ.div hden hdenpos.ne'
    change Tendsto (fun N => finiteY T.val N [] x) atTop (𝓝 (limitY T x)) at hY0
    exact hY0
  have hYd : Tendsto (fun N => deriv (fun z => finiteY T.val N [] z) x) atTop
      (𝓝 (deriv (fun z => limitY T z) x)) := by
    rw [(hasDerivAt_limitY hT hx hxm).deriv]
    have hc : Tendsto (fun _ : ℕ => x - 1) atTop (𝓝 (x - 1)) := tendsto_const_nhds
    have hnum := (hc.mul hdβ).sub hβ
    have ht := hnum.div (hden.pow 2) (pow_ne_zero 2 hdenpos.ne')
    apply ht.congr'
    filter_upwards with N
    exact (hasDerivAt_finiteY_simple hx N []
      (leaflessBelow_tree hT.1.1 N [] (present_nil T))).deriv.symm
  have hlogY := (Real.continuousAt_log hymem.1.ne').tendsto.comp hY
  have hA : Tendsto (fun N => -finiteY T.val N [] x * Real.log (finiteY T.val N [] x))
      atTop (𝓝 (-limitY T x * Real.log (limitY T x))) := hY.neg.mul hlogY
  have hB : Tendsto (fun N => -x * Real.log x *
      deriv (fun z => finiteY T.val N [] z) x) atTop
      (𝓝 (-x * Real.log x * deriv (fun z => limitY T z) x)) :=
    tendsto_const_nhds.mul hYd
  have hz : 0 ≤ -x * Real.log x * deriv (fun z => limitY T z) x -
      -limitY T x * Real.log (limitY T x) := by
    apply ge_of_tendsto (hB.sub hA)
    filter_upwards with N
    exact sub_nonneg.mpr (finiteY_log_bound hx N []
      (leaflessBelow_tree hT.1.1 N [] (present_nil T)))
  linarith

/-- The lower bound for the response of Lemma 4.2 (`lem:log-response`). -/
theorem phiResp_le_resp (h : OffspringHyp μ) {T : Tree} (hT : RegTree μ T)
    {l : ℝ} (hl : 1 < l) (hlm : l < mean μ) :
    phiResp l (escape l T) ≤ resp l T := by
  let a : ℝ := l - 1
  let β : ℝ := escape l T
  let y : ℝ := β / (a + β)
  have hl0 : 0 < l := by linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have hlogpos : 0 < Real.log l := Real.log_pos hl
  have hβ0 : 0 < β := hT.1.2 l ⟨hl0, hlm⟩ [] (present_nil T)
  have hβ1 : β < 1 := escape_lt_one hl0 T
  have hD : 0 < a + β := add_pos ha hβ0
  have hymem : y ∈ Set.Ioo 0 1 := by
    have := limitY_mem hT hl hlm
    exact this
  have hlog := limitY_log_bound hT hl hlm
  have hQY : -l * Real.log l * deriv (fun z => limitY T z) l =
      (a * Real.log l * resp l T + l * Real.log l * β) / (a + β) ^ 2 := by
    rw [(hasDerivAt_limitY hT hl hlm).deriv, resp]
    dsimp [a, β]
    ring
  rw [hQY] at hlog
  have hscaled : -y * Real.log y * (a + β) ^ 2 ≤
      a * Real.log l * resp l T + l * Real.log l * β := by
    apply (le_div_iff₀ (sq_pos_of_pos hD)).1
    exact hlog
  have hy1 : 1 - y = a / (a + β) := by
    dsimp [y]
    field_simp [hD.ne']
    <;> ring
  have hResp : y * (-a / Real.log l * Real.log y - l * (1 - y)) ≤
      (1 - y) ^ 2 * resp l T := by
    apply (mul_le_mul_iff_of_pos_left hlogpos).mp
    have hid : Real.log l * ((1 - y) ^ 2 * resp l T) -
        Real.log l * (y * (-a / Real.log l * Real.log y - l * (1 - y))) =
        a / (a + β) ^ 2 *
          ((a * Real.log l * resp l T + l * Real.log l * β) -
            -y * Real.log y * (a + β) ^ 2) := by
      rw [hy1]
      dsimp [y]
      field_simp [hD.ne', hlogpos.ne']
      <;> ring
    have hfac : 0 ≤ a / (a + β) ^ 2 := div_nonneg ha.le (sq_nonneg _)
    have hnon := mul_nonneg hfac (sub_nonneg.mpr hscaled)
    nlinarith
  apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos (sub_pos.mpr hymem.2))).mp
  have hid := phiResp_identity hl (b := β) ⟨hβ0, hβ1⟩
  dsimp only at hid
  have hid' : (1 - y) ^ 2 * phiResp l β =
      y * (-a / Real.log l * Real.log y - l * (1 - y)) := by
    simpa only [y, a, neg_div] using hid
  rw [hid']
  exact hResp

end LPPMonotonicityProof.Analytic
