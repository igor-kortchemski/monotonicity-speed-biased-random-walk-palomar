module

public import LPPMonotonicityProof.Analytic.LowWindowReciprocal3
public import LPPMonotonicityProof.Analytic.HalfResponse
public import LPPMonotonicityProof.Analytic.LogResponse
public import LPPMonotonicityProof.Analytic.Ceiling2
public import LPPMonotonicityProof.Analytic.FirstSplit2
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Response loss and the reduced low-window inequality

This module proves the response-loss bound and the reduced cost inequality
`h𝒞 ≥ 1 - Vd - h𝓛` of the proof of Theorem 4.3 (`thm:low-window`). It proves the
scalar support-line estimates separately, then lifts them to tree and pair integrals.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private lemma ae_regular_pair_reduced (h : OffspringHyp μ) :
    ∀ᵐ z : Tree × Tree ∂(GW μ).prod (GW μ), RegTree μ z.1 ∧ RegTree μ z.2 :=
  (Measure.quasiMeasurePreserving_fst.ae (ae_regTree h)).and
    (Measure.quasiMeasurePreserving_snd.ae (ae_regTree h))

/-- The classical logarithm estimate `log x ≤ (x - 1) / √x` for `x ≥ 1`. -/
private lemma log_le_div_sqrt_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x - 1) / Real.sqrt x := by
  let G : ℝ → ℝ := fun y => (y - 1) / Real.sqrt y - Real.log y
  have hGder {y : ℝ} (hy : 0 < y) : HasDerivAt G
      ((Real.sqrt y - 1) ^ 2 / (2 * y * Real.sqrt y)) y := by
    have hs : Real.sqrt y ≠ 0 := Real.sqrt_ne_zero'.mpr hy
    have hsqrt := Real.hasDerivAt_sqrt (x := y) hy.ne'
    have hnum := (hasDerivAt_id y).sub_const (1 : ℝ)
    have hlog := Real.hasDerivAt_log hy.ne'
    have hdiv := hnum.div hsqrt hs
    have hsub := hdiv.sub hlog
    convert hsub using 1
    · funext z
      rfl
    field_simp [hs, hy.ne']
    have hys : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    simp only [id_eq]
    nlinarith [hys]
  have hcont : ContinuousOn G (Set.Ici 1) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.div
      · fun_prop
      · exact Real.continuous_sqrt.continuousOn
      · intro y hy
        have hy1 : 1 ≤ y := hy
        have hy0 : 0 < y := by linarith
        exact Real.sqrt_ne_zero'.mpr hy0
    · exact continuousOn_id.log (fun y hy => ne_of_gt (zero_lt_one.trans_le hy))
  have hdiff : DifferentiableOn ℝ G (interior (Set.Ici (1 : ℝ))) := by
    intro y hy
    have hy1 : 1 < y := by simpa only [interior_Ici, Set.mem_Ioi] using hy
    exact (hGder (by linarith)).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ y ∈ interior (Set.Ici (1 : ℝ)), 0 ≤ deriv G y := by
    intro y hy
    have hy1 : 1 < y := by simpa only [interior_Ici, Set.mem_Ioi] using hy
    rw [(hGder (by linarith)).deriv]
    have hy0 : 0 < y := by linarith
    positivity
  have hmono : MonotoneOn G (Set.Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 1) hcont hdiff hnonneg
  have hle := hmono (show (1 : ℝ) ∈ Set.Ici 1 by simp) hx hx
  have hG1 : G 1 = 0 := by norm_num [G]
  rw [hG1] at hle
  dsimp only [G] at hle
  linarith

private lemma one_add_div_three_le_sqrt {a : ℝ} (ha : 0 ≤ a) (ha3 : a ≤ 3) :
    1 + a / 3 ≤ Real.sqrt (1 + a) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  nlinarith [sq_nonneg a]

private lemma response_log_factor {l : ℝ} (hl : 1 < l) (ha3 : l - 1 ≤ 3) :
    1 + (l - 1) / 3 ≤ (l - 1) / Real.log l := by
  have ha : 0 < l - 1 := by linarith
  have hlog : 0 < Real.log l := Real.log_pos hl
  have hs := log_le_div_sqrt_of_one_le (show 1 ≤ l by linarith)
  have hs1 : Real.sqrt l = Real.sqrt (1 + (l - 1)) := by congr 1 <;> ring
  rw [hs1] at hs
  have hsqrt := one_add_div_three_le_sqrt ha.le ha3
  have hspos : 0 < Real.sqrt (1 + (l - 1)) := Real.sqrt_pos.2 (by linarith)
  have hleft : 0 < 1 + (l - 1) / 3 := by positivity
  apply (le_div_iff₀ hlog).2
  have hmul := mul_le_mul_of_nonneg_left hs hleft.le
  have hmul' := mul_le_mul_of_nonneg_right hsqrt (div_nonneg ha.le hspos.le)
  have hid : (1 + (l - 1) / 3) * ((l - 1) / Real.sqrt (1 + (l - 1))) ≤ l - 1 :=
    (mul_le_mul_of_nonneg_right hsqrt (div_nonneg ha.le hspos.le)).trans_eq (by
      field_simp [hspos.ne'])
  exact hmul.trans hid

/-- A supporting line for a convex function on `Icc 0 1`. -/
private lemma convex_support_on_unit {F : ℝ → ℝ} {c D t : ℝ}
    (hF : ConvexOn ℝ (Set.Icc 0 1) F) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hd : HasDerivAt F D c) :
    F c + D * (t - c) ≤ F t := by
  rcases lt_trichotomy c t with hct | rfl | htc
  · have hs := hF.le_slope_of_hasDerivAt hc ht hct hd
    rw [slope_def_field] at hs
    have hp : 0 < t - c := sub_pos.mpr hct
    have hm := (le_div_iff₀ hp).1 hs
    linarith
  · simp
  · have hs := hF.slope_le_of_hasDerivAt ht hc htc hd
    rw [slope_def_field] at hs
    have hn : 0 < c - t := sub_pos.mpr htc
    have hm := (div_le_iff₀ hn).1 hs
    linarith

private lemma convexOn_inv_affine_unit {c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d) :
    ConvexOn ℝ (Set.Icc 0 1) (fun t => (d + c * t)⁻¹) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy u v hu hv huv
  have hx0 : 0 ≤ x := hx.1
  have hy0 : 0 ≤ y := hy.1
  have hA : 0 < d + c * x := by positivity
  have hB : 0 < d + c * y := by positivity
  have hden : d + c * (u * x + v * y) =
      u * (d + c * x) + v * (d + c * y) := by
    have hvdef : v = 1 - u := by linarith
    subst v
    ring
  simp only [smul_eq_mul]
  rw [hden]
  have hsum : 0 < u * (d + c * x) + v * (d + c * y) := by
    by_cases hu0 : u = 0
    · have hv1 : v = 1 := by linarith
      simp [hu0, hv1, hB]
    · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hv0 : 0 ≤ v * (d + c * y) := by positivity
      have : 0 < u * (d + c * x) := by positivity
      linarith
  have hratio : u * (d + c * x)⁻¹ + v * (d + c * y)⁻¹ =
      (u * (d + c * y) + v * (d + c * x)) / ((d + c * x) * (d + c * y)) := by
    field_simp [hA.ne', hB.ne']
  rw [inv_eq_one_div, hratio]
  apply (div_le_div_iff₀ hsum (mul_pos hA hB)).2
  have hid : (u * (d + c * y) + v * (d + c * x)) *
      (u * (d + c * x) + v * (d + c * y)) =
      (d + c * x) * (d + c * y) +
        u * v * ((d + c * x) - (d + c * y)) ^ 2 := by
    have hvdef : v = 1 - u := by linarith
    subst v
    ring
  have hnon : 0 ≤ u * v * ((d + c * x) - (d + c * y)) ^ 2 := by positivity
  nlinarith

private lemma inv_affine_unit_antitone {c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d) :
    AntitoneOn (fun t => (d + c * t)⁻¹) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx.1
  have hy0 : 0 ≤ y := hy.1
  have hxpos : 0 < d + c * x := by positivity
  have hypos : 0 < d + c * y := by positivity
  apply (inv_le_inv₀ hypos hxpos).2
  nlinarith

private lemma triangular_integral_monomials {c₀ c₁ c₂ : ℝ} :
    (∫ t in (0 : ℝ)..1, c₀ + c₁ * t + c₂ * t ^ 2) = c₀ + c₁ / 2 + c₂ / 3 := by
  have hi₀ : IntervalIntegrable (fun _ : ℝ => c₀) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable; fun_prop
  have hi₁ : IntervalIntegrable (fun t : ℝ => c₁ * t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable; fun_prop
  have hi₂ : IntervalIntegrable (fun t : ℝ => c₂ * t ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add (hi₀.add hi₁) hi₂,
    intervalIntegral.integral_add hi₀ hi₁, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero, mul_one]
  rw [show (∫ t in (0 : ℝ)..1, c₁ * t) = c₁ * ∫ t in (0 : ℝ)..1, t from
    intervalIntegral.integral_const_mul _ _]
  rw [show (∫ t in (0 : ℝ)..1, c₂ * t ^ 2) = c₂ * ∫ t in (0 : ℝ)..1, t ^ 2 from
    intervalIntegral.integral_const_mul _ _]
  rw [integral_id]
  have hp := integral_pow (a := (0 : ℝ)) (b := 1) (n := 2)
  norm_num at hp ⊢
  ring

/-- Jensen under the triangular density `2(1-t)` for the product of the two
positive decreasing convex factors appearing in `phiResp`. -/
private lemma triangular_jensen_response {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((1 + a / 3) * (1 + a / 3 / b))⁻¹ ≤
      ∫ t in (0 : ℝ)..1, 2 * (1 - t) * ((1 + a * t)⁻¹ * (1 + a * t / b)⁻¹) := by
  let c : ℝ := 1 / 3
  let F : ℝ → ℝ := fun t => (1 + a * t)⁻¹ * (1 + a * t / b)⁻¹
  let D : ℝ := -(a * (1 + a * c / b) + a / b * (1 + a * c)) /
    ((1 + a * c) ^ 2 * (1 + a * c / b) ^ 2)
  have hf : ConvexOn ℝ (Set.Icc 0 1) (fun t => (1 + a * t)⁻¹) := by
    simpa using convexOn_inv_affine_unit (c := a) (d := 1) ha.le zero_lt_one
  have hg : ConvexOn ℝ (Set.Icc 0 1) (fun t => (1 + a * t / b)⁻¹) := by
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      convexOn_inv_affine_unit (c := a / b) (d := 1)
        (div_nonneg ha.le hb.le) zero_lt_one
  have hfa : AntitoneOn (fun t => (1 + a * t)⁻¹) (Set.Icc 0 1) :=
    inv_affine_unit_antitone ha.le zero_lt_one
  have hga : AntitoneOn (fun t => (1 + a * t / b)⁻¹) (Set.Icc 0 1) := by
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      inv_affine_unit_antitone (c := a / b) (d := 1)
        (div_nonneg ha.le hb.le) zero_lt_one
  have hF : ConvexOn ℝ (Set.Icc 0 1) F := by
    have hm := hf.mul hg
      (fun x hx => inv_nonneg.mpr (by have hx0 : 0 ≤ x := hx.1; positivity))
      (fun x hx => inv_nonneg.mpr (by have hx0 : 0 ≤ x := hx.1; positivity))
      (hfa.monovaryOn hga)
    change ConvexOn ℝ (Set.Icc 0 1) ((fun t => (1 + a * t)⁻¹) * (fun t => (1 + a * t / b)⁻¹))
    exact hm
  have hden1 : 1 + a * c ≠ 0 := by positivity
  have hden2 : 1 + a * c / b ≠ 0 := by positivity
  have hd1 : HasDerivAt (fun t : ℝ => 1 + a * t) a c := by
    simpa using ((hasDerivAt_id c).const_mul a).const_add (1 : ℝ)
  have hd2 : HasDerivAt (fun t : ℝ => 1 + a * t / b) (a / b) c := by
    simpa only [id_eq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, mul_one] using
      ((hasDerivAt_id c).const_mul (a / b)).const_add (1 : ℝ)
  have hd : HasDerivAt F D c := by
    have hi := (hd1.inv hden1).mul (hd2.inv hden2)
    change HasDerivAt F _ c at hi
    convert hi using 1
    dsimp only [D]
    simp only [F, Pi.inv_apply]
    field_simp [hden1, hden2]
    ring
  have hc : c ∈ Set.Icc (0 : ℝ) 1 := by norm_num [c]
  have hFcont : ContinuousOn F (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀ (by fun_prop)
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      positivity
    · apply ContinuousOn.inv₀ (by fun_prop)
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      positivity
  have hiF : IntervalIntegrable (fun t => 2 * (1 - t) * F t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : ContinuousOn (fun t : ℝ => 2 * (1 - t)) _).mul hFcont
  have hiL : IntervalIntegrable
      (fun t => 2 * (1 - t) * (F c + D * (t - c))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have hle := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (by norm_num) hiL hiF (fun t ht => by
      have hw : 0 ≤ 2 * (1 - t) := by have := ht.2; positivity
      exact mul_le_mul_of_nonneg_left (convex_support_on_unit hF hc ht hd) hw)
  have hleft : (∫ t in (0 : ℝ)..1, 2 * (1 - t) * (F c + D * (t - c))) = F c := by
    have heq : (fun t => 2 * (1 - t) * (F c + D * (t - c))) =
        fun t => (2 * F c - 2 * D * c) + (2 * D * c - 2 * F c + 2 * D) * t +
          (-2 * D) * t ^ 2 := by funext t; ring
    rw [heq, triangular_integral_monomials]
    dsimp only [c]
    ring
  rw [hleft] at hle
  dsimp only [F, c] at hle
  simpa only [one_div, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc,
    one_mul] using hle

private lemma phiResp_two_lower {l b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioc 0 1)
    (ha3 : l - 1 ≤ 3) :
    (1 - b) / (1 + (l - 1) / (3 * b)) ≤ 2 * phiResp l b := by
  let a := l - 1
  let d₀ := a / Real.log l
  let D₀ := 1 + a / 3
  let Db := 1 + a / (3 * b)
  have ha : 0 < a := by dsimp [a]; linarith
  have hlog : 0 < Real.log l := Real.log_pos hl
  have hb0 : 0 < b := hb.1
  have hd₀ : D₀ ≤ d₀ := response_log_factor hl ha3
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  have hDb : 0 < Db := by dsimp [Db]; positivity
  have hweight : 0 ≤ (1 - b) * d₀ :=
    mul_nonneg (sub_nonneg.mpr hb.2) (div_nonneg ha.le hlog.le)
  have hJ := triangular_jensen_response ha hb.1
  have hInt : (∫ t in (0 : ℝ)..1,
      2 * (1 - t) * ((1 + a * t)⁻¹ * (1 + a * t / b)⁻¹)) =
      2 * ∫ t in (0 : ℝ)..1, (1 - t) / ((1 + a * t) * (1 + a * t / b)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    field_simp
  rw [hInt] at hJ
  have hmul := mul_le_mul_of_nonneg_left hJ hweight
  have hright : (1 - b) * d₀ *
      (2 * ∫ t in (0 : ℝ)..1, (1 - t) / ((1 + a * t) * (1 + a * t / b))) =
      2 * phiResp l b := by
    dsimp only [phiResp, a, d₀]
    ring
  rw [hright] at hmul
  have hfactor : (1 - b) / Db ≤
      (1 - b) * d₀ * ((D₀ * Db)⁻¹) := by
    have hratio : 1 ≤ d₀ / D₀ := (le_div_iff₀ hD₀).2 (by simpa using hd₀)
    have hbase : 0 ≤ (1 - b) / Db := div_nonneg (sub_nonneg.mpr hb.2) hDb.le
    have hm := mul_le_mul_of_nonneg_right hratio hbase
    have heq : (1 - b) * d₀ * ((D₀ * Db)⁻¹) =
        ((1 - b) / Db) * (d₀ / D₀) := by
      field_simp [hD₀.ne', hDb.ne']
    rw [heq]
    simpa only [mul_comm, one_mul] using hm
  exact hfactor.trans (by simpa only [D₀, Db, div_div] using hmul)

private lemma phiResp_loss_scalar {l b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Ioc 0 1)
    (ha3 : l - 1 ≤ 3) :
    1 - b - 2 * phiResp l b ≤ (l - 1) * (1 - b) / (3 * b + (l - 1)) := by
  have hphi := phiResp_two_lower hl hb ha3
  have ha : 0 < l - 1 := by linarith
  have hb0 : 0 < b := hb.1
  have hden : 0 < 1 + (l - 1) / (3 * b) := by positivity
  have hid : 1 - b - (1 - b) / (1 + (l - 1) / (3 * b)) =
      (l - 1) * (1 - b) / (3 * b + (l - 1)) := by
    field_simp [hb0.ne']
    ring
  linarith

private lemma reciprocal_scaled_tangent {s T B : ℝ}
    (hs : 0 < s) (hT : 0 < T) (hB : 0 < B) :
    T / (1 + s * T) ≤ B / (2 + s * B) +
      4 / (2 + s * B) ^ 2 * (T - B / 2) := by
  have hTden : 0 < 1 + s * T := by positivity
  have hh : 0 < 2 + s * B := by positivity
  have hid : B / (2 + s * B) + 4 / (2 + s * B) ^ 2 * (T - B / 2) -
      T / (1 + s * T) =
      4 * s * (T - B / 2) ^ 2 /
        ((2 + s * B) ^ 2 * (1 + s * T)) := by
    field_simp [hTden.ne', hh.ne']
    ring
  have hnon : 0 ≤ 4 * s * (T - B / 2) ^ 2 /
      ((2 + s * B) ^ 2 * (1 + s * T)) := by positivity
  linarith

private lemma response_loss_tangent {s R M p : ℝ}
    (hs : 0 < s) (hR : 0 < R) (hM : 0 < M) (hp : 0 ≤ p) :
    s * (R - p) / (3 + s * R) ≤ s * (M - p) / (3 + s * M) +
      s * (3 + s * p) / (3 + s * M) ^ 2 * (R - M) := by
  have hRd : 0 < 3 + s * R := by positivity
  have hMd : 0 < 3 + s * M := by positivity
  have hid : s * (M - p) / (3 + s * M) +
      s * (3 + s * p) / (3 + s * M) ^ 2 * (R - M) -
      s * (R - p) / (3 + s * R) =
      s ^ 2 * (3 + s * p) * (R - M) ^ 2 /
        ((3 + s * M) ^ 2 * (3 + s * R)) := by
    field_simp [hRd.ne', hMd.ne', hs.ne']
    ring_nf
  have hnon : 0 ≤ s ^ 2 * (3 + s * p) * (R - M) ^ 2 /
      ((3 + s * M) ^ 2 * (3 + s * R)) := by positivity
  linarith

private lemma response_loss_mono {s R M p : ℝ}
    (hs : 0 ≤ s) (hR : 0 ≤ R) (hM : 0 ≤ M) (hp : 0 ≤ p) (hRM : R ≤ M) :
    s * (R - p) / (3 + s * R) ≤ s * (M - p) / (3 + s * M) := by
  have hRd : 0 < 3 + s * R := by positivity
  have hMd : 0 < 3 + s * M := by positivity
  apply (div_le_div_iff₀ hRd hMd).2
  have hm := mul_nonneg hs (sub_nonneg.mpr hRM)
  have hid : s * (M - p) * (3 + s * R) - s * (R - p) * (3 + s * M) =
      (3 + s * p) * (s * (M - R)) := by ring
  have hnon : 0 ≤ (3 + s * p) * (s * (M - R)) :=
    mul_nonneg (by positivity) hm
  linarith

private lemma lowWindow_R_integrable (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    Integrable (fun T => pBr μ / escape l T) (GW μ) := by
  let p := pBr μ
  let A := 1 - eJ μ - sS μ l * (p1 μ + pBr μ * eJ μ)
  have hp : 0 < p := pBr_pos h
  have hA : 3 / 8 ≤ A := lowWindow_reciprocal_A_lower h hl hlm hs
  have hA0 : 0 < A := by linarith
  have hX : 1 - l * invMean μ = p * A := by
    have hq : p1 μ = 1 - pBr μ := by linarith [p1_add_pBr h]
    dsimp only [p, A]
    rw [invMean_eq_p1_add h, hq, sS]
    field_simp [(pBr_pos h).ne']
    ring
  have hU : l * invMean μ < 1 := by
    have hpos : 0 < p * A := mul_pos hp hA0
    linarith
  have hi := (integrable_inv_escape h (by linarith : 0 < l) hU).2.const_mul p
  simpa only [p, div_eq_mul_inv] using hi

private lemma ae_R_bounds (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) :
    ∀ᵐ T ∂GW μ, 0 < pBr μ / escape l T ∧ pBr μ ≤ pBr μ / escape l T := by
  have hlmem : l ∈ Set.Ioo 0 (mean μ) := ⟨by linarith, hlm⟩
  filter_upwards [ae_regTree h] with T hT
  have he := escape_mem_Ioc_of_regTree hT hlmem
  have hp := pBr_pos h
  constructor
  · exact div_pos hp he.1
  · exact (le_div_iff₀ he.1).2 (by nlinarith [he.2])

private lemma lowWindow_K0_le (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    let p := pBr μ
    let q := p1 μ
    let e := eJ μ
    let s := sS μ l
    let A := 1 - e - s * (q + p * e)
    let d := (1 - s * q ^ 2 / 2) / A - q * (1 + p) / 4
    let hh := 2 + s * (p + d)
    0 < hh ∧ K0 μ l ≤ (p + d) / (p * hh) := by
  intro p q e s A d hh
  let B := p + d
  let R : Tree → ℝ := fun T => p / escape l T
  let T : Tree × Tree → ℝ := fun z => p / tau (escape l z.1) (escape l z.2)
  let J : Tree × Tree → ℝ := fun z => p / DfunProv l (escape l z.1) (escape l z.2)
  let ν := (GW μ).prod (GW μ)
  have hp : 0 < p := pBr_pos h
  have hs0 : 0 < s := by dsimp [s, sS]; positivity
  have hlmem : l ∈ Set.Ioo 0 (mean μ) := ⟨by linarith, hlm⟩
  have hlps : l = 1 + p * s := by
    dsimp only [s, p, sS]
    field_simp [(pBr_pos h).ne']
    ring
  have hRint : Integrable R (GW μ) := lowWindow_R_integrable h hl hlm hs
  have hRb := ae_R_bounds h hl hlm
  have hpairb : ∀ᵐ z ∂ν, 0 < R z.1 ∧ p ≤ R z.1 ∧ 0 < R z.2 ∧ p ≤ R z.2 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst.ae hRb),
      (Measure.quasiMeasurePreserving_snd.ae hRb)] with z hz1 hz2
    exact ⟨hz1.1, hz1.2, hz2.1, hz2.2⟩
  have hTprops : ∀ᵐ z ∂ν, 0 < T z ∧ T z ≤ R z.1 + R z.2 := by
    filter_upwards [hpairb, ae_regular_pair_reduced h] with z hz hreg
    have hb1 := escape_mem_Ioc_of_regTree hreg.1 hlmem
    have hb2 := escape_mem_Ioc_of_regTree hreg.2 hlmem
    have hτ : 0 < tau (escape l z.1) (escape l z.2) := by
      unfold tau
      nlinarith [mul_nonneg hb1.1.le (sub_nonneg.mpr hb2.2), hb2.1]
    have hTpos : 0 < T z := div_pos hp hτ
    refine ⟨hTpos, ?_⟩
    have hden : 0 < R z.1 + R z.2 - p := by
      have hp1 : p ≤ R z.1 := hz.2.1
      have hp2 : p ≤ R z.2 := hz.2.2.2
      linarith
    have hid : T z = R z.1 * R z.2 / (R z.1 + R z.2 - p) := by
      dsimp only [T, R, tau]
      field_simp [hp.ne', hb1.1.ne', hb2.1.ne']
      ring
    rw [hid]
    apply (div_le_iff₀ hden).2
    have hpos : 0 ≤ R z.1 * (R z.1 - p) + R z.2 * (R z.2 - p) + R z.1 * R z.2 := by
      have hp1 := hz.2.1
      have hp2 := hz.2.2.2
      have hr10 := hz.1.le
      have hr20 := hz.2.2.1.le
      positivity
    nlinarith
  have hTmeas : Measurable T := by
    dsimp only [T]
    unfold tau
    have he := measurable_escape l
    exact measurable_const.div
      (((he.comp measurable_fst).add (he.comp measurable_snd)).sub
        ((he.comp measurable_fst).mul (he.comp measurable_snd)))
  have hTint : Integrable T ν := by
    have hi := (hRint.comp_fst (GW μ)).add (hRint.comp_snd (GW μ))
    apply hi.mono' hTmeas.aestronglyMeasurable
    filter_upwards [hTprops] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg hz.1.le]
    exact hz.2
  have hTpos : 0 < ∫ z, T z ∂ν := integral_pos_of_ae_pos hTint (hTprops.mono fun z hz => hz.1)
  have hpair : 2 * (∫ z, T z ∂ν) - p ≤ d := by
    have h5 := lowWindow_reciprocal h hl hlm hs
    exact h5.2.2.2.2
  have hBpos : 0 < B := by dsimp only [B]; linarith
  have hhpos : 0 < hh := by dsimp only [hh, B]; positivity
  have hET : (∫ z, T z ∂ν) ≤ B / 2 := by linarith
  have hJint : Integrable J ν := by
    have hi : Integrable (fun z => p * (1 / Dfun l (escape l z.1) (escape l z.2))) ν :=
      (integrable_inv_D h hlmem).const_mul p
    apply hi.congr
    filter_upwards with z
    dsimp [J, DfunProv, Dfun]
    ring
  have hRhsInt : Integrable (fun z => B / hh + 4 / hh ^ 2 * (T z - B / 2)) ν := by
    have hi := (integrable_const (B / hh)).add ((hTint.sub (integrable_const (B / 2))).const_mul
      (4 / hh ^ 2))
    convert hi using 1
  have hpoint : ∀ᵐ z ∂ν, J z ≤ B / hh + 4 / hh ^ 2 * (T z - B / 2) := by
    filter_upwards [hpairb, ae_regular_pair_reduced h] with z hz hreg
    have hb1 := escape_mem_Ioc_of_regTree hreg.1 hlmem
    have hb2 := escape_mem_Ioc_of_regTree hreg.2 hlmem
    have hτ : 0 < tau (escape l z.1) (escape l z.2) := by
      unfold tau
      nlinarith [mul_nonneg hb1.1.le (sub_nonneg.mpr hb2.2), hb2.1]
    have hTpos : 0 < T z := div_pos hp hτ
    have hD := DfunProv_pos_of_regTrees hreg.1 hreg.2 hlmem
    have h1T : 0 < 1 + s * T z := by positivity
    have hJeq : J z = T z / (1 + s * T z) := by
      dsimp only [J, DfunProv]
      have hdenEq : l - 1 + escape l z.1 + escape l z.2 - escape l z.1 * escape l z.2 =
          p * s + tau (escape l z.1) (escape l z.2) := by
        rw [hlps]
        unfold tau
        ring
      dsimp only [DfunProv] at hD
      rw [hdenEq] at hD ⊢
      rw [show T z = p / tau (escape l z.1) (escape l z.2) from rfl]
      field_simp [hp.ne', hτ.ne', hD.ne', h1T.ne']
      ring
    rw [hJeq]
    have htan := reciprocal_scaled_tangent hs0 hTpos hBpos
    have hheq : hh = 2 + s * B := by dsimp [hh, B]
    rw [hheq]
    exact htan
  have hcompare := integral_mono_ae hJint hRhsInt hpoint
  have hsub : (∫ z, T z - B / 2 ∂ν) = (∫ z, T z ∂ν) - B / 2 := by
    rw [integral_sub hTint (integrable_const _), integral_const]
    simp only [ν, probReal_univ, smul_eq_mul, one_mul]
  have hEq : (∫ z, B / hh + 4 / hh ^ 2 * (T z - B / 2) ∂ν) =
      B / hh + 4 / hh ^ 2 * ((∫ z, T z ∂ν) - B / 2) := by
    calc
      _ = (∫ _ : Tree × Tree, B / hh ∂ν) +
          ∫ z, 4 / hh ^ 2 * (T z - B / 2) ∂ν :=
        integral_add (integrable_const _) ((hTint.sub (integrable_const _)).const_mul _)
      _ = B / hh + 4 / hh ^ 2 * (∫ z, T z - B / 2 ∂ν) := by
        rw [integral_const_mul, integral_const]
        simp only [ν, probReal_univ, smul_eq_mul, one_mul]
      _ = _ := by rw [hsub]
  have hJle : (∫ z, J z ∂ν) ≤ B / hh := by
    rw [hEq] at hcompare
    have hc : 0 ≤ 4 / hh ^ 2 := by positivity
    nlinarith
  have hK : (∫ z, J z ∂ν) = p * K0 μ l := by
    dsimp only [J, K0, pairE, ν]
    simp_rw [div_eq_mul_inv]
    rw [integral_const_mul]
    simp only [one_mul]
  refine ⟨hhpos, ?_⟩
  apply (le_div_iff₀ (mul_pos hp hhpos)).2
  have hm := mul_le_mul_of_nonneg_right hJle hhpos.le
  rw [hK] at hm
  calc
    K0 μ l * (p * hh) = p * K0 μ l * hh := by ring
    _ ≤ B / hh * hh := hm
    _ = B := by field_simp [hhpos.ne']

private lemma measurable_Gam_escape_reduced (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (l : ℝ) : Measurable (fun T => Gam μ l (escape l T)) := by
  have he := measurable_escape l
  have hm : Measurable (fun z : Tree × Tree =>
      Pol l (speedValueProv μ l) (escape l z.2) /
        DfunProv l (escape l z.1) (escape l z.2) ^ 2) := by
    unfold Pol DfunProv
    fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := GW μ)).measurable

private lemma lowWindow_response_loss (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    let p := pBr μ
    let q := p1 μ
    let e := eJ μ
    let s := sS μ l
    let A := 1 - e - s * (q + p * e)
    let L := s * (1 / A - p) / ((1 + s) * (3 + s / A))
    (∫ T, (1 - escape l T - 2 * resp l T) * Gam μ l (escape l T) ∂GW μ) ≤ L := by
  intro p q e s A L
  let R : Tree → ℝ := fun T => p / escape l T
  let M := ∫ T, R T ∂GW μ
  let F : Tree → ℝ := fun T => s * (R T - p) / (3 + s * R T)
  let FM := s * (M - p) / (3 + s * M)
  let C := s * (3 + s * p) / (3 + s * M) ^ 2
  let X := ∫ T, (1 - escape l T - 2 * resp l T) * Gam μ l (escape l T) ∂GW μ
  have hp : 0 < p := pBr_pos h
  have hp1 : p ≤ 1 := by
    have hq : 0 ≤ q := ENNReal.toReal_nonneg
    have hpq := p1_add_pBr h
    dsimp only [q, p] at *
    linarith
  have hs0 : 0 < s := by dsimp [s, sS]; positivity
  have hlmem : l ∈ Set.Ioo 0 (mean μ) := ⟨by linarith, hlm⟩
  have hlps : l = 1 + p * s := by
    dsimp only [s, p, sS]
    field_simp [(pBr_pos h).ne']
    ring
  have hA : 3 / 8 ≤ A := lowWindow_reciprocal_A_lower h hl hlm hs
  have hA0 : 0 < A := by linarith
  have hRint : Integrable R (GW μ) := lowWindow_R_integrable h hl hlm hs
  have hRb := ae_R_bounds h hl hlm
  have hM : M ≤ 1 / A := by
    have h5 := lowWindow_reciprocal h hl hlm hs
    exact h5.2.1
  have hMp : p ≤ M := by
    have hm := integral_mono_ae (integrable_const p) hRint (hRb.mono fun T hT => hT.2)
    simpa only [M, integral_const, probReal_univ, smul_eq_mul, one_mul] using hm
  have hM0 : 0 < M := hp.trans_le hMp
  have hRmeas : Measurable R := by
    dsimp only [R]
    exact measurable_const.div (measurable_escape l)
  have hFmeas : Measurable F := by
    dsimp only [F]
    fun_prop
  have hFprops : ∀ᵐ T ∂GW μ, 0 ≤ F T ∧ F T ≤ 1 := by
    filter_upwards [hRb] with T hT
    have hden : 0 < 3 + s * R T := by nlinarith [mul_pos hs0 hT.1]
    have hnum : 0 ≤ s * (R T - p) := mul_nonneg hs0.le (sub_nonneg.mpr hT.2)
    have hle : F T ≤ 1 := by
      dsimp only [F]
      apply (div_le_one hden).2
      nlinarith [mul_pos hs0 hp]
    exact ⟨div_nonneg hnum hden.le, hle⟩
  have hFint : Integrable F (GW μ) := by
    apply Integrable.of_bound hFmeas.aestronglyMeasurable 1
    filter_upwards [hFprops] with T hT
    rw [Real.norm_eq_abs, abs_of_nonneg hT.1]
    exact hT.2
  have hRhsInt : Integrable (fun T => FM + C * (R T - M)) (GW μ) := by
    exact (integrable_const FM).add ((hRint.sub (integrable_const M)).const_mul C)
  have htangent : ∀ᵐ T ∂GW μ, F T ≤ FM + C * (R T - M) := by
    filter_upwards [hRb] with T hT
    exact response_loss_tangent hs0 hT.1 hM0 hp.le
  have hEq : (∫ T, FM + C * (R T - M) ∂GW μ) = FM := by
    calc
      _ = (∫ _ : Tree, FM ∂GW μ) + ∫ T, C * (R T - M) ∂GW μ :=
        integral_add (integrable_const _) ((hRint.sub (integrable_const _)).const_mul _)
      _ = FM + C * (∫ T, R T - M ∂GW μ) := by
        rw [integral_const_mul, integral_const]
        simp only [probReal_univ, smul_eq_mul, one_mul]
      _ = FM := by rw [integral_sub hRint (integrable_const _), integral_const]; simp [M]
  have hIntF : (∫ T, F T ∂GW μ) ≤ FM := by
    have hc := integral_mono_ae hFint hRhsInt htangent
    rwa [hEq] at hc
  have hmono : FM ≤ s * (1 / A - p) / (3 + s / A) := by
    simpa only [FM, div_eq_mul_inv, one_mul] using response_loss_mono hs0.le hM0.le (by positivity) hp.le hM
  have hw : wbar μ l < 1 := by
    have hd := dW_pos h hl hlm
    dsimp only [dW] at hd
    linarith
  have hmu : muY μ l ≤ 1 / (1 + s) := by
    rw [muY_eq h hl hlm]
    exact (div_le_div_iff_of_pos_right (by positivity)).2 hw.le
  have hG : ∀ᵐ T ∂GW μ, 0 < Gam μ l (escape l T) ∧
      Gam μ l (escape l T) ≤ 1 / (1 + s) := by
    filter_upwards [ae_regTree h] with T hT
    have hb := escape_mem_Ioc_of_regTree hT hlmem
    have hg := Gam_pos_le μ h hl hlm ⟨hb.1.le, hb.2⟩
    exact ⟨hg.1, hg.2.trans hmu⟩
  have hbaseInt : Integrable (fun T => (1 - escape l T) * Gam μ l (escape l T)) (GW μ) := by
    have hm : Measurable (fun T => (1 - escape l T) * Gam μ l (escape l T)) :=
      (measurable_const.sub (measurable_escape l)).mul (measurable_Gam_escape_reduced μ l)
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [hG, ae_regTree h] with T hGT hT
    have hb := escape_mem_Ioc_of_regTree hT hlmem
    have hnone : 0 ≤ (1 - escape l T) * Gam μ l (escape l T) :=
      mul_nonneg (sub_nonneg.mpr hb.2) hGT.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg hnone]
    calc
      (1 - escape l T) * Gam μ l (escape l T) ≤ 1 * Gam μ l (escape l T) :=
        mul_le_mul_of_nonneg_right (by linarith [hb.1]) hGT.1.le
      _ ≤ 1 / (1 + s) := by simpa only [one_mul] using hGT.2
      _ ≤ 1 := by exact (div_le_one (by positivity)).2 (by linarith)
  have hXint : Integrable (fun T =>
      (1 - escape l T - 2 * resp l T) * Gam μ l (escape l T)) (GW μ) := by
    have hi := hbaseInt.sub ((integrable_resp_Gam h hlmem).const_mul 2)
    convert hi using 1
    funext T
    simp only [Pi.sub_apply]
    ring
  have hFdivInt : Integrable (fun T => F T / (1 + s)) (GW μ) := hFint.div_const _
  have hpoint : ∀ᵐ T ∂GW μ,
      (1 - escape l T - 2 * resp l T) * Gam μ l (escape l T) ≤ F T / (1 + s) := by
    filter_upwards [hG, ae_regTree h, hRb] with T hGT hT hRT
    have hb := escape_mem_Ioc_of_regTree hT hlmem
    have hdenF : 0 < 3 + s * R T := by nlinarith [mul_pos hs0 hRT.1]
    have hFnp' : 0 ≤ F T :=
      div_nonneg (mul_nonneg hs0.le (sub_nonneg.mpr hRT.2)) hdenF.le
    have hps : p * s ≤ 1 / 8 := by
      calc
        p * s ≤ 1 * (1 / 8) := mul_le_mul hp1 hs hs0.le zero_le_one
        _ = 1 / 8 := one_mul _
    have ha3 : l - 1 ≤ 3 := by rw [hlps]; linarith
    have hscalar := phiResp_loss_scalar hl hb ha3
    have hresp := phiResp_le_resp h hT hl hlm
    have hfeq : (l - 1) * (1 - escape l T) / (3 * escape l T + (l - 1)) = F T := by
      rw [show l - 1 = p * s by linarith [hlps]]
      dsimp only [F, R]
      have hden : 0 < 3 + s * (p / escape l T) := by nlinarith [mul_pos hs0 (div_pos hp hb.1)]
      field_simp [hp.ne', hb.1.ne', hden.ne']
    have hx : 1 - escape l T - 2 * resp l T ≤ F T := by
      rw [← hfeq]
      linarith
    have h1s : 0 < 1 + s := by positivity
    by_cases hx0 : 0 ≤ 1 - escape l T - 2 * resp l T
    · calc
        (1 - escape l T - 2 * resp l T) * Gam μ l (escape l T) ≤
            F T * Gam μ l (escape l T) := mul_le_mul_of_nonneg_right hx hGT.1.le
        _ ≤ F T * (1 / (1 + s)) := mul_le_mul_of_nonneg_left hGT.2 hFnp'
        _ = F T / (1 + s) := by ring
    · have hx0' : 1 - escape l T - 2 * resp l T ≤ 0 := le_of_not_ge hx0
      have hleft : (1 - escape l T - 2 * resp l T) * Gam μ l (escape l T) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hx0' hGT.1.le
      exact hleft.trans (div_nonneg hFnp' h1s.le)
  have hcompare := integral_mono_ae hXint hFdivInt hpoint
  rw [integral_div] at hcompare
  have hdiv1 := div_le_div_of_nonneg_right hIntF (by positivity : 0 ≤ 1 + s)
  have hdiv2 := div_le_div_of_nonneg_right hmono (by positivity : 0 ≤ 1 + s)
  change X ≤ L
  calc
    X ≤ (∫ T, F T ∂GW μ) / (1 + s) := hcompare
    _ ≤ FM / (1 + s) := hdiv1
    _ ≤ (s * (1 / A - p) / (3 + s / A)) / (1 + s) := hdiv2
    _ = L := by dsimp [L]; rw [div_div]; ring


/-- **Response loss and the reduced inequality** on the low window (proof of
Theorem 4.3). -/
theorem lowWindow_reduced (h : OffspringHyp μ) {l : ℝ} (hl : 1 < l)
    (hlm : l < mean μ) (hs : sS μ l ≤ 1 / 8) :
    let p := pBr μ
    let q := p1 μ
    let e := eJ μ
    let s := sS μ l
    let A := 1 - e - s * (q + p * e)
    let d := (1 - s * q ^ 2 / 2) / A - q * (1 + p) / 4
    let hh := 2 + s * (p + d)
    let L := s * (1 / A - p) / ((1 + s) * (3 + s / A))
    1 - Vsc μ l * d - hh * L ≤ hh * cost μ l := by
  intro p q e s A d hh L
  let B := p + d
  let X := ∫ T, (1 - escape l T - 2 * resp l T) * Gam μ l (escape l T) ∂GW μ
  let v := speedValue μ l
  let C := l - 1 + (l + 1) * v
  have hp : 0 < p := pBr_pos h
  have hlmem : l ∈ Set.Ioo 0 (mean μ) := ⟨by linarith, hlm⟩
  have hlps : l = 1 + p * s := by
    dsimp only [s, p, sS]
    field_simp [(pBr_pos h).ne']
    ring
  have hloss : X ≤ L := lowWindow_response_loss h hl hlm hs
  have hKdata := lowWindow_K0_le h hl hlm hs
  have hhpos : 0 < hh := hKdata.1
  have hK : K0 μ l ≤ B / (p * hh) := hKdata.2
  have hw : wbar μ l < 1 := by
    have hd := dW_pos h hl hlm
    dsimp only [dW] at hd
    linarith
  have hmu : muY μ l ≤ 1 / (1 + s) := by
    rw [muY_eq h hl hlm]
    have hs0 : 0 < s := by dsimp [s, sS]; positivity
    exact (div_le_div_iff_of_pos_right (by positivity)).2 hw.le
  have hbaseInt : Integrable (fun T => (1 - escape l T) * Gam μ l (escape l T)) (GW μ) := by
    have hm : Measurable (fun T => (1 - escape l T) * Gam μ l (escape l T)) :=
      (measurable_const.sub (measurable_escape l)).mul (measurable_Gam_escape_reduced μ l)
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [ae_regTree h] with T hT
    have hb := escape_mem_Ioc_of_regTree hT hlmem
    have hg := Gam_pos_le μ h hl hlm ⟨hb.1.le, hb.2⟩
    have hnone : 0 ≤ (1 - escape l T) * Gam μ l (escape l T) :=
      mul_nonneg (sub_nonneg.mpr hb.2) hg.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg hnone]
    calc
      (1 - escape l T) * Gam μ l (escape l T) ≤ 1 * Gam μ l (escape l T) :=
        mul_le_mul_of_nonneg_right (by linarith [hb.1]) hg.1.le
      _ ≤ muY μ l := by simpa only [one_mul] using hg.2
      _ ≤ 1 / (1 + s) := hmu
      _ ≤ 1 := by
        have hs0 : 0 < s := by dsimp [s, sS]; positivity
        exact (div_le_one (by positivity)).2 (by linarith)
  have hXi : X = (∫ T, (1 - escape l T) * Gam μ l (escape l T) ∂GW μ) -
      2 * ∫ T, resp l T * Gam μ l (escape l T) ∂GW μ := by
    dsimp only [X]
    rw [show (fun T => (1 - escape l T - 2 * resp l T) * Gam μ l (escape l T)) =
        fun T => (1 - escape l T) * Gam μ l (escape l T) -
          2 * (resp l T * Gam μ l (escape l T)) by funext T; ring]
    rw [integral_sub hbaseInt ((integrable_resp_Gam h hlmem).const_mul 2), integral_const_mul]
  have hbase : 2 * cost μ l = 1 + v - C * K0 μ l - 2 * X := by
    rw [cost_eq h hlmem]
    have hhresp := half_response h hlmem
    have hfar := far_six h hlmem
    rw [hXi]
    dsimp only [C, v]
    linarith
  have hv : 0 < v := speedValue_pos μ h l ⟨by linarith, hlm⟩
  have hC : 0 < C := by dsimp [C]; nlinarith
  have hcost_lower : 1 + v - C * (B / (p * hh)) - 2 * L ≤ 2 * cost μ l := by
    have hk := mul_le_mul_of_nonneg_left hK hC.le
    linarith
  have hvV : v = p * Vsc μ l := by
    dsimp only [v]
    rw [speedValue_eq_speedValueProv]
    dsimp only [Vsc, p]
    field_simp [(pBr_pos h).ne']
  have hAlg : hh * (1 + v - C * (B / (p * hh)) - 2 * L) =
      2 * (1 - Vsc μ l * d - hh * L) := by
    dsimp only [B, C, hh]
    rw [hvV, hlps]
    dsimp only [hh] at hhpos
    field_simp [hp.ne', hhpos.ne']
    ring
  have hm := mul_le_mul_of_nonneg_left hcost_lower hhpos.le
  rw [hAlg] at hm
  linarith

end LPPMonotonicityProof.Analytic
