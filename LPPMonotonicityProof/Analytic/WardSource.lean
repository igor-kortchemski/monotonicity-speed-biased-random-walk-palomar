module

public import LPPMonotonicityProof.Analytic.Ward
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Ward source test

This module proves Corollary 3.6 (`cor:ward-source`).
The algebraic kernels are private. The public test `Qtest` and both
derivative conclusions use the speed of the actual walk.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

local notation "ρ" => Measure.prod (GW μ) (GW μ)

private noncomputable def sourceR (l : ℝ) : ℝ := muY μ l - l * momY μ l 2

private noncomputable def sourceTheta (l : ℝ) : ℝ :=
  1 - (1 + speedValueProv μ l) * sourceR μ l / (2 * muY μ l)

/-- The explicit two-moment sign test in `cor:ward-source`. -/
noncomputable def Qtest (l : ℝ) : ℝ :=
  let μ₁ := muY μ l; let c := momY μ l 2 / μ₁; let r := rr μ l
  2 - c - l*c^2 - r * (2/μ₁ - 2*(1+l) + (1+l)*c + (l-1)*l*c^2)

private noncomputable def sourceG (l r θ y : ℝ) : ℝ :=
  2 * l * (y - r * (1 - l*y)) * (1-y) + (2*θ - 1 + (l-1)*r) * y * (1-l*y)

private noncomputable def centeredG (l r θ c y : ℝ) : ℝ :=
  2*l * fθ l r θ y + l * (1 + (l-1)*r) * y * (c-y)

private noncomputable def wardMain (l θ v b b' : ℝ) : ℝ :=
  b * (1-b) * (2*l * (b' - v*(1-b')) + (2*θ - 1+v) * b' * (1-b')) /
    DfunProv l b b' ^ 2

private noncomputable def wardResidual (l θ v b b' : ℝ) : ℝ :=
  (b-b') * (b*b'*(2*θ+v) - v*(b+b'-1)) / DfunProv l b b' ^ 2

private noncomputable def wardAfter (l θ v b b' : ℝ) : ℝ :=
  ((l-DfunProv l b b') * (b*b'-v*tau b b') + 2*θ*b*b'*(1-b') +
    2*b*(1-b)*(Pol l v b' - θ*b'^2)) / DfunProv l b b' ^ 2

private noncomputable def wardOriginal (l θ v b b' : ℝ) : ℝ :=
  (l * (b*b'-v*tau b b') + 2*θ*b*b'*(1-b') +
    2*b*(1-b)*(Pol l v b' - θ*b'^2)) / DfunProv l b b' ^ 2

private noncomputable def stationaryKernel (l v b b' : ℝ) : ℝ :=
  (b*b'-v*tau b b') / DfunProv l b b'

private lemma Dfun_lower_source {l b b' : ℝ} (hl : 1 < l)
    (hb : b ∈ Set.Icc 0 1) (hb' : b' ∈ Set.Icc 0 1) :
    l-1 ≤ DfunProv l b b' := by
  have h : 0 ≤ b*(1-b')+b' :=
    add_nonneg (mul_nonneg hb.1 (sub_nonneg.mpr hb'.2)) hb'.1
  unfold DfunProv
  linarith

private lemma Dfun_pos_source {l b b' : ℝ} (hl : 1 < l)
    (hb : b ∈ Set.Icc 0 1) (hb' : b' ∈ Set.Icc 0 1) :
    0 < DfunProv l b b' :=
  lt_of_lt_of_le (by linarith) (Dfun_lower_source hl hb hb')

private lemma ae_pair_source (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    ∀ᵐ p : Tree × Tree ∂ρ,
      escape l p.1 ∈ Set.Ioo 0 1 ∧ escape l p.2 ∈ Set.Ioo 0 1 := by
  have hmem := ae_escape_mem_Ioo h (by linarith) hlm
  exact ((Measure.quasiMeasurePreserving_fst (μ := GW μ) (ν := GW μ)).ae hmem).and
    ((Measure.quasiMeasurePreserving_snd (μ := GW μ) (ν := GW μ)).ae hmem)

private lemma ae_Yt_source (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    ∀ᵐ T ∂GW μ, Yt l T ∈ Set.Ioo 0 (1/l) := by
  filter_upwards [ae_escape_pos h (by linarith) hlm] with T hT
  exact Yt_mem hl hT

private lemma integrable_Yt_source (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : Integrable (Yt l) (GW μ) := by
  apply Integrable.of_bound (measurable_Yt l).aestronglyMeasurable (1/l)
  filter_upwards [ae_Yt_source μ h hl hlm] with T hT
  rw [Real.norm_eq_abs, abs_of_pos hT.1]
  exact hT.2.le

private lemma integrable_Yt_sq_source (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : Integrable (fun T => Yt l T ^ 2) (GW μ) := by
  apply Integrable.of_bound ((measurable_Yt l).pow_const 2).aestronglyMeasurable 1
  filter_upwards [ae_Yt_source μ h hl hlm] with T hT
  have hu : 1/l ≤ 1 := (div_le_one (by linarith : 0 < l)).2 (by linarith)
  rw [Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos hT.1)]
  nlinarith [mul_pos hT.1 (sub_pos.mpr (hT.2.trans_le hu))]

private lemma integrable_quadratic_source {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : AEMeasurable Z P)
    (hZb : ∀ᵐ ω ∂P, |Z ω| ≤ 1) (A B C : ℝ) :
    Integrable (fun ω => -A * Z ω ^ 2 + B * Z ω + C) P := by
  have hZi : Integrable Z P := Integrable.of_bound hZ.aestronglyMeasurable 1 hZb
  have hZ2i : Integrable (fun ω => Z ω ^ 2) P := by
    apply Integrable.of_bound (hZ.pow_const 2).aestronglyMeasurable 1
    filter_upwards [hZb] with ω hω
    rw [Real.norm_eq_abs, abs_pow]
    nlinarith [abs_nonneg (Z ω)]
  exact ((hZ2i.const_mul (-A)).add (hZi.const_mul B)).add (integrable_const C)

private lemma integrable_div_sq_source {q : Tree × Tree → ℝ} {l K : ℝ}
    (hl : 1 < l) (hq : Measurable q) (hK : ∀ p, ‖q p‖ ≤ K) :
    Integrable (fun p => q p / DfunProv l (escape l p.1) (escape l p.2) ^ 2) ρ := by
  have hm : Measurable (fun p : Tree × Tree =>
      DfunProv l (escape l p.1) (escape l p.2)) := by
    unfold DfunProv
    exact (((measurable_const.add ((measurable_escape l).comp measurable_fst)).add
      ((measurable_escape l).comp measurable_snd)).sub
      (((measurable_escape l).comp measurable_fst).mul ((measurable_escape l).comp measurable_snd)))
  apply Integrable.of_bound (hq.div (hm.pow_const 2)).aestronglyMeasurable (K/(l-1)^2)
  filter_upwards with p
  have hb := escape_mem_Icc (by linarith : 0 < l) p.1
  have hb' := escape_mem_Icc (by linarith : 0 < l) p.2
  have hD := Dfun_pos_source hl hb hb'
  have hDs : (l-1)^2 ≤ DfunProv l (escape l p.1) (escape l p.2)^2 :=
    (sq_le_sq₀ (by linarith) hD.le).2 (Dfun_lower_source hl hb hb')
  change ‖q p / DfunProv l (escape l p.1) (escape l p.2)^2‖ ≤ _
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hD]
  exact (div_le_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos (by linarith : 0 < l-1))).2
    (mul_le_mul (hK p) hDs (sq_nonneg _) ((norm_nonneg (q p)).trans (hK p)))

private lemma integrable_div_source {q : Tree × Tree → ℝ} {l K : ℝ}
    (hl : 1 < l) (hq : Measurable q) (hK : ∀ p, ‖q p‖ ≤ K) :
    Integrable (fun p => q p / DfunProv l (escape l p.1) (escape l p.2)) ρ := by
  have hm : Measurable (fun p : Tree × Tree =>
      DfunProv l (escape l p.1) (escape l p.2)) := by
    unfold DfunProv
    exact (((measurable_const.add ((measurable_escape l).comp measurable_fst)).add
      ((measurable_escape l).comp measurable_snd)).sub
      (((measurable_escape l).comp measurable_fst).mul ((measurable_escape l).comp measurable_snd)))
  apply Integrable.of_bound (hq.div hm).aestronglyMeasurable (K/(l-1))
  filter_upwards with p
  have hb := escape_mem_Icc (by linarith : 0 < l) p.1
  have hb' := escape_mem_Icc (by linarith : 0 < l) p.2
  have hD := Dfun_pos_source hl hb hb'
  change ‖q p / DfunProv l (escape l p.1) (escape l p.2)‖ ≤ _
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hD]
  exact (div_le_div_iff₀ hD (by linarith : 0 < l-1)).2
    (mul_le_mul (hK p) (Dfun_lower_source hl hb hb') (by linarith) ((norm_nonneg (q p)).trans (hK p)))

private lemma ward_after_eq_main_add_residual (l θ v b b' : ℝ) :
    wardAfter l θ v b b' = wardMain l θ v b b' + wardResidual l θ v b b' := by
  unfold wardAfter wardMain wardResidual Pol tau DfunProv
  ring

private lemma ward_original_eq_after_add_stationary (l θ v b b' : ℝ)
    (hD : DfunProv l b b' ≠ 0) :
    wardOriginal l θ v b b' = wardAfter l θ v b b' + stationaryKernel l v b b' := by
  unfold wardOriginal wardAfter stationaryKernel
  field_simp [hD]
  ring

private lemma wardResidual_swap (l θ v b b' : ℝ) :
    wardResidual l θ v b' b = -wardResidual l θ v b b' := by
  unfold wardResidual DfunProv
  ring

private lemma wardMain_transform {l θ v b b' : ℝ} (hl : 1 < l)
    (hb : b ∈ Set.Ioo 0 1) (hb' : b' ∈ Set.Ioo 0 1) :
    wardMain l θ v b b' =
      let y := b/(l-1+b); let y' := b'/(l-1+b')
      y * (1-l*y) * sourceG l (v/(l-1)) θ y' / (1-l*y*y')^2 := by
  have ha : 0 < l-1 := by linarith
  have hden : 0 < l-1+b := by linarith [hb.1]
  have hden' : 0 < l-1+b' := by linarith [hb'.1]
  have hD := Dfun_pos_source hl ⟨hb.1.le,hb.2.le⟩ ⟨hb'.1.le,hb'.2.le⟩
  have hid := (collapse_identities hl hb hb').1
  have hD0 : Dfun l b b' ≠ 0 := hD.ne'
  have hq : 0 < 1-l*(b/(l-1+b))*(b'/(l-1+b')) := by
    rw [hid]
    exact div_pos (mul_pos ha hD) (mul_pos hden hden')
  have hDform : DfunProv l b b' =
      (1-l*(b/(l-1+b))*(b'/(l-1+b')))*(l-1+b)*(l-1+b')/(l-1) := by
    rw [hid]
    field_simp [ha.ne', hden.ne', hden'.ne', hD0]
    rfl
  dsimp only
  unfold wardMain sourceG
  rw [hDform]
  field_simp [ha.ne', hden.ne', hden'.ne', hq.ne']
  ring

private lemma sourceG_eq_centered {l r θ c : ℝ}
    (hθ : 2*θ - 1 + (l-1)*r = l*(1+(l-1)*r)*c) (y : ℝ) :
    sourceG l r θ y = centeredG l r θ c y := by
  calc
    sourceG l r θ y = centeredG l r θ c y +
        (2*θ - 1 + (l-1)*r - l*(1+(l-1)*r)*c) * y := by
      unfold sourceG centeredG fθ
      ring
    _ = centeredG l r θ c y := by rw [hθ]; ring

private lemma sourceTheta_relation {l m₂ μ₁ v : ℝ} (hμ : μ₁ ≠ 0) :
    let R := μ₁-l*m₂
    let θ := 1-(1+v)*R/(2*μ₁)
    2*θ - 1+v = l*(1+v)*(m₂/μ₁) := by
  dsimp only
  field_simp [hμ]
  ring

/-- A concave quadratic with opposite endpoint signs has one sign crossing. -/
private lemma concave_single_crossing {A B C u : ℝ} (hA : 0 < A) (hu : 0 < u)
    (hC : C < 0) (hqu : 0 < -A*u^2+B*u+C) :
    ∃ c ∈ Set.Ioo 0 u,
      (∀ y ∈ Set.Icc 0 u, y < c → -A*y^2+B*y+C ≤ 0) ∧
      (∀ y ∈ Set.Icc 0 u, c < y → 0 ≤ -A*y^2+B*y+C) := by
  let q : ℝ → ℝ := fun y => -A*y^2+B*y+C
  have hcont : Continuous q := by dsimp [q]; fun_prop
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hu.le hcont.continuousOn
    (show 0 ∈ Set.Icc (q 0) (q u) by
      constructor
      · simpa [q] using hC.le
      · simpa [q] using hqu.le)
  change q c = 0 at hfc
  have hc0 : 0 < c := by
    rcases hc.1.eq_or_lt with heq | hlt
    · subst c; simp [q] at hfc; linarith
    · exact hlt
  have hcu : c < u := by
    rcases hc.2.eq_or_lt with heq | hlt
    · rw [heq] at hfc
      change -A*u^2+B*u+C = 0 at hfc
      linarith
    · exact hlt
  let d := -C/(A*c)
  have hAc : 0 < A*c := mul_pos hA hc0
  have hd : B = A*(c+d) := by
    have hcne : c ≠ 0 := hc0.ne'
    dsimp [d]
    change -A*c^2+B*c+C = 0 at hfc
    field_simp [hAc.ne', hcne]
    nlinarith
  have hfac (y : ℝ) : q y = -A*(y-c)*(y-d) := by
    dsimp [q]
    rw [hd]
    have hdC : A*c*d = -C := by dsimp [d]; field_simp [hAc.ne']
    nlinarith
  have hdu : u < d := by
    have hupos : 0 < A*(u-c) := mul_pos hA (sub_pos.mpr hcu)
    have hqu' : 0 < q u := hqu
    rw [hfac u] at hqu'
    nlinarith
  refine ⟨c, ⟨hc0,hcu⟩, ?_, ?_⟩
  · intro y hy hyc
    have hyd : y < d := lt_of_le_of_lt hy.2 hdu
    change q y ≤ 0
    rw [hfac]
    have hp : 0 ≤ (y-c)*(y-d) := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    nlinarith [mul_nonneg hA.le hp]
  · intro y hy hcy
    have hyd : y < d := lt_of_le_of_lt hy.2 hdu
    change 0 ≤ q y
    rw [hfac]
    have hp : (y-c)*(y-d) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith [mul_nonneg hA.le (neg_nonneg.mpr hp)]

private lemma momY_sq_pos (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : 0 < momY μ l 2 := by
  apply integral_pos_of_ae_pos (integrable_Yt_sq_source μ h hl hlm)
  filter_upwards [ae_Yt_source μ h hl hlm] with T hT
  exact sq_pos_of_pos hT.1

private lemma sourceR_pos (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : 0 < sourceR μ l := by
  exact sub_pos.mpr (R0_pos μ h hl hlm)

private lemma sourceR_lt (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : sourceR μ l < muY μ l := by
  have hm₂ := momY_sq_pos μ h hl hlm
  unfold sourceR
  nlinarith

private lemma sourceTheta_lt_one (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : sourceTheta μ l < 1 := by
  have hμ := (muY_mem μ h hl hlm).1
  have hv := speedValue_pos μ h l ⟨(by linarith),hlm⟩
  have hR := sourceR_pos μ h hl hlm
  have hp : 0 < (1+speedValueProv μ l)*sourceR μ l/(2*muY μ l) :=
    div_pos (mul_pos (by linarith) hR) (by positivity)
  unfold sourceTheta
  linarith

private lemma sourceTheta_pos (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) : 0 < sourceTheta μ l := by
  have hμ := (muY_mem μ h hl hlm).1
  have hv0 := speedValue_pos μ h l ⟨(by linarith),hlm⟩
  have hv1 := speedValue_lt_one μ h (by linarith) hlm
  have hR0 := sourceR_pos μ h hl hlm
  have hR1 := sourceR_lt μ h hl hlm
  have hnum : (1+speedValueProv μ l)*sourceR μ l < 2*muY μ l := by
    calc
      _ ≤ (1+speedValueProv μ l)*muY μ l :=
        mul_le_mul_of_nonneg_left hR1.le (by linarith)
      _ < 2*muY μ l := mul_lt_mul_of_pos_right (by linarith) hμ
  have hquot : (1+speedValueProv μ l)*sourceR μ l/(2*muY μ l) < 1 := by
    rw [div_lt_one (by positivity)]
    exact hnum
  unfold sourceTheta
  linarith

private lemma integral_fθ_source (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (θ : ℝ) :
    ∫ T, fθ l (rr μ l) θ (Yt l T) ∂GW μ =
      -(rr μ l) + (1+(rr μ l)*(1+l))*muY μ l - (θ+(rr μ l)*l)*momY μ l 2 := by
  have hY := integrable_Yt_source μ h hl hlm
  have hY₂ := integrable_Yt_sq_source μ h hl hlm
  let r := rr μ l
  let A := θ+r*l
  let B := 1+r*(1+l)
  have hfun : (fun T => fθ l r θ (Yt l T)) =
      (fun T => -r+B*Yt l T-A*Yt l T^2) := by
    funext T
    unfold fθ
    dsimp [A,B]
    ring
  change (∫ T, fθ l r θ (Yt l T) ∂GW μ) = -r+B*muY μ l-A*momY μ l 2
  rw [hfun, integral_sub (f := fun T => -r+B*Yt l T) (g := fun T => A*Yt l T^2)
    ((integrable_const (-r)).add (hY.const_mul B)) (hY₂.const_mul A),
    integral_add (f := fun _ : Tree => (-r : ℝ)) (g := fun T => B*Yt l T)
      (integrable_const (-r)) (hY.const_mul B), integral_const_mul,
    integral_const_mul, integral_const]
  simp [Measure.real, muY, momY]

private lemma two_integral_fθ_eq_Q (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    2 * (∫ T, fθ l (rr μ l) (sourceTheta μ l) (Yt l T) ∂GW μ) =
      muY μ l * Qtest μ l := by
  rw [integral_fθ_source μ h hl hlm]
  have hμ := (muY_mem μ h hl hlm).1
  have ha : 0 < l-1 := by linarith
  unfold Qtest sourceTheta sourceR rr speedValueProv
  dsimp only
  field_simp [hμ.ne', ha.ne']
  ring

private lemma integral_centered_source (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (θ c : ℝ) (hc : c * muY μ l = momY μ l 2) :
    (∫ T, centeredG l (rr μ l) θ c (Yt l T) ∂GW μ) =
      2*l * (∫ T, fθ l (rr μ l) θ (Yt l T) ∂GW μ) := by
  have hY := integrable_Yt_source μ h hl hlm
  have hY₂ := integrable_Yt_sq_source μ h hl hlm
  have hf : Integrable (fun T => fθ l (rr μ l) θ (Yt l T)) (GW μ) := by
    have hQ := integrable_quadratic_source (measurable_Yt l).aemeasurable
      (P := GW μ) (Z := Yt l) (A := θ+(rr μ l)*l)
      (B := 1+(rr μ l)*(1+l)) (C := -(rr μ l)) ?_ 
    · apply hQ.congr
      filter_upwards with T
      unfold fθ
      ring
    · filter_upwards [ae_Yt_source μ h hl hlm] with T hT
      rw [abs_of_pos hT.1]
      exact hT.2.le.trans ((div_le_one (by linarith : 0 < l)).2 (by linarith))
  have hw : (∫ T, (c*Yt l T-Yt l T^2) ∂GW μ) = 0 := by
    rw [integral_sub (hY.const_mul c) hY₂, integral_const_mul]
    change c*muY μ l-momY μ l 2 = 0
    rw [hc, sub_self]
  have hfun : (fun T => centeredG l (rr μ l) θ c (Yt l T)) =
      (fun T => 2*l*fθ l (rr μ l) θ (Yt l T) +
        l*(1+(l-1)*(rr μ l))*(c*Yt l T-Yt l T^2)) := by
    funext T
    unfold centeredG
    ring
  rw [hfun, integral_add (f := fun T => 2*l*fθ l (rr μ l) θ (Yt l T))
    (g := fun T => l*(1+(l-1)*(rr μ l))*(c*Yt l T-Yt l T^2))
    (hf.const_mul (2*l))
    ((hY.const_mul c).sub hY₂ |>.const_mul (l*(1+(l-1)*(rr μ l)))),
    integral_const_mul, integral_const_mul, hw]
  ring

private lemma centered_endpoint {l r θ c : ℝ} (hl : 1 < l)
    (hθ : 2*θ-1+(l-1)*r = l*(1+(l-1)*r)*c) :
    centeredG l r θ c (1/l) = 2*(l-1)/l := by
  have hid : centeredG l r θ c (1/l) =
      (2*(l-1) - (2*θ-1+(l-1)*r-l*(1+(l-1)*r)*c))/l := by
    unfold centeredG fθ
    field_simp [(by linarith : l ≠ 0)]
    ring
  rw [hid, hθ]
  ring

private lemma tau_mem_source {b b' : ℝ} (hb : b ∈ Set.Icc 0 1)
    (hb' : b' ∈ Set.Icc 0 1) : tau b b' ∈ Set.Icc 0 1 := by
  constructor
  · unfold tau
    rw [show b+b'-b*b' = b*(1-b')+b' by ring]
    exact add_nonneg (mul_nonneg hb.1 (sub_nonneg.mpr hb'.2)) hb'.1
  · have hp := mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr hb'.2)
    unfold tau
    nlinarith

private lemma norm_Pol_source {l v b : ℝ} (hl : 1 < l) (hb : b ∈ Set.Icc 0 1) :
    ‖Pol l v b‖ ≤ 1+(l-1)+2*(l-1)*|v| := by
  have ha : 0 ≤ l-1 := by linarith
  have hb0 := hb.1
  have hb1 := hb.2
  have hab : |b| ≤ 1 := by rw [abs_of_nonneg hb0]; exact hb1
  have habs : |Pol l v b| ≤ |b^2|+|(l-1)*b|+|(l-1)*(v*b)|+|(l-1)*v| := by
    unfold Pol
    calc
      _ = |b^2+(l-1)*b+(l-1)*(v*b)-(l-1)*v| := by congr 1; ring
      _ ≤ |b^2+(l-1)*b+(l-1)*(v*b)|+|(l-1)*v| := abs_sub _ _
      _ ≤ |b^2+(l-1)*b|+|(l-1)*(v*b)|+|(l-1)*v| := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by gcongr; exact abs_add_le _ _
  rw [Real.norm_eq_abs]
  refine habs.trans ?_
  have hb2 : |b^2| ≤ 1 := by rw [abs_pow]; nlinarith [abs_nonneg b]
  have hvprod : |v*b| ≤ |v| := by
    rw [abs_mul]
    calc
      |v| * |b| ≤ |v| *1 := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
      _ = |v| := mul_one _
  simp only [abs_mul, abs_of_nonneg ha]
  have hvprod' : |v| * |b| ≤ |v| := by simpa [abs_mul] using hvprod
  nlinarith [mul_le_mul_of_nonneg_left hab ha,
    mul_le_mul_of_nonneg_left hvprod' ha]

private lemma norm_stationary_numerator {l v b b' : ℝ}
    (hb : b ∈ Set.Icc 0 1) (hb' : b' ∈ Set.Icc 0 1) :
    ‖b*b'-v*tau b b'‖ ≤ 1+|v| := by
  have hbb : |b*b'| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hb.1, abs_of_nonneg hb'.1]
    exact mul_le_one₀ hb.2 hb'.1 hb'.2
  have ht : |tau b b'| ≤ 1 := by
    have h := tau_mem_source hb hb'
    rw [abs_of_nonneg h.1]
    exact h.2
  rw [Real.norm_eq_abs]
  calc
    |b*b'-v*tau b b'| ≤ |b*b'|+|v*tau b b'| := abs_sub _ _
    _ = |b*b'|+|v| * |tau b b'| := by simp only [abs_mul]
    _ ≤ _ := by nlinarith [abs_nonneg v]

private lemma integrable_RW_source {l : ℝ} (hl : 1 < l) :
    Integrable (fun p : Tree × Tree =>
      escape l p.1 * escape l p.2 * (1-escape l p.2) /
        DfunProv l (escape l p.1) (escape l p.2)^2) ρ := by
  apply integrable_div_sq_source (μ := μ) hl (K := 1)
  · have he₁ : Measurable (fun p : Tree × Tree => escape l p.1) :=
      (measurable_escape l).comp measurable_fst
    have he₂ : Measurable (fun p : Tree × Tree => escape l p.2) :=
      (measurable_escape l).comp measurable_snd
    fun_prop
  · intro p
    have hb := escape_mem_Icc (by linarith : 0 < l) p.1
    have hb' := escape_mem_Icc (by linarith : 0 < l) p.2
    have hq : 0 ≤ escape l p.1 * escape l p.2 * (1-escape l p.2) :=
      mul_nonneg (mul_nonneg hb.1 hb'.1) (sub_nonneg.mpr hb'.2)
    rw [Real.norm_eq_abs, abs_of_nonneg hq]
    have hbb : escape l p.1 * escape l p.2 ≤ 1 := mul_le_one₀ hb.2 hb'.1 hb'.2
    exact mul_le_one₀ hbb (sub_nonneg.mpr hb'.2) (sub_le_self 1 hb'.1)

private lemma integrable_weighted_sq_source {l : ℝ} (hl : 1 < l) :
    Integrable (fun p : Tree × Tree =>
      escape l p.1 * (1-escape l p.1) * escape l p.2^2 /
        DfunProv l (escape l p.1) (escape l p.2)^2) ρ := by
  apply integrable_div_sq_source (μ := μ) hl (K := 1)
  · have he₁ : Measurable (fun p : Tree × Tree => escape l p.1) :=
      (measurable_escape l).comp measurable_fst
    have he₂ : Measurable (fun p : Tree × Tree => escape l p.2) :=
      (measurable_escape l).comp measurable_snd
    fun_prop
  · intro p
    have hb := escape_mem_Icc (by linarith : 0 < l) p.1
    have hb' := escape_mem_Icc (by linarith : 0 < l) p.2
    have hq : 0 ≤ escape l p.1 * (1-escape l p.1) * escape l p.2^2 :=
      mul_nonneg (mul_nonneg hb.1 (sub_nonneg.mpr hb.2)) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hq]
    have hs : escape l p.1 * (1-escape l p.1) ≤ 1 :=
      mul_le_one₀ hb.2 (sub_nonneg.mpr hb.2) (sub_le_self 1 hb.1)
    have hsq : escape l p.2^2 ≤ 1 := by
      rw [pow_two]
      exact mul_le_one₀ hb'.2 hb'.1 hb'.2
    exact mul_le_one₀ hs (sq_nonneg _) hsq

private lemma integrable_weighted_Pol_source {l v : ℝ} (hl : 1 < l) :
    Integrable (fun p : Tree × Tree =>
      escape l p.1 * (1-escape l p.1) * Pol l v (escape l p.2) /
        DfunProv l (escape l p.1) (escape l p.2)^2) ρ := by
  apply integrable_div_sq_source (μ := μ) hl (K := 1+(l-1)+2*(l-1)*|v|)
  · have he₁ : Measurable (fun p : Tree × Tree => escape l p.1) :=
      (measurable_escape l).comp measurable_fst
    have he₂ : Measurable (fun p : Tree × Tree => escape l p.2) :=
      (measurable_escape l).comp measurable_snd
    unfold Pol
    fun_prop
  · intro p
    have hb := escape_mem_Icc (by linarith : 0 < l) p.1
    have hb' := escape_mem_Icc (by linarith : 0 < l) p.2
    have hs : |escape l p.1 * (1-escape l p.1)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hb.1, abs_of_nonneg (sub_nonneg.mpr hb.2)]
      exact mul_le_one₀ hb.2 (sub_nonneg.mpr hb.2) (sub_le_self 1 hb.1)
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ 1 * ‖Pol l v (escape l p.2)‖ := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      _ ≤ _ := by simpa using norm_Pol_source (v := v) hl hb'

private lemma integrable_stationary_source {l v : ℝ} (hl : 1 < l) :
    Integrable (fun p : Tree × Tree => stationaryKernel l v (escape l p.1) (escape l p.2)) ρ := by
  unfold stationaryKernel
  apply integrable_div_source (μ := μ) hl (K := 1+|v|)
  · have he₁ : Measurable (fun p : Tree × Tree => escape l p.1) :=
      (measurable_escape l).comp measurable_fst
    have he₂ : Measurable (fun p : Tree × Tree => escape l p.2) :=
      (measurable_escape l).comp measurable_snd
    unfold tau
    fun_prop
  · intro p
    exact norm_stationary_numerator (l := l) (v := v)
      (escape_mem_Icc (by linarith : 0 < l) p.1) (escape_mem_Icc (by linarith : 0 < l) p.2)

private lemma integrable_main_source {l θ v : ℝ} (hl : 1 < l) :
    Integrable (fun p : Tree × Tree => wardMain l θ v (escape l p.1) (escape l p.2)) ρ := by
  unfold wardMain
  apply integrable_div_sq_source (μ := μ) hl
    (K := 2*l*(1+|v|) + (2*|θ|+1+|v|))
  · have he₁ : Measurable (fun p : Tree × Tree => escape l p.1) :=
      (measurable_escape l).comp measurable_fst
    have he₂ : Measurable (fun p : Tree × Tree => escape l p.2) :=
      (measurable_escape l).comp measurable_snd
    fun_prop
  · intro p
    have hb := escape_mem_Icc (by linarith : 0 < l) p.1
    have hb' := escape_mem_Icc (by linarith : 0 < l) p.2
    have hs : |escape l p.1 * (1-escape l p.1)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hb.1, abs_of_nonneg (sub_nonneg.mpr hb.2)]
      exact mul_le_one₀ hb.2 (sub_nonneg.mpr hb.2) (sub_le_self 1 hb.1)
    have hfirst : ‖escape l p.2-v*(1-escape l p.2)‖ ≤ 1+|v| := by
      rw [Real.norm_eq_abs]
      calc
        _ ≤ |escape l p.2|+|v*(1-escape l p.2)| := abs_sub _ _
        _ = |escape l p.2|+|v| * |1-escape l p.2| := by simp only [abs_mul]
        _ ≤ 1+|v| := by
          have hone : |1-escape l p.2| ≤ 1 := by
            rw [abs_of_nonneg (sub_nonneg.mpr hb'.2)]
            exact sub_le_self 1 hb'.1
          exact add_le_add (show |escape l p.2| ≤ 1 by rw [abs_of_nonneg hb'.1]; exact hb'.2)
            (by simpa using mul_le_mul_of_nonneg_left hone (abs_nonneg v))
    have hB : ‖2*l*(escape l p.2-v*(1-escape l p.2)) +
        (2*θ-1+v)*escape l p.2*(1-escape l p.2)‖ ≤
        2*l*(1+|v|)+(2*|θ|+1+|v|) := by
      rw [Real.norm_eq_abs]
      have hprod : |escape l p.2 * (1-escape l p.2)| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hb'.1, abs_of_nonneg (sub_nonneg.mpr hb'.2)]
        exact mul_le_one₀ hb'.2 (sub_nonneg.mpr hb'.2) (sub_le_self 1 hb'.1)
      calc
        _ ≤ |2*l*(escape l p.2-v*(1-escape l p.2))| +
            |(2*θ-1+v)*escape l p.2*(1-escape l p.2)| := abs_add_le _ _
        _ = 2*l*‖escape l p.2-v*(1-escape l p.2)‖ +
            |2*θ-1+v| * |escape l p.2*(1-escape l p.2)| := by
          simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith : 0 < l)]
          norm_num
          ring
        _ ≤ _ := by
          have hc : |2*θ-1+v| ≤ 2*|θ|+1+|v| := by
            calc
              |2*θ-1+v| = |2*θ+(-1+v)| := by congr 1; ring
              _ ≤ |2*θ|+|-1+v| := abs_add_le _ _
              _ ≤ 2*|θ|+(1+|v|) := by
                have hθabs : |2*θ| = 2*|θ| := by rw [abs_mul]; norm_num
                have hvabs : |-1+v| ≤ 1+|v| := by
                  calc
                    |-1+v| ≤ |-1|+|v| := abs_add_le _ _
                    _ = 1+|v| := by norm_num
                rw [hθabs]
                exact add_le_add le_rfl hvabs
              _ = 2*|θ|+1+|v| := by ring
          have hv := abs_nonneg v
          have hθ := abs_nonneg θ
          have hfirst' : |escape l p.2-v*(1-escape l p.2)| ≤ 1+|v| := by
            simpa [Real.norm_eq_abs] using hfirst
          nlinarith [mul_le_mul_of_nonneg_left hfirst' (show 0 ≤ 2*l by linarith),
            mul_le_mul_of_nonneg_right hprod (abs_nonneg (2*θ-1+v))]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ 1 * ‖2*l*(escape l p.2-v*(1-escape l p.2)) +
          (2*θ-1+v)*escape l p.2*(1-escape l p.2)‖ := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      _ ≤ _ := by simpa [Real.norm_eq_abs] using hB

private lemma integrable_residual_source {l θ v : ℝ} (hl : 1 < l) :
    Integrable (fun p : Tree × Tree => wardResidual l θ v (escape l p.1) (escape l p.2)) ρ := by
  unfold wardResidual
  apply integrable_div_sq_source (μ := μ) hl (K := 8*|θ|+16*|v|)
  · have he₁ : Measurable (fun p : Tree × Tree => escape l p.1) :=
      (measurable_escape l).comp measurable_fst
    have he₂ : Measurable (fun p : Tree × Tree => escape l p.2) :=
      (measurable_escape l).comp measurable_snd
    fun_prop
  · intro p
    have hb := escape_mem_Icc (by linarith : 0 < l) p.1
    have hb' := escape_mem_Icc (by linarith : 0 < l) p.2
    have hab : |escape l p.1| ≤ 1 := by rw [abs_of_nonneg hb.1]; exact hb.2
    have hab' : |escape l p.2| ≤ 1 := by rw [abs_of_nonneg hb'.1]; exact hb'.2
    have hprod : |escape l p.1 * escape l p.2| ≤ 1 := by
      rw [abs_mul]
      exact mul_le_one₀ hab (abs_nonneg _) hab'
    have hsum : |escape l p.1+escape l p.2-1| ≤ 3 := by
      calc
        _ ≤ |escape l p.1+escape l p.2|+|1| := abs_sub _ _
        _ ≤ (|escape l p.1|+|escape l p.2|)+1 :=
          add_le_add (abs_add_le _ _) (by norm_num)
        _ ≤ 3 := by linarith
    have hbracket : |escape l p.1 * escape l p.2 * (2*θ+v) -
        v*(escape l p.1+escape l p.2-1)| ≤ 4*|θ|+8*|v| := by
      calc
        _ ≤ |escape l p.1 * escape l p.2 * (2*θ+v)| +
            |v*(escape l p.1+escape l p.2-1)| := abs_sub _ _
        _ = |escape l p.1 * escape l p.2| * |2*θ+v| + |v| *
            |escape l p.1+escape l p.2-1| := by simp only [abs_mul]
        _ ≤ 1*(2*|θ|+|v|)+|v| *3 := by
          gcongr
          calc |2*θ+v| ≤ |2*θ|+|v| := abs_add_le _ _
               _ = 2*|θ|+|v| := by rw [abs_mul]; norm_num
        _ ≤ _ := by nlinarith [abs_nonneg v, abs_nonneg θ]
    have hdiff : |escape l p.1-escape l p.2| ≤ 2 := by
      calc
        _ ≤ |escape l p.1|+|escape l p.2| := abs_sub _ _
        _ ≤ 2 := by linarith
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [mul_le_mul hdiff hbracket (by positivity) (by positivity)]

private lemma integrable_after_source {l θ v : ℝ} (hl : 1 < l) :
    Integrable (fun p : Tree × Tree => wardAfter l θ v (escape l p.1) (escape l p.2)) ρ := by
  apply ((integrable_main_source (μ := μ) (θ := θ) (v := v) hl).add
    (integrable_residual_source (μ := μ) (θ := θ) (v := v) hl)).congr
  filter_upwards with p
  exact (ward_after_eq_main_add_residual l θ v (escape l p.1) (escape l p.2)).symm

private lemma stationary_integral_zero (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    (∫ p : Tree × Tree, stationaryKernel l (speedValueProv μ l)
      (escape l p.1) (escape l p.2) ∂ρ) = 0 := by
  let v := speedValueProv μ l
  have hZ := (Speed.Zval_pos μ (by linarith) h hlm).ne'
  have hv : NvalProv μ l = v * ZvalProv μ l := by
    change Nval μ l = v * Zval μ l
    dsimp [v]
    rw [speedValueProv_eq, ite_eq_right (by linarith : l ≠ 0), div_mul_cancel₀ _ hZ]
  rw [Nval_eq_pairE, Zval_eq_pairE] at hv
  have hN : Integrable (fun p : Tree × Tree =>
      escape l p.1 * escape l p.2 / DfunProv l (escape l p.1) (escape l p.2)) ρ := by
    apply integrable_div_source (μ := μ) hl (K := 1)
    · have he₁ : Measurable (fun p : Tree × Tree => escape l p.1) :=
        (measurable_escape l).comp measurable_fst
      have he₂ : Measurable (fun p : Tree × Tree => escape l p.2) :=
        (measurable_escape l).comp measurable_snd
      fun_prop
    · intro p
      have hb := escape_mem_Icc (by linarith : 0 < l) p.1
      have hb' := escape_mem_Icc (by linarith : 0 < l) p.2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 hb'.1)]
      exact mul_le_one₀ hb.2 hb'.1 hb'.2
  have hτ : Integrable (fun p : Tree × Tree =>
      tau (escape l p.1) (escape l p.2) / DfunProv l (escape l p.1) (escape l p.2)) ρ := by
    apply integrable_div_source (μ := μ) hl (K := 1)
    · have he₁ : Measurable (fun p : Tree × Tree => escape l p.1) :=
        (measurable_escape l).comp measurable_fst
      have he₂ : Measurable (fun p : Tree × Tree => escape l p.2) :=
        (measurable_escape l).comp measurable_snd
      unfold tau
      fun_prop
    · intro p
      have ht := tau_mem_source (escape_mem_Icc (by linarith : 0 < l) p.1)
        (escape_mem_Icc (by linarith : 0 < l) p.2)
      rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact ht.2
  change (∫ p : Tree × Tree,
    (escape l p.1 * escape l p.2-v*tau (escape l p.1) (escape l p.2)) /
      DfunProv l (escape l p.1) (escape l p.2) ∂ρ) = 0
  have hdecomp : (fun p : Tree × Tree =>
      (escape l p.1 * escape l p.2-v*tau (escape l p.1) (escape l p.2)) /
        DfunProv l (escape l p.1) (escape l p.2)) =
      (fun p => escape l p.1 * escape l p.2 / DfunProv l (escape l p.1) (escape l p.2) -
        v * (tau (escape l p.1) (escape l p.2) / DfunProv l (escape l p.1) (escape l p.2))) := by
    funext p
    ring
  rw [hdecomp, integral_sub hN (hτ.const_mul v), integral_const_mul]
  unfold pairE at hv
  linarith

private noncomputable def wardResponse (l θ v b b' : ℝ) : ℝ :=
  b*(1-b)*(Pol l v b'-θ*b'^2)/DfunProv l b b'^2

private noncomputable def Hkernel (l v b b' : ℝ) : ℝ :=
  (b*b'-v*tau b b')/DfunProv l b b'^2

private noncomputable def RWkernel (l b b' : ℝ) : ℝ :=
  b*b'*(1-b')/DfunProv l b b'^2

private lemma integrable_response_source {l θ v : ℝ} (hl : 1 < l) :
    Integrable (fun p : Tree × Tree => wardResponse l θ v (escape l p.1) (escape l p.2)) ρ := by
  have hP := integrable_weighted_Pol_source (μ := μ) (l := l) (v := v) hl
  have hQ := integrable_weighted_sq_source (μ := μ) (l := l) hl
  apply (hP.sub (hQ.const_mul θ)).congr
  filter_upwards with p
  simp only [Pi.sub_apply]
  unfold wardResponse
  ring

private lemma integrable_original_source {l θ : ℝ} (h : OffspringHyp μ)
    (hl : 1 < l) (hlm : l < mean μ) :
    Integrable (fun p : Tree × Tree =>
      wardOriginal l θ (speedValueProv μ l) (escape l p.1) (escape l p.2)) ρ := by
  have hl0 : l ∈ Set.Ioo 0 (mean μ) := ⟨by linarith,hlm⟩
  have hH := integrable_Hval_kernel h hl0
  have hR := integrable_RW_source (μ := μ) (l := l) hl
  have hD := integrable_response_source (μ := μ) (l := l) (θ := θ)
    (v := speedValueProv μ l) hl
  apply (((hH.const_mul l).add (hR.const_mul (2*θ))).add (hD.const_mul 2)).congr
  filter_upwards with p
  simp only [Pi.add_apply, Pi.mul_apply]
  unfold wardOriginal wardResponse
  ring

private lemma root_response_as_pair (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (θ : ℝ) :
    (∫ T, escape l T*(1-escape l T) *
      (Gam μ l (escape l T)-θ*Gam2 μ l (escape l T)) ∂GW μ) =
      ∫ p : Tree × Tree, wardResponse l θ (speedValueProv μ l)
        (escape l p.1) (escape l p.2) ∂ρ := by
  generalize hv : speedValueProv μ l = v
  have hP₀ := integrable_weighted_Pol_source (μ := μ) (l := l) (v := v) hl
  have hP : Integrable (fun p : Tree × Tree => escape l p.1*(1-escape l p.1) *
      (Pol l v (escape l p.2)/DfunProv l (escape l p.1) (escape l p.2)^2)) ρ := by
    apply hP₀.congr
    filter_upwards with p
    ring
  have hQ₀ := integrable_weighted_sq_source (μ := μ) (l := l) hl
  have hQ : Integrable (fun p : Tree × Tree => escape l p.1*(1-escape l p.1) *
      (escape l p.2^2/DfunProv l (escape l p.1) (escape l p.2)^2)) ρ := by
    apply hQ₀.congr
    filter_upwards with p
    ring
  have hG : (∫ p : Tree × Tree, escape l p.1*(1-escape l p.1) *
      (Pol l v (escape l p.2)/DfunProv l (escape l p.1) (escape l p.2)^2) ∂ρ) =
      ∫ T, escape l T*(1-escape l T)*Gam μ l (escape l T) ∂GW μ := by
    have hP' : Integrable (fun p : Tree × Tree => escape l p.1*(1-escape l p.1) *
        (Pol l (speedValueProv μ l) (escape l p.2) /
          DfunProv l (escape l p.1) (escape l p.2)^2)) ρ := by
      rw [hv]
      exact hP
    have hG0 := integral_Gam_weight (fun T => escape l T*(1-escape l T)) hP'
    rw [hv] at hG0
    exact hG0
  have hG2 : (∫ p : Tree × Tree, escape l p.1*(1-escape l p.1) *
      (escape l p.2^2/DfunProv l (escape l p.1) (escape l p.2)^2) ∂ρ) =
      ∫ T, escape l T*(1-escape l T)*Gam2 μ l (escape l T) ∂GW μ := by
    rw [integral_prod _ hQ]
    simp only [Gam2]
    apply integral_congr_ae
    filter_upwards with T
    rw [← integral_const_mul]
  have hPL := hP.integral_prod_left
  have hQL := hQ.integral_prod_left
  rw [← hv] at hPL
  simp only [integral_const_mul, Gam] at hPL
  simp only [integral_const_mul, Gam2] at hQL
  have hroot : (∫ T, escape l T*(1-escape l T) *
      (Gam μ l (escape l T)-θ*Gam2 μ l (escape l T)) ∂GW μ) =
      ∫ p : Tree × Tree, wardResponse l θ v (escape l p.1) (escape l p.2) ∂ρ := by
    have houter : Integrable (fun T => escape l T*(1-escape l T)*Gam μ l (escape l T)) (GW μ) := hPL
    have houter2 : Integrable (fun T => escape l T*(1-escape l T)*Gam2 μ l (escape l T)) (GW μ) := hQL
    rw [show (fun T => escape l T*(1-escape l T) *
      (Gam μ l (escape l T)-θ*Gam2 μ l (escape l T))) =
      (fun T => escape l T*(1-escape l T)*Gam μ l (escape l T) -
        θ*(escape l T*(1-escape l T)*Gam2 μ l (escape l T))) by funext T; ring]
    rw [integral_sub houter (houter2.const_mul θ), integral_const_mul, ← hG, ← hG2,
      ← integral_const_mul, ← integral_sub hP (hQ.const_mul θ)]
    apply integral_congr_ae
    filter_upwards with p
    unfold wardResponse
    ring
  exact hroot


-- Keep the kernels opaque when applying integral rules. Their definitions are
-- needed only in these conversion lemmas and in pointwise real algebra.
private lemma Hval_as_pair (l : ℝ) :
    Hval μ l = pairE μ l (Hkernel l (speedValueProv μ l)) := rfl

private lemma RW_as_pair (l : ℝ) :
    RW μ l = pairE μ l (RWkernel l) := rfl

private lemma integrable_Hkernel (h : OffspringHyp μ) {l : ℝ}
    (hl : l ∈ Set.Ioo 0 (mean μ)) :
    Integrable (fun p : Tree × Tree =>
      Hkernel l (speedValueProv μ l) (escape l p.1) (escape l p.2)) ρ :=
  integrable_Hval_kernel h hl

private lemma integrable_RWkernel {l : ℝ} (hl : 1 < l) :
    Integrable (fun p : Tree × Tree => RWkernel l (escape l p.1) (escape l p.2)) ρ :=
  integrable_RW_source μ hl

attribute [local irreducible] Hkernel RWkernel wardResponse wardOriginal wardAfter
  wardMain wardResidual stationaryKernel

private lemma ward_original_split (l θ v b b' : ℝ) :
    wardOriginal l θ v b b' =
      l * Hkernel l v b b' + (2*θ) * RWkernel l b b' + 2 * wardResponse l θ v b b' := by
  unfold wardOriginal Hkernel RWkernel wardResponse
  ring

private lemma integral_ward_original (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (θ : ℝ) :
    (∫ p : Tree × Tree, wardOriginal l θ (speedValueProv μ l)
      (escape l p.1) (escape l p.2) ∂ρ) =
      l * Hval μ l + 2 * θ * RW μ l +
      2 * ∫ T, escape l T*(1-escape l T) *
        (Gam μ l (escape l T)-θ*Gam2 μ l (escape l T)) ∂GW μ := by
  let v := speedValueProv μ l
  let H : Tree × Tree → ℝ := fun p => Hkernel l v (escape l p.1) (escape l p.2)
  let W : Tree × Tree → ℝ := fun p => RWkernel l (escape l p.1) (escape l p.2)
  let R : Tree × Tree → ℝ := fun p => wardResponse l θ v (escape l p.1) (escape l p.2)
  have hiH : Integrable H ρ := integrable_Hkernel μ h ⟨by linarith, hlm⟩
  have hiW : Integrable W ρ := integrable_RWkernel μ hl
  have hiR : Integrable R ρ := integrable_response_source μ hl
  rw [Hval_as_pair, RW_as_pair, root_response_as_pair μ h hl hlm]
  change _ = l * (∫ p, H p ∂ρ) + (2*θ) * (∫ p, W p ∂ρ) + 2 * (∫ p, R p ∂ρ)
  calc
    _ = ∫ p, l * H p + (2*θ) * W p + 2 * R p ∂ρ := by
      apply integral_congr_ae
      filter_upwards with p
      exact ward_original_split l θ v (escape l p.1) (escape l p.2)
    _ = _ := by
      have hiHW : Integrable (fun p => l * H p + (2*θ) * W p) ρ :=
        (hiH.const_mul l).add (hiW.const_mul (2*θ))
      rw [integral_add hiHW (hiR.const_mul 2),
        integral_add (hiH.const_mul l) (hiW.const_mul (2*θ)),
        integral_const_mul, integral_const_mul, integral_const_mul]

private lemma integral_ward_residual (l θ v : ℝ) :
    (∫ p : Tree × Tree, wardResidual l θ v (escape l p.1) (escape l p.2) ∂ρ) = 0 := by
  let R : Tree × Tree → ℝ := fun p => wardResidual l θ v (escape l p.1) (escape l p.2)
  have heq : (∫ p, R p ∂ρ) = ∫ p, -R p ∂ρ := by
    rw [← integral_prod_swap R]
    apply integral_congr_ae
    filter_upwards with p
    exact wardResidual_swap l θ v (escape l p.1) (escape l p.2)
  rw [integral_neg] at heq
  change (∫ p, R p ∂ρ) = 0
  linarith

private lemma integral_ward_main (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (θ : ℝ) :
    (∫ p : Tree × Tree, wardOriginal l θ (speedValueProv μ l)
      (escape l p.1) (escape l p.2) ∂ρ) =
    ∫ p : Tree × Tree, wardMain l θ (speedValueProv μ l)
      (escape l p.1) (escape l p.2) ∂ρ := by
  let v := speedValueProv μ l
  let A : Tree × Tree → ℝ := fun p => wardAfter l θ v (escape l p.1) (escape l p.2)
  let S : Tree × Tree → ℝ := fun p => stationaryKernel l v (escape l p.1) (escape l p.2)
  let M : Tree × Tree → ℝ := fun p => wardMain l θ v (escape l p.1) (escape l p.2)
  let R : Tree × Tree → ℝ := fun p => wardResidual l θ v (escape l p.1) (escape l p.2)
  change _ = ∫ p, M p ∂ρ
  calc
    _ = ∫ p, A p + S p ∂ρ := by
      apply integral_congr_ae
      filter_upwards with p
      have hl0 : 0 < l := by linarith
      exact ward_original_eq_after_add_stationary l θ v _ _
        (Dfun_pos_source hl (escape_mem_Icc hl0 p.1) (escape_mem_Icc hl0 p.2)).ne'
    _ = ∫ p, A p ∂ρ := by
      have hiA : Integrable A ρ := integrable_after_source μ hl
      have hiS : Integrable S ρ := integrable_stationary_source μ hl
      have hz : (∫ p, S p ∂ρ) = 0 := stationary_integral_zero μ h hl hlm
      rw [integral_add hiA hiS, hz, add_zero]
    _ = ∫ p, M p + R p ∂ρ := by
      apply integral_congr_ae
      filter_upwards with p
      exact ward_after_eq_main_add_residual l θ v (escape l p.1) (escape l p.2)
    _ = _ := by
      have hiM : Integrable M ρ := integrable_main_source μ hl
      have hiR : Integrable R ρ := integrable_residual_source μ hl
      have hz : (∫ p, R p ∂ρ) = 0 := integral_ward_residual μ l θ v
      rw [integral_add hiM hiR, hz, add_zero]

private lemma ward_main_le_cost (h : OffspringHyp μ) {l θ : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (hθ : Admissible μ l θ) :
    (∫ p : Tree × Tree, wardMain l θ (speedValueProv μ l)
      (escape l p.1) (escape l p.2) ∂ρ) ≤ cost μ l := by
  rw [← integral_ward_main μ h hl hlm θ, integral_ward_original μ h hl hlm θ]
  have hl0 : l ∈ Set.Ioo 0 (mean μ) := ⟨by linarith, hlm⟩
  have hm : Measurable (fun T => escape l T * (1 - escape l T)) :=
    (measurable_escape l).mul (measurable_const.sub (measurable_escape l))
  apply ward_lower h hl hlm hθ hm.aemeasurable
  filter_upwards [ae_regTree h] with T hT
  have hb := escape_mem_Icc hl0.1 T
  exact ⟨mul_nonneg hb.1 (sub_nonneg.mpr hb.2), resp_ge hT hl0⟩


private lemma centered_source_crossing {l r θ c : ℝ} (hl : 1 < l) (hr : 0 < r)
    (hθ0 : 0 < θ) (hθ : 2*θ-1+(l-1)*r = l*(1+(l-1)*r)*c) :
    ∃ x ∈ Set.Ioo 0 (1/l),
      (∀ y ∈ Set.Icc 0 (1/l), y < x → centeredG l r θ c y ≤ 0) ∧
      (∀ y ∈ Set.Icc 0 (1/l), x < y → 0 ≤ centeredG l r θ c y) := by
  let A := 2*l*(θ+r*l) + l*(1+(l-1)*r)
  let B := 2*l*(1+r*(1+l)) + l*(1+(l-1)*r)*c
  let C := -2*l*r
  have heq (y : ℝ) : centeredG l r θ c y = -A*y^2+B*y+C := by
    unfold centeredG fθ
    dsimp [A, B, C]
    ring
  have hl0 : 0 < l := by linarith
  have ha : 0 < l-1 := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : C < 0 := by dsimp [C]; nlinarith [mul_pos hl0 hr]
  have hend : 0 < -A*(1/l)^2+B*(1/l)+C := by
    rw [← heq, centered_endpoint hl hθ]
    positivity
  simpa only [heq] using concave_single_crossing hA (one_div_pos.mpr hl0) hC hend

private noncomputable def sourceWeight (l y t : ℝ) : ℝ := 1 / (1-l*y*t)^2

private lemma source_weight_denom {l y t : ℝ} (hl : 1 < l)
    (hy : y ∈ Set.Icc 0 (1/l)) (ht : t ∈ Set.Icc 0 (1/l)) :
    0 < 1-l*y*t ∧ 1-l*y*t ≤ 1 := by
  have hl0 : 0 < l := by linarith
  have hy' : l*y ≤ 1 := by
    rw [mul_comm]
    exact (le_div_iff₀ hl0).mp hy.2
  have hprod : l*y*t ≤ t := by simpa using mul_le_mul_of_nonneg_right hy' ht.1
  have ht' : t < 1 := ht.2.trans_lt ((div_lt_one hl0).2 hl)
  exact ⟨sub_pos.mpr (hprod.trans_lt ht'), sub_le_self _ (mul_nonneg (mul_nonneg hl0.le hy.1) ht.1)⟩

private lemma weighted_centered_source (h : OffspringHyp μ) {l y θ c x : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (hy : y ∈ Set.Icc 0 (1/l))
    (hx : x ∈ Set.Ioo 0 (1/l))
    (hneg : ∀ t ∈ Set.Icc 0 (1/l), t < x → centeredG l (rr μ l) θ c t ≤ 0)
    (hpos : ∀ t ∈ Set.Icc 0 (1/l), x < t → 0 ≤ centeredG l (rr μ l) θ c t)
    (hmean : 0 ≤ ∫ T, centeredG l (rr μ l) θ c (Yt l T) ∂GW μ) :
    (∫ T, centeredG l (rr μ l) θ c (Yt l T) ∂GW μ) ≤
      ∫ T, centeredG l (rr μ l) θ c (Yt l T) * sourceWeight l y (Yt l T) ∂GW μ := by
  let : IsProbabilityMeasure (Ylaw μ l) := by
    unfold Ylaw
    infer_instance
  let g := centeredG l (rr μ l) θ c
  let w := sourceWeight l y
  let s := Set.Icc (0 : ℝ) (1/l)
  have hx' : x ∈ s := ⟨hx.1.le, hx.2.le⟩
  have hs : ∀ᵐ t ∂Ylaw μ l, t ∈ s :=
    (ae_Ylaw_mem μ h hl hlm).mono fun _ ht => ⟨ht.1.le, ht.2.le⟩
  have hg : Continuous g := by unfold g centeredG fθ; fun_prop
  have hw : Measurable w := by unfold w sourceWeight; fun_prop
  have hwc : ContinuousOn w s := by
    unfold w sourceWeight
    exact continuousOn_const.div (by fun_prop) fun t ht =>
      pow_ne_zero _ (source_weight_denom hl hy ht).1.ne'
  have hi {F : ℝ → ℝ} (hm : Measurable F) (hc : ContinuousOn F s) :
      Integrable F (Ylaw μ l) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    exact Integrable.of_bound hm.aestronglyMeasurable C (hs.mono fun t ht => hC t ht)
  have hmono : MonotoneOn w s := by
    intro t ht u hu htu
    have hD := (source_weight_denom hl hy hu).1
    have hle : 1-l*y*u ≤ 1-l*y*t :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left htu (mul_nonneg (by linarith) hy.1)) _
    exact one_div_le_one_div_of_le (sq_pos_of_pos hD) (pow_le_pow_left₀ hD.le hle 2)
  have hcross := single_crossing hs (g := g) (h := w) hneg hpos
    (by simpa only [Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr hx')] using hmono)
    (Set.mem_union_right _ (Set.mem_singleton x))
    (hi hg.measurable hg.continuousOn) (hi (hg.measurable.mul hw) (hg.continuousOn.mul hwc))
  have hw1 : 1 ≤ w x := by
    have hD := source_weight_denom hl hy hx'
    change 1 ≤ 1 / (1-l*y*x)^2
    rw [le_div_iff₀ (sq_pos_of_pos hD.1), one_mul]
    simpa using pow_le_pow_left₀ hD.1.le hD.2 2
  have hmap {F : ℝ → ℝ} (hm : Measurable F) :
      (∫ t, F t ∂Ylaw μ l) = ∫ T, F (Yt l T) ∂GW μ :=
    integral_map (measurable_Yt l).aemeasurable hm.aestronglyMeasurable
  have hmap_mul : (∫ t, g t * w t ∂Ylaw μ l) = ∫ T, g (Yt l T) * w (Yt l T) ∂GW μ :=
    hmap (hg.measurable.mul hw)
  rw [hmap hg.measurable, hmap_mul] at hcross
  exact (le_mul_of_one_le_left hmean hw1).trans hcross

private noncomputable def sourcePair (l r θ c y t : ℝ) : ℝ :=
  y*(1-l*y) * (centeredG l r θ c t * sourceWeight l y t)

private lemma ward_main_eq_source_pair {l θ v c b b' : ℝ} (hl : 1 < l)
    (hb : b ∈ Set.Ioo 0 1) (hb' : b' ∈ Set.Ioo 0 1)
    (hθ : 2*θ-1+(l-1)*(v/(l-1)) = l*(1+(l-1)*(v/(l-1)))*c) :
    wardMain l θ v b b' = sourcePair l (v/(l-1)) θ c (b/(l-1+b)) (b'/(l-1+b')) := by
  rw [wardMain_transform hl hb hb']
  dsimp only
  rw [sourceG_eq_centered hθ]
  unfold sourcePair sourceWeight
  ring

attribute [local irreducible] sourcePair

private lemma sourceR_as_integral (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) :
    (∫ T, Yt l T * (1-l*Yt l T) ∂GW μ) = sourceR μ l := by
  calc
    _ = ∫ T, Yt l T - l * Yt l T^2 ∂GW μ := by
      apply integral_congr_ae
      filter_upwards with T
      ring
    _ = _ := by
      rw [integral_sub (integrable_Yt_source μ h hl hlm)
        ((integrable_Yt_sq_source μ h hl hlm).const_mul l), integral_const_mul]
      rfl

private lemma source_integral_le_ward_main (h : OffspringHyp μ) {l θ c : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (hθ0 : 0 < θ)
    (hθ : 2*θ-1+(l-1)*(rr μ l) = l*(1+(l-1)*(rr μ l))*c)
    (hmean : 0 ≤ ∫ T, centeredG l (rr μ l) θ c (Yt l T) ∂GW μ) :
    sourceR μ l * (∫ T, centeredG l (rr μ l) θ c (Yt l T) ∂GW μ) ≤
      ∫ p : Tree × Tree, wardMain l θ (speedValueProv μ l)
        (escape l p.1) (escape l p.2) ∂ρ := by
  let g := centeredG l (rr μ l) θ c
  let F : Tree × Tree → ℝ := fun p => sourcePair l (rr μ l) θ c (Yt l p.1) (Yt l p.2)
  let A : Tree → ℝ := fun T => Yt l T*(1-l*Yt l T)
  let M : ℝ := ∫ T, g (Yt l T) ∂GW μ
  have heq : (fun p : Tree × Tree => wardMain l θ (speedValueProv μ l)
      (escape l p.1) (escape l p.2)) =ᵐ[ρ] F := by
    filter_upwards [ae_pair_source μ h hl hlm] with p hp
    exact ward_main_eq_source_pair hl hp.1 hp.2 hθ
  have hiF : Integrable F ρ := (integrable_main_source μ hl).congr heq
  have hiA : Integrable A (GW μ) := by
    apply ((integrable_Yt_source μ h hl hlm).sub
      ((integrable_Yt_sq_source μ h hl hlm).const_mul l)).congr
    filter_upwards with T
    dsimp only [A, Pi.sub_apply]
    ring
  obtain ⟨x, hx, hneg, hpos⟩ := centered_source_crossing hl (rr_pos μ h hl hlm) hθ0 hθ
  calc
    _ = ∫ T, M * A T ∂GW μ := by
      rw [integral_const_mul, show (∫ T, A T ∂GW μ) = sourceR μ l from
        sourceR_as_integral μ h hl hlm]
      exact mul_comm _ _
    _ ≤ ∫ T, ∫ U, F (T, U) ∂GW μ ∂GW μ := by
      apply integral_mono_ae (hiA.const_mul M) hiF.integral_prod_left
      filter_upwards [ae_Yt_source μ h hl hlm] with T hT
      have hA : 0 ≤ A T := by
        have hl0 : 0 < l := by linarith
        exact mul_nonneg hT.1.le (sub_nonneg.mpr (by
          have hh := (le_div_iff₀ hl0).mp hT.2.le
          simpa only [mul_comm l (Yt l T)] using hh))
      have hc := weighted_centered_source μ h hl hlm ⟨hT.1.le, hT.2.le⟩ hx hneg hpos hmean
      change M * A T ≤ _
      rw [mul_comm M, show (fun U => F (T, U)) =
          (fun U => A T * (g (Yt l U) * sourceWeight l (Yt l T) (Yt l U))) by
        funext U
        unfold F sourcePair A g
        rfl, integral_const_mul]
      exact mul_le_mul_of_nonneg_left hc hA
    _ = ∫ p, F p ∂ρ := (integral_prod F hiF).symm
    _ = _ := (integral_congr_ae heq).symm

private lemma deriv_neg_of_source_mean (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ)
    (hf : 0 < ∫ T, fθ l (rr μ l) (sourceTheta μ l) (Yt l T) ∂GW μ) :
    deriv (speedValue μ) l < 0 := by
  let θ := sourceTheta μ l
  let c := momY μ l 2 / muY μ l
  have hμ := (muY_mem μ h hl hlm).1
  have hl0 : 0 < l := by linarith
  have ha : l-1 ≠ 0 := by linarith
  have hv : (l-1)*rr μ l = speedValueProv μ l := by
    unfold rr
    rw [mul_comm, div_mul_cancel₀ _ ha]
  have hθ : 2*θ-1+(l-1)*(rr μ l) = l*(1+(l-1)*(rr μ l))*c := by
    rw [hv]
    exact sourceTheta_relation (l := l) (m₂ := momY μ l 2)
      (v := speedValueProv μ l) hμ.ne'
  have hc : c * muY μ l = momY μ l 2 := div_mul_cancel₀ _ hμ.ne'
  have hg : 0 < ∫ T, centeredG l (rr μ l) θ c (Yt l T) ∂GW μ := by
    rw [integral_centered_source μ h hl hlm θ c hc]
    exact mul_pos (by positivity) hf
  have hm := source_integral_le_ward_main μ h hl hlm (sourceTheta_pos μ h hl hlm) hθ hg.le
  have hw := ward_main_le_cost μ h hl hlm (θ := θ) ⟨(sourceTheta_lt_one μ h hl hlm).le, hf.le⟩
  have hcost := (mul_pos (sourceR_pos μ h hl hlm) hg).trans_le (hm.trans hw)
  have hZ := Speed.Zval_pos μ hl0 h hlm
  change 0 < -l * Zval μ l * deriv (speedValue μ) l at hcost
  exact neg_of_mul_pos_right hcost (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl0.le) hZ.le)

/-- **Corollary 3.6**, two-moment Ward source test (`cor:ward-source`): `Q > 0` gives
`v' < 0`. -/
theorem deriv_neg_of_Qtest_pos (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (hQ : 0 < Qtest μ l) :
    deriv (speedValue μ) l < 0 := by
  apply deriv_neg_of_source_mean μ h hl hlm
  have hp := mul_pos (muY_mem μ h hl hlm).1 hQ
  rw [← two_integral_fθ_eq_Q μ h hl hlm] at hp
  linarith

/-- **Corollary 3.6**, Ward source test from admissibility at one (`cor:ward-source`). -/
theorem deriv_neg_of_admissible_one (h : OffspringHyp μ) {l : ℝ}
    (hl : 1 < l) (hlm : l < mean μ) (h1 : Admissible μ l 1) :
    deriv (speedValue μ) l < 0 := by
  apply deriv_neg_of_source_mean μ h hl hlm
  have hbase := h1.2
  rw [integral_fθ_source μ h hl hlm] at hbase ⊢
  have hp := mul_pos (sub_pos.mpr (sourceTheta_lt_one μ h hl hlm)) (momY_sq_pos μ h hl hlm)
  nlinarith only [hbase, hp]

end LPPMonotonicityProof.Analytic
