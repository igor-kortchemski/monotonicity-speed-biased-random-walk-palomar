module

public import LPPMonotonicityProof.Ergodic.Maximal
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.BirkhoffSum.NormedSpace
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Birkhoff's pointwise ergodic theorem for bounded observables

This is a project-independent development of the bounded pointwise
ergodic theorem.
-/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped BigOperators Topology

variable {α : Type*} [MeasurableSpace α]
variable {T : α → α} {μ : Measure α} {f : α → ℝ}

theorem measurable_birkhoffAverage (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffAverage ℝ T f n) := by
  change Measurable (fun x => (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, f (T^[j] x))
  exact (Finset.measurable_sum _ fun j _ => hf.comp (hT.iterate j)).const_smul (M := ℝ) _

omit [MeasurableSpace α] in
theorem norm_birkhoffAverage_le {C : ℝ} (hfb : ∀ x, ‖f x‖ ≤ C) (n : ℕ) (x : α) :
    ‖birkhoffAverage ℝ T f n x‖ ≤ C := by
  by_cases hn : n = 0
  · subst n
    simpa using (norm_nonneg (f x)).trans (hfb x)
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : ‖birkhoffSum T f n x‖ ≤ n * C := by
    calc
      ‖birkhoffSum T f n x‖ ≤ ∑ j ∈ Finset.range n, ‖f (T^[j] x)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range n, C := Finset.sum_le_sum fun j _ => hfb (T^[j] x)
      _ = n * C := by simp
  rw [birkhoffAverage, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnR]
  calc
    (n : ℝ)⁻¹ * ‖birkhoffSum T f n x‖ ≤ (n : ℝ)⁻¹ * (n * C) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hnR.le)
    _ = C := by rw [← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul]

theorem integrable_of_measurable_of_norm_le [IsFiniteMeasure μ]
    (hf : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hfb
  refine (integrable_const |C|).mono hf.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  simpa only [Real.norm_of_nonneg (abs_nonneg C)] using (hC x).trans (le_abs_self C)

omit [MeasurableSpace α] in
theorem isBounded_range_of_norm_le (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    Bornology.IsBounded (range f) := by
  obtain ⟨C, hC⟩ := hfb
  rw [Metric.isBounded_range_iff]
  exact ⟨C + C, fun x y => (dist_le_norm_add_norm (f x) (f y)).trans (add_le_add (hC x) (hC y))⟩

/-- The points where the upper limit of the Birkhoff averages exceeds `c`. -/
noncomputable def birkhoffUpperExceptionalSet (T : α → α) (f : α → ℝ) (c : ℝ) : Set α :=
  {x | c < limsup (fun n => birkhoffAverage ℝ T f n x) atTop}

theorem measurableSet_birkhoffUpperExceptionalSet
    (hT : Measurable T) (hf : Measurable f) (c : ℝ) :
    MeasurableSet (birkhoffUpperExceptionalSet T f c) := by
  exact measurableSet_lt measurable_const
    (Measurable.limsup fun n => measurable_birkhoffAverage hT hf n)

omit [MeasurableSpace α] in
theorem limsup_birkhoffAverage_shift (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) (x : α) :
    limsup (fun n => birkhoffAverage ℝ T f n (T x)) atTop =
      limsup (fun n => birkhoffAverage ℝ T f n x) atTop := by
  obtain ⟨C, hC⟩ := hfb
  let A : ℕ → ℝ := fun n => birkhoffAverage ℝ T f n x
  let B : ℕ → ℝ := fun n => birkhoffAverage ℝ T f n (T x)
  let D : ℕ → ℝ := fun n => B n - A n
  have hAup : IsBoundedUnder (· ≤ ·) atTop A := isBoundedUnder_of ⟨C, fun n =>
    le_of_abs_le (by simpa only [Real.norm_eq_abs] using norm_birkhoffAverage_le hC n x)⟩
  have hAlow : IsBoundedUnder (· ≥ ·) atTop A := isBoundedUnder_of ⟨-C, fun n =>
    neg_le_of_abs_le (by simpa only [Real.norm_eq_abs] using norm_birkhoffAverage_le hC n x)⟩
  have hBup : IsBoundedUnder (· ≤ ·) atTop B := isBoundedUnder_of ⟨C, fun n =>
    le_of_abs_le (by simpa only [Real.norm_eq_abs] using norm_birkhoffAverage_le hC n (T x))⟩
  have hBlow : IsBoundedUnder (· ≥ ·) atTop B := isBoundedUnder_of ⟨-C, fun n =>
    neg_le_of_abs_le (by simpa only [Real.norm_eq_abs] using norm_birkhoffAverage_le hC n (T x))⟩
  have hD : Tendsto D atTop (𝓝 0) := by
    simpa only [D, A, B] using tendsto_birkhoffAverage_apply_sub_birkhoffAverage'
      ℝ (isBounded_range_of_norm_le ⟨C, hC⟩) T x
  have hDn : Tendsto (fun n => -D n) atTop (𝓝 0) := by simpa using hD.neg
  have hBD : B = A + D := by
    funext n
    dsimp [A, B, D]
    abel
  have hAD : A = B + fun n => -D n := by
    funext n
    dsimp [A, B, D]
    abel
  change limsup B atTop = limsup A atTop
  apply le_antisymm
  · rw [hBD]
    calc
      limsup (A + D) atTop ≤ limsup A atTop + limsup D atTop :=
        limsup_add_le hAlow hAup hD.isBoundedUnder_ge.isCoboundedUnder_le hD.isBoundedUnder_le
      _ = limsup A atTop := by rw [hD.limsup_eq, add_zero]
  · rw [hAD]
    calc
      limsup (B + fun n => -D n) atTop ≤ limsup B atTop + limsup (fun n => -D n) atTop :=
        limsup_add_le hBlow hBup hDn.isBoundedUnder_ge.isCoboundedUnder_le hDn.isBoundedUnder_le
      _ = limsup B atTop := by rw [hDn.limsup_eq, add_zero]

omit [MeasurableSpace α] in
theorem preimage_birkhoffUpperExceptionalSet (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) (c : ℝ) :
    T ⁻¹' birkhoffUpperExceptionalSet T f c = birkhoffUpperExceptionalSet T f c := by
  ext x
  change (c < limsup (fun n => birkhoffAverage ℝ T f n (T x)) atTop) ↔
    c < limsup (fun n => birkhoffAverage ℝ T f n x) atTop
  rw [limsup_birkhoffAverage_shift (T := T) hfb x]

omit [MeasurableSpace α] in
theorem birkhoffUpperExceptionalSet_subset_iUnion_max
    (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) (c : ℝ) :
    birkhoffUpperExceptionalSet T f c ⊆
      ⋃ N, {x | 0 < maxBirkhoffSum T (f - fun _ => c) N x} := by
  obtain ⟨C, hC⟩ := hfb
  let g : α → ℝ := f - fun _ => c
  change birkhoffUpperExceptionalSet T f c ⊆ ⋃ N, {x | 0 < maxBirkhoffSum T g N x}
  intro x hx
  change c < limsup (fun n => birkhoffAverage ℝ T f n x) atTop at hx
  have hAlow : IsBoundedUnder (· ≥ ·) atTop
      (fun n => birkhoffAverage ℝ T f n x) := isBoundedUnder_of ⟨-C, fun n =>
    neg_le_of_abs_le (by simpa only [Real.norm_eq_abs] using norm_birkhoffAverage_le hC n x)⟩
  have hAcob : IsCoboundedUnder (· ≤ ·) atTop
      (fun n => birkhoffAverage ℝ T f n x) := hAlow.isCoboundedUnder_le
  obtain ⟨b, hcb, hb⟩ := exists_between hx
  have hfreq := frequently_lt_of_lt_limsup hAcob hb
  obtain ⟨n, hbn, hn⟩ := (hfreq.and_eventually (eventually_gt_atTop 0)).exists
  have hconst : birkhoffAverage ℝ T (fun _ : α => c) n x = c :=
    birkhoffAverage_apply_of_comp_eq ℝ rfl (Nat.cast_ne_zero.mpr hn.ne') x
  have hgavg : birkhoffAverage ℝ T g n x = birkhoffAverage ℝ T f n x - c := by
    dsimp [g]
    rw [birkhoffAverage_sub_apply, hconst]
  have hgavgpos : 0 < birkhoffAverage ℝ T g n x := by
    rw [hgavg]
    exact sub_pos.mpr (hcb.trans hbn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul : 0 < (n : ℝ)⁻¹ * birkhoffSum T g n x := by
    simpa only [birkhoffAverage, smul_eq_mul] using hgavgpos
  have hsum : 0 < birkhoffSum T g n x :=
    pos_of_mul_pos_right hmul (inv_nonneg.mpr hnR.le)
  exact mem_iUnion.mpr ⟨n, hsum.trans_le (birkhoffSum_le_maxBirkhoffSum T g le_rfl x)⟩

theorem not_ae_mem_birkhoffUpperExceptionalSet [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hf : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C)
    {c : ℝ} (hc : (∫ y, f y ∂μ) < c)
    (hfull : ∀ᵐ x ∂μ, x ∈ birkhoffUpperExceptionalSet T f c) : False := by
  let g : α → ℝ := f - fun _ => c
  have hfint : Integrable f μ := integrable_of_measurable_of_norm_le hf hfb
  have hgmeas : Measurable g := hf.sub measurable_const
  have hgint : Integrable g μ := hfint.sub (integrable_const c)
  let A : ℕ → Set α := fun N => {x | 0 < maxBirkhoffSum T g N x}
  have hAm : ∀ N, MeasurableSet (A N) := fun N =>
    measurableSet_lt measurable_const (measurable_maxBirkhoffSum hT.measurable hgmeas N)
  have hAmono : Monotone A := by
    intro N K hNK x hx
    exact lt_of_lt_of_le hx
      (monotone_nat_of_le_succ (fun n => maxBirkhoffSum_mono_succ T g n x) hNK)
  have hmax : ∀ N, 0 ≤ ∫ x in A N, g x ∂μ := fun N =>
    integral_nonneg_on_maxBirkhoffSum_pos hT.toMeasurePreserving hgint N
  have hbad_subset : birkhoffUpperExceptionalSet T f c ⊆ ⋃ N, A N := by
    simpa only [g, A] using birkhoffUpperExceptionalSet_subset_iUnion_max (T := T) hfb c
  have hU : ∀ᵐ x ∂μ, x ∈ ⋃ N, A N := hfull.mono fun _ hx => hbad_subset hx
  have htend := tendsto_setIntegral_of_monotone (μ := μ) (f := g) hAm hAmono hgint.integrableOn
  have hnonneg : 0 ≤ ∫ x, g x ∂μ := by
    have hlim := ge_of_tendsto htend (Eventually.of_forall hmax)
    rw [Measure.restrict_eq_self_of_ae_mem hU] at hlim
    exact hlim
  have hgval : (∫ x, g x ∂μ) = (∫ y, f y ∂μ) - c := by
    dsimp [g]
    rw [integral_sub hfint (integrable_const c), integral_const]
    simp [measureReal_def]
  have hgneg : (∫ x, g x ∂μ) < 0 := by rw [hgval]; exact sub_neg.mpr hc
  exact (not_lt_of_ge hnonneg) hgneg

theorem ae_notMem_birkhoffUpperExceptionalSet [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hf : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C)
    {c : ℝ} (hc : (∫ y, f y ∂μ) < c) :
    ∀ᵐ x ∂μ, x ∉ birkhoffUpperExceptionalSet T f c := by
  have hm := measurableSet_birkhoffUpperExceptionalSet hT.measurable hf c
  have hi : T ⁻¹' birkhoffUpperExceptionalSet T f c =ᵐ[μ]
      birkhoffUpperExceptionalSet T f c :=
    by rw [preimage_birkhoffUpperExceptionalSet hfb c]
  have hcase := PreErgodic.ae_mem_or_ae_notMem (f := T) (μ := μ)
    (s := birkhoffUpperExceptionalSet T f c) hT.toPreErgodic hm.nullMeasurableSet hi
  rcases hcase with hfull | hnull
  · exact (not_ae_mem_birkhoffUpperExceptionalSet (T := T) (f := f) (μ := μ) (c := c)
    hT hf hfb hc hfull).elim
  · exact hnull

theorem ae_limsup_birkhoffAverage_le_integral [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hf : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∀ᵐ x ∂μ, limsup (fun n => birkhoffAverage ℝ T f n x) atTop ≤ ∫ y, f y ∂μ := by
  have hq : ∀ q : ℚ, ∀ᵐ x ∂μ, (∫ y, f y ∂μ) < (q : ℝ) →
      limsup (fun n => birkhoffAverage ℝ T f n x) atTop ≤ (q : ℝ) := by
    intro q
    by_cases hIq : (∫ y, f y ∂μ) < (q : ℝ)
    · filter_upwards [ae_notMem_birkhoffUpperExceptionalSet hT hf hfb hIq] with x hx
      intro _
      exact le_of_not_gt hx
    · filter_upwards [] with x
      intro h
      exact (hIq h).elim
  filter_upwards [ae_all_iff.mpr hq] with x hx
  exact le_of_forall_lt_rat_imp_le fun q hIq => hx q hIq

/-- **Birkhoff's pointwise ergodic theorem**, for a bounded measurable real observable. -/
theorem tendsto_birkhoffAverage_of_ergodic [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hf : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (∫ y, f y ∂μ)) := by
  obtain ⟨C, hC⟩ := hfb
  have hupp := ae_limsup_birkhoffAverage_le_integral hT hf ⟨C, hC⟩
  have hfbneg : ∃ D, ∀ x, ‖(-f) x‖ ≤ D := ⟨C, fun x => by simpa using hC x⟩
  have hlow := ae_limsup_birkhoffAverage_le_integral hT hf.neg hfbneg
  filter_upwards [hupp, hlow] with x hux hlx
  have hup : IsBoundedUnder (· ≤ ·) atTop (fun n => birkhoffAverage ℝ T f n x) :=
    isBoundedUnder_of ⟨C, fun n => le_of_abs_le
      (by simpa only [Real.norm_eq_abs] using norm_birkhoffAverage_le hC n x)⟩
  have hdown : IsBoundedUnder (· ≥ ·) atTop (fun n => birkhoffAverage ℝ T f n x) :=
    isBoundedUnder_of ⟨-C, fun n => neg_le_of_abs_le
      (by simpa only [Real.norm_eq_abs] using norm_birkhoffAverage_le hC n x)⟩
  have havgneg : (fun n => birkhoffAverage ℝ T (-f) n x) =
      (fun n => -birkhoffAverage ℝ T f n x) := by
    funext n
    rw [birkhoffAverage_neg_apply]
  rw [havgneg] at hlx
  simp only [Pi.neg_apply, integral_neg] at hlx
  have hlimneg : limsup (fun n => -birkhoffAverage ℝ T f n x) atTop =
      -liminf (fun n => birkhoffAverage ℝ T f n x) atTop := by
    simpa only [zero_sub] using
      (limsup_const_sub atTop (fun n => birkhoffAverage ℝ T f n x) 0
        hup.isCoboundedUnder_ge hdown)
  rw [hlimneg] at hlx
  exact tendsto_of_le_liminf_of_limsup_le (by linarith) hux hup hdown

end
