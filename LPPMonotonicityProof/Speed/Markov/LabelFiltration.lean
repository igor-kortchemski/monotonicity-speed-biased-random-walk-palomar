module

public import LPPMonotonicityProof.Speed.Markov.Label
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# The finite-label filtration and its Markov property
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Preorder Filtration Filter
open scoped ENNReal BigOperators Function

namespace LPPMonotonicityProof.Speed.Markov.LabelSpec

variable {S : Type*} [MeasurableSpace S]

/-- The initial state together with the first `n` labels. -/
def prefixLabels {S : Type*} [MeasurableSpace S] (n : ℕ) :
    S × (ℕ → ℕ) → S × (Fin n → ℕ) :=
  fun x => (x.1, fun i => x.2 i.1)

lemma measurable_prefixLabels {S : Type*} [MeasurableSpace S] (n : ℕ) :
    Measurable (prefixLabels (S := S) n) := by
  apply Measurable.prodMk measurable_fst
  refine .of_eval fun i => (measurable_pi_apply i.1).comp measurable_snd

/-- The filtration which records the initial state and the first `n` labels. -/
def labelFiltration {S : Type*} [MeasurableSpace S] :
    Filtration ℕ (inferInstance : MeasurableSpace (S × (ℕ → ℕ))) where
  seq n := MeasurableSpace.comap (prefixLabels n) inferInstance
  mono' m n hmn := by
    intro B hB
    rcases hB with ⟨C, hC, rfl⟩
    let r : S × (Fin n → ℕ) → S × (Fin m → ℕ) := fun q =>
      (q.1, fun i => q.2 ⟨i.1, lt_of_lt_of_le i.2 hmn⟩)
    have hr : Measurable r := by
      apply Measurable.prodMk measurable_fst
      refine .of_eval fun i => (measurable_pi_apply _).comp measurable_snd
    refine ⟨r ⁻¹' C, hC.preimage hr, ?_⟩
    rfl
  le' n := (measurable_prefixLabels n).comap_le

lemma iSup_labelFiltration {S : Type*} [MeasurableSpace S] :
    ⨆ n, labelFiltration n = (inferInstance : MeasurableSpace (S × (ℕ → ℕ))) := by
  apply le_antisymm
  · exact iSup_le fun n => (labelFiltration (S := S)).le n
  · change MeasurableSpace.prod _ _ ≤ ⨆ n, labelFiltration n
    unfold MeasurableSpace.prod
    apply sup_le
    · have hfst : Measurable[labelFiltration (S := S) 0] (fun x : S × (ℕ → ℕ) => x.1) := by
        intro B hB
        exact ⟨Prod.fst ⁻¹' B, hB.preimage measurable_fst, rfl⟩
      exact hfst.comap_le.trans (le_iSup labelFiltration 0)
    · change MeasurableSpace.comap Prod.snd MeasurableSpace.pi ≤ ⨆ n, labelFiltration n
      unfold MeasurableSpace.pi
      rw [MeasurableSpace.comap_iSup]
      apply iSup_le
      intro n
      have hn : Measurable[labelFiltration (S := S) (n + 1)] (fun x => x.2 n) := by
        intro D hD
        refine ⟨(fun q : S × (Fin (n + 1) → ℕ) => q.2 ⟨n, Nat.lt_succ_self n⟩) ⁻¹' D,
          hD.preimage ((measurable_pi_apply _).comp measurable_snd), rfl⟩
      rw [MeasurableSpace.comap_comp]
      exact hn.comap_le.trans (le_iSup labelFiltration (n + 1))

/-- The edge-recording one-step shift. -/
def shift (G : LabelSpec S) (x : S × (ℕ → ℕ)) : S × (ℕ → ℕ) :=
  (G.next x.1 (x.2 0), seqTail x.2)

lemma measurable_shift (G : LabelSpec S) : Measurable G.shift := by
  have hnext : Measurable (fun x : S × (ℕ → ℕ) => G.next x.1 (x.2 0)) := by
    have h : Measurable (fun p : S × ℕ => G.next p.1 p.2) :=
      measurable_from_prod_countable_left fun j => G.measurable_next j
    exact h.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  apply hnext.prodMk
  refine .of_eval fun n => (measurable_pi_apply (n + 1)).comp measurable_snd

lemma measurable_shift_iterate (G : LabelSpec S) (n : ℕ) : Measurable (G.shift^[n]) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => rw [Function.iterate_succ]; exact ih.comp G.measurable_shift

/-- Iterating the shift produces the current state and the remaining labels. -/
theorem shift_iterate (G : LabelSpec S) (n : ℕ) (x : S × (ℕ → ℕ)) :
    G.shift^[n] x = (G.state x.1 x.2 n, fun k => x.2 (k + n)) := by
  induction n generalizing x with
  | zero =>
      apply Prod.ext
      · rfl
      · funext k
        rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      apply Prod.ext
      · exact G.state_succ x.1 x.2 n
      · funext k
        rfl

lemma setLIntegral_law_firstStep (G : LabelSpec S) (s : S)
    {C : Set (ℕ → ℕ)} (hC : MeasurableSet C) {F : (ℕ → ℕ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ c in C, F c ∂G.law s = ∑' j, G.weight s j *
      ∫⁻ c in seqCons j ⁻¹' C, F (seqCons j c) ∂G.law (G.next s j) := by
  rw [← lintegral_indicator hC, G.law_firstStep]
  simp only [lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul]
  apply tsum_congr
  intro j
  rw [lintegral_indicator hC]
  exact congrArg (fun r => G.weight s j * r) (setLIntegral_map hC hF (measurable_seqCons j))

/-- Prepending a fixed label to the label component of an environment. -/
def consAt {S : Type*} [MeasurableSpace S] (s : S) (j : ℕ) (x : S × (ℕ → ℕ)) :
    S × (ℕ → ℕ) := (s, seqCons j x.2)

/-- The corresponding operation on a finite label prefix. -/
def prefixCons {S : Type*} [MeasurableSpace S] (s : S) (j : ℕ) (n : ℕ) :
    S × (Fin n → ℕ) → S × (Fin (n + 1) → ℕ) :=
  fun q => (s, Fin.cases j q.2)

lemma measurablePrefixCons {S : Type*} [MeasurableSpace S] (s : S) (j : ℕ) (n : ℕ) :
    Measurable (prefixCons s j n) := by
  apply Measurable.prodMk measurable_const
  refine .of_eval fun i => ?_
  refine Fin.cases ?_ (fun k => ?_) i
  · exact measurable_const
  · exact (measurable_pi_apply k).comp measurable_snd

lemma measurableSet_preimage_consAt (G : LabelSpec S) (s : S) (j : ℕ) (n : ℕ)
    {B : Set (S × (ℕ → ℕ))} (hB : MeasurableSet[labelFiltration (n + 1)] B) :
    MeasurableSet[labelFiltration n] (consAt s j ⁻¹' B) := by
  change MeasurableSet[MeasurableSpace.comap (prefixLabels (n + 1)) inferInstance] B at hB
  rcases hB with ⟨C, hC, rfl⟩
  refine ⟨prefixCons s j n ⁻¹' C, hC.preimage (measurablePrefixCons s j n), ?_⟩
  rw [← Set.preimage_comp]
  congr 1
  funext x
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun k => ?_) i <;> rfl

lemma mem_of_labelFiltration_zero {B : Set (S × (ℕ → ℕ))}
    (hB : MeasurableSet[labelFiltration 0] B) (s : S) (c d : ℕ → ℕ) :
    (s, c) ∈ B ↔ (s, d) ∈ B := by
  change MeasurableSet[MeasurableSpace.comap (prefixLabels 0) inferInstance] B at hB
  rcases hB with ⟨C, hC, rfl⟩
  change prefixLabels 0 (s, c) ∈ C ↔ prefixLabels 0 (s, d) ∈ C
  have heq : prefixLabels 0 (s, c) = prefixLabels 0 (s, d) := by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  rw [heq]

lemma jointLaw_apply_set (G : LabelSpec S) (s : S) {A : Set (S × (ℕ → ℕ))}
    (hA : MeasurableSet A) : G.jointLaw s A = G.law s (Prod.mk s ⁻¹' A) := by
  rw [jointLaw_apply, Measure.compProd_apply hA]
  simp only [Kernel.const_apply]
  apply lintegral_dirac'
  exact measurable_measure_prodMk_left hA

/-- Pointwise form of the Markov property at time `n` for a labelled chain. -/
lemma law_markov (G : LabelSpec S) (s : S) (n : ℕ)
    {B : Set (S × (ℕ → ℕ))} (hB : MeasurableSet[labelFiltration n] B)
    {A : Set (S × (ℕ → ℕ))} (hA : MeasurableSet A) :
    G.law s (Prod.mk s ⁻¹' (B ∩ G.shift^[n] ⁻¹' A)) =
      ∫⁻ c in Prod.mk s ⁻¹' B, G.jointLaw (G.state s c n) A ∂G.law s := by
  induction n generalizing s B with
  | zero =>
      have hsec : Prod.mk s ⁻¹' B = Set.univ ∨ Prod.mk s ⁻¹' B = ∅ := by
        by_cases h : (s, fun _ => 0) ∈ B
        · left
          apply Set.eq_univ_of_forall
          intro c
          exact (mem_of_labelFiltration_zero hB s _ _).2 h
        · right
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro c hc
          exact h ((mem_of_labelFiltration_zero hB s _ _).1 hc)
      rcases hsec with hsec | hsec <;> simp [hsec, state, jointLaw_apply_set G s hA]
  | succ n ih =>
      let F : (ℕ → ℕ) → ℝ≥0∞ := fun c => G.jointLaw (G.state s c (n + 1)) A
      have hF : Measurable F :=
        (G.jointLaw.measurable_coe hA).comp
        ((G.measurable_state (n + 1)).comp (measurable_const.prodMk measurable_id))
      have hBg : MeasurableSet B := (labelFiltration.le (n + 1)) B hB
      have hD : MeasurableSet (Prod.mk s ⁻¹' (B ∩ G.shift^[n + 1] ⁻¹' A)) :=
        measurable_prodMk_left (hBg.inter (hA.preimage (G.measurable_shift_iterate (n + 1))))
      have hC : MeasurableSet (Prod.mk s ⁻¹' B) := measurable_prodMk_left hBg
      rw [setLIntegral_law_firstStep G s hC hF]
      rw [G.law_firstStep s, Measure.sum_apply _ hD]
      simp only [Measure.smul_apply, smul_eq_mul,
        Measure.map_apply (measurable_seqCons _) hD]
      apply tsum_congr
      intro j
      let B' : Set (S × (ℕ → ℕ)) := consAt s j ⁻¹' B
      have hB' : MeasurableSet[labelFiltration n] B' := G.measurableSet_preimage_consAt s j n hB
      have hset : seqCons j ⁻¹' (Prod.mk s ⁻¹' (B ∩ G.shift^[n + 1] ⁻¹' A)) =
          Prod.mk (G.next s j) ⁻¹' (B' ∩ G.shift^[n] ⁻¹' A) := by
        ext c
        change ((s, seqCons j c) ∈ B ∧ G.shift^[n + 1] (s, seqCons j c) ∈ A) ↔
          ((G.next s j, c) ∈ B' ∧ G.shift^[n] (G.next s j, c) ∈ A)
        rw [Function.iterate_succ_apply]
        rfl
      rw [hset, ih (G.next s j) hB']
      congr 1
      have hsetC : Prod.mk (G.next s j) ⁻¹' B' = seqCons j ⁻¹' (Prod.mk s ⁻¹' B) := rfl
      rw [hsetC]
      apply setLIntegral_congr_fun (hC.preimage (measurable_seqCons j))
      intro c hc
      change G.jointLaw (G.state (G.next s j) c n) A = F (seqCons j c)
      dsimp only [F]
      rw [G.state_seqCons s j c]
      rfl


/-- The finite-label Markov property, integrated over the initial state law. -/
theorem setLIntegral_shift (G : LabelSpec S) (π : Measure S) [IsProbabilityMeasure π]
    (n : ℕ) {B : Set (S × (ℕ → ℕ))} (hB : MeasurableSet[labelFiltration n] B)
    {A : Set (S × (ℕ → ℕ))} (hA : MeasurableSet A) :
    (π ⊗ₘ G.law) (B ∩ G.shift^[n] ⁻¹' A) =
      ∫⁻ x in B, G.law (G.state x.1 x.2 n)
        {c | (G.state x.1 x.2 n, c) ∈ A} ∂(π ⊗ₘ G.law) := by
  have hBg : MeasurableSet B := (labelFiltration.le n) B hB
  have hD : MeasurableSet (B ∩ G.shift^[n] ⁻¹' A) :=
    hBg.inter (hA.preimage (G.measurable_shift_iterate n))
  have hF : Measurable (fun x : S × (ℕ → ℕ) => G.jointLaw (G.state x.1 x.2 n) A) :=
    (G.jointLaw.measurable_coe hA).comp (G.measurable_state n)
  have hjoint : ∀ x : S × (ℕ → ℕ),
      G.law (G.state x.1 x.2 n) {c | (G.state x.1 x.2 n, c) ∈ A} =
        G.jointLaw (G.state x.1 x.2 n) A := by
    intro x
    exact (G.jointLaw_apply_set _ hA).symm
  simp_rw [hjoint]
  rw [Measure.compProd_apply hD]
  simp_rw [G.law_markov _ n hB hA]
  rw [← lintegral_indicator hBg, Measure.lintegral_compProd (hF.indicator hBg)]
  apply lintegral_congr
  intro s
  rw [← lintegral_indicator (measurable_prodMk_left hBg)]
  apply lintegral_congr
  intro c
  by_cases hc : (s, c) ∈ B <;> simp [Set.indicator, hc]

lemma state_eq_of_forall_lt (G : LabelSpec S) (s : S) (c d : ℕ → ℕ) (n : ℕ)
    (h : ∀ i < n, c i = d i) : G.state s c n = G.state s d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [state, state, ih (fun i hi => h i (Nat.lt.step hi)),
        h n (Nat.lt_succ_self n)]

/-- Extend a finite label prefix by zero. -/
def extendPrefix {n : ℕ} (q : Fin n → ℕ) : ℕ → ℕ := fun i =>
  if hi : i < n then q ⟨i, hi⟩ else 0

lemma measurable_extendPrefix (n : ℕ) : Measurable (fun q : Fin n → ℕ => extendPrefix q) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases hi : i < n
  · simpa only [extendPrefix, hi, dite_eq_left] using
      (measurable_pi_apply (⟨i, hi⟩ : Fin n))
  · simp [extendPrefix, hi]

lemma state_extendPrefix (G : LabelSpec S) (s : S) (c : ℕ → ℕ) (n : ℕ) :
    G.state s (extendPrefix fun i : Fin n => c i.1) n = G.state s c n := by
  apply G.state_eq_of_forall_lt s _ c n
  intro i hi
  simp [extendPrefix, hi]

lemma measurable_state_prefix (G : LabelSpec S) (n : ℕ) :
    Measurable (fun q : S × (Fin n → ℕ) =>
      G.state q.1 (extendPrefix q.2) n) := by
  have h : Measurable (fun q : S × (Fin n → ℕ) => (q.1, extendPrefix q.2)) :=
    measurable_fst.prodMk ((measurable_extendPrefix n).comp measurable_snd)
  change Measurable ((fun p : S × (ℕ → ℕ) => G.state p.1 p.2 n) ∘
    fun q : S × (Fin n → ℕ) => (q.1, extendPrefix q.2))
  exact (G.measurable_state n).comp h

lemma measurable_futureProb_labelFiltration (G : LabelSpec S) (n : ℕ)
    {A : Set (S × (ℕ → ℕ))} (hA : MeasurableSet A) :
    Measurable[labelFiltration n] (fun x : S × (ℕ → ℕ) =>
      (G.jointLaw (G.state x.1 x.2 n) A).toReal) := by
  let q : S × (ℕ → ℕ) → S × (Fin n → ℕ) := prefixLabels n
  let g : S × (Fin n → ℕ) → ℝ := fun z =>
    (G.jointLaw (G.state z.1 (extendPrefix z.2) n) A).toReal
  have hg : Measurable g :=
    (G.jointLaw.measurable_coe hA |>.comp (G.measurable_state_prefix n)).ennreal_toReal
  have heq : (fun x : S × (ℕ → ℕ) => (G.jointLaw (G.state x.1 x.2 n) A).toReal) = g ∘ q := by
    funext x
    change (G.jointLaw (G.state x.1 x.2 n) A).toReal =
      (G.jointLaw (G.state x.1 (extendPrefix fun i : Fin n => x.2 i.1) n) A).toReal
    rw [G.state_extendPrefix x.1 x.2 n]
  rw [heq]
  intro D hD
  exact ⟨g ⁻¹' D, hg hD, rfl⟩


/-- Conditional probability after `n` steps, relative to the finite-label
filtration. -/
theorem condExp_shift (G : LabelSpec S) (π : Measure S) [IsProbabilityMeasure π]
    (n : ℕ) {A : Set (S × (ℕ → ℕ))} (hA : MeasurableSet A) :
    (π ⊗ₘ G.law)[(G.shift^[n] ⁻¹' A).indicator 1 | labelFiltration n] =ᵐ[π ⊗ₘ G.law]
      fun x => (G.law (G.state x.1 x.2 n)
        {c | (G.state x.1 x.2 n, c) ∈ A}).toReal := by
  let μ : Measure (S × (ℕ → ℕ)) := π ⊗ₘ G.law
  let C : Set (S × (ℕ → ℕ)) := G.shift^[n] ⁻¹' A
  let F : (S × (ℕ → ℕ)) → ℝ≥0∞ := fun x => G.jointLaw (G.state x.1 x.2 n) A
  let g : (S × (ℕ → ℕ)) → ℝ := fun x => (F x).toReal
  have hjoint : ∀ x : S × (ℕ → ℕ),
      G.law (G.state x.1 x.2 n) {c | (G.state x.1 x.2 n, c) ∈ A} = F x := by
    intro x
    exact (G.jointLaw_apply_set _ hA).symm
  simp_rw [hjoint]
  change μ[C.indicator 1 | labelFiltration n] =ᵐ[μ] g
  have hC : MeasurableSet C := hA.preimage (G.measurable_shift_iterate n)
  have hF : Measurable F := (G.jointLaw.measurable_coe hA).comp (G.measurable_state n)
  have hg : Measurable g := hF.ennreal_toReal
  have hg_int : Integrable g μ := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 prob_le_one
  have hf_int : Integrable (C.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hC
  refine (ae_eq_condExp_of_forall_setIntegral_eq (labelFiltration.le n) hf_int
    (fun B _ _ => hg_int.integrableOn) ?_ ?_).symm
  · intro B hB hμB
    have hBg : MeasurableSet B := (labelFiltration.le n) B hB
    calc
      ∫ x in B, g x ∂μ = μ.real (B ∩ C) := by
        rw [integral_toReal hF.aemeasurable.restrict
          (ae_of_all _ fun x => measure_lt_top _ _)]
        simp_rw [← hjoint]
        rw [← G.setLIntegral_shift π n hB hA]
        rfl
      _ = ∫ x in B, C.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [← integral_indicator hBg]
        have hfun : B.indicator (C.indicator (fun _ => (1 : ℝ))) =
            (B ∩ C).indicator 1 := by
          ext x
          by_cases hxB : x ∈ B <;> by_cases hxC : x ∈ C <;>
            simp [Set.indicator, hxB, hxC]
        rw [hfun, integral_indicator_one (hBg.inter hC)]
  · exact (stronglyMeasurable_iff_measurable.mpr
      (G.measurable_futureProb_labelFiltration n hA)).aestronglyMeasurable

end LPPMonotonicityProof.Speed.Markov.LabelSpec
