module

public import LPPMonotonicityProof.Analytic.Interface2
public import LPPMonotonicityProof.Analytic.Regularity.Envelope
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Moments of the response envelope

This module proves that the response envelope of Proposition 2.5 (`prop:regularity`)
is integrable on every compact bias interval, through the moment bounds
`E M_k^γ ≤ r_γ^k` on the path maxima in the proof of that proposition. Indexed sibling
factors are extended by zero away from the existing children; on leafless trees this
agrees with the formulas of the paper.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private noncomputable def sibRatio (l : ℝ) (T : Tree) (j : ℕ) : ℝ :=
  l / (l + (childSum l T - escape l (child T (j + 1))))

private theorem sum_erase_child (l : ℝ) (T : Tree) (i : Fin (degree T)) :
    (∑ j ∈ Finset.univ.erase i, escape l (child T (j + 1))) =
      childSum l T - escape l (child T (i + 1)) := by
  rw [childSum]
  exact Finset.sum_erase_eq_sub (Finset.mem_univ i)

/-- The indexed sibling factor as an extended nonnegative real. -/
noncomputable def sibIdx (l : ℝ) (T : Tree) (j : ℕ) : ℝ≥0∞ :=
  if h : j < degree T then (sib l T ⟨j, h⟩ : ℝ≥0∞) else 0

private theorem sibIdx_eq (l : ℝ) (T : Tree) (j : ℕ) :
    sibIdx l T j = if j < degree T then ENNReal.ofReal (sibRatio l T j) else 0 := by
  classical
  by_cases hj : j < degree T
  · let i : Fin (degree T) := ⟨j, hj⟩
    have hne : (child T (i + 1)) = child T (j + 1) := rfl
    simp only [sibIdx, hj, dif_pos, sib, sibRatio, i]
    rw [sum_erase_child]
    rfl
  · simp [sibIdx, hj]

private theorem measurable_sibRatio (l : ℝ) (j : ℕ) : Measurable (fun T => sibRatio l T j) := by
  exact measurable_const.div (measurable_const.add
    ((measurable_childSum l).sub ((measurable_escape l).comp (continuous_child (j + 1)).measurable)))

theorem measurable_sibIdx (l : ℝ) (j : ℕ) : Measurable (fun T => sibIdx l T j) := by
  simp_rw [sibIdx_eq]
  exact Measurable.ite (measurableSet_lt measurable_const continuous_degree.measurable)
    (ENNReal.measurable_ofReal.comp (measurable_sibRatio l j)) measurable_const

/-- The candidate for the maximum path product ending at child `j`. -/
noncomputable def pathStepIdx (l : ℝ) (k : ℕ) (T : Tree) (j : ℕ) : ℝ≥0∞ :=
  if h : j < degree T then
    ((sib l T ⟨j, h⟩ * pathMax l k (child T (j + 1)) : ℝ≥0) : ℝ≥0∞)
  else 0

private theorem coe_pathMax_succ (l : ℝ) (k : ℕ) (T : Tree) :
    (pathMax l (k + 1) T : ℝ≥0∞) = ⨆ j : ℕ, pathStepIdx l k T j := by
  let f : Fin (degree T) → ℝ≥0 := fun i => sib l T i * pathMax l k (child T (i + 1))
  have hcoe (ι : Type) (s : Finset ι) (g : ι → ℝ≥0) : ((s.sup g : ℝ≥0) : ℝ≥0∞) =
      s.sup (fun i => (g i : ℝ≥0∞)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.sup_insert, ha, ih]
  change ((Finset.univ.sup f : ℝ≥0) : ℝ≥0∞) = _
  rw [hcoe, Finset.sup_eq_iSup]
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun _ => ?_
    have heq : (f i : ℝ≥0∞) = pathStepIdx l k T i.val := by
      simp [f, pathStepIdx, i.isLt]
    rw [heq]
    exact le_iSup (fun j : ℕ => pathStepIdx l k T j) i.val
  · refine iSup_le fun j => ?_
    by_cases hj : j < degree T
    · have heq : pathStepIdx l k T j = (f ⟨j, hj⟩ : ℝ≥0∞) := by
        simp [f, pathStepIdx, hj]
      rw [heq]
      exact le_iSup_of_le ⟨j, hj⟩ (le_iSup_of_le (Finset.mem_univ _) le_rfl)
    · simp [pathStepIdx, hj]

theorem measurable_pathMax (l : ℝ) (k : ℕ) : Measurable (fun T => (pathMax l k T : ℝ≥0∞)) := by
  induction k with
  | zero => simp [pathMax]
  | succ k ih =>
      simp_rw [coe_pathMax_succ]
      apply Measurable.iSup
      intro j
      simp only [pathStepIdx]
      refine Measurable.dite (s := {T : Tree | j < degree T})
        (f := fun T : {T : Tree // j < degree T} =>
          ((sib l T.val ⟨j, T.property⟩ * pathMax l k (child T.val (j + 1)) : ℝ≥0) : ℝ≥0∞))
        ?_ measurable_const
        (measurableSet_lt measurable_const continuous_degree.measurable)
      have hs : Measurable (fun T : {T : Tree // j < degree T} => sibIdx l T.val j) :=
        (measurable_sibIdx l j).comp measurable_subtype_coe
      have hp : Measurable (fun T : {T : Tree // j < degree T} =>
          (pathMax l k (child T.val (j + 1)) : ℝ≥0∞)) :=
        ih.comp ((continuous_child (j + 1)).measurable.comp measurable_subtype_coe)
      have hs' : Measurable (fun T : {T : Tree // j < degree T} =>
          (sib l T.val ⟨j, T.property⟩ : ℝ≥0∞)) := by
        have hp : ∀ T : {T : Tree // j < degree T}, j < degree T.val := fun T => T.property
        simpa only [sibIdx, dif_pos, hp] using hs
      exact hs'.mul hp

theorem measurable_pathStepIdx (l : ℝ) (k : ℕ) (j : ℕ) :
    Measurable (fun T => pathStepIdx l k T j) := by
  simp only [pathStepIdx]
  refine Measurable.dite (s := {T : Tree | j < degree T})
    (f := fun T : {T : Tree // j < degree T} =>
      ((sib l T.val ⟨j, T.property⟩ * pathMax l k (child T.val (j + 1)) : ℝ≥0) : ℝ≥0∞))
    ?_ measurable_const
    (measurableSet_lt measurable_const continuous_degree.measurable)
  have hs : Measurable (fun T : {T : Tree // j < degree T} => sibIdx l T.val j) :=
    (measurable_sibIdx l j).comp measurable_subtype_coe
  have hp : Measurable (fun T : {T : Tree // j < degree T} =>
      (pathMax l k (child T.val (j + 1)) : ℝ≥0∞)) :=
    (measurable_pathMax l k).comp ((continuous_child (j + 1)).measurable.comp measurable_subtype_coe)
  have hs' : Measurable (fun T : {T : Tree // j < degree T} =>
      (sib l T.val ⟨j, T.property⟩ : ℝ≥0∞)) := by
    have hp : ∀ T : {T : Tree // j < degree T}, j < degree T.val := fun T => T.property
    simpa only [sibIdx, dif_pos, hp] using hs
  exact hs'.mul hp

theorem measurable_envelope (lNeg lPos : ℝ) : Measurable (envelope lNeg lPos) := by
  exact measurable_const.mul (Measurable.tsum fun k => measurable_pathMax lPos (k + 1))

/-- Sum of the powers of all sibling factors at the root. -/
noncomputable def sibMoment (l : ℝ) (T : Tree) (γ : ℕ) : ℝ≥0∞ :=
  ∑ i : Fin (degree T), (sib l T i : ℝ≥0∞) ^ γ

/-- The one-step moment occurring in the path-product recursion. -/
noncomputable def rGamma (l : ℝ) (γ : ℕ) : ℝ≥0∞ := ∫⁻ T, sibMoment l T γ ∂GW μ

/-- The `γ`-moment of the maximum path product at a given depth. -/
noncomputable def pathMoment (l : ℝ) (k γ : ℕ) : ℝ≥0∞ :=
  ∫⁻ T, (pathMax l k T : ℝ≥0∞) ^ γ ∂GW μ

theorem measurable_sibMoment (l : ℝ) (γ : ℕ) : Measurable (fun T => sibMoment l T γ) := by
  have h : Measurable (fun p : ℕ × Tree =>
      ∑ j ∈ Finset.range p.1, sibIdx l p.2 j ^ γ) :=
    measurable_from_prod_countable_right fun n =>
      (Finset.range n).measurable_sum fun j _ => (measurable_sibIdx l j).pow_const γ
  have heq : (fun T => sibMoment l T γ) = (fun T =>
      ∑ j ∈ Finset.range (degree T), sibIdx l T j ^ γ) := by
    funext T
    unfold sibMoment
    rw [← Fin.sum_univ_eq_sum_range (fun j => sibIdx l T j ^ γ)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [sibIdx, dif_pos, Fin.is_lt]
  rw [heq]
  exact h.comp (continuous_degree.measurable.prodMk measurable_id)

private theorem finset_sup_pow_le_sum_pow {ι : Type} (s : Finset ι) (f : ι → ℝ≥0∞) (γ : ℕ)
    (hγ : 0 < γ) :
    (s.sup f) ^ γ ≤ ∑ i ∈ s, f i ^ γ := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => simp [hγ.ne']
  | insert a s ha ih =>
      rw [Finset.sup_insert, Finset.sum_insert ha]
      rcases le_total (f a) (s.sup f) with h | h
      · have hs : f a ⊔ s.sup f = s.sup f := sup_eq_right.mpr h
        rw [hs]
        exact (ih f).trans (le_add_of_nonneg_left bot_le)
      · have hs : f a ⊔ s.sup f = f a := sup_eq_left.mpr h
        rw [hs]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => bot_le)

private theorem coe_finset_sup {ι : Type} (s : Finset ι) (f : ι → ℝ≥0) :
    ((s.sup f : ℝ≥0) : ℝ≥0∞) = s.sup (fun i => (f i : ℝ≥0∞)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sup_insert, ih]

private theorem pathMax_pow_le_sum (l : ℝ) (k γ : ℕ) (hγ : 0 < γ) (T : Tree) :
    (pathMax l (k + 1) T : ℝ≥0∞) ^ γ ≤
      ∑ i : Fin (degree T), (sib l T i : ℝ≥0∞) ^ γ *
        (pathMax l k (child T (i + 1)) : ℝ≥0∞) ^ γ := by
  let f : Fin (degree T) → ℝ≥0 := fun i => sib l T i * pathMax l k (child T (i + 1))
  change ((Finset.univ.sup f : ℝ≥0) : ℝ≥0∞) ^ γ ≤ _
  rw [coe_finset_sup]
  apply (finset_sup_pow_le_sum_pow Finset.univ (fun i => (f i : ℝ≥0∞)) γ hγ).trans_eq
  apply Finset.sum_congr rfl
  intro i _
  simp [f, mul_pow]

private noncomputable def siblingsRatio (l : ℝ) {n : ℕ} (i : Fin n)
    (xs : (↥(Finset.univ.erase i) → Tree)) : ℝ≥0∞ :=
  ENNReal.ofReal (l / (l + ∑ j : ↥(Finset.univ.erase i), escape l (xs j)))

private noncomputable def markedPath (l : ℝ) {n : ℕ} (i : Fin n) (k : ℕ)
    (xs : (↥({i} : Finset (Fin n)) → Tree)) : ℝ≥0∞ :=
  (pathMax l k (xs ⟨i, Finset.mem_singleton_self i⟩) : ℝ≥0∞)

private theorem measurable_siblingsRatio (l : ℝ) {n : ℕ} (i : Fin n) :
    Measurable (siblingsRatio l i) := by
  apply ENNReal.measurable_ofReal.comp
  apply measurable_const.div
  apply measurable_const.add
  exact Finset.univ.measurable_sum fun j _ => (measurable_escape l).comp (measurable_pi_apply j)

private theorem measurable_markedPath (l : ℝ) {n : ℕ} (i : Fin n) (k : ℕ) :
    Measurable (markedPath l i k) := by
  exact (measurable_pathMax l k).comp
    (measurable_pi_apply (⟨i, Finset.mem_singleton_self i⟩ : ↥({i} : Finset (Fin n))))

private theorem sib_nodeFin (l : ℝ) {n : ℕ} (ts : Fin n → Tree) (i : Fin n) :
    (sib l (nodeFin n ts) i : ℝ≥0∞) = siblingsRatio l i (fun j => ts j) := by
  simp only [sib, siblingsRatio, degree_nodeFin, children_nodeFin]
  change ENNReal.ofReal _ = ENNReal.ofReal _
  congr 2
  exact congrArg (fun x => l + x)
    (Finset.sum_coe_sort (Finset.univ.erase i) (fun j : Fin n => escape l (ts j))).symm

private theorem measurable_sibNodeFin (l : ℝ) {n : ℕ} (i : Fin n) :
    Measurable (fun ts : Fin n → Tree => (sib l (nodeFin n ts) i : ℝ≥0∞)) := by
  have hm : Measurable (fun ts : Fin n → Tree => (fun j : ↥(Finset.univ.erase i) => ts j)) :=
    Measurable.of_eval fun j => measurable_pi_apply j.val
  have hs := (measurable_siblingsRatio l i).comp hm
  simpa only [Function.comp_def, sib_nodeFin] using hs

private theorem lintegral_sib_mul_path (l : ℝ) {n : ℕ} (i : Fin n) (k γ : ℕ) :
    (∫⁻ ts : Fin n → Tree, (sib l (nodeFin n ts) i : ℝ≥0∞) ^ γ *
      (pathMax l k (ts i) : ℝ≥0∞) ^ γ ∂Measure.pi (fun _ : Fin n => GW μ)) =
    (∫⁻ ts : Fin n → Tree, (sib l (nodeFin n ts) i : ℝ≥0∞) ^ γ
        ∂Measure.pi (fun _ : Fin n => GW μ)) * pathMoment (μ := μ) l k γ := by
  let π : Measure (Fin n → Tree) := Measure.pi (fun _ : Fin n => GW μ)
  let S : Finset (Fin n) := Finset.univ.erase i
  let T : Finset (Fin n) := {i}
  have hST : Disjoint S T := by simp [S, T]
  have hbase : iIndepFun (fun (j : Fin n) (ts : Fin n → Tree) => ts j) π :=
    iIndepFun_pi (μ := fun _ : Fin n => GW μ) (fun _ => measurable_id.aemeasurable)
  have hind : IndepFun (fun ts (j : ↥S) => ts j) (fun ts (j : ↥T) => ts j) π :=
    hbase.indepFun_finset S T hST (fun _ => measurable_pi_apply _)
  let F : (↥S → Tree) → ℝ≥0∞ := fun xs => (siblingsRatio l i xs) ^ γ
  let G : (↥T → Tree) → ℝ≥0∞ := fun xs => (markedPath l i k xs) ^ γ
  have hF : Measurable F := (measurable_siblingsRatio l i).pow_const γ
  have hG : Measurable G := (measurable_markedPath l i k).pow_const γ
  have hFG : IndepFun (fun ts => F (fun j : ↥S => ts j))
      (fun ts => G (fun j : ↥T => ts j)) π := hind.comp hF hG
  have hf : Measurable (fun ts : Fin n → Tree => F (fun j : ↥S => ts j)) :=
    hF.comp (Measurable.of_eval fun j => measurable_pi_apply j.val)
  have hg : Measurable (fun ts : Fin n → Tree => G (fun j : ↥T => ts j)) :=
    hG.comp (Measurable.of_eval fun j => measurable_pi_apply j.val)
  have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hf hg hFG
  calc
    _ = ∫⁻ ts : Fin n → Tree, F (fun j : ↥S => ts j) * G (fun j : ↥T => ts j) ∂π := by
      apply lintegral_congr
      intro ts
      simp only [F, G, S, T, markedPath]
      rw [sib_nodeFin]
    _ = (∫⁻ ts : Fin n → Tree, F (fun j : ↥S => ts j) ∂π) *
        ∫⁻ ts : Fin n → Tree, G (fun j : ↥T => ts j) ∂π := hmul
    _ = _ := by
      congr 1
      · apply lintegral_congr
        intro ts
        simp only [F, S]
        rw [sib_nodeFin]
      · simpa only [pathMoment, Function.comp_def, G, T, markedPath] using
          (measurePreserving_eval (fun _ : Fin n => GW μ) i).lintegral_comp
            ((measurable_pathMax l k).pow_const γ)

private theorem pathMoment_succ_le (l : ℝ) (k γ : ℕ) (hγ : 0 < γ) :
    pathMoment (μ := μ) l (k + 1) γ ≤ rGamma (μ := μ) l γ * pathMoment (μ := μ) l k γ := by
  rw [pathMoment, lintegral_GW_eq_tsum _ ((measurable_pathMax l (k + 1)).pow_const γ)]
  have hroot (n : ℕ) :
      (∫⁻ ts : Fin n → Tree, (pathMax l (k + 1) (nodeFin n ts) : ℝ≥0∞) ^ γ
        ∂Measure.pi (fun _ : Fin n => GW μ)) ≤
      (∫⁻ ts : Fin n → Tree, sibMoment l (nodeFin n ts) γ
        ∂Measure.pi (fun _ : Fin n => GW μ)) * pathMoment (μ := μ) l k γ := by
    calc
      _ ≤ ∫⁻ ts : Fin n → Tree, ∑ i : Fin n, (sib l (nodeFin n ts) i : ℝ≥0∞) ^ γ *
          (pathMax l k (ts i) : ℝ≥0∞) ^ γ ∂Measure.pi (fun _ : Fin n => GW μ) := by
        refine lintegral_mono_ae (Filter.Eventually.of_forall fun ts : Fin n → Tree => ?_)
        convert pathMax_pow_le_sum l k γ hγ (nodeFin n ts) using 1
        apply Finset.sum_congr rfl
        intro i _
        simp only [degree_nodeFin, children_nodeFin]
      _ = ∑ i : Fin n, ∫⁻ ts : Fin n → Tree, (sib l (nodeFin n ts) i : ℝ≥0∞) ^ γ *
          (pathMax l k (ts i) : ℝ≥0∞) ^ γ ∂Measure.pi (fun _ : Fin n => GW μ) := by
        rw [lintegral_finsetSum]
        intro i _
        exact ((measurable_sibNodeFin l i).pow_const γ).mul
          ((measurable_pathMax l k).comp (measurable_pi_apply i) |>.pow_const γ)
      _ = ∑ i : Fin n, (∫⁻ ts : Fin n → Tree, (sib l (nodeFin n ts) i : ℝ≥0∞) ^ γ
          ∂Measure.pi (fun _ : Fin n => GW μ)) * pathMoment (μ := μ) l k γ := by
        exact Finset.sum_congr rfl (fun i _ => lintegral_sib_mul_path l i k γ)
      _ = _ := by
        rw [← Finset.sum_mul, ← lintegral_finsetSum]
        · rfl
        · intro i _
          exact (measurable_sibNodeFin l i).pow_const γ
  calc
    _ ≤ ∑' n : ℕ, (μ {n} * ∫⁻ ts : Fin n → Tree, sibMoment l (nodeFin n ts) γ
        ∂Measure.pi (fun _ : Fin n => GW μ)) * pathMoment (μ := μ) l k γ :=
      ENNReal.tsum_le_tsum fun n => by
        simpa only [mul_assoc] using mul_le_mul_right (hroot n) (μ {n})
    _ = (∑' n : ℕ, μ {n} * ∫⁻ ts : Fin n → Tree, sibMoment l (nodeFin n ts) γ
        ∂Measure.pi (fun _ : Fin n => GW μ)) * pathMoment (μ := μ) l k γ := by
      rw [ENNReal.tsum_mul_right]
    _ = rGamma (μ := μ) l γ * pathMoment (μ := μ) l k γ := by
      rw [rGamma, lintegral_GW_eq_tsum _ (measurable_sibMoment l γ)]

theorem pathMoment_le_pow (l : ℝ) (k γ : ℕ) (hγ : 0 < γ) :
    pathMoment (μ := μ) l k γ ≤ rGamma (μ := μ) l γ ^ k := by
  induction k with
  | zero => simp [pathMoment, pathMax]
  | succ k ih =>
      calc
        pathMoment (μ := μ) l (k + 1) γ ≤ rGamma (μ := μ) l γ * pathMoment (μ := μ) l k γ :=
          pathMoment_succ_le l k γ hγ
        _ ≤ rGamma (μ := μ) l γ * rGamma (μ := μ) l γ ^ k := mul_le_mul_right ih _
        _ = rGamma (μ := μ) l γ ^ (k + 1) := by rw [pow_succ, mul_comm]

private theorem sib_lt_one {l : ℝ} (hl : 0 < l) {T : Tree} (hdeg : 2 ≤ degree T)
    (hpos : ∀ i : Fin (degree T), 0 < escape l (child T (i + 1))) (i : Fin (degree T)) :
    (sib l T i : ℝ≥0∞) < 1 := by
  let j : Fin (degree T) := ⟨if i.val = 0 then 1 else 0, by split <;> omega⟩
  have hji : j ≠ i := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp [j] at hv
    split at hv <;> omega
  have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
  have hsum : 0 < ∑ j ∈ Finset.univ.erase i, escape l (child T (j + 1)) :=
    Finset.sum_pos (fun j _ => hpos j) ⟨j, hjmem⟩
  have hr : (sib l T i : ℝ) < 1 := by
    rw [coe_sib hl]
    apply (div_lt_one (add_pos_of_pos_of_nonneg hl hsum.le)).2
    linarith
  exact_mod_cast hr

private theorem sibMoment_le_degree {l : ℝ} (hl : 0 < l) (T : Tree) (γ : ℕ) :
    sibMoment l T γ ≤ (degree T : ℝ≥0∞) := by
  calc
    sibMoment l T γ ≤ ∑ _i : Fin (degree T), 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_one₀ bot_le (by exact_mod_cast sib_le_one hl T i)
    _ = (degree T : ℝ≥0∞) := by simp

private theorem lintegral_degree : ∫⁻ T, (degree T : ℝ≥0∞) ∂GW μ = ∫⁻ k, (k : ℝ≥0∞) ∂μ := by
  calc
    _ = ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂(GW μ).map degree :=
      (lintegral_map (measurable_of_countable _) continuous_degree.measurable).symm
    _ = _ := by rw [bienaymeLaw_map_degree]

private theorem rGamma_ne_top (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (γ : ℕ) :
    rGamma (μ := μ) l γ ≠ ⊤ := by
  apply ne_top_of_le_ne_top h.mean_lt_top.ne
  apply (lintegral_mono (fun T : Tree => sibMoment_le_degree hl T γ)).trans_eq
  exact lintegral_degree

private noncomputable def unaryIndicator (T : Tree) : ℝ≥0∞ := if degree T = 1 then 1 else 0

private theorem tendsto_sibMoment (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ) :
    ∀ᵐ T ∂GW μ, Tendsto (fun γ : ℕ => sibMoment l T γ) atTop (𝓝 (unaryIndicator T)) := by
  filter_upwards [LPPMonotonicityProof.RTL.Leafless.ae_present_offspring_pos μ h.zero,
    ae_escape_pos_subtrees h hl hlm] with T hleaf hesc
  have hpos (i : Fin (degree T)) : 0 < escape l (child T (i + 1)) := by
    have hp : Present T [i.val + 1] := ⟨Nat.succ_pos _, i.isLt, present_nil T⟩
    simpa only [subtree_cons, subtree_nil] using hesc [i.val + 1] hp
  by_cases h1 : degree T = 1
  · let i0 : Fin (degree T) := ⟨0, by omega⟩
    have hempty : Finset.univ.erase i0 = ∅ := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.notMem_empty, iff_false]
      intro hj
      apply hj
      apply Fin.ext
      have hjlt := j.isLt
      have hi0lt := i0.isLt
      dsimp [i0]
      omega
    have hsib : (sib l T i0 : ℝ≥0∞) = 1 := by
      have hr : (sib l T i0 : ℝ) = 1 := by
        rw [coe_sib hl, hempty, Finset.sum_empty, add_zero, div_self hl.ne']
      exact_mod_cast hr
    have heq : (fun γ : ℕ => sibMoment l T γ) = fun _ => 1 := by
      funext γ
      calc
        sibMoment l T γ = (sib l T i0 : ℝ≥0∞) ^ γ := by
          unfold sibMoment
          apply Finset.sum_eq_single i0
          · intro j _ hj
            exfalso
            apply hj
            apply Fin.ext
            have hjlt := j.isLt
            have hi0lt := i0.isLt
            dsimp [i0] at hi0lt
            omega
          · simp
        _ = 1 := by rw [hsib, one_pow]
    rw [unaryIndicator, if_pos h1, heq]
    exact tendsto_const_nhds
  · have hdeg : 2 ≤ degree T := by
      have hroot := hleaf [] (present_nil T)
      change 0 < degree T at hroot
      omega
    have ht : Tendsto (fun γ : ℕ => ∑ i : Fin (degree T), (sib l T i : ℝ≥0∞) ^ γ)
        atTop (𝓝 (∑ _i : Fin (degree T), (0 : ℝ≥0∞))) :=
      tendsto_finsetSum Finset.univ (fun i _ =>
        ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (sib_lt_one hl hdeg hpos i))
    rw [unaryIndicator, if_neg h1]
    simpa only [sibMoment, Finset.sum_const_zero] using ht

private theorem lintegral_unaryIndicator : ∫⁻ T, unaryIndicator T ∂GW μ = μ {1} := by
  rw [show (fun T => unaryIndicator T) = {T : Tree | degree T = 1}.indicator 1 by
    funext T
    simp [unaryIndicator, Set.indicator_apply]]
  calc
    _ = GW μ {T : Tree | degree T = 1} :=
      lintegral_indicator_one (μ := GW μ)
        (continuous_degree.measurable (measurableSet_singleton 1))
    _ = μ {1} := by
      have hm := congrArg (fun ν : Measure ℕ => ν {1}) (bienaymeLaw_map_degree μ)
      change GW μ (degree ⁻¹' {1}) = μ {1}
      rw [Measure.map_apply continuous_degree.measurable (measurableSet_singleton 1)] at hm
      exact hm

theorem tendsto_rGamma (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ) :
    Tendsto (fun γ : ℕ => rGamma (μ := μ) l γ) atTop (𝓝 (μ {1})) := by
  rw [← lintegral_unaryIndicator]
  apply tendsto_lintegral_of_dominated_convergence (fun T : Tree => (degree T : ℝ≥0∞))
  · exact fun γ => measurable_sibMoment l γ
  · exact fun γ => Filter.Eventually.of_forall fun T => sibMoment_le_degree hl T γ
  · rw [lintegral_degree]
    exact ne_of_lt h.mean_lt_top
  · exact tendsto_sibMoment h hl hlm

private theorem unary_mass_lt_one (h : OffspringHyp μ) : μ {1} < 1 := by
  have hp : p1 μ < 1 := by
    have hsum := p1_add_pBr h
    have hb := pBr_pos h
    linarith
  exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mp hp

theorem exists_rGamma_lt_one (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l) (hlm : l < mean μ) :
    ∃ γ : ℕ, 0 < γ ∧ rGamma (μ := μ) l γ < 1 := by
  have hev := (tendsto_rGamma h hl hlm).eventually (gt_mem_nhds (unary_mass_lt_one h))
  obtain ⟨γ, hγ, hγ1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  exact ⟨γ, zero_lt_one.trans_le hγ1, hγ⟩

private theorem measurable_pathMax_real (l : ℝ) (k : ℕ) :
    Measurable (fun T => (pathMax l k T : ℝ)) := by
  have hm := (measurable_pathMax l k).ennreal_toReal
  simpa only [Function.comp_def, ENNReal.toReal, ENNReal.toNNReal_coe] using hm

private theorem pathMax_real_nonneg (l : ℝ) (k : ℕ) (T : Tree) : 0 ≤ (pathMax l k T : ℝ) :=
  (pathMax l k T).2

private theorem pathMax_real_le_one {l : ℝ} (hl : 0 < l) (k : ℕ) (T : Tree) :
    (pathMax l k T : ℝ) ≤ 1 := by exact_mod_cast pathMax_le_one hl k T

private theorem integrable_pathMax_rpow {l : ℝ} (hl : 0 < l) (k : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun T => (pathMax l k T : ℝ) ^ q) (GW μ) := by
  apply Integrable.of_bound
    (((Real.continuous_rpow_const hq).measurable.comp (measurable_pathMax_real l k))).aestronglyMeasurable 1
  filter_upwards with T
  simp only [Function.comp_def, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (pathMax_real_nonneg l k T) q)]
  exact Real.rpow_le_one (pathMax_real_nonneg l k T) (pathMax_real_le_one hl k T) hq

private noncomputable def realPathMoment (l : ℝ) (k : ℕ) (q : ℝ) : ℝ :=
  ∫ T, (pathMax l k T : ℝ) ^ q ∂GW μ

private theorem realPathMoment_nonneg (l : ℝ) (k : ℕ) (q : ℝ) :
    0 ≤ realPathMoment (μ := μ) l k q := by
  apply integral_nonneg_of_ae
  exact Filter.Eventually.of_forall fun T => Real.rpow_nonneg (pathMax_real_nonneg l k T) q

private theorem ofReal_realPathMoment_nat {l : ℝ} (hl : 0 < l) (k γ : ℕ) :
    ENNReal.ofReal (realPathMoment (μ := μ) l k (γ : ℝ)) = pathMoment (μ := μ) l k γ := by
  rw [realPathMoment, ofReal_integral_eq_lintegral_ofReal
    (integrable_pathMax_rpow hl k (γ : ℝ) (Nat.cast_nonneg γ))
    (Filter.Eventually.of_forall fun T => Real.rpow_nonneg (pathMax_real_nonneg l k T) (γ : ℝ))]
  apply lintegral_congr
  intro T
  rw [Real.rpow_natCast, ENNReal.ofReal_pow (pathMax_real_nonneg l k T)]
  exact congrArg (fun x : ℝ≥0∞ => x ^ γ) (ENNReal.coe_nnreal_eq _).symm

private theorem realPathMoment_le_rGamma_pow (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (k γ : ℕ) (hγ : 0 < γ) :
    realPathMoment (μ := μ) l k (γ : ℝ) ≤ (rGamma (μ := μ) l γ).toReal ^ k := by
  have hp := pathMoment_le_pow (μ := μ) l k γ hγ
  rw [← ofReal_realPathMoment_nat hl k γ] at hp
  have hpowTop : rGamma (μ := μ) l γ ^ k ≠ ⊤ := ENNReal.pow_ne_top (rGamma_ne_top h hl γ)
  have ht := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hpowTop).2 hp
  simpa only [ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (realPathMoment_nonneg (μ := μ) l k (γ : ℝ))] using ht

private theorem realPathMoment_one_le_root {l : ℝ} (hl : 0 < l) (k γ : ℕ) (hγ : 0 < γ) :
    realPathMoment (μ := μ) l k 1 ≤ realPathMoment (μ := μ) l k (γ : ℝ) ^ ((γ : ℝ)⁻¹) := by
  let p : ℝ := (γ : ℝ)⁻¹
  have hp : 0 ≤ p := inv_nonneg.mpr (Nat.cast_nonneg γ)
  have hp1 : p ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact_mod_cast hγ
  have hfi := integrable_pathMax_rpow (μ := μ) hl k (γ : ℝ) (Nat.cast_nonneg γ)
  have hpow (T : Tree) : ((pathMax l k T : ℝ) ^ (γ : ℝ)) ^ p = (pathMax l k T : ℝ) := by
    have hmul : (γ : ℝ) * p = 1 := by
      dsimp [p]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hγ.ne')
    calc
      _ = (pathMax l k T : ℝ) ^ ((γ : ℝ) * p) :=
        (Real.rpow_mul (pathMax_real_nonneg l k T) (γ : ℝ) p).symm
      _ = (pathMax l k T : ℝ) ^ (1 : ℝ) := by rw [hmul]
      _ = (pathMax l k T : ℝ) := Real.rpow_one _
  have hgi : Integrable ((fun x : ℝ => x ^ p) ∘ fun T => (pathMax l k T : ℝ) ^ (γ : ℝ)) (GW μ) := by
    have hi := integrable_pathMax_rpow (μ := μ) hl k 1 zero_le_one
    apply hi.congr
    filter_upwards with T
    simp only [Function.comp_def, Real.rpow_one]
    exact (hpow T).symm
  have hj := (Real.concaveOn_rpow hp hp1).le_map_integral
    (Real.continuous_rpow_const hp).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun T => Real.rpow_nonneg (pathMax_real_nonneg l k T) (γ : ℝ)) hfi hgi
  simpa only [Function.comp_def, hpow, realPathMoment, p, Real.rpow_one] using hj

private theorem geometric_pathMoment (h : OffspringHyp μ) {l : ℝ} (hl : 0 < l)
    (γ : ℕ) (hγ : 0 < γ) (hr : rGamma (μ := μ) l γ < 1) :
    ∃ ρ : ℝ≥0∞, ρ < 1 ∧ ∀ k : ℕ, pathMoment (μ := μ) l k 1 ≤ ρ ^ k := by
  let p : ℝ := (γ : ℝ)⁻¹
  let r : ℝ := (rGamma (μ := μ) l γ).toReal ^ p
  have hp : 0 < p := inv_pos.mpr (Nat.cast_pos.mpr hγ)
  have hrTop : rGamma (μ := μ) l γ ≠ ⊤ := rGamma_ne_top h hl γ
  have hrReal : (rGamma (μ := μ) l γ).toReal < 1 :=
    (ENNReal.toReal_lt_toReal hrTop ENNReal.one_ne_top).2 hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg ENNReal.toReal_nonneg p
  have hr1 : r < 1 := Real.rpow_lt_one ENNReal.toReal_nonneg hrReal hp
  refine ⟨ENNReal.ofReal r, ENNReal.ofReal_lt_one.mpr hr1, fun k => ?_⟩
  have hfirst := (realPathMoment_one_le_root (μ := μ) hl k γ hγ).trans
    (Real.rpow_le_rpow (realPathMoment_nonneg (μ := μ) l k (γ : ℝ))
      (realPathMoment_le_rGamma_pow h hl k γ hγ) hp.le)
  have hrpow : realPathMoment (μ := μ) l k 1 ≤ r ^ k := by
    apply hfirst.trans_eq
    change ((rGamma (μ := μ) l γ).toReal ^ k) ^ p = r ^ k
    calc
      _ = (rGamma (μ := μ) l γ).toReal ^ ((k : ℝ) * p) :=
        (Real.rpow_natCast_mul ENNReal.toReal_nonneg k p).symm
      _ = (rGamma (μ := μ) l γ).toReal ^ (p * (k : ℝ)) := by rw [mul_comm]
      _ = r ^ k := Real.rpow_mul_natCast ENNReal.toReal_nonneg p k
  calc
    pathMoment (μ := μ) l k 1 = ENNReal.ofReal (realPathMoment (μ := μ) l k 1) := by
      simpa only [Nat.cast_one] using (ofReal_realPathMoment_nat hl k 1).symm
    _ ≤ ENNReal.ofReal (r ^ k) := ENNReal.ofReal_le_ofReal hrpow
    _ = ENNReal.ofReal r ^ k := ENNReal.ofReal_pow hr0 k

/-- The Galton--Watson integral of every compact-bias response envelope is finite. -/
theorem lintegral_envelope_lt_top (h : OffspringHyp μ) {lNeg lPos : ℝ}
    (h0 : 0 < lNeg) (hle : lNeg ≤ lPos) (hm : lPos < mean μ) :
    ∫⁻ T, envelope lNeg lPos T ∂GW μ < ⊤ := by
  have hlPos : 0 < lPos := h0.trans_le hle
  obtain ⟨γ, hγ, hrγ⟩ := exists_rGamma_lt_one h hlPos hm
  obtain ⟨ρ, hρ, hbound⟩ := geometric_pathMoment h hlPos γ hγ hrγ
  have hsum : (∑' k : ℕ, pathMoment (μ := μ) lPos (k + 1) 1) ≤ ∑' k : ℕ, ρ ^ (k + 1) :=
    ENNReal.tsum_le_tsum (fun k => hbound (k + 1))
  have heq : (∫⁻ T, envelope lNeg lPos T ∂GW μ) =
      (ENNReal.ofReal lNeg)⁻¹ * ∑' k : ℕ, pathMoment (μ := μ) lPos (k + 1) 1 := by
    unfold envelope
    rw [lintegral_const_mul _ (Measurable.tsum fun k => measurable_pathMax lPos (k + 1)),
      lintegral_tsum (fun k => (measurable_pathMax lPos (k + 1)).aemeasurable)]
    congr 1
    apply tsum_congr
    intro k
    simp [pathMoment]
  rw [heq]
  calc
    _ ≤ (ENNReal.ofReal lNeg)⁻¹ * ∑' k : ℕ, ρ ^ (k + 1) := mul_le_mul_right hsum _
    _ = (ENNReal.ofReal lNeg)⁻¹ * (ρ * (1 - ρ)⁻¹) := by rw [ENNReal.tsum_geometric_add_one]
    _ < ⊤ := by
      apply ENNReal.mul_lt_top
      · exact (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr h0)).trans_le le_top
      · apply ENNReal.mul_lt_top
        · exact hρ.trans_le le_top
        · exact ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hρ)

end LPPMonotonicityProof.Analytic
