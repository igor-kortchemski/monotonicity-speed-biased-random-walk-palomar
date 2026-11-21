module

public import LPPMonotonicityProof.Speed.Escape.Capped
public import LPPMonotonicityProof.Speed.Interface.Subtrees
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Expected energy of the capped finite flow

This module bounds the expected energy of the unit flow carried by the capped
generations, a step of the direct proof of Lemma 2.1(iv) (`lem:escape`).  The proof
uses disjoint coordinate blocks under the infinite product law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- Energy contributed by one level of the capped finite flow. -/
noncomputable def levelEnergy (B : ℕ) (b : ℝ) (ω : Offspring) (N k : ℕ) : ℝ :=
  generationSum ω (fun w => capFlow B b ω N w ^ 2) [] k

/-- Weighted energy of the capped finite flow through height `N`. -/
noncomputable def energy (B : ℕ) (b l : ℝ) (ω : Offspring) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), l ^ k * levelEnergy B b ω N k

@[simp] theorem levelEnergy_nonneg (B : ℕ) (b : ℝ) (ω : Offspring) (N k : ℕ) :
    0 ≤ levelEnergy B b ω N k := by
  apply Finset.sum_nonneg
  intro w hw
  positivity

@[simp] theorem energy_nonneg (B : ℕ) (b : ℝ) {l : ℝ} (hl : 0 ≤ l)
    (ω : Offspring) (N : ℕ) : 0 ≤ energy B b l ω N := by
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (pow_nonneg hl _) (levelEnergy_nonneg _ _ _ _ _)

/-- Capped generation size is measurable at a fixed address. -/
theorem measurable_capZ (B : ℕ) (v : Address) (j : ℕ) :
    Measurable (fun ω => capZ B ω v j) := by
  rw [show (fun ω => capZ B ω v j) =
    (fun T => generationSize T j) ∘ (fun ω => cappedTree B ω v) by
      funext ω; exact capZ_eq_generationSize B ω v j]
  exact (measurable_generationSize j).comp (measurable_cappedTree B v)

/-- Capped-generation membership at a fixed address is measurable. -/
theorem measurableSet_mem_capGen (B : ℕ) (w : Address) (k : ℕ) :
    MeasurableSet {ω | w ∈ capGen B ω [] k} := by
  have hp : MeasurableSet {ω | Present (cappedTree B ω []) w} :=
    (measurableSet_present w).preimage (measurable_cappedTree B [])
  have hk : MeasurableSet {ω : Offspring | w.length = k} := by
    by_cases h : w.length = k <;> simp [h]
  simpa only [Set.ofPred_and, mem_capGen_root] using hp.inter hk

/-- The capped flow at a fixed address is measurable. -/
theorem measurable_capFlow (B : ℕ) (b : ℝ) (N : ℕ) (w : Address) :
    Measurable (fun ω => capFlow B b ω N w) := by
  apply Measurable.ite (measurableSet_mem_capGen B w w.length)
  · exact measurable_const.mul
      ((show Measurable (fun n : ℕ => (n : ℝ)) by fun_prop).comp
        (measurable_capZ B w (N - w.length)))
  · exact measurable_const

/-- All addresses through depth `k` using one-based entries at most `B`. -/
def capAddr (B : ℕ) : ℕ → Finset Address
  | 0 => {[]}
  | k + 1 => (Finset.range B).biUnion fun i =>
      (capAddr B k).image fun w => w ++ [i + 1]

/-- Every address in `capAddr B k` has length `k`. -/
theorem length_of_mem_capAddr (B : ℕ) : ∀ (k : ℕ) (w : Address),
    w ∈ capAddr B k → w.length = k := by
  intro k
  induction k with
  | zero => intro w hw; simpa [capAddr] using hw
  | succ k ih =>
      intro w hw
      rw [capAddr] at hw
      obtain ⟨i, hi, hw⟩ := Finset.mem_biUnion.mp hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      simp [ih v hv]

/-- A valid one-based child of a raw-generation vertex belongs to the next raw
generation. -/
theorem mem_generation_offChild (ω : Offspring) : ∀ (k : ℕ) (u v : Address),
    v ∈ _root_.generation ω u k → ∀ i : Fin (ω v),
      offChild ω v i ∈ _root_.generation ω u (k + 1) := by
  intro k
  induction k with
  | zero =>
      intro u v hv i
      have hv0 : v = u := by simpa [_root_.generation] using hv
      subst v
      rw [_root_.generation]
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      simp [_root_.generation, offChild]
  | succ k ih =>
      intro u v hv i
      rw [_root_.generation] at hv ⊢
      obtain ⟨j, hj, hv⟩ := Finset.mem_biUnion.mp hv
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_univ _, ?_⟩
      exact ih (offChild ω u j) v hv i

/-- Capped-generation membership is contained in the raw generation. -/
theorem capGen_subset_generation (B : ℕ) (ω : Offspring) :
    ∀ k, capGen B ω [] k ⊆ _root_.generation ω [] k := by
  intro k
  induction k with
  | zero =>
      intro w hw
      have hwlen : w.length = 0 := ((mem_capGen_root B ω w 0).1 hw).2
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero hwlen
      subst w
      simp [_root_.generation]
  | succ k ih =>
      intro w hw
      have hwlen : w.length = k + 1 := ((mem_capGen_root B ω w (k + 1)).1 hw).2
      have hwne : w ≠ [] := by intro h; simp [h] at hwlen
      let v := w.dropLast
      let i := w.getLast hwne
      have hwvi : v ++ [i] = w := List.dropLast_append_getLast hwne
      have hw' : v ++ [i] ∈ capGen B ω [] (k + 1) := by simpa only [hwvi] using hw
      have hv := (mem_capGen_append_one B ω v i k).1 hw'
      have hvgen : v ∈ _root_.generation ω [] k := ih hv.1
      let j : Fin (ω v) := ⟨i - 1, by omega⟩
      have hj : offChild ω v j = v ++ [i] := by simp [offChild, j, Nat.sub_add_cancel hv.2.1]
      have hc := mem_generation_offChild ω k [] v hvgen j
      simpa only [hj, hwvi] using hc

/-- Every capped vertex at level `k` lies in the deterministic address set. -/
theorem capGen_subset_capAddr (B : ℕ) (ω : Offspring) :
    ∀ k, capGen B ω [] k ⊆ capAddr B k := by
  intro k
  induction k with
  | zero =>
      intro w hw
      have hwlen : w.length = 0 := ((mem_capGen_root B ω w 0).1 hw).2
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero hwlen
      subst w
      simp [capAddr]
  | succ k ih =>
      intro w hw
      have hwlen : w.length = k + 1 := ((mem_capGen_root B ω w (k + 1)).1 hw).2
      have hwne : w ≠ [] := by intro h; simp [h] at hwlen
      let v := w.dropLast
      let i := w.getLast hwne
      have hwvi : v ++ [i] = w := List.dropLast_append_getLast hwne
      have hw' : v ++ [i] ∈ capGen B ω [] (k + 1) := by simpa only [hwvi] using hw
      have hv := (mem_capGen_append_one B ω v i k).1 hw'
      rw [hwvi.symm, capAddr]
      apply Finset.mem_biUnion.mpr
      refine ⟨i - 1, Finset.mem_range.mpr (by omega), ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨v, ih hv.1, by simp [Nat.sub_add_cancel hv.2.1]⟩

/-- A level of capped-flow energy can be summed over the deterministic capped
address set instead of the random raw generation. -/
theorem generationSum_capFlow_sq (B : ℕ) (b : ℝ) (ω : Offspring) (N k : ℕ) :
    generationSum ω (fun w => capFlow B b ω N w ^ 2) [] k =
      ∑ w ∈ capAddr B k, capFlow B b ω N w ^ 2 := by
  unfold generationSum
  have hraw : capGen B ω [] k ⊆ _root_.generation ω [] k := capGen_subset_generation B ω k
  have haddr : capGen B ω [] k ⊆ capAddr B k := capGen_subset_capAddr B ω k
  calc
    _ = ∑ w ∈ capGen B ω [] k, capFlow B b ω N w ^ 2 := by
      symm
      apply Finset.sum_subset hraw
      intro w hw hwc
      have hwlen : w.length = k := by simpa using length_of_mem_generation ω k [] w hw
      have hn : w ∉ capGen B ω [] w.length := by
        simpa only [hwlen] using hwc
      rw [capFlow, ite_eq_right hn]
      norm_num
    _ = _ := by
      apply Finset.sum_subset haddr
      intro w hw hwc
      have hwlen : w.length = k := length_of_mem_capAddr B k w hw
      have hn : w ∉ capGen B ω [] w.length := by
        simpa only [hwlen] using hwc
      rw [capFlow, ite_eq_right hn]
      norm_num

/-- Each level energy is measurable. -/
theorem measurable_levelEnergy (B : ℕ) (b : ℝ) (N k : ℕ) :
    Measurable (fun ω => levelEnergy B b ω N k) := by
  simp only [levelEnergy, generationSum_capFlow_sq]
  exact Finset.measurable_sum _ fun w _ => (measurable_capFlow B b N w).pow_const 2

/-- Each weighted finite-horizon energy is measurable. -/
theorem measurable_energy (B : ℕ) (b l : ℝ) (N : ℕ) :
    Measurable (fun ω => energy B b l ω N) := by
  unfold energy
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_levelEnergy B b N k)

/-- Shifted capped-generation second moments do not depend on the base address. -/
theorem lintegral_capZ_shift_sq (B : ℕ) (w : Address) (j : ℕ) :
    (∫⁻ ω, (capZ B ω w j : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ) =
      ∫⁻ ω, (capZ B ω [] j : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ := by
  let shift : Offspring → Offspring := fun ω u => ω (w ++ u)
  have hm : Measurable shift := Measurable.of_eval fun u => measurable_pi_apply (w ++ u)
  have hmp : MeasurePreserving shift (offspringFieldLaw μ) (offspringFieldLaw μ) :=
    ⟨hm, map_shift_offspringFieldLaw μ w⟩
  have hf : Measurable (fun ω => (capZ B ω [] j : ℝ≥0∞) ^ 2) :=
    ((show Measurable (fun n : ℕ => (n : ℝ≥0∞)) by fun_prop).comp
      (measurable_capZ B [] j)).pow_const 2
  have heq : (fun ω => capZ B (shift ω) [] j) = (fun ω => capZ B ω w j) := by
    funext ω
    have ht : cappedTree B (shift ω) [] = cappedTree B ω w := by
      apply congrArg prune
      funext u
      rfl
    simp only [capZ_eq_generationSize, ht]
  calc
    _ = ∫⁻ ω, (capZ B (shift ω) [] j : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ := by
      apply lintegral_congr
      intro ω
      rw [congrFun heq ω]
    _ = _ := hmp.lintegral_comp hf

/-- Independence of the strict-prefix indicator and a squared capped generation
below the address. -/
theorem indepFun_capGen_capZ_sq (B : ℕ) (w : Address) (k j : ℕ) :
    IndepFun
      (fun ω => {ω | w ∈ capGen B ω [] k}.indicator (1 : Offspring → ℝ≥0∞) ω)
      (fun ω => (capZ B ω w j : ℝ≥0∞) ^ 2) (offspringFieldLaw μ) := by
  classical
  let S : Set Address := {p | p <+: w ∧ p ≠ w}
  let T : Set Address := {a | ∃ u, a = w ++ u}
  let f : Offspring → ℝ≥0∞ := fun ω =>
    {ω | w ∈ capGen B ω [] k}.indicator (1 : Offspring → ℝ≥0∞) ω
  let g : Offspring → ℝ≥0∞ := fun ω => (capZ B ω w j : ℝ≥0∞) ^ 2
  let extendS : (Π _ : S, ℕ) → Offspring := fun x a =>
    if h : a ∈ S then x ⟨a, h⟩ else 0
  let extendT : (Π _ : T, ℕ) → Offspring := fun x a =>
    if h : a ∈ T then x ⟨a, h⟩ else 0
  have hmS : Measurable extendS := Measurable.of_eval fun a => by
    by_cases ha : a ∈ S
    · simpa only [extendS, dite_eq_left ha] using measurable_pi_apply (⟨a, ha⟩ : S)
    · simp [extendS, ha]
  have hmT : Measurable extendT := Measurable.of_eval fun a => by
    by_cases ha : a ∈ T
    · simpa only [extendT, dite_eq_left ha] using measurable_pi_apply (⟨a, ha⟩ : T)
    · simp [extendT, ha]
  have hcoord : iIndepFun (fun a : Address => fun ω : Offspring => ω a)
      (offspringFieldLaw μ) := iIndepFun_infinitePi fun _ => measurable_id
  have hdisj : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro p hpS hpT
    obtain ⟨u, rfl⟩ := hpT
    have hle : (w ++ u).length ≤ w.length := hpS.1.length_le
    have hle' : w.length ≤ (w ++ u).length := by simp
    have hu : u = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_append] at hle hle'
      omega
    exact hpS.2 (by simp [hu])
  have hblock := hcoord.indepFun_set S T hdisj fun a => measurable_pi_apply a
  have hfdep : DependsOn f S := by
    intro ω η h
    have hm := mem_capGen_dependsOn B w k h
    simp only [f, Set.indicator]
    split_ifs <;> simp_all
  have hgdep : DependsOn g T := by
    intro ω η h
    have hz := capZ_dependsOn B w j h
    simp only [g, hz]
  have hfactor : f = (f ∘ extendS) ∘ S.domRestrict := by
    funext ω
    apply hfdep
    intro a ha
    simp [extendS, Set.domRestrict, ha]
  have hgfactor : g = (g ∘ extendT) ∘ T.domRestrict := by
    funext ω
    apply hgdep
    intro a ha
    simp [extendT, Set.domRestrict, ha]
  have hfmeas : Measurable f := measurable_one.indicator (measurableSet_mem_capGen B w k)
  have hgmeas : Measurable g :=
    ((show Measurable (fun n : ℕ => (n : ℝ≥0∞)) by fun_prop).comp
      (measurable_capZ B w j)).pow_const 2
  change IndepFun f g (offspringFieldLaw μ)
  rw [hfactor, hgfactor]
  exact hblock.comp (hfmeas.comp hmS) (hgmeas.comp hmT)

/-- Exact fixed-address expectation factorization for the squared capped flow. -/
theorem lintegral_capFlow_sq (B : ℕ) (b : ℝ) (N k : ℕ) (w : Address)
    (hw : w.length = k) :
    (∫⁻ ω, ENNReal.ofReal (capFlow B b ω N w ^ 2) ∂offspringFieldLaw μ) =
      ENNReal.ofReal ((b⁻¹ ^ N) ^ 2) * offspringFieldLaw μ {ω | w ∈ capGen B ω [] k} *
        ∫⁻ ω, (capZ B ω [] (N - k) : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ := by
  let A : Offspring → ℝ≥0∞ := fun ω =>
    {ω | w ∈ capGen B ω [] k}.indicator (1 : Offspring → ℝ≥0∞) ω
  let Z : Offspring → ℝ≥0∞ := fun ω => (capZ B ω w (N - k) : ℝ≥0∞) ^ 2
  have hA : Measurable A := measurable_one.indicator (measurableSet_mem_capGen B w k)
  have hZ : Measurable Z :=
    ((show Measurable (fun n : ℕ => (n : ℝ≥0∞)) by fun_prop).comp
      (measurable_capZ B w (N - k))).pow_const 2
  have hind : IndepFun A Z (offspringFieldLaw μ) := indepFun_capGen_capZ_sq B w k (N - k)
  have hpoint (ω : Offspring) : ENNReal.ofReal (capFlow B b ω N w ^ 2) =
      ENNReal.ofReal ((b⁻¹ ^ N) ^ 2) * (A ω * Z ω) := by
    by_cases hm : w ∈ capGen B ω [] k
    · have hm' : w ∈ capGen B ω [] w.length := by simpa only [hw] using hm
      have hAω : A ω = 1 := by
        change {ω | w ∈ capGen B ω [] k}.indicator (1 : Offspring → ℝ≥0∞) ω = 1
        exact Set.indicator_of_mem (s := {ω : Offspring | w ∈ capGen B ω [] k}) hm (1 : Offspring → ℝ≥0∞)
      rw [capFlow, ite_eq_left hm', hAω]
      simp only [one_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _), hw]
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    · have hm' : w ∉ capGen B ω [] w.length := by simpa only [hw] using hm
      have hAω : A ω = 0 := by
        change {ω | w ∈ capGen B ω [] k}.indicator (1 : Offspring → ℝ≥0∞) ω = 0
        exact Set.indicator_of_notMem (s := {ω : Offspring | w ∈ capGen B ω [] k}) hm (1 : Offspring → ℝ≥0∞)
      rw [capFlow, ite_eq_right hm', hAω]
      simp [Z]
  calc
    _ = ∫⁻ ω, ENNReal.ofReal ((b⁻¹ ^ N) ^ 2) * (A ω * Z ω) ∂offspringFieldLaw μ :=
      lintegral_congr hpoint
    _ = ENNReal.ofReal ((b⁻¹ ^ N) ^ 2) * ∫⁻ ω, A ω * Z ω ∂offspringFieldLaw μ := by
      exact lintegral_const_mul _ (f := fun ω => A ω * Z ω) (hA.mul hZ)
    _ = ENNReal.ofReal ((b⁻¹ ^ N) ^ 2) * ((∫⁻ ω, A ω ∂offspringFieldLaw μ) *
        ∫⁻ ω, Z ω ∂offspringFieldLaw μ) := by
      have hfac := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hA hZ hind
      change (∫⁻ ω, A ω * Z ω ∂offspringFieldLaw μ) = _ at hfac
      rw [hfac]
    _ = _ := by
      have hshift := lintegral_capZ_shift_sq (μ := μ) B w (N - k)
      dsimp only [A, Z]
      rw [lintegral_indicator_one (measurableSet_mem_capGen B w k), hshift]
      ring

/-- Sum of the strict-prefix membership probabilities over all capped addresses. -/
theorem sum_measure_capGen (B : ℕ) (k : ℕ) :
    (∑ w ∈ capAddr B k, offspringFieldLaw μ {ω | w ∈ capGen B ω [] k}) =
      cappedMean μ B ^ k := by
  have hsum : ∀ ω : Offspring,
      (∑ w ∈ capAddr B k,
        {ω | w ∈ capGen B ω [] k}.indicator (1 : Offspring → ℝ≥0∞) ω) =
        (capZ B ω [] k : ℝ≥0∞) := by
    intro ω
    classical
    have hfilter : {w ∈ capAddr B k | w ∈ capGen B ω [] k} = capGen B ω [] k := by
      ext w
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨capGen_subset_capAddr B ω k h, h⟩⟩
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, Finset.sum_ite_mem]
    rw [Finset.inter_eq_right.mpr (capGen_subset_capAddr B ω k)]
    simp [capZ]
  calc
    _ = ∑ w ∈ capAddr B k, ∫⁻ ω,
        {ω | w ∈ capGen B ω [] k}.indicator (1 : Offspring → ℝ≥0∞) ω ∂offspringFieldLaw μ := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [lintegral_indicator_one (measurableSet_mem_capGen B w k)]
    _ = ∫⁻ ω, ∑ w ∈ capAddr B k,
        {ω | w ∈ capGen B ω [] k}.indicator (1 : Offspring → ℝ≥0∞) ω ∂offspringFieldLaw μ := by
      symm
      apply lintegral_finsetSum
      intro w hw
      exact measurable_one.indicator (measurableSet_mem_capGen B w k)
    _ = ∫⁻ ω, (capZ B ω [] k : ℝ≥0∞) ∂offspringFieldLaw μ := lintegral_congr hsum
    _ = cappedMean μ B ^ k := lintegral_capZ B k

/-- Exact level-energy identity before applying the uniform second-moment bound. -/
theorem lintegral_levelEnergy_eq (B : ℕ) (b : ℝ) (N k : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (levelEnergy B b ω N k) ∂offspringFieldLaw μ) =
      ENNReal.ofReal ((b⁻¹ ^ N) ^ 2) * cappedMean μ B ^ k *
        ∫⁻ ω, (capZ B ω [] (N - k) : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ := by
  have hnonneg (ω : Offspring) : 0 ≤ levelEnergy B b ω N k := levelEnergy_nonneg _ _ _ _ _
  have hsum (ω : Offspring) : ENNReal.ofReal (levelEnergy B b ω N k) =
      ∑ w ∈ capAddr B k, ENNReal.ofReal (capFlow B b ω N w ^ 2) := by
    rw [levelEnergy, generationSum_capFlow_sq]
    exact ENNReal.ofReal_sum_of_nonneg fun w hw => sq_nonneg _
  calc
    _ = ∫⁻ ω, ∑ w ∈ capAddr B k,
        ENNReal.ofReal (capFlow B b ω N w ^ 2) ∂offspringFieldLaw μ := lintegral_congr hsum
    _ = ∑ w ∈ capAddr B k, ∫⁻ ω,
        ENNReal.ofReal (capFlow B b ω N w ^ 2) ∂offspringFieldLaw μ := by
      apply lintegral_finsetSum
      intro w hw
      exact ENNReal.measurable_ofReal.comp ((measurable_capFlow B b N w).pow_const 2)
    _ = ∑ w ∈ capAddr B k,
        (ENNReal.ofReal ((b⁻¹ ^ N) ^ 2) * offspringFieldLaw μ {ω | w ∈ capGen B ω [] k} *
          ∫⁻ ω, (capZ B ω [] (N - k) : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ) := by
      apply Finset.sum_congr rfl
      intro w hw
      have hlen : w.length = k := length_of_mem_capAddr B k w hw
      rw [lintegral_capFlow_sq B b N k w hlen]
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, sum_measure_capGen]

private theorem flow_power_identity (b C : ℝ) (hb : 0 < b) (N k : ℕ) (hk : k ≤ N) :
    ((b⁻¹ ^ N) ^ 2) * b ^ k * (C * b ^ (2 * (N - k))) = C * b⁻¹ ^ k := by
  have hdiff : k + 2 * (N - k) + k = 2 * N := by omega
  calc
    _ = C * ((b⁻¹ ^ N) ^ 2 * (b ^ k * b ^ (2 * (N - k)))) := by ring
    _ = C * ((b⁻¹ ^ N) ^ 2 * b ^ (k + 2 * (N - k))) := by rw [← pow_add]
    _ = C * b⁻¹ ^ k := by
      rw [← pow_mul]
      have hpow : (b⁻¹ ^ (2 * N)) * b ^ (k + 2 * (N - k)) = b⁻¹ ^ k := by
        rw [inv_pow, inv_pow]
        field_simp [hb.ne']
        rw [← pow_add, hdiff]
      rw [show N * 2 = 2 * N by omega]
      exact congrArg (fun x : ℝ => C * x) hpow

/-- **Level energy.** Independence of strict-prefix and descendant blocks turns the
capped moment bounds (`lintegral_capZ`, `lintegral_capZ_sq_le`) into the level bound
`C * b⁻¹ ^ k`. -/
theorem lintegral_levelEnergy (B : ℕ) {b : ℝ} (hb : b = cappedMeanReal μ B)
    (hb1 : 1 < b) (N k : ℕ) (hk : k ≤ N) :
    (∫⁻ ω, ENNReal.ofReal (levelEnergy B b ω N k) ∂offspringFieldLaw μ) ≤
      ENNReal.ofReal (cappedMomentBound μ B * b⁻¹ ^ k) := by
  subst b
  rw [lintegral_levelEnergy_eq]
  have hsquare := lintegral_capZ_sq_le (μ := μ) hb1 (N - k)
  have hbreal : 0 < cappedMeanReal μ B := zero_lt_one.trans hb1
  have hbpos : 0 < cappedMean μ B := by
    rw [← ENNReal.ofReal_toReal (cappedMean_ne_top B)]
    exact ENNReal.ofReal_pos.mpr hbreal
  have hC : 0 ≤ cappedMomentBound μ B :=
    zero_le_one.trans (one_le_cappedMomentBound (μ := μ) hb1)
  calc
    _ ≤ ENNReal.ofReal (((cappedMeanReal μ B)⁻¹ ^ N) ^ 2) * cappedMean μ B ^ k *
        (ENNReal.ofReal (cappedMomentBound μ B) * cappedMean μ B ^ (2 * (N - k))) := by
      gcongr
    _ = ENNReal.ofReal (cappedMomentBound μ B * (cappedMeanReal μ B)⁻¹ ^ k) := by
      rw [ENNReal.ofReal_mul hC,
        ENNReal.ofReal_pow (inv_nonneg.mpr hbreal.le),
        ENNReal.ofReal_inv_of_pos hbreal]
      rw [ENNReal.ofReal_pow (pow_nonneg (inv_nonneg.mpr hbreal.le) N)]
      have hbne : cappedMean μ B ≠ 0 := hbpos.ne'
      have hleftTop :
          (ENNReal.ofReal ((cappedMeanReal μ B)⁻¹ ^ N) ^ 2 * cappedMean μ B ^ k *
            (ENNReal.ofReal (cappedMomentBound μ B) * cappedMean μ B ^ (2 * (N - k)))) ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
          · exact ENNReal.pow_ne_top (cappedMean_ne_top B)
        · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.pow_ne_top (cappedMean_ne_top B))
      have hrightTop :
          (ENNReal.ofReal (cappedMomentBound μ B) *
            (ENNReal.ofReal (cappedMeanReal μ B))⁻¹ ^ k) ≠ ⊤ := by
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hbreal).ne'))
      apply (ENNReal.toReal_eq_toReal_iff' hleftTop hrightTop).1
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal hC,
        ENNReal.toReal_ofReal ENNReal.toReal_nonneg, cappedMeanReal]
      rw [ENNReal.toReal_ofReal (show 0 ≤ (cappedMean μ B).toReal⁻¹ ^ N by positivity)]
      exact flow_power_identity (cappedMeanReal μ B) (cappedMomentBound μ B) hbreal N k hk

/-- **Total energy.** The weighted level bounds sum to the geometric
bound `C / (1 - l / b)`; only capped second moments are used. -/
theorem lintegral_energy (B : ℕ) {b l : ℝ} (hb : b = cappedMeanReal μ B)
    (hb1 : 1 < b) (hl : 0 < l) (hlb : l < b) (N : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (energy B b l ω N) ∂offspringFieldLaw μ) ≤
      ENNReal.ofReal (cappedMomentBound μ B / (1 - l / b)) := by
  have hb0 : 0 < b := zero_lt_one.trans hb1
  have hC : 0 ≤ cappedMomentBound μ B := zero_le_one.trans
    (one_le_cappedMomentBound (μ := μ) (by rwa [← hb]))
  have hr0 : 0 ≤ l / b := div_nonneg hl.le hb0.le
  have hr1 : l / b < 1 := (div_lt_one hb0).2 hlb
  have hsumnonneg (ω : Offspring) (k : ℕ) (hk : k ∈ Finset.range (N + 1)) :
      0 ≤ l ^ k * levelEnergy B b ω N k :=
    mul_nonneg (pow_nonneg hl.le _) (levelEnergy_nonneg _ _ _ _ _)
  have hof (ω : Offspring) : ENNReal.ofReal (energy B b l ω N) =
      ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (l ^ k * levelEnergy B b ω N k) := by
    unfold energy
    exact ENNReal.ofReal_sum_of_nonneg (hsumnonneg ω)
  have hleft : (∫⁻ ω, ENNReal.ofReal (energy B b l ω N) ∂offspringFieldLaw μ) =
      ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal l ^ k *
        ∫⁻ ω, ENNReal.ofReal (levelEnergy B b ω N k) ∂offspringFieldLaw μ := by
    calc
      _ = ∫⁻ ω, ∑ k ∈ Finset.range (N + 1),
          ENNReal.ofReal (l ^ k * levelEnergy B b ω N k) ∂offspringFieldLaw μ :=
        lintegral_congr hof
      _ = ∑ k ∈ Finset.range (N + 1), ∫⁻ ω,
          ENNReal.ofReal (l ^ k * levelEnergy B b ω N k) ∂offspringFieldLaw μ := by
        apply lintegral_finsetSum
        intro k hk
        exact ENNReal.measurable_ofReal.comp
          (measurable_const.mul (measurable_levelEnergy B b N k))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        simp_rw [ENNReal.ofReal_mul (pow_nonneg hl.le _), ENNReal.ofReal_pow hl.le]
        exact lintegral_const_mul _
          (ENNReal.measurable_ofReal.comp (measurable_levelEnergy B b N k))
  rw [hleft]
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal l ^ k *
        ENNReal.ofReal (cappedMomentBound μ B * b⁻¹ ^ k) := by
      apply Finset.sum_le_sum
      intro k hk
      gcongr
      exact lintegral_levelEnergy B hb hb1 N k (by simpa using Finset.mem_range.mp hk)
    _ = ENNReal.ofReal (cappedMomentBound μ B * ∑ k ∈ Finset.range (N + 1), (l / b) ^ k) := by
      rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg (fun k hk => pow_nonneg hr0 k),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow (inv_nonneg.mpr hb0.le),
        ENNReal.ofReal_inv_of_pos hb0, ENNReal.ofReal_pow hr0,
        ENNReal.ofReal_div_of_pos hb0]
      rw [ENNReal.div_eq_inv_mul, mul_pow]
      ring
    _ ≤ ENNReal.ofReal (cappedMomentBound μ B / (1 - l / b)) := by
      apply ENNReal.ofReal_le_ofReal
      have hC : 0 ≤ cappedMomentBound μ B := zero_le_one.trans
        (one_le_cappedMomentBound (μ := μ) (by simpa [hb] using hb1))
      have hgeom : (∑ k ∈ Finset.range (N + 1), (l / b) ^ k) ≤ (1 - l / b)⁻¹ := by
        simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := N + 1) hr0 hr1)
      calc
        cappedMomentBound μ B * ∑ k ∈ Finset.range (N + 1), (l / b) ^ k ≤
            cappedMomentBound μ B * (1 - l / b)⁻¹ := mul_le_mul_of_nonneg_left hgeom hC
        _ = cappedMomentBound μ B / (1 - l / b) := (div_eq_mul_inv _ _).symm

end LPPMonotonicityProof.Speed
