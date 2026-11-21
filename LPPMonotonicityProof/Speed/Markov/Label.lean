module

public import LPPMonotonicityProof.Speed.Markov.Path
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.Composition.KernelLemmas
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Labelled Markov chains

A general labelled chain may have an arbitrary measurable state space.  The
specification is nested in `Markov` because the public-walk interface
(`Speed/Interface/Labels.lean`) has its own countable-state `Speed.LabelSpec`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Preorder Filtration
open scoped ENNReal BigOperators Function

namespace LPPMonotonicityProof.Speed.Markov

variable {S : Type*} [MeasurableSpace S]

/-- A labelled transition specification, with total label mass one. -/
structure LabelSpec (S : Type*) [MeasurableSpace S] where
  next : S → ℕ → S
  weight : S → ℕ → ℝ≥0∞
  measurable_next : ∀ j, Measurable fun s => next s j
  measurable_weight : ∀ j, Measurable fun s => weight s j
  tsum_weight : ∀ s, ∑' j, weight s j = 1

namespace LabelSpec

variable {S : Type*} [MeasurableSpace S]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

noncomputable def weightedDeterministic (f : α → β) (hf : Measurable f)
    (w : α → ℝ≥0∞) : Kernel α β :=
  Kernel.withDensity (Kernel.deterministic f hf) (fun a _ => w a)

lemma weightedDeterministic_apply (f : α → β) (hf : Measurable f)
    (w : α → ℝ≥0∞) (hw : Measurable w) (a : α) :
    weightedDeterministic f hf w a = w a • Measure.dirac (f a) := by
  rw [weightedDeterministic, Kernel.withDensity_apply _
    (show Measurable (Function.uncurry fun a (_ : β) => w a) from hw.comp measurable_fst),
    Kernel.deterministic_apply, dirac_withDensity' measurable_const]

/-- The transition kernel obtained by forgetting the label. -/
noncomputable def stateKernel (G : LabelSpec S) : Kernel S S :=
  Kernel.sum fun j => weightedDeterministic (fun s => G.next s j) (G.measurable_next j)
    (fun s => G.weight s j)

/-- The transition kernel which records the selected label in the second coordinate. -/
noncomputable def edgeKernel (G : LabelSpec S) : Kernel (S × ℕ) (S × ℕ) :=
  Kernel.sum fun j => weightedDeterministic (fun p => (G.next p.1 j, j))
    ((G.measurable_next j).comp measurable_fst |>.prodMk measurable_const)
    (fun p => G.weight p.1 j)

lemma stateKernel_apply (G : LabelSpec S) (s : S) :
    G.stateKernel s = Measure.sum fun j => G.weight s j • Measure.dirac (G.next s j) := by
  rw [stateKernel, Kernel.sum_apply]
  apply congrArg Measure.sum
  funext j
  exact weightedDeterministic_apply _ _ _ (G.measurable_weight j) s

lemma edgeKernel_apply (G : LabelSpec S) (p : S × ℕ) :
    G.edgeKernel p = Measure.sum fun j =>
      G.weight p.1 j • Measure.dirac (G.next p.1 j, j) := by
  rw [edgeKernel, Kernel.sum_apply]
  apply congrArg Measure.sum
  funext j
  exact weightedDeterministic_apply _ _ _ ((G.measurable_weight j).comp measurable_fst) p

instance (G : LabelSpec S) : IsMarkovKernel G.stateKernel := by
  refine ⟨fun s => ⟨?_⟩⟩
  rw [stateKernel_apply, Measure.sum_apply _ MeasurableSet.univ]
  simpa using G.tsum_weight s

instance (G : LabelSpec S) : IsMarkovKernel G.edgeKernel := by
  refine ⟨fun p => ⟨?_⟩⟩
  rw [edgeKernel_apply, Measure.sum_apply _ MeasurableSet.univ]
  simpa using G.tsum_weight p.1

/-- Extract the labels from an edge path, dropping its initial dummy label. -/
def labelSeq (ω : ℕ → S × ℕ) : ℕ → ℕ := fun n => (ω (n + 1)).2

lemma measurable_labelSeq : Measurable (fun ω : ℕ → S × ℕ => labelSeq ω) := by
  refine .of_eval fun n => (measurable_pi_apply (n + 1)).snd

/-- Prepend a label to a label sequence. -/
def seqCons (j : ℕ) (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => j
  | n + 1 => c n

/-- Remove the first label. -/
def seqTail (c : ℕ → ℕ) : ℕ → ℕ := fun n => c (n + 1)

lemma measurable_seqCons (j : ℕ) : Measurable (seqCons j) := by
  refine .of_eval fun n => ?_
  cases n with
  | zero => exact measurable_const
  | succ n => exact measurable_pi_apply n

/-- The law of the label sequence. -/
noncomputable def law (G : LabelSpec S) : Kernel S (ℕ → ℕ) :=
  Kernel.map ((path G.edgeKernel).comap (fun s => (s, 0)) (by fun_prop)) labelSeq

instance (G : LabelSpec S) : IsMarkovKernel G.law := by
  exact Kernel.IsMarkovKernel.map _ measurable_labelSeq

/-- The state reached after reading the first labels. -/
def state (G : LabelSpec S) (s : S) (c : ℕ → ℕ) : ℕ → S
  | 0 => s
  | n + 1 => G.next (G.state s c n) (c n)

lemma map_eval_zero_path {T : Type*} [MeasurableSpace T] (K : Kernel T T) [IsMarkovKernel K]
    (x : T) : (path K x).map (fun ω => ω 0) = Measure.dirac x := by
  let z : (Π _ : Finset.Iic 0, T) := fun _ => x
  have h := map_frestrictLe_path_zero K z 0
  have heval : (fun ω : ℕ → T => ω 0) =
      (fun u : (Π _ : Finset.Iic 0, T) => u ⟨0, by simp⟩) ∘ Preorder.frestrictLe 0 := rfl
  rw [heval]
  calc
    (path K x).map ((fun u : (Π _ : Finset.Iic 0, T) => u ⟨0, by simp⟩) ∘
        Preorder.frestrictLe 0) =
        ((path K x).map (Preorder.frestrictLe 0)).map
          (fun u : (Π _ : Finset.Iic 0, T) => u ⟨0, by simp⟩) :=
      (Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe 0)).symm
    _ = (Kernel.partialTraj (X := fun _ => T) (homKernel K) 0 0 z).map
          (fun u : (Π _ : Finset.Iic 0, T) => u ⟨0, by simp⟩) := by rw [h]
    _ = Measure.dirac x := by
      rw [Kernel.partialTraj_self, Kernel.id_apply, Measure.map_dirac' (measurable_pi_apply _)]

lemma ae_initial_label (G : LabelSpec S) (s : S) (j : ℕ) :
    ∀ᵐ ω ∂path G.edgeKernel (s, j), (ω 0).2 = j := by
  have hset : MeasurableSet {p : S × ℕ | p.2 ≠ j} :=
    (measurableSet_eq_fun measurable_snd measurable_const).compl
  have hnull : path G.edgeKernel (s, j) {ω | (ω 0).2 ≠ j} = 0 := by
    change path G.edgeKernel (s, j) ((fun ω => ω 0) ⁻¹' {p : S × ℕ | p.2 ≠ j}) = 0
    rw [← Measure.map_apply (measurable_pi_apply 0) hset, map_eval_zero_path,
      Measure.dirac_apply' _ hset]
    simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with ω hω
  exact not_not.mp hω

lemma map_labelSeq_path_eq (G : LabelSpec S) (s : S) (j : ℕ) :
    (path G.edgeKernel (s, j)).map labelSeq = (path G.edgeKernel (s, 0)).map labelSeq := by
  let fullLabels : (ℕ → S × ℕ) → (ℕ → ℕ) := fun ω n => (ω n).2
  have hfull : Measurable fullLabels := by
    refine .of_eval fun n => (measurable_pi_apply n).snd
  have hcomp : (labelSeq : (ℕ → S × ℕ) → ℕ → ℕ) = fullLabels ∘ shiftPath := rfl
  simp only [hcomp, ← Measure.map_map hfull measurable_shiftPath, path_shift]
  have he : G.edgeKernel (s, j) = G.edgeKernel (s, 0) := by
    rw [edgeKernel_apply, edgeKernel_apply]
  rw [he]

/-- First-step decomposition of the label law. -/
theorem law_firstStep (G : LabelSpec S) (s : S) :
    G.law s = Measure.sum fun j =>
      G.weight s j • (G.law (G.next s j)).map (seqCons j) := by
  simp only [law, Kernel.map_apply _ measurable_labelSeq, Kernel.comap_apply]
  rw [path_firstStep]
  rw [Measure.map_bind (Kernel.aemeasurable _) measurable_labelSeq.aemeasurable]
  rw [edgeKernel_apply]
  let η : Kernel (S × ℕ) (ℕ → ℕ) :=
    Kernel.map ((path G.edgeKernel).map (pcons (s, 0))) labelSeq
  have hη : Measurable (fun p : S × ℕ =>
      Measure.map labelSeq (((path G.edgeKernel).map (pcons (s, 0))) p)) := by
    have heq : (fun p : S × ℕ =>
        Measure.map labelSeq (((path G.edgeKernel).map (pcons (s, 0))) p)) = (fun p => η p) := by
      funext p
      simp only [η, Kernel.map_apply _ measurable_labelSeq]
    rw [heq]
    exact Kernel.measurable η
  rw [Measure.bind_sum _ _ hη.aemeasurable]
  apply congrArg Measure.sum
  funext j
  rw [Measure.bind_smul _ _ hη.aemeasurable]
  rw [Measure.dirac_bind hη]
  simp only [Kernel.map_apply _ (measurable_pcons (s, 0)),
    Kernel.map_apply _ measurable_labelSeq]
  change G.weight s j • ((path G.edgeKernel (G.next s j, j)).map (pcons (s, 0))).map
    labelSeq = G.weight s j • ((path G.edgeKernel (G.next s j, 0)).map labelSeq).map (seqCons j)
  congr 1
  calc
    ((path G.edgeKernel (G.next s j, j)).map (pcons (s, 0))).map labelSeq =
        (path G.edgeKernel (G.next s j, j)).map (seqCons j ∘ labelSeq) := by
      rw [Measure.map_map measurable_labelSeq (measurable_pcons (s, 0))]
      apply Measure.map_congr
      filter_upwards [ae_initial_label G (G.next s j) j] with ω hω
      funext n
      cases n with
      | zero => simp [labelSeq, pcons, seqCons, hω]
      | succ n => rfl
    _ = ((path G.edgeKernel (G.next s j, j)).map labelSeq).map (seqCons j) :=
      (Measure.map_map (measurable_seqCons j) measurable_labelSeq).symm
    _ = ((path G.edgeKernel (G.next s j, 0)).map labelSeq).map (seqCons j) := by
      rw [map_labelSeq_path_eq]


/-- The cylinder which fixes the first `n` labels to those of `w`. -/
def wordCylinder (w : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  {c | ∀ i < n, c i = w i}

lemma measurableSet_wordCylinder (w : ℕ → ℕ) (n : ℕ) :
    MeasurableSet (wordCylinder w n) := by
  have heq : wordCylinder w n = ⋂ i : Fin n, {c | c i.1 = w i.1} := by
    ext c
    simp only [wordCylinder, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h i
      exact h i.1 i.2
    · intro h i hi
      exact h ⟨i, hi⟩
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    measurableSet_eq_fun (measurable_pi_apply i.1) measurable_const

lemma state_succ (G : LabelSpec S) (s : S) (w : ℕ → ℕ) (i : ℕ) :
    G.state (G.next s (w 0)) (seqTail w) i = G.state s w (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [state, state, ← ih]
      rfl

/-- The probability of a finite word cylinder is its product of label weights. -/
theorem law_cylinder (G : LabelSpec S) (s : S) (w : ℕ → ℕ) (n : ℕ) :
    G.law s (wordCylinder w n) =
      ∏ i ∈ Finset.range n, G.weight (G.state s w i) (w i) := by
  induction n generalizing s w with
  | zero => simp [wordCylinder]
  | succ n ih =>
      rw [G.law_firstStep s, Measure.sum_apply _ (measurableSet_wordCylinder w (n + 1))]
      simp only [Measure.smul_apply, smul_eq_mul,
        Measure.map_apply (measurable_seqCons _) (measurableSet_wordCylinder w (n + 1))]
      rw [tsum_eq_single (w 0)]
      · have hpre : seqCons (w 0) ⁻¹' wordCylinder w (n + 1) =
            wordCylinder (seqTail w) n := by
          ext c
          constructor
          · intro h i hi
            exact h (i + 1) (Nat.succ_lt_succ hi)
          · intro h i hi
            cases i with
            | zero => rfl
            | succ i => exact h i (Nat.succ_lt_succ_iff.mp hi)
        rw [hpre, ih, Finset.prod_range_succ', mul_comm]
        change (∏ i ∈ Finset.range n, G.weight
          (G.state (G.next s (w 0)) (seqTail w) i) (seqTail w i)) * G.weight s (w 0) =
          (∏ i ∈ Finset.range n, G.weight (G.state s w (i + 1)) (w (i + 1))) *
            G.weight s (w 0)
        apply congrArg (fun r : ℝ≥0∞ => r * G.weight s (w 0))
        apply Finset.prod_congr rfl
        intro i hi
        rw [state_succ]
        rfl
      · intro j hj
        have hpre : seqCons j ⁻¹' wordCylinder w (n + 1) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro c hc
          exact hj (hc 0 (Nat.zero_lt_succ n))
        rw [hpre]
        simp


/-- Word cylinders together with the empty set. -/
def wordCylinderSystem : Set (Set (ℕ → ℕ)) :=
  {∅} ∪ Set.range (fun p : (ℕ → ℕ) × ℕ => wordCylinder p.1 p.2)

lemma isPiSystem_wordCylinderSystem : IsPiSystem wordCylinderSystem := by
  intro s hs t ht hst
  simp only [wordCylinderSystem, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hs ht ⊢
  rcases hs with rfl | ⟨⟨w, n⟩, rfl⟩
  · simp at hst
  rcases ht with rfl | ⟨⟨v, m⟩, rfl⟩
  · simp at hst
  by_cases hc : ∀ i < min n m, w i = v i
  · right
    let u : ℕ → ℕ := fun i => if i < n then w i else v i
    refine ⟨⟨u, max n m⟩, ?_⟩
    ext c
    change (∀ i < max n m, c i = u i) ↔
      (∀ i < n, c i = w i) ∧ (∀ i < m, c i = v i)
    constructor
    · intro h
      constructor
      · intro i hi
        have hu := h i (by omega : i < max n m)
        simpa [u, hi] using hu
      · intro i hi
        have hu := h i (by omega : i < max n m)
        by_cases hin : i < n
        · have hwi := hc i (by omega)
          simp only [u, hin, ↓reduceIte] at hu
          exact hu.trans hwi
        · simpa [u, hin] using hu
    · rintro ⟨hw, hv⟩ i hi
      by_cases hin : i < n
      · simpa [u, hin] using hw i hin
      · have him : i < m := by omega
        simpa [u, hin] using hv i him
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hmem
    simp only [not_forall, not_imp] at hc
    rcases hc with ⟨i, hi, hne⟩
    exact hne ((hmem.1 i (by omega)).symm.trans (hmem.2 i (by omega)))

lemma generateFrom_wordCylinderSystem :
    (inferInstance : MeasurableSpace (ℕ → ℕ)) =
      MeasurableSpace.generateFrom wordCylinderSystem := by
  apply le_antisymm
  · change MeasurableSpace.pi ≤ MeasurableSpace.generateFrom wordCylinderSystem
    unfold MeasurableSpace.pi
    apply iSup_le
    intro i
    rw [← measurable_iff_comap_le]
    intro B hB
    have hdecomp : (fun c : ℕ → ℕ => c i) ⁻¹' B =
        ⋃ b ∈ B, (fun c : ℕ → ℕ => c i) ⁻¹' {b} := by
      ext c
      simp
    rw [hdecomp]
    apply MeasurableSet.biUnion (Set.to_countable B)
    intro b hb
    let extend : (Fin (i + 1) → ℕ) → ℕ → ℕ := fun w k =>
      if hk : k < i + 1 then w ⟨k, hk⟩ else 0
    have hsingle : (fun c : ℕ → ℕ => c i) ⁻¹' {b} =
        ⋃ w : {w : Fin (i + 1) → ℕ // w ⟨i, Nat.lt_succ_self i⟩ = b},
          wordCylinder (extend w.1) (i + 1) := by
      ext c
      constructor
      · intro hc
        let w : Fin (i + 1) → ℕ := fun k => c k.1
        have hw : w ⟨i, Nat.lt_succ_self i⟩ = b := hc
        apply Set.mem_iUnion.mpr
        refine ⟨⟨w, hw⟩, ?_⟩
        intro k hk
        change c k = extend w k
        dsimp [extend]
        rw [dif_pos hk]
      · intro hc
        rcases Set.mem_iUnion.mp hc with ⟨w, hw⟩
        have hi := hw i (Nat.lt_succ_self i)
        have he : extend w.1 i = b := by
          dsimp [extend]
          rw [dif_pos (Nat.lt_succ_self i)]
          exact w.2
        exact hi.trans he
    rw [hsingle]
    apply MeasurableSet.iUnion
    intro w
    apply MeasurableSpace.measurableSet_generateFrom
    exact Or.inr ⟨⟨extend w.1, i + 1⟩, rfl⟩
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    rcases hs with (rfl | ⟨⟨w, n⟩, rfl⟩)
    · exact MeasurableSet.empty
    · exact measurableSet_wordCylinder w n

/-- A finite measure on label sequences is determined by its word cylinders. -/
theorem law_ext (G : LabelSpec S) (s : S) {η : Measure (ℕ → ℕ)} [IsFiniteMeasure η]
    (h : ∀ w n, η (wordCylinder w n) = G.law s (wordCylinder w n)) : η = G.law s := by
  apply MeasureTheory.ext_of_generate_finite wordCylinderSystem generateFrom_wordCylinderSystem
    isPiSystem_wordCylinderSystem
  · intro t ht
    rcases ht with (rfl | ⟨⟨w, n⟩, rfl⟩)
    · simp
    · exact h w n
  · have h0 := h (fun _ => 0) 0
    simpa [wordCylinder] using h0


lemma measurable_state (G : LabelSpec S) (n : ℕ) :
    Measurable (fun p : S × (ℕ → ℕ) => G.state p.1 p.2 n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      have hnext : Measurable (fun p : S × ℕ => G.next p.1 p.2) :=
        measurable_from_prod_countable_left fun j => G.measurable_next j
      exact hnext.comp (ih.prodMk ((measurable_pi_apply n).comp measurable_snd))

lemma measurable_state_apply (G : LabelSpec S) (s : S) : Measurable (G.state s) := by
  refine .of_eval fun n => ?_
  exact (G.measurable_state n).comp (measurable_const.prodMk measurable_id)

lemma measurable_state_uncurry (G : LabelSpec S) :
    Measurable (fun p : S × (ℕ → ℕ) => G.state p.1 p.2) := by
  refine .of_eval fun n => G.measurable_state n

/-- The joint law of the initial state and its label sequence. -/
noncomputable def jointLaw (G : LabelSpec S) : Kernel S (S × (ℕ → ℕ)) :=
  Kernel.id ⊗ₖ Kernel.prodMkLeft S G.law

instance (G : LabelSpec S) : IsMarkovKernel G.jointLaw := by
  unfold jointLaw
  infer_instance

lemma jointLaw_apply (G : LabelSpec S) (s : S) :
    G.jointLaw s = Measure.dirac s ⊗ₘ Kernel.const S (G.law s) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [jointLaw, Kernel.lintegral_compProd _ _ _ hf, Measure.lintegral_compProd hf]
  simp only [Kernel.prodMkLeft_apply, Kernel.id_apply, Kernel.const_apply]
  rw [lintegral_dirac' s hf.lintegral_kernel_prod_right']
  symm
  apply lintegral_dirac'
  exact hf.lintegral_kernel_prod_right' (κ := Kernel.const S (G.law s))

lemma dirac_compProd (G : LabelSpec S) (s : S) :
    Measure.dirac s ⊗ₘ Kernel.const S (G.law s) = (G.law s).map (Prod.mk s) := by
  ext A hA
  rw [Measure.compProd_apply (κ := Kernel.const S (G.law s)) hA,
    Measure.map_apply measurable_prodMk_left hA]
  simp only [Kernel.const_apply]
  apply lintegral_dirac'
  exact measurable_measure_prodMk_left hA

/-- The law of the state path induced by a labelled chain. -/
noncomputable def statePathKernel (G : LabelSpec S) : Kernel S (ℕ → S) :=
  Kernel.map G.jointLaw (fun p => G.state p.1 p.2)

instance (G : LabelSpec S) : IsMarkovKernel G.statePathKernel := by
  exact Kernel.IsMarkovKernel.map _ G.measurable_state_uncurry

lemma statePathKernel_apply (G : LabelSpec S) (s : S) :
    G.statePathKernel s = (G.law s).map (G.state s) := by
  rw [statePathKernel, Kernel.map_apply _ G.measurable_state_uncurry,
    jointLaw_apply, dirac_compProd, Measure.map_map G.measurable_state_uncurry
      measurable_prodMk_left]
  rfl

lemma state_seqCons (G : LabelSpec S) (s : S) (j : ℕ) (c : ℕ → ℕ) (n : ℕ) :
    G.state s (seqCons j c) n = pcons s (G.state (G.next s j) c) n := by
  induction n generalizing s j with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          change G.next (G.state s (seqCons j c) (n + 1)) (c n) =
            G.next (G.state (G.next s j) c n) (c n)
          rw [ih]
          rfl

lemma statePathKernel_firstStep (G : LabelSpec S) (s : S) :
    G.statePathKernel s = (Kernel.map G.statePathKernel (pcons s)) ∘ₘ G.stateKernel s := by
  rw [statePathKernel_apply, G.law_firstStep]
  rw [Measure.map_sum (G.measurable_state_apply s).aemeasurable]
  rw [stateKernel_apply]
  let η : Kernel S (ℕ → S) := Kernel.map G.statePathKernel (pcons s)
  rw [Measure.bind_sum _ _ (Kernel.aemeasurable η)]
  apply congrArg Measure.sum
  funext j
  rw [Measure.map_smul _ (G.measurable_state_apply s).aemeasurable]
  rw [Measure.bind_smul _ _ (Kernel.aemeasurable η), Measure.dirac_bind (Kernel.measurable η)]
  dsimp only [η]
  rw [Kernel.map_apply _ (measurable_pcons s), statePathKernel_apply]
  congr 1
  calc
    ((G.law (G.next s j)).map (seqCons j)).map (G.state s) =
        (G.law (G.next s j)).map (G.state s ∘ seqCons j) :=
      Measure.map_map (G.measurable_state_apply s) (measurable_seqCons j)
    _ = (G.law (G.next s j)).map (pcons s ∘ G.state (G.next s j)) := by
      apply congrArg (fun f => (G.law (G.next s j)).map f)
      funext c n
      exact G.state_seqCons s j c n
    _ = ((G.law (G.next s j)).map (G.state (G.next s j))).map (pcons s) :=
      (Measure.map_map (measurable_pcons s) (G.measurable_state_apply _)).symm

/-- Forgetting the labels in a labelled chain gives its state path law. -/
theorem path_stateKernel (G : LabelSpec S) (s : S) :
    path G.stateKernel s = (G.law s).map (G.state s) := by
  rw [← statePathKernel_apply,
    eq_path_of_firstStep G.stateKernel G.statePathKernel G.statePathKernel_firstStep]

end LabelSpec
end LPPMonotonicityProof.Speed.Markov
