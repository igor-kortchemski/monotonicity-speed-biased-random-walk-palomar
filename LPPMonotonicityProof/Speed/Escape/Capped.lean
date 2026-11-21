module

public import LPPMonotonicityProof.Escape.FiniteFlow
public import LPPMonotonicityProof.Speed.Hyp
public import LPPMonotonicityProof.RTL.LocallyFinite.GenerationLaw
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Capped generations and their moments

This is the first step of a direct proof of the positivity of the escape in
Lemma 2.1(iv) (`lem:escape`), which the paper obtains from Lyons; the later steps
are in `Energy.lean`, `EnergyEscape.lean` and `Positive.lean`.  We choose a cap, cap
every coordinate of the raw offspring field, then use the RTL Bienaymé law of the
resulting field, and bound the first two moments of the capped generation sizes.  Root
decomposition, rather than a generation-history Markov property, gives the
moment recursion.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace LPPMonotonicityProof.Speed

open LPPMonotonicityProof.RTL.LocallyFinite

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- The offspring law obtained by retaining at most `B` children. -/
noncomputable def cappedLaw (μ : Measure ℕ) (B : ℕ) : Measure ℕ :=
  μ.map (fun k => min k B)

instance cappedLaw_probability (μ : Measure ℕ) [IsProbabilityMeasure μ] (B : ℕ) :
    IsProbabilityMeasure (cappedLaw μ B) := by
  unfold cappedLaw
  infer_instance

/-- The capped field, before pruning absent addresses. -/
def cappedField (B : ℕ) (ω : Offspring) : Offspring :=
  fun v => min (ω v) B

/-- The capped descendant tree at address `v`. -/
def cappedTree (B : ℕ) (ω : Offspring) (v : Address) : Tree :=
  prune (fun u => min (ω (v ++ u)) B)

/-- Vertices at relative depth `j` in the capped descendant tree at `v`. -/
def capGen (B : ℕ) (ω : Offspring) (v : Address) (j : ℕ) : Finset Address :=
  (generation (cappedTree B ω v) j).image (fun u => v ++ u)

/-- Size of a capped generation. -/
def capZ (B : ℕ) (ω : Offspring) (v : Address) (j : ℕ) : ℕ :=
  (capGen B ω v j).card

/-- The extended mean of the capped offspring law. -/
noncomputable def cappedMean (μ : Measure ℕ) [IsProbabilityMeasure μ] (B : ℕ) : ℝ≥0∞ :=
  ∫⁻ k, ((min k B : ℕ) : ℝ≥0∞) ∂μ

/-- The second moment of the capped offspring law. -/
noncomputable def cappedSecondMoment (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (B : ℕ) : ℝ≥0∞ :=
  ∫⁻ k, ((min k B : ℕ) : ℝ≥0∞) ^ 2 ∂μ

/-- The real mean used to normalize the flow. -/
noncomputable def cappedMeanReal (μ : Measure ℕ) [IsProbabilityMeasure μ] (B : ℕ) : ℝ :=
  (cappedMean μ B).toReal

/-- Unit mass is assigned to every capped vertex at depth `N` and propagated
upwards.  Off the capped tree the flow is zero. -/
noncomputable def capFlow (B : ℕ) (b : ℝ) (ω : Offspring) (N : ℕ) (w : Address) : ℝ :=
  if w ∈ capGen B ω [] w.length then
    b⁻¹ ^ N * capZ B ω w (N - w.length)
  else 0

@[simp] theorem capGen_root (B : ℕ) (ω : Offspring) (j : ℕ) :
    capGen B ω [] j = generation (cappedTree B ω []) j := by
  simp [capGen]

@[simp] theorem capZ_eq_generationSize (B : ℕ) (ω : Offspring) (v : Address) (j : ℕ) :
    capZ B ω v j = generationSize (cappedTree B ω v) j := by
  rw [capZ, capGen, generationSize, Finset.card_image_of_injective]
  exact List.append_right_injective v

@[simp] theorem degree_cappedTree (B : ℕ) (ω : Offspring) (v : Address) :
    degree (cappedTree B ω v) = min (ω v) B := by
  simp [cappedTree]

/-- Monotone convergence supplies a cap whose mean exceeds every prescribed
value below the uncapped mean. -/
theorem exists_cap (h : OffspringHyp μ) {l : ℝ} (hl : l < mean μ) :
    ∃ B : ℕ, max 1 l < (cappedMean μ B).toReal := by
  have hmeas (B : ℕ) : Measurable (fun k : ℕ => ((min k B : ℕ) : ℝ≥0∞)) :=
    measurable_of_countable _
  have hmono : Monotone (fun B k => ((min k B : ℕ) : ℝ≥0∞)) := by
    intro B B' hBB' k
    change ((min k B : ℕ) : ℝ≥0∞) ≤ ((min k B' : ℕ) : ℝ≥0∞)
    exact_mod_cast min_le_min (le_refl k) hBB'
  have hsup : (⨆ B, cappedMean μ B) = ∫⁻ k, (k : ℝ≥0∞) ∂μ := by
    unfold cappedMean
    rw [← lintegral_iSup hmeas hmono]
    apply lintegral_congr
    intro k
    apply le_antisymm
    · exact iSup_le fun B => by exact_mod_cast Nat.min_le_left k B
    · exact le_iSup_of_le k (by simp)
  have hone : (1 : ℝ) < mean μ := by
    have hh := (ENNReal.toReal_lt_toReal (by simp) h.mean_lt_top.ne).2 h.one_lt_mean
    simpa [mean] using hh
  have hlt : max 1 l < mean μ := max_lt hone hl
  have hraw : ENNReal.ofReal (max 1 l) < ∫⁻ k, (k : ℝ≥0∞) ∂μ :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) h.mean_lt_top.ne).2
      (by simpa [mean] using hlt)
  rw [← hsup] at hraw
  obtain ⟨B, hB⟩ := lt_iSup_iff.mp hraw
  have hle : cappedMean μ B ≤ ∫⁻ k, (k : ℝ≥0∞) ∂μ := by
    apply lintegral_mono
    intro k
    change ((min k B : ℕ) : ℝ≥0∞) ≤ (k : ℝ≥0∞)
    exact_mod_cast Nat.min_le_left k B
  refine ⟨B, (ENNReal.ofReal_lt_iff_lt_toReal (by positivity)
    (ne_top_of_le_ne_top h.mean_lt_top.ne hle)).1 hB⟩

@[simp] theorem cappedLaw_mean (B : ℕ) :
    (∫⁻ k, (k : ℝ≥0∞) ∂cappedLaw μ B) = cappedMean μ B := by
  exact lintegral_map (measurable_of_countable _) (measurable_of_countable _)

/-- Capping each coordinate pushes the iid field law to the iid capped law. -/
theorem map_cappedField (B : ℕ) :
    (offspringFieldLaw μ).map (cappedField B) = offspringFieldLaw (cappedLaw μ B) := by
  unfold offspringFieldLaw cappedField cappedLaw
  simpa only [cappedField, cappedLaw, offspringFieldLaw] using
    (Measure.infinitePi_map_pi (μ := fun _ : Address => μ)
      (f := fun _ k => min k B) (fun _ => measurable_of_countable _))

/-- The root capped tree has the Bienaymé law of the capped offspring. -/
theorem map_cappedTree (B : ℕ) :
    (offspringFieldLaw μ).map (fun ω => cappedTree B ω []) =
      bienaymeLaw (cappedLaw μ B) := by
  have hm : Measurable (cappedField B) :=
    Measurable.of_eval fun v => (measurable_pi_apply v).min measurable_const
  have heq : (fun ω => cappedTree B ω []) = prune ∘ cappedField B := by
    funext ω
    rfl
  rw [heq, bienaymeLaw, ← map_cappedField (μ := μ) B,
    Measure.map_map measurable_prune hm]


/-- A present address followed by one child is present exactly when that
child index is valid at the address. -/
theorem present_append_one_iff (T : Tree) (u : Address) (i : ℕ) :
    Present T (u ++ [i]) ↔ Present T u ∧ (1 ≤ i ∧ i ≤ T.val u) := by
  induction u generalizing T with
  | nil => simp [degree]
  | cons j u ih =>
      simp only [List.cons_append, present_cons]
      rw [ih]
      tauto

/-- Rerooting a capped tree at one of its children is the same as moving the
base address to that child. -/
theorem child_cappedTree (B : ℕ) (ω : Offspring) (v : Address) (i : ℕ) :
    child (cappedTree B ω v) i =
      if 1 ≤ i ∧ i ≤ min (ω v) B then cappedTree B ω (v ++ [i]) else leaf := by
  rw [cappedTree, child_prune]
  simp only [List.append_nil]
  split_ifs with hi
  · apply congrArg prune
    funext u
    simp only [List.singleton_append, List.append_assoc]
  · rfl

/-- Root decomposition of capped generation sizes. -/
theorem capZ_succ (B : ℕ) (ω : Offspring) (v : Address) (j : ℕ) :
    capZ B ω v (j + 1) =
      ∑ i : Fin (min (ω v) B), capZ B ω (v ++ [i.val + 1]) j := by
  rw [capZ_eq_generationSize, generationSize_succ_eq_sum, degree_cappedTree]
  apply Finset.sum_congr rfl
  intro i _
  rw [child_cappedTree, ite_eq_left]
  · exact (capZ_eq_generationSize B ω (v ++ [i.val + 1]) j).symm
  · exact ⟨Nat.succ_pos _, i.isLt⟩

@[simp] theorem mem_capGen_root (B : ℕ) (ω : Offspring) (w : Address) (k : ℕ) :
    w ∈ capGen B ω [] k ↔ Present (cappedTree B ω []) w ∧ w.length = k := by
  rw [capGen_root, mem_generation]

/-- Membership at a child is membership at its parent together with survival
of the one-based child index under the cap. -/
theorem mem_capGen_append_one (B : ℕ) (ω : Offspring) (w : Address) (i j : ℕ) :
    w ++ [i] ∈ capGen B ω [] (j + 1) ↔
      w ∈ capGen B ω [] j ∧ (1 ≤ i ∧ i ≤ min (ω w) B) := by
  rw [mem_capGen_root, mem_capGen_root, present_append_one_iff, List.length_append,
    List.length_singleton]
  constructor
  · rintro ⟨⟨hp, hi⟩, hlen⟩
    have hval : (cappedTree B ω []).val w = min (ω w) B := by
      simpa [cappedTree] using prune_val_of_present hp
    refine ⟨⟨hp, by omega⟩, ?_⟩
    rwa [hval] at hi
  · rintro ⟨⟨hp, hlen⟩, hi⟩
    have hval : (cappedTree B ω []).val w = min (ω w) B := by
      simpa [cappedTree] using prune_val_of_present hp
    refine ⟨⟨hp, ?_⟩, by omega⟩
    rwa [hval]

/-- Raw RTL generation membership fixes the address length. -/
theorem length_of_mem_generation (ω : Offspring) :
    ∀ (j : ℕ) (v w : Address), w ∈ _root_.generation ω v j → w.length = v.length + j := by
  intro j
  induction j with
  | zero =>
      intro v w h
      have h' : w = v := by simpa [_root_.generation] using h
      subst w
      simp
  | succ j ih =>
      intro v w h
      rw [_root_.generation] at h
      obtain ⟨i, -, hw⟩ := Finset.mem_biUnion.mp h
      rw [ih _ _ hw]
      simp [offChild, Nat.add_comm, Nat.add_left_comm]

/-- Flow conservation at every nonterminal vertex of the original tree. -/
theorem flow_conservation (B : ℕ) (b : ℝ) (ω : Offspring) (N : ℕ) :
    ∀ j < N, ∀ w ∈ _root_.generation ω [] j,
      capFlow B b ω N w = ∑ i : Fin (ω w), capFlow B b ω N (offChild ω w i) := by
  intro j hj w hwg
  have hwlen : w.length = j := by simpa using length_of_mem_generation ω j [] w hwg
  by_cases hw : w ∈ capGen B ω [] j
  · have hN : N - w.length = N - (j + 1) + 1 := by omega
    have hsplit : min (ω w) B ≤ ω w := Nat.min_le_left _ _
    have hleft : capFlow B b ω N w =
        b⁻¹ ^ N * capZ B ω w (N - (j + 1) + 1) := by
      rw [capFlow, ite_eq_left (by simpa [hwlen] using hw), hwlen]
      rw [show N - j = N - (j + 1) + 1 by omega]
    rw [hleft, capZ_succ, Nat.cast_sum, Finset.mul_sum]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => b⁻¹ ^ N * capZ B ω (w ++ [i + 1]) (N - (j + 1))) (min (ω w) B)]
    simp only [offChild]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => capFlow B b ω N (w ++ [i + 1])) (ω w)]
    calc
      _ = ∑ i ∈ Finset.range (min (ω w) B),
          capFlow B b ω N (w ++ [i + 1]) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hib : i < min (ω w) B := Finset.mem_range.mp hi
        have hc : w ++ [i + 1] ∈ capGen B ω [] (j + 1) :=
          (mem_capGen_append_one B ω w (i + 1) j).2 ⟨hw, by omega⟩
        rw [capFlow, ite_eq_left (by simpa [List.length_append, hwlen] using hc)]
        simp [List.length_append, hwlen]
      _ = _ := by
        apply Finset.sum_subset (s₁ := Finset.range (min (ω w) B))
          (s₂ := Finset.range (ω w)) (Finset.range_mono hsplit)
        intro i hi hi'
        have hibound : min (ω w) B ≤ i := by
          simpa only [Finset.mem_range, Nat.not_lt] using hi'
        have hchildnot : ¬ w ++ [i + 1] ∈ capGen B ω [] (j + 1) := by
          intro hc
          have hh := (mem_capGen_append_one B ω w (i + 1) j).1 hc
          omega
        rw [capFlow, ite_eq_right]
        simpa [List.length_append, hwlen] using hchildnot
  · have hz (i : Fin (ω w)) : capFlow B b ω N (offChild ω w i) = 0 := by
      rw [capFlow, ite_eq_right]
      intro hc
      apply hw
      have hc' : w ++ [i.val + 1] ∈ capGen B ω [] (j + 1) := by
        simpa only [offChild, List.nil_append, List.length_append, List.length_singleton,
          hwlen] using hc
      exact ((mem_capGen_append_one B ω w (i.val + 1) j).1 hc').1
    have hleft : capFlow B b ω N w = 0 := by
      rw [capFlow, ite_eq_right (by simpa [hwlen] using hw)]
    rw [hleft]
    exact (Finset.sum_eq_zero fun i _ => hz i).symm


/-- A capped generation size at `v` depends only on coordinates below `v`. -/
theorem capZ_dependsOn (B : ℕ) (v : Address) (j : ℕ) :
    DependsOn (fun ω => capZ B ω v j) {a | ∃ u, a = v ++ u} := by
  intro ω η h
  have hf : (fun u => min (ω (v ++ u)) B) = (fun u => min (η (v ++ u)) B) := by
    funext u
    rw [h (v ++ u) ⟨u, rfl⟩]
  simp only [capZ_eq_generationSize, cappedTree, hf]

/-- Presence in the capped tree depends only on the strict prefixes of the
address being tested. -/
theorem cappedPresent_dependsOn (B : ℕ) (w : Address) :
    DependsOn (fun ω => Present (cappedTree B ω []) w)
      {p | p <+: w ∧ p ≠ w} := by
  intro ω η h
  induction w generalizing ω η with
  | nil => rfl
  | cons i u ih =>
      have hroot : ω [] = η [] := h [] ⟨⟨i :: u, rfl⟩, by simp⟩
      by_cases hω : 1 ≤ i ∧ i ≤ min (ω []) B
      · have hη : 1 ≤ i ∧ i ≤ min (η []) B := by rwa [← hroot]
        have hrec := ih (ω := fun x => ω (i :: x)) (η := fun x => η (i :: x)) (by
          intro p hp
          exact h (i :: p) ⟨(List.cons_prefix_cons).2 ⟨rfl, hp.1⟩,
            fun heq => hp.2 (List.cons.inj heq).2⟩)
        change (1 ≤ i ∧ i ≤ min (ω []) B ∧
            Present (child (cappedTree B ω []) i) u) =
          (1 ≤ i ∧ i ≤ min (η []) B ∧
            Present (child (cappedTree B η []) i) u)
        rw [child_cappedTree, child_cappedTree, ite_eq_left hω, ite_eq_left hη]
        have hωtree : cappedTree B (fun x => ω (i :: x)) [] = cappedTree B ω [i] := by
          apply congrArg prune
          funext x
          rfl
        have hηtree : cappedTree B (fun x => η (i :: x)) [] = cappedTree B η [i] := by
          apply congrArg prune
          funext x
          rfl
        simpa only [hω, hη, true_and, List.nil_append, hωtree, hηtree] using hrec
      · have hη : ¬(1 ≤ i ∧ i ≤ min (η []) B) := by rwa [← hroot]
        change (1 ≤ i ∧ i ≤ min (ω []) B ∧
            Present (child (cappedTree B ω []) i) u) =
          (1 ≤ i ∧ i ≤ min (η []) B ∧
            Present (child (cappedTree B η []) i) u)
        apply propext
        constructor
        · intro hc
          exact (hω ⟨hc.1, hc.2.1⟩).elim
        · intro hc
          exact (hη ⟨hc.1, hc.2.1⟩).elim

/-- Capped-generation membership reads exactly the strict-ancestor block. -/
theorem mem_capGen_dependsOn (B : ℕ) (w : Address) (k : ℕ) :
    DependsOn (fun ω => w ∈ capGen B ω [] k)
      {p | p <+: w ∧ p ≠ w} := by
  intro ω η h
  have hp := cappedPresent_dependsOn B w h
  simp only [mem_capGen_root, hp]


/-- Measurability of the capped descendant-tree map. -/
theorem measurable_cappedTree (B : ℕ) (v : Address) :
    Measurable (fun ω => cappedTree B ω v) := by
  apply measurable_prune.comp
  exact Measurable.of_eval fun u => (measurable_pi_apply (v ++ u)).min measurable_const

/-- **First moment.** Capped generation sizes have mean `b ^ j`. -/
theorem lintegral_capZ (B : ℕ) (j : ℕ) :
    (∫⁻ ω, (capZ B ω [] j : ℝ≥0∞) ∂offspringFieldLaw μ) = cappedMean μ B ^ j := by
  have hmp : MeasurePreserving (fun ω => cappedTree B ω [])
      (offspringFieldLaw μ) (bienaymeLaw (cappedLaw μ B)) :=
    ⟨measurable_cappedTree B [], map_cappedTree B⟩
  have hf : Measurable (fun T : Tree => (generationSize T j : ℝ≥0∞)) :=
    (measurable_of_countable _).comp (measurable_generationSize j)
  calc
    _ = ∫⁻ T, (generationSize T j : ℝ≥0∞) ∂bienaymeLaw (cappedLaw μ B) := by
      simpa only [capZ_eq_generationSize] using hmp.lintegral_comp hf
    _ = (∫⁻ k, (k : ℝ≥0∞) ∂cappedLaw μ B) ^ j :=
      lintegral_generationSize (cappedLaw μ B) j
    _ = cappedMean μ B ^ j := by rw [cappedLaw_mean]

private theorem sum_ite_eq_add_off {k : ℕ} (A M : ℝ≥0∞) (i : Fin k) :
    (∑ j : Fin k, if i = j then A else M) = A + (k - 1) * M := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin k)) (fun j => i = j)]
  have heq : {x ∈ (Finset.univ : Finset (Fin k)) | i = x} = {i} := by
    ext x
    simp [eq_comm]
  have hne : {x ∈ (Finset.univ : Finset (Fin k)) | ¬i = x} = Finset.univ \ {i} := by
    ext x
    simp [eq_comm]
  rw [heq, hne]
  have hsum : (∑ x ∈ Finset.univ \ {i}, if i = x then A else M) =
      ∑ _x ∈ Finset.univ \ ({i} : Finset (Fin k)), M := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxi : ¬i = x := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and] at hx
      exact fun h => hx h.symm
    rw [ite_eq_right hxi]
  rw [hsum]
  have hcard : (Finset.univ \ ({i} : Finset (Fin k))).card = k - 1 := by
    rw [Finset.card_sdiff]
    simp
  simp only [Finset.sum_singleton, ite_true, Finset.sum_const, nsmul_eq_mul]
  rw [hcard, ENNReal.natCast_sub k 1]
  simp

/-- The square of a sum over independent child observables, with diagonal
term `A` and common first moment `M`. -/
theorem lintegral_pi_sum_sq {k : ℕ} (μ : Measure Tree) [IsProbabilityMeasure μ]
    (f : Tree → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ts : Fin k → Tree, (∑ i, f (ts i)) ^ 2 ∂Measure.pi (fun _ => μ)) =
      (k : ℝ≥0∞) * (∫⁻ T, f T ^ 2 ∂μ) +
        (k : ℝ≥0∞) * (k - 1) * (∫⁻ T, f T ∂μ) ^ 2 := by
  let A : ℝ≥0∞ := ∫⁻ T, f T ^ 2 ∂μ
  let M : ℝ≥0∞ := ∫⁻ T, f T ∂μ
  have hm (i : Fin k) : Measurable (fun ts : Fin k → Tree => f (ts i)) :=
    hf.comp (measurable_pi_apply i)
  have heval {g : Tree → ℝ≥0∞} (hg : Measurable g) (i : Fin k) :
      (∫⁻ ts : Fin k → Tree, g (ts i) ∂Measure.pi (fun _ => μ)) = ∫⁻ T, g T ∂μ :=
    (measurePreserving_eval (fun _ : Fin k => μ) i).lintegral_comp hg
  have hind : iIndepFun (fun (i : Fin k) (ts : Fin k → Tree) => f (ts i))
      (Measure.pi fun _ : Fin k => μ) := iIndepFun_pi (fun _ => hf.aemeasurable)
  have hp (i j : Fin k) :
      (∫⁻ ts : Fin k → Tree, f (ts i) * f (ts j) ∂Measure.pi (fun _ => μ)) =
        if i = j then A else M ^ 2 := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      dsimp only [A]
      simp_rw [pow_two]
      exact heval (hf.mul hf) i
    · simp only [ite_eq_right hij]
      rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (hm i).aemeasurable
        (hm j).aemeasurable (hind.indepFun hij), heval hf i, heval hf j, pow_two]
  calc
    _ = ∫⁻ ts : Fin k → Tree, ∑ i : Fin k, ∑ j : Fin k, f (ts i) * f (ts j) ∂
        Measure.pi (fun _ => μ) := by
      apply lintegral_congr
      intro ts
      rw [pow_two, Fintype.sum_mul_sum]
    _ = ∑ i : Fin k, ∫⁻ ts : Fin k → Tree, ∑ j : Fin k, f (ts i) * f (ts j) ∂
        Measure.pi (fun _ => μ) := by
      rw [lintegral_finsetSum (f := fun (i : Fin k) (ts : Fin k → Tree) =>
        ∑ j : Fin k, f (ts i) * f (ts j)) _
        (fun i _ => Finset.univ.measurable_sum (fun j _ => (hm i).mul (hm j)))]
    _ = ∑ i : Fin k, ∑ j : Fin k, if i = j then A else M ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [lintegral_finsetSum (f := fun (j : Fin k) (ts : Fin k → Tree) =>
        f (ts i) * f (ts j)) _ (fun j _ => (hm i).mul (hm j))]
      exact Finset.sum_congr rfl (fun j _ => hp i j)
    _ = (k : ℝ≥0∞) * A + (k : ℝ≥0∞) * (k - 1) * M ^ 2 := by
      simp_rw [sum_ite_eq_add_off]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_add]
      ac_rfl
    _ = _ := rfl


private theorem lintegral_bienayme_eq_tsum_degree (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (g : Tree → ℝ≥0∞) :
    ∫⁻ T, g T ∂bienaymeLaw μ = ∑' k : ℕ, ∫⁻ T in {T | degree T = k}, g T ∂bienaymeLaw μ := by
  have hu : ⋃ k : ℕ, {T | degree T = k} = Set.univ := by ext T; simp
  have h := lintegral_iUnion (μ := bienaymeLaw μ) (s := fun k : ℕ => {T | degree T = k})
    (fun k => continuous_degree.measurable (measurableSet_singleton k))
    (fun i j hij => Set.disjoint_left.mpr fun T hi hj => hij (hi.symm.trans hj)) g
  simpa only [hu, Measure.restrict_univ] using h

/-- Subtraction-free exact second-moment recursion for RTL generation sizes. -/
theorem lintegral_generationSize_sq_succ_add (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (j : ℕ) :
    (∫⁻ T, (generationSize T (j + 1) : ℝ≥0∞) ^ 2 ∂bienaymeLaw μ) +
        (∫⁻ k, (k : ℝ≥0∞) ∂μ) * ((∫⁻ k, (k : ℝ≥0∞) ∂μ) ^ j) ^ 2 =
      (∫⁻ k, (k : ℝ≥0∞) ∂μ) * ∫⁻ T, (generationSize T j : ℝ≥0∞) ^ 2 ∂bienaymeLaw μ +
        (∫⁻ k, (k : ℝ≥0∞) ^ 2 ∂μ) * ((∫⁻ k, (k : ℝ≥0∞) ∂μ) ^ j) ^ 2 := by
  let b : ℝ≥0∞ := ∫⁻ k, (k : ℝ≥0∞) ∂μ
  let q : ℝ≥0∞ := ∫⁻ k, (k : ℝ≥0∞) ^ 2 ∂μ
  let A : ℝ≥0∞ := ∫⁻ T, (generationSize T j : ℝ≥0∞) ^ 2 ∂bienaymeLaw μ
  let M : ℝ≥0∞ := b ^ j
  have hf : Measurable (fun T : Tree => (generationSize T j : ℝ≥0∞)) :=
    (measurable_of_countable _).comp (measurable_generationSize j)
  have hroot (k : ℕ) :
      (∫⁻ T in {T | degree T = k}, (generationSize T (j + 1) : ℝ≥0∞) ^ 2 ∂bienaymeLaw μ) =
        μ {k} * ((k : ℝ≥0∞) * A + (k : ℝ≥0∞) * (k - 1) * M ^ 2) := by
    have he : (∫⁻ T in {T | degree T = k}, (generationSize T (j + 1) : ℝ≥0∞) ^ 2 ∂
        bienaymeLaw μ) = ∫⁻ T in {T | degree T = k},
        (∑ i : Fin k, (generationSize (child T (i.val + 1)) j : ℝ≥0∞)) ^ 2 ∂bienaymeLaw μ := by
      apply setLIntegral_congr_fun (continuous_degree.measurable (measurableSet_singleton k))
      intro T hT
      change degree T = k at hT
      dsimp only
      rw [generationSize_succ_eq_sum, hT, Nat.cast_sum]
    have hg : Measurable (fun ts : Fin k → Tree =>
        (∑ i : Fin k, (generationSize (ts i) j : ℝ≥0∞)) ^ 2) :=
      (Finset.univ.measurable_sum fun i _ => hf.comp (measurable_pi_apply i)).pow_const 2
    rw [he, lintegral_children_of_degree μ k hg]
    congr 1
    simpa only [A, M, lintegral_generationSize] using
      lintegral_pi_sum_sq (bienaymeLaw μ) (fun T => (generationSize T j : ℝ≥0∞)) hf
  have hdecomp :
      (∫⁻ T, (generationSize T (j + 1) : ℝ≥0∞) ^ 2 ∂bienaymeLaw μ) =
        ∑' k : ℕ, μ {k} * ((k : ℝ≥0∞) * A + (k : ℝ≥0∞) * (k - 1) * M ^ 2) := by
    rw [lintegral_bienayme_eq_tsum_degree]
    exact tsum_congr hroot
  have hbA : b * A = ∑' k : ℕ, μ {k} * ((k : ℝ≥0∞) * A) := by
    dsimp only [b]
    rw [lintegral_countable', ← ENNReal.tsum_mul_right]
    exact tsum_congr fun k => by ac_rfl
  have hbM : b * M ^ 2 = ∑' k : ℕ, μ {k} * ((k : ℝ≥0∞) * M ^ 2) := by
    dsimp only [b]
    rw [lintegral_countable', ← ENNReal.tsum_mul_right]
    exact tsum_congr fun k => by ac_rfl
  have hqM : q * M ^ 2 = ∑' k : ℕ, μ {k} * ((k : ℝ≥0∞) ^ 2 * M ^ 2) := by
    dsimp only [q]
    rw [lintegral_countable', ← ENNReal.tsum_mul_right]
    exact tsum_congr fun k => by ac_rfl
  have hnat (k : ℕ) : k * (k - 1) + k = k * k := by
    cases k with
    | zero => simp
    | succ k => simp [Nat.succ_mul, Nat.mul_add]
  have hk (k : ℕ) : (k : ℝ≥0∞) * (k - 1) + k = (k : ℝ≥0∞) ^ 2 := by
    calc
      _ = ((k * (k - 1) + k : ℕ) : ℝ≥0∞) := by
        simp [Nat.cast_add, Nat.cast_mul, ENNReal.natCast_sub]
      _ = ((k * k : ℕ) : ℝ≥0∞) := by rw [hnat]
      _ = _ := by simp [pow_two]
  change (∫⁻ T, (generationSize T (j + 1) : ℝ≥0∞) ^ 2 ∂bienaymeLaw μ) + b * M ^ 2 =
    b * A + q * M ^ 2
  rw [hdecomp, hbM, hbA, hqM, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  apply tsum_congr
  intro k
  calc
    μ {k} * ((k : ℝ≥0∞) * A + (k : ℝ≥0∞) * (k - 1) * M ^ 2) +
        μ {k} * ((k : ℝ≥0∞) * M ^ 2) =
      μ {k} * ((k : ℝ≥0∞) * A +
        ((k : ℝ≥0∞) * (k - 1) * M ^ 2 + k * M ^ 2)) := by
          simp only [mul_add, add_assoc]
    _ = μ {k} * ((k : ℝ≥0∞) * A + (k : ℝ≥0∞) ^ 2 * M ^ 2) := by
      congr 2
      rw [← add_mul, hk]
    _ = μ {k} * ((k : ℝ≥0∞) * A) + μ {k} * ((k : ℝ≥0∞) ^ 2 * M ^ 2) := by
      rw [mul_add]


/-- Hölder with exponents two gives nonnegativity of the extended second
moment minus the square of the first. -/
theorem lintegral_sq_le_lintegral_sq (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (f : ℕ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ k, f k ∂μ) ^ 2 ≤ ∫⁻ k, f k ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2)
    (g := fun _ => 1) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    hf.aemeasurable measurable_const.aemeasurable
  simp only [Pi.mul_apply, mul_one, measure_univ, lintegral_const, ENNReal.one_rpow] at h
  have hh := ENNReal.rpow_le_rpow h (show 0 ≤ (2 : ℝ) by norm_num)
  rw [← ENNReal.rpow_mul] at hh
  norm_num at hh
  simpa only [ENNReal.rpow_natCast] using hh

@[simp] theorem cappedLaw_secondMoment (B : ℕ) :
    (∫⁻ k, (k : ℝ≥0∞) ^ 2 ∂cappedLaw μ B) = cappedSecondMoment μ B := by
  exact lintegral_map (measurable_of_countable _) (measurable_of_countable _)

/-- Transport of the extended squared-generation integral to the capped
Bienaymé law. -/
theorem lintegral_capZ_sq (B : ℕ) (j : ℕ) :
    (∫⁻ ω, (capZ B ω [] j : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ) =
      ∫⁻ T, (generationSize T j : ℝ≥0∞) ^ 2 ∂bienaymeLaw (cappedLaw μ B) := by
  have hmp : MeasurePreserving (fun ω => cappedTree B ω [])
      (offspringFieldLaw μ) (bienaymeLaw (cappedLaw μ B)) :=
    ⟨measurable_cappedTree B [], map_cappedTree B⟩
  have hf : Measurable (fun T : Tree => (generationSize T j : ℝ≥0∞) ^ 2) :=
    ((measurable_of_countable _).comp (measurable_generationSize j)).pow_const 2
  simpa only [capZ_eq_generationSize] using hmp.lintegral_comp hf

/-- Exact root recursion for capped generation second moments. -/
theorem lintegral_capZ_sq_succ_add (B : ℕ) (j : ℕ) :
    (∫⁻ ω, (capZ B ω [] (j + 1) : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ) +
        cappedMean μ B * (cappedMean μ B ^ j) ^ 2 =
      cappedMean μ B * ∫⁻ ω, (capZ B ω [] j : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ +
        cappedSecondMoment μ B * (cappedMean μ B ^ j) ^ 2 := by
  have h := lintegral_generationSize_sq_succ_add (cappedLaw μ B) j
  rwa [← lintegral_capZ_sq (μ := μ) B (j + 1), ← lintegral_capZ_sq (μ := μ) B j,
    cappedLaw_mean, cappedLaw_secondMoment] at h

/-- Pruning never increases a uniform bound on an offspring field. -/
theorem pruneRaw_le_of_forall (f : Offspring) {B : ℕ} (h : ∀ u, f u ≤ B) :
    ∀ u, pruneRaw f u ≤ B := by
  intro u
  induction u generalizing f with
  | nil => exact h []
  | cons j u ih =>
      simp only [pruneRaw]
      split_ifs
      · exact ih (fun v => f (j :: v)) (fun v => h (j :: v))
      · exact Nat.zero_le B

@[simp] theorem cappedTree_offspring_le (B : ℕ) (ω : Offspring) (v u : Address) :
    (cappedTree B ω v).val u ≤ B := by
  apply pruneRaw_le_of_forall
  intro a
  exact Nat.min_le_right _ _

/-- A tree with offspring at most `B` has at most `B ^ j` vertices in
 generation `j`. -/
theorem generationSize_le_of_forall_offspring_le (T : Tree) {B : ℕ}
    (h : ∀ u, T.val u ≤ B) : ∀ j, generationSize T j ≤ B ^ j := by
  intro j
  induction j generalizing T with
  | zero => simp
  | succ j ih =>
      rw [generationSize_succ]
      calc
        _ ≤ ∑ _j ∈ Finset.range (degree T), B ^ j := by
          apply Finset.sum_le_sum
          intro i _
          exact ih (child T (i + 1)) (fun u => h ((i + 1) :: u))
        _ = degree T * B ^ j := by simp
        _ ≤ B * B ^ j := Nat.mul_le_mul_right _ (by simpa [degree] using h [])
        _ = B ^ (j + 1) := by rw [pow_succ']

@[simp] theorem capZ_le (B : ℕ) (ω : Offspring) (v : Address) (j : ℕ) :
    capZ B ω v j ≤ B ^ j := by
  rw [capZ_eq_generationSize]
  exact generationSize_le_of_forall_offspring_le (cappedTree B ω v)
    (cappedTree_offspring_le B ω v) j

@[simp] theorem cappedMean_ne_top (B : ℕ) : cappedMean μ B ≠ ⊤ := by
  apply (IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal μ
    ⟨(B : ℝ≥0), fun k => by exact_mod_cast Nat.min_le_right k B⟩).ne

@[simp] theorem cappedSecondMoment_ne_top (B : ℕ) : cappedSecondMoment μ B ≠ ⊤ := by
  apply (IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal μ
    ⟨((B : ℝ≥0) ^ 2), fun k => by
      exact_mod_cast pow_le_pow_left' (Nat.min_le_right k B) 2⟩).ne

@[simp] theorem lintegral_capZ_sq_ne_top (B : ℕ) (j : ℕ) :
    (∫⁻ ω, (capZ B ω [] j : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ) ≠ ⊤ := by
  apply (IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal _
    ⟨((B : ℝ≥0) ^ j) ^ 2, fun ω => by
      exact_mod_cast pow_le_pow_left' (capZ_le B ω [] j) 2⟩).ne

/-- Real form of the exact recursion, with the subtraction justified by the
boundedness of every capped generation. -/
theorem lintegral_capZ_sq_toReal_succ (B : ℕ) (j : ℕ) :
    (∫⁻ ω, (capZ B ω [] (j + 1) : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ).toReal =
      cappedMeanReal μ B *
          (∫⁻ ω, (capZ B ω [] j : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ).toReal +
        ((cappedSecondMoment μ B).toReal - cappedMeanReal μ B) *
          (cappedMeanReal μ B ^ j) ^ 2 := by
  have h := congrArg ENNReal.toReal (lintegral_capZ_sq_succ_add (μ := μ) B j)
  have hbM : cappedMean μ B * (cappedMean μ B ^ j) ^ 2 ≠ ⊤ := by
    exact ENNReal.mul_ne_top (cappedMean_ne_top B)
      (ENNReal.pow_ne_top (ENNReal.pow_ne_top (cappedMean_ne_top B)))
  rw [ENNReal.toReal_add (lintegral_capZ_sq_ne_top B (j + 1)) hbM] at h
  have hbA : cappedMean μ B *
      (∫⁻ ω, (capZ B ω [] j : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ) ≠ ⊤ :=
    ENNReal.mul_ne_top (cappedMean_ne_top B) (lintegral_capZ_sq_ne_top B j)
  have hqM : cappedSecondMoment μ B * (cappedMean μ B ^ j) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (cappedSecondMoment_ne_top B)
      (ENNReal.pow_ne_top (ENNReal.pow_ne_top (cappedMean_ne_top B)))
  rw [ENNReal.toReal_add hbA hqM] at h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow] at h
  dsimp only [cappedMeanReal]
  linarith


/-- Variance of the bounded capped offspring, in real form. -/
noncomputable def cappedVariance (μ : Measure ℕ) [IsProbabilityMeasure μ] (B : ℕ) : ℝ :=
  (cappedSecondMoment μ B).toReal - (cappedMeanReal μ B) ^ 2

/-- The uniform second-moment constant `1 + σ² / (b * (b - 1))`. -/
noncomputable def cappedMomentBound (μ : Measure ℕ) [IsProbabilityMeasure μ] (B : ℕ) : ℝ :=
  1 + cappedVariance μ B / (cappedMeanReal μ B * (cappedMeanReal μ B - 1))

/-- Nonnegative capped variance makes this constant at least one. -/
theorem one_le_cappedMomentBound {B : ℕ} (hb : 1 < cappedMeanReal μ B) :
    1 ≤ cappedMomentBound μ B := by
  have hvE : cappedMean μ B ^ 2 ≤ cappedSecondMoment μ B :=
    lintegral_sq_le_lintegral_sq μ (fun k => ((min k B : ℕ) : ℝ≥0∞))
      (measurable_of_countable _)
  have hv : (cappedMeanReal μ B) ^ 2 ≤ (cappedSecondMoment μ B).toReal := by
    have hh := (ENNReal.toReal_le_toReal
      (ENNReal.pow_ne_top (cappedMean_ne_top B)) (cappedSecondMoment_ne_top B)).2 hvE
    simpa only [ENNReal.toReal_pow, cappedMeanReal] using hh
  have hb0 : 0 < cappedMeanReal μ B := zero_lt_one.trans hb
  have hd : 0 < cappedMeanReal μ B * (cappedMeanReal μ B - 1) :=
    mul_pos hb0 (sub_pos.mpr hb)
  have hv0 : 0 ≤ cappedVariance μ B := by
    dsimp only [cappedVariance]
    linarith
  have hr : 0 ≤ cappedVariance μ B /
      (cappedMeanReal μ B * (cappedMeanReal μ B - 1)) := div_nonneg hv0 hd.le
  dsimp only [cappedMomentBound]
  linarith

/-- Real second-moment estimate for capped generations. -/
theorem lintegral_capZ_sq_toReal_le {B : ℕ} (hb : 1 < cappedMeanReal μ B) (j : ℕ) :
    (∫⁻ ω, (capZ B ω [] j : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ).toReal ≤
      cappedMomentBound μ B * cappedMeanReal μ B ^ (2 * j) := by
  let A : ℕ → ℝ := fun j =>
    (∫⁻ ω, (capZ B ω [] j : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ).toReal
  let b : ℝ := cappedMeanReal μ B
  let q : ℝ := (cappedSecondMoment μ B).toReal
  let C : ℝ := cappedMomentBound μ B
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hCdyn : b * C + (q - b) = C * b ^ 2 := by
    dsimp only [C, cappedMomentBound, cappedVariance, q, b]
    field_simp [hb0.ne', (sub_pos.mpr hb).ne']
    ring
  change A j ≤ C * b ^ (2 * j)
  induction j with
  | zero =>
      have hC := one_le_cappedMomentBound (μ := μ) hb
      simpa [A, b, capZ_eq_generationSize, cappedTree] using hC
  | succ j ih =>
      have hrec := lintegral_capZ_sq_toReal_succ (μ := μ) B j
      change A (j + 1) = b * A j + (q - b) * (b ^ j) ^ 2 at hrec
      have hpow : (b ^ j) ^ 2 = b ^ (2 * j) := by
        rw [← pow_mul]
        congr 1
        omega
      rw [hpow] at hrec
      calc
        A (j + 1) = b * A j + (q - b) * b ^ (2 * j) := hrec
        _ ≤ b * (C * b ^ (2 * j)) + (q - b) * b ^ (2 * j) :=
          add_le_add (mul_le_mul_of_nonneg_left ih hb0.le) le_rfl
        _ = (b * C + (q - b)) * b ^ (2 * j) := by ring
        _ = (C * b ^ 2) * b ^ (2 * j) := by rw [hCdyn]
        _ = C * b ^ (2 * (j + 1)) := by
          rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
          ring

/-- **Second moment.** The normalized capped second moments are bounded
uniformly by `1 + σ² / (b * (b - 1))`. -/
theorem lintegral_capZ_sq_le {B : ℕ} (hb : 1 < cappedMeanReal μ B) (j : ℕ) :
    (∫⁻ ω, (capZ B ω [] j : ℝ≥0∞) ^ 2 ∂offspringFieldLaw μ) ≤
      ENNReal.ofReal (cappedMomentBound μ B) * cappedMean μ B ^ (2 * j) := by
  have hC : 0 ≤ cappedMomentBound μ B :=
    zero_le_one.trans (one_le_cappedMomentBound (μ := μ) hb)
  have hr : (ENNReal.ofReal (cappedMomentBound μ B) * cappedMean μ B ^ (2 * j)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (cappedMean_ne_top B))
  apply (ENNReal.toReal_le_toReal (lintegral_capZ_sq_ne_top B j) hr).1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_pow]
  exact lintegral_capZ_sq_toReal_le (μ := μ) hb j

end LPPMonotonicityProof.Speed
