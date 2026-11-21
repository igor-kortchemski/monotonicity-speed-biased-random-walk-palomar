module

public import LPPMonotonicityProof.Analytic.Interface
public import LPPMonotonicityProof.Speed.Env.Lin
public import LPPMonotonicityProof.Speed.Env.Swap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The first branching vertex

This module proves the pathwise identity `Y = L W` with `L = λ^(-G)` and the law
part of Lemma 4.1 (`lem:prefix-terminal`): the unary prefix length `G` is geometric
and independent of the split tree, whose law is the Bienaymé law conditioned on
`ν ≥ 2`.  The proof first isolates the pathwise recursion of
`prefixLen` and `splitTree`, then applies the ordered root decomposition of the
Bienaymé law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem subtree_replicate_succ (T : Tree) (n : ℕ) :
    subtree T (List.replicate (n + 1) 1) = subtree (child T 1) (List.replicate n 1) := by
  rw [List.replicate_succ, subtree_cons]

private theorem prefixLen_eq_zero_of_degree_ne_one {T : Tree} (hT : degree T ≠ 1) :
    prefixLen T = 0 := by
  unfold prefixLen
  rw [Nat.sInf_eq_zero]
  left
  simpa using hT

private theorem degree_eq_one_of_prefixLen_succ {T : Tree} {n : ℕ}
    (hT : prefixLen T = n + 1) : degree T = 1 := by
  by_contra hdeg
  have hz := prefixLen_eq_zero_of_degree_ne_one hdeg
  omega

private theorem prefixLen_child_of_succ {T : Tree} {n : ℕ}
    (hT : prefixLen T = n + 1) : prefixLen (child T 1) = n := by
  have hne : {j | degree (subtree T (List.replicate j 1)) ≠ 1}.Nonempty :=
    Nat.nonempty_of_sInf_eq_succ hT
  have hmem := Nat.sInf_mem hne
  change degree (subtree T (List.replicate (prefixLen T) 1)) ≠ 1 at hmem
  rw [hT, subtree_replicate_succ] at hmem
  change prefixLen (child T 1) = n
  apply le_antisymm (Nat.sInf_le hmem)
  by_contra hle
  have hlt : prefixLen (child T 1) < n := Nat.lt_of_not_ge hle
  have hcmem := Nat.sInf_mem (show {j | degree (subtree (child T 1)
    (List.replicate j 1)) ≠ 1}.Nonempty from ⟨n, hmem⟩)
  change degree (subtree (child T 1)
    (List.replicate (prefixLen (child T 1)) 1)) ≠ 1 at hcmem
  have hrootmem : degree (subtree T
      (List.replicate (prefixLen (child T 1) + 1) 1)) ≠ 1 := by
    rwa [subtree_replicate_succ]
  have hle' : sInf {j | degree (subtree T (List.replicate j 1)) ≠ 1} ≤
      prefixLen (child T 1) + 1 := Nat.sInf_le hrootmem
  change prefixLen T ≤ prefixLen (child T 1) + 1 at hle'
  omega

private theorem splitTree_child_of_succ {T : Tree} {n : ℕ}
    (hT : prefixLen T = n + 1) : splitTree T = splitTree (child T 1) := by
  unfold splitTree
  rw [hT, prefixLen_child_of_succ hT, subtree_replicate_succ]

private def UnaryRay : Set Tree :=
  {T | ∀ n, degree (subtree T (List.replicate n 1)) = 1}

private theorem measurableSet_unaryRay : MeasurableSet (UnaryRay : Set Tree) := by
  rw [show (UnaryRay : Set Tree) = ⋂ n : ℕ,
    {T : Tree | degree (subtree T (List.replicate n 1)) = 1} by
      ext T
      simp [UnaryRay]]
  exact MeasurableSet.iInter fun n =>
    (continuous_degree.measurable.comp (measurable_subtree _)) (measurableSet_singleton 1)

private theorem unaryRay_iff (T : Tree) :
    T ∈ UnaryRay ↔ degree T = 1 ∧ child T 1 ∈ UnaryRay := by
  constructor
  · intro hT
    have hdeg := hT 0
    simp only [List.replicate_zero, subtree_nil] at hdeg
    refine ⟨hdeg, fun n => ?_⟩
    have hs := hT (n + 1)
    rwa [subtree_replicate_succ] at hs
  · rintro ⟨hdeg, hchild⟩ n
    cases n with
    | zero => simpa using hdeg
    | succ n =>
        rw [subtree_replicate_succ]
        exact hchild n

private theorem not_unaryRay_of_prefixLen_succ {T : Tree} {n : ℕ}
    (hT : prefixLen T = n + 1) : T ∉ UnaryRay := by
  intro hray
  have hne : {j | degree (subtree T (List.replicate j 1)) ≠ 1}.Nonempty :=
    Nat.nonempty_of_sInf_eq_succ hT
  have hmem := Nat.sInf_mem hne
  exact hmem (hray _)

private theorem allUnary_of_prefixLen_zero_of_degree_one {T : Tree}
    (hpre : prefixLen T = 0) (hdeg : degree T = 1) : T ∈ UnaryRay := by
  intro n
  by_contra hbad
  have hmem := Nat.sInf_mem (show {j | degree (subtree T
    (List.replicate j 1)) ≠ 1}.Nonempty from ⟨n, hbad⟩)
  change degree (subtree T (List.replicate (prefixLen T) 1)) ≠ 1 at hmem
  rw [hpre] at hmem
  exact hmem (by simpa using hdeg)

private theorem sInf_eq_of_mem_min {S : Set ℕ} {n : ℕ}
    (hn : n ∈ S) (hmin : ∀ j < n, j ∉ S) : sInf S = n := by
  apply le_antisymm (Nat.sInf_le hn)
  by_contra hle
  have hlt : sInf S < n := Nat.lt_of_not_ge hle
  exact hmin _ hlt (Nat.sInf_mem ⟨n, hn⟩)

private theorem prefixLen_succ_of_child {T : Tree} {n : ℕ}
    (hdeg : degree T = 1) (hchild : prefixLen (child T 1) = n)
    (hray : T ∉ UnaryRay) : prefixLen T = n + 1 := by
  have hchildray : child T 1 ∉ UnaryRay := by
    intro hc
    exact hray ((unaryRay_iff T).2 ⟨hdeg, hc⟩)
  have hne : {j | degree (subtree (child T 1) (List.replicate j 1)) ≠ 1}.Nonempty := by
    by_contra hnone
    rw [Set.not_nonempty_iff_eq_empty] at hnone
    apply hchildray
    intro j
    by_contra hj
    have : j ∈ {j | degree (subtree (child T 1) (List.replicate j 1)) ≠ 1} := hj
    rw [hnone] at this
    exact this
  have hmem := Nat.sInf_mem hne
  change degree (subtree (child T 1)
    (List.replicate (prefixLen (child T 1)) 1)) ≠ 1 at hmem
  rw [hchild] at hmem
  apply sInf_eq_of_mem_min
  · change degree (subtree T (List.replicate (n + 1) 1)) ≠ 1
    rwa [subtree_replicate_succ]
  · intro j hj
    cases j with
    | zero => simpa using hdeg
    | succ j =>
        simp only [Set.mem_setOf_eq, subtree_replicate_succ]
        exact Nat.notMem_of_lt_sInf (by change j < prefixLen (child T 1); omega)

/-- The local split identity `λ Y = W` at an arbitrary tree. -/
theorem l_mul_Yt_eq_Wt {l : ℝ} (hl : 1 < l) (T : Tree) :
    l * Yt l T = Wt l T := by
  have hl0 : 0 < l := lt_trans zero_lt_one hl
  have hS : 0 ≤ childSum l T := by
    unfold childSum
    exact Finset.sum_nonneg fun i _ => (escape_mem_Icc hl0 _).1
  have hden₁ : l + childSum l T ≠ 0 := by positivity
  have hden₂ : l - 1 + childSum l T ≠ 0 := by positivity
  rw [Yt, Wt, escape_eq hl0]
  field_simp
  ring

private theorem l_mul_Yt_eq_Yt_child {l : ℝ} (hl : 1 < l) {T : Tree}
    (hdeg : degree T = 1) : l * Yt l T = Yt l (child T 1) := by
  rw [l_mul_Yt_eq_Wt hl]
  unfold Wt Yt
  have hc : childSum l T = escape l (child T 1) := by
    unfold childSum
    rw [hdeg]
    exact Fin.sum_univ_one _
  rw [hc]

/-- Lemma 4.1 (`lem:prefix-terminal`): `Y = L · W` pathwise, with `L = l ^ (-G)`. -/
theorem Yt_eq_prefix {l : ℝ} (hl : 1 < l) (T : Tree)
    (hsplit : 2 ≤ degree (splitTree T)) :
    Yt l T = l ^ (-(Gt T : ℤ)) * Wt l (splitTree T) := by
  generalize hpre : prefixLen T = n
  revert T
  induction n with
  | zero =>
      intro T hsplit hpre
      have hst : splitTree T = T := by simp [splitTree, hpre]
      have hgt : Gt T = 1 := by simp [Gt, hpre]
      rw [hst, hgt]
      have h := l_mul_Yt_eq_Wt hl T
      have hl0 : l ≠ 0 := ne_of_gt (lt_trans zero_lt_one hl)
      rw [show (-((1 : ℕ) : ℤ)) = -1 by norm_num, zpow_neg_one]
      field_simp
      simpa [mul_comm] using h
  | succ n ih =>
      intro T hsplit hpre
      have hdeg := degree_eq_one_of_prefixLen_succ hpre
      have hchild := prefixLen_child_of_succ hpre
      have hst := splitTree_child_of_succ hpre
      have hsplitchild : 2 ≤ degree (splitTree (child T 1)) := by rwa [← hst]
      have hrec := ih (child T 1) hsplitchild hchild
      have hlocal := l_mul_Yt_eq_Yt_child hl hdeg
      have hgt : Gt T = Gt (child T 1) + 1 := by simp [Gt, hpre, hchild]
      have hl0 : l ≠ 0 := ne_of_gt (lt_trans zero_lt_one hl)
      rw [hgt]
      rw [show -((Gt (child T 1) + 1 : ℕ) : ℤ) =
        -(Gt (child T 1) : ℤ) + (-1 : ℤ) by push_cast; ring]
      rw [zpow_add₀ hl0, zpow_neg_one]
      rw [← hst] at hrec
      have hy : Yt l T = Yt l (child T 1) / l := by
        apply (eq_div_iff hl0).2
        simpa [mul_comm] using hlocal
      rw [hy, hrec]
      field_simp

private theorem child_nodeFin_one (ts : Fin 1 → Tree) : child (nodeFin 1 ts) 1 = ts 0 := by
  rw [nodeFin, child_node_of_valid _ (by omega)]
  simp

private theorem measure_unary_preimage {E : Set Tree} (hE : MeasurableSet E) :
    GW μ {T | degree T = 1 ∧ child T 1 ∈ E} = μ {1} * GW μ E := by
  have hpre : MeasurableSet ((fun T : Tree => child T 1) ⁻¹' E) :=
    (continuous_child 1).measurable hE
  calc
    GW μ {T | degree T = 1 ∧ child T 1 ∈ E} =
        (GW μ).restrict {T | degree T = 1} ((fun T : Tree => child T 1) ⁻¹' E) := by
      rw [Measure.restrict_apply hpre]
      congr 1
      ext T
      simp [and_comm]
    _ = (μ {1} • (Measure.pi fun _ : Fin 1 => GW μ).map (nodeFin 1))
        ((fun T : Tree => child T 1) ⁻¹' E) := by rw [bienaymeLaw_restrict_degree]
    _ = μ {1} * ((Measure.pi fun _ : Fin 1 => GW μ).map (nodeFin 1))
        ((fun T : Tree => child T 1) ⁻¹' E) := by rw [Measure.smul_apply, smul_eq_mul]
    _ = μ {1} * (Measure.pi fun _ : Fin 1 => GW μ)
        (nodeFin 1 ⁻¹' ((fun T : Tree => child T 1) ⁻¹' E)) := by
      rw [Measure.map_apply (measurable_nodeFin 1) hpre]
    _ = μ {1} * (Measure.pi fun _ : Fin 1 => GW μ) ((fun ts : Fin 1 → Tree => ts 0) ⁻¹' E) := by
      congr 2
    _ = μ {1} * GW μ E := by
      rw [← Measure.map_apply (measurable_pi_apply 0) hE,
        (measurePreserving_eval (fun _ : Fin 1 => GW μ) 0).map_eq]

private theorem unaryRay_measure_zero (h : OffspringHyp μ) : GW μ UnaryRay = 0 := by
  have hset : UnaryRay = {T : Tree | degree T = 1 ∧ child T 1 ∈ UnaryRay} := by
    ext T
    exact unaryRay_iff T
  have heq : GW μ UnaryRay = μ {1} * GW μ UnaryRay := by
    calc
      GW μ UnaryRay = GW μ {T : Tree | degree T = 1 ∧ child T 1 ∈ UnaryRay} :=
        congrArg (GW μ) hset
      _ = μ {1} * GW μ UnaryRay := measure_unary_preimage measurableSet_unaryRay
  have hp : p1 μ < 1 := by
    have hsum := p1_add_pBr h
    have hp := pBr_pos h
    linarith
  have hreal : (GW μ UnaryRay).toReal = p1 μ * (GW μ UnaryRay).toReal := by
    have hr := congrArg ENNReal.toReal heq
    simpa [p1] using hr
  have hz : (GW μ UnaryRay).toReal = 0 := by nlinarith
  rw [ENNReal.toReal_eq_zero_iff] at hz
  exact hz.resolve_right (measure_ne_top _ _)

private theorem GW_degree_zero (h : OffspringHyp μ) : GW μ {T | degree T = 0} = 0 := by
  have hmap := congrArg (fun ν : Measure ℕ => ν {0}) (bienaymeLaw_map_degree μ)
  rw [Measure.map_apply continuous_degree.measurable (measurableSet_singleton 0)] at hmap
  exact hmap.trans h.zero

private theorem measurableSet_firstSplit (n : ℕ) {A : Set Tree} (hA : MeasurableSet A) :
    MeasurableSet {T : Tree | prefixLen T = n ∧ splitTree T ∈ A} := by
  exact ((measurable_prefixLen (measurableSet_singleton n)).inter
    (measurable_splitTree hA))

/-- Lemma 4.1 (`lem:prefix-terminal`): the joint law of the unary prefix length and the
terminal split tree. -/
theorem measure_firstSplit (h : OffspringHyp μ) (n : ℕ) {A : Set Tree}
    (hA : MeasurableSet A) :
    GW μ {T | prefixLen T = n ∧ splitTree T ∈ A} =
      μ {1} ^ n * GW μ (A ∩ {T | 2 ≤ degree T}) := by
  induction n with
  | zero =>
      have hray := unaryRay_measure_zero h
      have hzero := GW_degree_zero h
      have hae : {T : Tree | prefixLen T = 0 ∧ splitTree T ∈ A} =ᵐ[GW μ]
          A ∩ {T | 2 ≤ degree T} := by
        filter_upwards [show ∀ᵐ T ∂GW μ, T ∉ UnaryRay from by
          rw [ae_iff]
          simpa using hray, show ∀ᵐ T ∂GW μ, degree T ≠ 0 from by
          rw [ae_iff]
          simpa using hzero] with T hT hT0
        apply propext
        by_cases hdeg : degree T = 1
        · have hpre : prefixLen T ≠ 0 := by
            intro hp
            exact hT (allUnary_of_prefixLen_zero_of_degree_one hp hdeg)
          simp [hpre, hdeg]
        · have hpre : prefixLen T = 0 := prefixLen_eq_zero_of_degree_ne_one hdeg
          have htwo : 2 ≤ degree T := by omega
          simp [hpre, hdeg, htwo, splitTree]
      rw [measure_congr hae]
      simp
  | succ n ih =>
      have hE : MeasurableSet {T : Tree | prefixLen T = n ∧ splitTree T ∈ A} :=
        measurableSet_firstSplit n hA
      have hae : {T : Tree | prefixLen T = n + 1 ∧ splitTree T ∈ A} =ᵐ[GW μ]
          {T : Tree | degree T = 1 ∧ child T 1 ∈
            {T : Tree | prefixLen T = n ∧ splitTree T ∈ A}} := by
        filter_upwards [show ∀ᵐ T ∂GW μ, T ∉ UnaryRay from by
          rw [ae_iff]
          simpa using unaryRay_measure_zero h] with T hray
        apply propext
        constructor
        · rintro ⟨hpre, hA'⟩
          have hdeg := degree_eq_one_of_prefixLen_succ hpre
          have hchild := prefixLen_child_of_succ hpre
          have hst := splitTree_child_of_succ hpre
          exact ⟨hdeg, hchild, by rwa [← hst]⟩
        · rintro ⟨hdeg, hchild, hA'⟩
          have hpre := prefixLen_succ_of_child hdeg hchild hray
          have hst : splitTree T = splitTree (child T 1) := by
            unfold splitTree
            rw [hpre, hchild, subtree_replicate_succ]
          exact ⟨hpre, by rwa [hst]⟩
      calc
        GW μ {T | prefixLen T = n + 1 ∧ splitTree T ∈ A} =
            GW μ {T | degree T = 1 ∧ child T 1 ∈
              {T : Tree | prefixLen T = n ∧ splitTree T ∈ A}} := measure_congr hae
        _ = μ {1} * GW μ {T | prefixLen T = n ∧ splitTree T ∈ A} :=
          measure_unary_preimage hE
        _ = μ {1} * (μ {1} ^ n * GW μ (A ∩ {T | 2 ≤ degree T})) := by rw [ih]
        _ = μ {1} ^ (n + 1) * GW μ (A ∩ {T | 2 ≤ degree T}) := by
          rw [pow_succ]
          ac_rfl


private theorem GW_branch_measure : GW μ {T | 2 ≤ degree T} = μ (Set.Ici 2) := by
  have hmap := congrArg (fun ν : Measure ℕ => ν (Set.Ici 2)) (bienaymeLaw_map_degree μ)
  rwa [Measure.map_apply continuous_degree.measurable measurableSet_Ici] at hmap

/-- The conditional split law again has the ordered-child root decomposition. -/
theorem splitLaw_restrict_degree (_h : OffspringHyp μ) (k : ℕ) (hk : 2 ≤ k) :
    (splitLaw μ).restrict {T | degree T = k} =
      (μ {k} / μ (Set.Ici 2)) • (Measure.pi fun _ : Fin k => GW μ).map (nodeFin k) := by
  have hsub : {T : Tree | degree T = k} ⊆ {T : Tree | 2 ≤ degree T} := by
    intro T hT
    change degree T = k at hT
    change 2 ≤ degree T
    omega
  calc
    (splitLaw μ).restrict {T | degree T = k} =
        (((GW μ) {T | 2 ≤ degree T})⁻¹ • (GW μ).restrict {T | 2 ≤ degree T}).restrict
          {T | degree T = k} := rfl
    _ = ((GW μ) {T | 2 ≤ degree T})⁻¹ •
        ((GW μ).restrict {T | 2 ≤ degree T}).restrict {T | degree T = k} := by
      rw [Measure.restrict_smul]
    _ = ((GW μ) {T | 2 ≤ degree T})⁻¹ • (GW μ).restrict {T | degree T = k} := by
      rw [Measure.restrict_restrict_of_subset hsub]
    _ = ((GW μ) {T | 2 ≤ degree T})⁻¹ •
        (μ {k} • (Measure.pi fun _ : Fin k => GW μ).map (nodeFin k)) := by
      rw [bienaymeLaw_restrict_degree]
    _ = (((GW μ) {T | 2 ≤ degree T})⁻¹ * μ {k}) •
        (Measure.pi fun _ : Fin k => GW μ).map (nodeFin k) := by rw [smul_smul]
    _ = (μ {k} / μ (Set.Ici 2)) •
        (Measure.pi fun _ : Fin k => GW μ).map (nodeFin k) := by
      rw [GW_branch_measure]
      congr 1
      simp [div_eq_mul_inv, mul_comm]

private theorem splitLaw_apply {A : Set Tree} (hA : MeasurableSet A) :
    splitLaw μ A = ((GW μ) {T | 2 ≤ degree T})⁻¹ * GW μ (A ∩ {T | 2 ≤ degree T}) := by
  unfold splitLaw
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]

private theorem branch_ne_zero (h : OffspringHyp μ) : GW μ {T | 2 ≤ degree T} ≠ 0 := by
  rw [GW_branch_measure]
  intro hz
  have hp := pBr_pos h
  rw [pBr, hz, ENNReal.toReal_zero] at hp
  exact (lt_irrefl 0 hp)

private theorem map_splitTree_restrict (h : OffspringHyp μ) (n : ℕ) :
    ((GW μ).restrict (prefixLen ⁻¹' {n})).map splitTree =
      (μ {1} ^ n * GW μ {T | 2 ≤ degree T}) • splitLaw μ := by
  ext A hA
  calc
    (((GW μ).restrict (prefixLen ⁻¹' {n})).map splitTree) A =
        GW μ {T | prefixLen T = n ∧ splitTree T ∈ A} := by
      rw [Measure.map_apply measurable_splitTree hA,
        Measure.restrict_apply (measurable_splitTree hA)]
      congr 1
      ext T
      simp [and_comm]
    _ = μ {1} ^ n * GW μ (A ∩ {T | 2 ≤ degree T}) := measure_firstSplit h n hA
    _ = (μ {1} ^ n * GW μ {T | 2 ≤ degree T}) * splitLaw μ A := by
      rw [splitLaw_apply hA]
      calc
        μ {1} ^ n * GW μ (A ∩ {T | 2 ≤ degree T}) =
            μ {1} ^ n * (GW μ {T | 2 ≤ degree T} *
              (GW μ {T | 2 ≤ degree T})⁻¹) * GW μ (A ∩ {T | 2 ≤ degree T}) := by
          rw [ENNReal.mul_inv_cancel (branch_ne_zero h) (measure_ne_top _ _)]
          simp
        _ = _ := by ac_rfl
    _ = ((μ {1} ^ n * GW μ {T | 2 ≤ degree T}) • splitLaw μ) A := by
      rw [Measure.smul_apply, smul_eq_mul]

private theorem firstSplit_weight (n : ℕ) :
    ENNReal.ofReal (p1 μ ^ n * pBr μ) = μ {1} ^ n * GW μ {T | 2 ≤ degree T} := by
  simp only [p1, pBr, Measure.real]
  rw [ENNReal.ofReal_mul (pow_nonneg ENNReal.toReal_nonneg _), ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _),
    GW_branch_measure]

private theorem lintegral_firstSplit_strand (h : OffspringHyp μ) {F : ℕ → Tree → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) (n : ℕ) :
    ∫⁻ T in prefixLen ⁻¹' {n}, F (n + 1) (splitTree T) ∂GW μ =
      (μ {1} ^ n * GW μ {T | 2 ≤ degree T}) * ∫⁻ T, F (n + 1) T ∂splitLaw μ := by
  have hsec : Measurable (fun T : Tree => F (n + 1) T) :=
    hF.comp (measurable_const.prodMk measurable_id)
  have hmap := map_splitTree_restrict (μ := μ) h n
  calc
    ∫⁻ T in prefixLen ⁻¹' {n}, F (n + 1) (splitTree T) ∂GW μ =
        ∫⁻ T, F (n + 1) T ∂((GW μ).restrict (prefixLen ⁻¹' {n})).map splitTree := by
      rw [lintegral_map hsec measurable_splitTree]
    _ = ∫⁻ T, F (n + 1) T ∂(μ {1} ^ n * GW μ {T | 2 ≤ degree T}) • splitLaw μ := by
      rw [hmap]
    _ = _ := by rw [lintegral_smul_measure]; rfl

/-- Expectation of a nonnegative function of the geometric prefix and independent split. -/
theorem lintegral_firstSplit (h : OffspringHyp μ) {F : ℕ → Tree → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    ∫⁻ T, F (Gt T) (splitTree T) ∂GW μ =
      ∑' n : ℕ, ENNReal.ofReal (p1 μ ^ n * pBr μ) * ∫⁻ T, F (n + 1) T ∂splitLaw μ := by
  have hmeas (n : ℕ) : Measurable (fun T : Tree => F (n + 1) (splitTree T)) :=
    hF.comp (measurable_const.prodMk measurable_splitTree)
  have hset (n : ℕ) : MeasurableSet (prefixLen ⁻¹' {n} : Set Tree) :=
    measurable_prefixLen (measurableSet_singleton n)
  have hpoint (T : Tree) : F (Gt T) (splitTree T) =
      ∑' n : ℕ, (prefixLen ⁻¹' {n}).indicator (fun T => F (n + 1) (splitTree T)) T := by
    rw [tsum_eq_single (prefixLen T) (fun n hn => by simp [Set.indicator, Ne.symm hn])]
    simp [Gt]
  calc
    ∫⁻ T, F (Gt T) (splitTree T) ∂GW μ =
        ∫⁻ T, ∑' n : ℕ, (prefixLen ⁻¹' {n}).indicator
          (fun T => F (n + 1) (splitTree T)) T ∂GW μ :=
      lintegral_congr hpoint
    _ = ∑' n : ℕ, ∫⁻ T, (prefixLen ⁻¹' {n}).indicator
          (fun T => F (n + 1) (splitTree T)) T ∂GW μ := by
      rw [lintegral_tsum (fun n => ((hmeas n).indicator (hset n)).aemeasurable)]
    _ = ∑' n : ℕ, ∫⁻ T in prefixLen ⁻¹' {n}, F (n + 1) (splitTree T) ∂GW μ := by
      apply tsum_congr
      intro n
      rw [lintegral_indicator (hset n)]
    _ = ∑' n : ℕ, (μ {1} ^ n * GW μ {T | 2 ≤ degree T}) *
          ∫⁻ T, F (n + 1) T ∂splitLaw μ := by
      apply tsum_congr
      intro n
      exact lintegral_firstSplit_strand h hF n
    _ = ∑' n : ℕ, ENNReal.ofReal (p1 μ ^ n * pBr μ) * ∫⁻ T, F (n + 1) T ∂splitLaw μ := by
      apply tsum_congr
      intro n
      rw [firstSplit_weight]

private theorem integral_firstSplit_strand (h : OffspringHyp μ) {F : ℕ → Tree → ℝ}
    (hF : Measurable (Function.uncurry F)) (n : ℕ) :
    ∫ T in prefixLen ⁻¹' {n}, F (n + 1) (splitTree T) ∂GW μ =
      (p1 μ ^ n * pBr μ) * ∫ T, F (n + 1) T ∂splitLaw μ := by
  have hsec : Measurable (fun T : Tree => F (n + 1) T) :=
    hF.comp (measurable_const.prodMk measurable_id)
  have hmap := map_splitTree_restrict (μ := μ) h n
  calc
    ∫ T in prefixLen ⁻¹' {n}, F (n + 1) (splitTree T) ∂GW μ =
        ∫ T, F (n + 1) T ∂((GW μ).restrict (prefixLen ⁻¹' {n})).map splitTree := by
      rw [integral_map measurable_splitTree.aemeasurable hsec.aestronglyMeasurable]
    _ = ∫ T, F (n + 1) T ∂(μ {1} ^ n * GW μ {T | 2 ≤ degree T}) • splitLaw μ := by
      rw [hmap]
    _ = (μ {1} ^ n * GW μ {T | 2 ≤ degree T}).toReal * ∫ T, F (n + 1) T ∂splitLaw μ := by
      rw [integral_smul_measure]
      rfl
    _ = _ := by
      rw [← firstSplit_weight]
      rw [ENNReal.toReal_ofReal (by
        apply mul_nonneg
        · exact pow_nonneg (by unfold p1; exact measureReal_nonneg) _
        · unfold pBr
          exact measureReal_nonneg)]

/-- Signed version of `lintegral_firstSplit`.  Joint measurability of `F` makes every displayed
section integral meaningful; global integrability permits the countable exchange. -/
theorem integral_firstSplit (h : OffspringHyp μ) {F : ℕ → Tree → ℝ}
    (hFm : Measurable (Function.uncurry F))
    (hF : Integrable (fun T => F (Gt T) (splitTree T)) (GW μ)) :
    ∫ T, F (Gt T) (splitTree T) ∂GW μ =
      ∑' n : ℕ, (p1 μ ^ n * pBr μ) * ∫ T, F (n + 1) T ∂splitLaw μ := by
  let f : ℕ → Tree → ℝ := fun n =>
    (prefixLen ⁻¹' {n}).indicator (fun T => F (n + 1) (splitTree T))
  have hmeas (n : ℕ) : Measurable (fun T : Tree => F (n + 1) (splitTree T)) :=
    hFm.comp (measurable_const.prodMk measurable_splitTree)
  have hset (n : ℕ) : MeasurableSet (prefixLen ⁻¹' {n} : Set Tree) :=
    measurable_prefixLen (measurableSet_singleton n)
  have hfmeas (n : ℕ) : Measurable (f n) := (hmeas n).indicator (hset n)
  have hpoint (T : Tree) : F (Gt T) (splitTree T) = ∑' n, f n T := by
    rw [tsum_eq_single (prefixLen T) (fun n hn => by simp [f, Set.indicator, Ne.symm hn])]
    simp [f, Gt]
  have hnorm : (∑' n, ∫⁻ T, ‖f n T‖ₑ ∂GW μ) =
      ∫⁻ T, ‖F (Gt T) (splitTree T)‖ₑ ∂GW μ := by
    rw [← lintegral_tsum (fun n => (hfmeas n).enorm.aemeasurable)]
    apply lintegral_congr
    intro T
    rw [tsum_eq_single (prefixLen T) (fun n hn => by simp [f, Set.indicator, Ne.symm hn])]
    simp [f, Gt]
  have hsum : ∫ T, F (Gt T) (splitTree T) ∂GW μ = ∑' n, ∫ T, f n T ∂GW μ := by
    calc
      ∫ T, F (Gt T) (splitTree T) ∂GW μ = ∫ T, ∑' n, f n T ∂GW μ :=
        integral_congr_ae (ae_of_all _ hpoint)
      _ = ∑' n, ∫ T, f n T ∂GW μ := by
        apply integral_tsum (fun n => (hfmeas n).aestronglyMeasurable)
        rw [hnorm]
        exact ne_of_lt hF.2
  rw [hsum]
  apply tsum_congr
  intro n
  change (∫ T, (prefixLen ⁻¹' {n}).indicator (fun T => F (n + 1) (splitTree T)) T ∂GW μ) = _
  rw [integral_indicator (hset n)]
  exact integral_firstSplit_strand h hFm n

/-- Almost surely, the terminal tree actually branches. -/
theorem ae_split_degree (h : OffspringHyp μ) : ∀ᵐ T ∂GW μ, 2 ≤ degree (splitTree T) := by
  rw [ae_iff]
  let B : Set Tree := {T | ¬2 ≤ degree T}
  have hB : MeasurableSet B :=
    (continuous_degree.measurable measurableSet_Ici).compl
  have hstrand (n : ℕ) :
      GW μ (prefixLen ⁻¹' {n} ∩ splitTree ⁻¹' B) = 0 := by
    have hm := measure_firstSplit h n hB
    have hset : {T : Tree | prefixLen T = n ∧ splitTree T ∈ B} =
        prefixLen ⁻¹' {n} ∩ splitTree ⁻¹' B := rfl
    rw [← hset, hm]
    have hempty : B ∩ {T : Tree | 2 ≤ degree T} = ∅ := by
      ext T
      simp [B]
    rw [hempty, measure_empty, mul_zero]
  have hunion : {T : Tree | ¬2 ≤ degree (splitTree T)} =
      ⋃ n : ℕ, prefixLen ⁻¹' {n} ∩ splitTree ⁻¹' B := by
    ext T
    simp [B]
  rw [hunion]
  exact measure_iUnion_null hstrand

end LPPMonotonicityProof.Analytic
