module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite-flow escape inequalities

This module uses one-based child addresses in a raw offspring field, as in
`random-trees-lean`.  The finite escape is indexed by the
remaining height.  No probability or infinite-tree construction is involved.
-/

open scoped BigOperators

@[expose] public section

noncomputable section

/-- The `i`-th child, using the one-based address convention. -/
def offChild (ν : List ℕ → ℕ) (v : List ℕ) (i : Fin (ν v)) : List ℕ :=
  v ++ [i.val + 1]

/-- The finite escape with `k` generations remaining. -/
def escapeN (ν : List ℕ → ℕ) (L : ℝ) : ℕ → List ℕ → ℝ
  | 0, _ => 1
  | k + 1, v =>
      (∑ i : Fin (ν v), escapeN ν L k (offChild ν v i)) /
        (L + ∑ i : Fin (ν v), escapeN ν L k (offChild ν v i))

/-- Every present vertex at relative depth strictly below `k` has a child. -/
def LeaflessBelow (ν : List ℕ → ℕ) : ℕ → List ℕ → Prop
  | 0, _ => True
  | k + 1, v => 1 ≤ ν v ∧ ∀ i : Fin (ν v), LeaflessBelow ν k (offChild ν v i)

/-- The finite set of descendants at relative depth `j`, defined recursively
through the first generation. -/
def generation (ν : List ℕ → ℕ) (v : List ℕ) : ℕ → Finset (List ℕ)
  | 0 => {v}
  | j + 1 => Finset.univ.biUnion fun i : Fin (ν v) =>
      generation ν (offChild ν v i) j

/-- The sum of `F` over one relative generation. -/
def generationSum (ν : List ℕ → ℕ) (F : List ℕ → ℝ) (v : List ℕ) (j : ℕ) : ℝ :=
  ∑ w ∈ generation ν v j, F w

/-- The deterministic local finite-flow inequality at one vertex. -/
theorem finite_flow_step {n : ℕ} (F β : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hβ : ∀ i, 0 < β i) (hS : 0 < ∑ i, β i) :
    (∑ i, F i)^2 / ((∑ i, β i) / (L + ∑ i, β i))
    ≤ (∑ i, F i)^2 + L * ∑ i, F i ^ 2 / β i := by
  have h := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin n)) F
      (g := β) (fun i _ => hβ i)
  calc
    _ = (∑ i, F i)^2 + L * ((∑ i, F i)^2 / ∑ i, β i) := by
      field_simp [hS.ne', (add_pos_of_nonneg_of_pos hL hS).ne']
      ring
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left h hL) _

private theorem escapeN_nonneg (ν : List ℕ → ℕ) {L : ℝ} (hL : 0 < L) :
    ∀ (k : ℕ) (v : List ℕ), 0 ≤ escapeN ν L k v := by
  intro k
  induction k with
  | zero => intro v; simp [escapeN]
  | succ k ih =>
      intro v
      rw [escapeN]
      apply div_nonneg
      · exact Finset.sum_nonneg fun i _ => ih (offChild ν v i)
      · have hS : 0 ≤ ∑ i : Fin (ν v), escapeN ν L k (offChild ν v i) :=
          Finset.sum_nonneg fun i _ => ih (offChild ν v i)
        positivity

/-- Positivity of every finite escape below a leafless finite ball. -/
theorem escapeN_pos (ν : List ℕ → ℕ) {L : ℝ} (hL : 0 < L) :
    ∀ (k : ℕ) (v : List ℕ), LeaflessBelow ν k v → 0 < escapeN ν L k v := by
  intro k
  induction k with
  | zero => intro v _; simp [escapeN]
  | succ k ih =>
      intro v hv
      rw [escapeN]
      have hS : 0 < ∑ i : Fin (ν v), escapeN ν L k (offChild ν v i) := by
        apply Finset.sum_pos
        · intro i _
          exact ih (offChild ν v i) (hv.2 i)
        · let i0 : Fin (ν v) := ⟨0, hv.1⟩
          exact ⟨i0, Finset.mem_univ i0⟩
      exact div_pos hS (by positivity)

/-- Every finite escape is at most one. -/
theorem escapeN_le_one (ν : List ℕ → ℕ) {L : ℝ} (hL : 0 < L) :
    ∀ (k : ℕ) (v : List ℕ), escapeN ν L k v ≤ 1 := by
  intro k v
  cases k with
  | zero => simp [escapeN]
  | succ k =>
      rw [escapeN]
      have hS : 0 ≤ ∑ i : Fin (ν v), escapeN ν L k (offChild ν v i) :=
        Finset.sum_nonneg fun i _ => escapeN_nonneg ν hL k (offChild ν v i)
      apply (div_le_one (by positivity)).2
      linarith

/-- With at least one remaining generation, the finite escape is strictly
below one, even when the vertex is a leaf. -/
theorem escapeN_succ_lt_one (ν : List ℕ → ℕ) {L : ℝ} (hL : 0 < L) (k : ℕ)
    (v : List ℕ) : escapeN ν L (k + 1) v < 1 := by
  rw [escapeN]
  have hS : 0 ≤ ∑ i : Fin (ν v), escapeN ν L k (offChild ν v i) :=
    Finset.sum_nonneg fun i _ => escapeN_nonneg ν hL k (offChild ν v i)
  apply (div_lt_one (by positivity)).2
  linarith

private lemma escape_ratio_mono {L A B : ℝ} (hL : 0 < L) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hAB : A ≤ B) : A / (L + A) ≤ B / (L + B) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_left hAB hL.le]

private lemma escape_ratio_bias {L M A B : ℝ} (hL : 0 < L) (hLM : L ≤ M)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hBA : B ≤ A) :
    B / (M + B) ≤ A / (L + A) := by
  have hM : 0 < M := hL.trans_le hLM
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_left hBA hL.le,
    mul_le_mul_of_nonneg_right hLM hA]

/-- Increasing the remaining height decreases the finite escape. -/
theorem escapeN_anti_height (ν : List ℕ → ℕ) {L : ℝ} (hL : 0 < L) :
    ∀ (k : ℕ) (v : List ℕ), escapeN ν L (k + 1) v ≤ escapeN ν L k v := by
  intro k
  induction k with
  | zero =>
      intro v
      exact (escapeN_succ_lt_one ν hL 0 v).le
  | succ k ih =>
      intro v
      rw [escapeN, escapeN]
      apply escape_ratio_mono hL
      · exact Finset.sum_nonneg fun i _ => escapeN_nonneg ν hL (k + 1) (offChild ν v i)
      · exact Finset.sum_nonneg fun i _ => escapeN_nonneg ν hL k (offChild ν v i)
      · exact Finset.sum_le_sum fun i _ => ih (offChild ν v i)

/-- The finite escape is antitone in the positive bias. -/
theorem escapeN_antitoneOn (ν : List ℕ → ℕ) (k : ℕ) (v : List ℕ) :
    AntitoneOn (fun L : ℝ => escapeN ν L k v) (Set.Ioi 0) := by
  intro A hA B hB hAB
  change escapeN ν B k v ≤ escapeN ν A k v
  induction k generalizing v with
  | zero => simp [escapeN]
  | succ k ih =>
      rw [escapeN, escapeN]
      apply escape_ratio_bias hA hAB
      · exact Finset.sum_nonneg fun i _ => escapeN_nonneg ν hA k (offChild ν v i)
      · exact Finset.sum_nonneg fun i _ => escapeN_nonneg ν hB k (offChild ν v i)
      · exact Finset.sum_le_sum fun i _ => ih (offChild ν v i)

/-- The finite low-bias lower bound from `lem:escape` (iii). -/
theorem escapeN_lower_bound (ν : List ℕ → ℕ) {L : ℝ} (hL : 0 < L) (hL1 : L < 1) :
    ∀ (k : ℕ) (v : List ℕ), LeaflessBelow ν k v → 1 - L ≤ escapeN ν L k v := by
  intro k
  induction k with
  | zero => intro v _; simp [escapeN]; linarith
  | succ k ih =>
      intro v hv
      rw [escapeN]
      let i0 : Fin (ν v) := ⟨0, hv.1⟩
      have hSnonneg : 0 ≤ ∑ i : Fin (ν v), escapeN ν L k (offChild ν v i) :=
        Finset.sum_nonneg fun i _ => escapeN_nonneg ν hL k (offChild ν v i)
      have hS : 1 - L ≤ ∑ i : Fin (ν v), escapeN ν L k (offChild ν v i) := by
        calc
          1 - L ≤ escapeN ν L k (offChild ν v i0) := ih _ (hv.2 i0)
          _ ≤ _ := Finset.single_le_sum
            (fun i _ => escapeN_nonneg ν hL k (offChild ν v i)) (Finset.mem_univ i0)
      have h := escape_ratio_mono hL (by linarith : 0 ≤ 1 - L) hSnonneg hS
      convert h using 1; ring

private lemma generation_prefix (ν : List ℕ → ℕ) :
    ∀ (j : ℕ) (v w : List ℕ), w ∈ generation ν v j → v <+: w := by
  intro j
  induction j with
  | zero =>
      intro v w hw
      simp only [generation, Finset.mem_singleton] at hw
      subst w
      exact List.prefix_rfl
  | succ j ih =>
      intro v w hw
      rw [generation] at hw
      rcases Finset.mem_biUnion.mp hw with ⟨i, _, hw⟩
      have hroot : v <+: offChild ν v i := ⟨[i.val + 1], rfl⟩
      exact hroot.trans (ih (offChild ν v i) w hw)

private lemma generation_disjoint (ν : List ℕ → ℕ) (v : List ℕ) (j : ℕ) :
    ((Finset.univ : Finset (Fin (ν v))) : Set (Fin (ν v))).PairwiseDisjoint
      (fun i => generation ν (offChild ν v i) j) := by
  intro i _ i' _ hii'
  apply Finset.disjoint_left.2
  intro w hw hw'
  have heq : offChild ν v i = offChild ν v i' := by
    rcases generation_prefix ν j (offChild ν v i) w hw with ⟨u, hu⟩
    rcases generation_prefix ν j (offChild ν v i') w hw' with ⟨u', hu'⟩
    exact List.append_inj_left (hu.trans hu'.symm) (by simp [offChild])
  have hsingletons : [i.val + 1] = [i'.val + 1] :=
    List.append_right_injective v heq
  have hvalues : i.val + 1 = i'.val + 1 := by simpa using hsingletons
  exact hii' (Fin.ext (Nat.add_right_cancel hvalues))

private lemma generationSum_succ (ν : List ℕ → ℕ) (F : List ℕ → ℝ)
    (v : List ℕ) (j : ℕ) :
    generationSum ν F v (j + 1) =
      ∑ i : Fin (ν v), generationSum ν F (offChild ν v i) j := by
  simp only [generationSum, generation]
  exact Finset.sum_biUnion (generation_disjoint ν v j)

private lemma generationSum_zero (ν : List ℕ → ℕ) (F : List ℕ → ℝ)
    (v : List ℕ) : generationSum ν F v 0 = F v := by
  simp [generationSum, generation]

private lemma mem_generation_succ (ν : List ℕ → ℕ) (v : List ℕ) (j : ℕ)
    (i : Fin (ν v)) (w : List ℕ) (hw : w ∈ generation ν (offChild ν v i) j) :
    w ∈ generation ν v (j + 1) := by
  rw [generation]
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hw⟩

/-- Iteration of the deterministic finite-flow inequality down to the boundary.
The `j = 0` term is `F v ^ 2`, and the upper limit `k + 1` includes the
boundary generation `j = k`, where the escape equals one. -/
theorem finite_flow_iterated (ν : List ℕ → ℕ) {L : ℝ} (hL : 0 < L) :
    ∀ (k : ℕ) (v : List ℕ), LeaflessBelow ν k v →
      ∀ (F : List ℕ → ℝ),
        (∀ j < k, ∀ w ∈ generation ν v j,
          F w = ∑ i : Fin (ν w), F (offChild ν w i)) →
        F v ^ 2 ≤ escapeN ν L k v *
          ∑ j ∈ Finset.range (k + 1), L ^ j * generationSum ν (fun w => F w ^ 2) v j := by
  intro k
  induction k with
  | zero =>
      intro v _ F _
      simp [escapeN, generationSum_zero]
  | succ k ih =>
      intro v hv F hF
      have hβ : ∀ i : Fin (ν v), 0 < escapeN ν L k (offChild ν v i) :=
        fun i => escapeN_pos ν hL k (offChild ν v i) (hv.2 i)
      have hS : 0 < ∑ i : Fin (ν v), escapeN ν L k (offChild ν v i) := by
        apply Finset.sum_pos
        · intro i _
          exact hβ i
        · let i0 : Fin (ν v) := ⟨0, hv.1⟩
          exact ⟨i0, Finset.mem_univ i0⟩
      have hFroot : F v = ∑ i : Fin (ν v), F (offChild ν v i) :=
        hF 0 (Nat.zero_lt_succ k) v (by simp [generation])
      have hFchild (i : Fin (ν v)) : ∀ j < k, ∀ w ∈ generation ν (offChild ν v i) j,
          F w = ∑ i' : Fin (ν w), F (offChild ν w i') := by
        intro j hj w hw
        exact hF (j + 1) (Nat.succ_lt_succ hj) w (mem_generation_succ ν v j i w hw)
      have hlocal : F v ^ 2 / escapeN ν L (k + 1) v ≤
          F v ^ 2 + L * ∑ i : Fin (ν v), F (offChild ν v i) ^ 2 /
            escapeN ν L k (offChild ν v i) := by
        rw [escapeN, hFroot]
        exact finite_flow_step (fun i : Fin (ν v) => F (offChild ν v i))
          (fun i : Fin (ν v) => escapeN ν L k (offChild ν v i)) L hL.le hβ hS
      have hchild (i : Fin (ν v)) : F (offChild ν v i) ^ 2 /
          escapeN ν L k (offChild ν v i) ≤
          ∑ j ∈ Finset.range (k + 1), L ^ j *
            generationSum ν (fun w => F w ^ 2) (offChild ν v i) j := by
        apply (div_le_iff₀ (hβ i)).2
        simpa [mul_comm] using ih (offChild ν v i) (hv.2 i) F (hFchild i)
      have hsum : (∑ i : Fin (ν v), F (offChild ν v i) ^ 2 /
          escapeN ν L k (offChild ν v i)) ≤
          ∑ i : Fin (ν v), ∑ j ∈ Finset.range (k + 1), L ^ j *
            generationSum ν (fun w => F w ^ 2) (offChild ν v i) j :=
        Finset.sum_le_sum fun i _ => hchild i
      have hbulk := hlocal.trans (add_le_add_right
        (mul_le_mul_of_nonneg_left hsum hL.le) (F v ^ 2))
      have hRHS : F v ^ 2 + L * (∑ i : Fin (ν v),
          ∑ j ∈ Finset.range (k + 1), L ^ j *
            generationSum ν (fun w => F w ^ 2) (offChild ν v i) j) =
          ∑ j ∈ Finset.range (k + 2), L ^ j *
            generationSum ν (fun w => F w ^ 2) v j := by
        calc
          _ = F v ^ 2 + ∑ j ∈ Finset.range (k + 1), L ^ (j + 1) *
                generationSum ν (fun w => F w ^ 2) v (j + 1) := by
              congr 1
              rw [Finset.mul_sum]
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro j _
              rw [pow_succ, generationSum_succ, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
          _ = _ := by
              simp only [Finset.sum_range_succ', pow_zero, one_mul,
                generationSum_zero, add_comm]
      have hdiv : F v ^ 2 / escapeN ν L (k + 1) v ≤
          ∑ j ∈ Finset.range (k + 2), L ^ j *
            generationSum ν (fun w => F w ^ 2) v j := hbulk.trans_eq hRHS
      have hfinal := (div_le_iff₀ (escapeN_pos ν hL (k + 1) v hv)).1 hdiv
      simpa [mul_comm] using hfinal
