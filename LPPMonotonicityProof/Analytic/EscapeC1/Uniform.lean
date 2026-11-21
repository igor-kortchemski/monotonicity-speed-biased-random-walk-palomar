module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Elementary uniform-limit algebra for the analytic escape proof

This module proves that uniform convergence on a set is preserved by index shifts,
by multiplication by constants, by products of limits with values in a compact set,
and by inversion away from zero.
-/

@[expose] public section

open Filter Topology
open scoped BigOperators

namespace LPPMonotonicityProof.Analytic

private theorem eventually_nat_add_one {P : ℕ → Prop} :
    (∀ᶠ N in atTop, P (N + 1)) ↔ ∀ᶠ N in atTop, P N := by
  constructor
  · intro h
    filter_upwards [eventually_ge_atTop 1, (tendsto_sub_atTop_nat 1).eventually h] with N hN hP
    convert hP using 1
    omega
  · intro h
    exact (tendsto_add_atTop_nat 1).eventually h

theorem tendstoUniformlyOn_nat_add_one_iff {α : Type*} {F : ℕ → α → ℝ}
    {f : α → ℝ} {s : Set α} :
    TendstoUniformlyOn (fun N => F (N + 1)) f atTop s ↔ TendstoUniformlyOn F f atTop s := by
  simp only [Metric.tendstoUniformlyOn_iff]
  constructor <;> intro h ε hε
  · exact eventually_nat_add_one.mp (h ε hε)
  · exact eventually_nat_add_one.mpr (h ε hε)

theorem Filter.Tendsto.tendstoUniformlyOn_const_mul {α : Type*} {F : ℕ → α → ℝ}
    {f : α → ℝ} {s : Set α} (C : ℝ) (h : TendstoUniformlyOn F f atTop s) :
    TendstoUniformlyOn (fun N x => C * F N x) (fun x => C * f x) atTop s := by
  exact Real.uniformContinuous_const_mul.comp_tendstoUniformlyOn h

theorem Filter.Tendsto.tendstoUniformlyOn_mul_const {α : Type*} {F : ℕ → α → ℝ}
    {f : α → ℝ} {s : Set α} (C : ℝ) (h : TendstoUniformlyOn F f atTop s) :
    TendstoUniformlyOn (fun N x => F N x * C) (fun x => f x * C) atTop s := by
  simpa only [mul_comm _ C] using Filter.Tendsto.tendstoUniformlyOn_const_mul C h

private theorem tendstoUniformlyOn_prodMk_same {α : Type*} {F G : ℕ → α → ℝ}
    {f g : α → ℝ} {s : Set α} (hF : TendstoUniformlyOn F f atTop s)
    (hG : TendstoUniformlyOn G g atTop s) :
    TendstoUniformlyOn (fun N x => (F N x, G N x)) (fun x => (f x, g x)) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF ε hε,
    Metric.tendstoUniformlyOn_iff.mp hG ε hε] with N hFN hGN
  intro x hx
  rw [Prod.dist_eq]
  exact max_lt (hFN x hx) (hGN x hx)

/-- Products of uniform limits may be composed when all values lie in one compact set. -/
theorem tendstoUniformlyOn_mul_of_compact {α : Type*} {F G : ℕ → α → ℝ}
    {f g : α → ℝ} {s : Set α} {K : Set (ℝ × ℝ)}
    (hF : TendstoUniformlyOn F f atTop s) (hG : TendstoUniformlyOn G g atTop s)
    (hK : IsCompact K) (hFG : ∀ N x, x ∈ s → (F N x, G N x) ∈ K)
    (hfg : ∀ x, x ∈ s → (f x, g x) ∈ K) :
    TendstoUniformlyOn (fun N x => F N x * G N x) (fun x => f x * g x) atTop s := by
  have hu : UniformContinuousOn (fun p : ℝ × ℝ => p.1 * p.2) K :=
    hK.uniformContinuousOn_of_continuous continuous_mul.continuousOn
  exact hu.comp_tendstoUniformlyOn_eventually (Filter.Eventually.of_forall hFG) hfg (tendstoUniformlyOn_prodMk_same hF hG)

/-- Inversion preserves uniform convergence on a fixed half-line away from zero. -/
theorem tendstoUniformlyOn_inv {α : Type*} {F : ℕ → α → ℝ}
    {f : α → ℝ} {s : Set α} {δ : ℝ} (hδ : 0 < δ)
    (hF : TendstoUniformlyOn F f atTop s) (hFs : ∀ N x, x ∈ s → F N x ∈ Set.Ici δ)
    (hfs : ∀ x, x ∈ s → f x ∈ Set.Ici δ) :
    TendstoUniformlyOn (fun N x => (F N x)⁻¹) (fun x => (f x)⁻¹) atTop s := by
  have hmem : (Set.Ici δ)ᶜ ∈ 𝓝 (0 : ℝ) := by
    simpa only [Set.compl_Ici] using Iio_mem_nhds hδ
  exact (uniformContinuousOn_inv₀ hmem).comp_tendstoUniformlyOn_eventually
    (Filter.Eventually.of_forall hFs) hfs hF

theorem tendstoUniformlyOn_sum {α ι : Type*} (t : Finset ι) {F : ι → ℕ → α → ℝ}
    {f : ι → α → ℝ} {s : Set α}
    (h : ∀ i ∈ t, TendstoUniformlyOn (F i) (f i) atTop s) :
    TendstoUniformlyOn (fun N x => ∑ i ∈ t, F i N x) (fun x => ∑ i ∈ t, f i x) atTop s := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).tendstoUniformlyOn_const s)
  | @insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end LPPMonotonicityProof.Analytic
