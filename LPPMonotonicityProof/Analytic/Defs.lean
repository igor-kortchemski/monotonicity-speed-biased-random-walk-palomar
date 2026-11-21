module

public import LPPMonotonicityProof.Speed.Escape.Positive
public import LPPMonotonicityProof.Speed.Interface.Model
public import LPPMonotonicityProof.Speed.Interface.Subtrees
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Analytic interface definitions

This module defines the quantities used by the analytic part of the proof: the
offspring scalars, the two-copy kernel quantities of Section 2, the transformed
escape of Section 3, the first-split quantities of Sections 4 and 5, the rank
moments of Proposition 5.2 (`prop:ward-ranks`), and the good events on trees.

The definitions with the suffix `Prov` are local copies of `Speed.Dfun`,
`Speed.escLaw`, `Speed.Nval`, `Speed.Zval` and `Speed.speedValue`, and of `sib`,
`pathMax` and `envelope` from `LPPMonotonicityProof.Analytic.Regularity.Envelope`.
Each copy has the same defining formula as its original, and the two are proved
equal (for instance `speedValue_eq_speedValueProv` and `envelope_eq_prov`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open LPPMonotonicityProof.Speed LPPMonotonicityProof.RTL.LocallyFinite

namespace LPPMonotonicityProof.Analytic

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

noncomputable abbrev GW : Measure Tree := bienaymeLaw μ

/-! ### Local copies of the two-copy kernel, the speed and the response envelope -/

/-- The two-copy denominator `D(b, b') = λ - 1 + b + b' - b b'` (copy of `Speed.Dfun`). -/
def DfunProv (l b b' : ℝ) : ℝ := l - 1 + b + b' - b * b'

/-- The law of the escape `β_λ` under the Bienaymé law (copy of `Speed.escLaw`). -/
noncomputable def escLawProv (l : ℝ) : Measure ℝ := (GW μ).map (escape l)

/-- `N = E[β β' / D]` for two independent escapes (copy of `Speed.Nval`). -/
noncomputable def NvalProv (l : ℝ) : ℝ :=
  ∫ p, p.1 * p.2 / DfunProv l p.1 p.2 ∂(escLawProv μ l).prod (escLawProv μ l)

/-- `Z = E[τ / D]` for two independent escapes (copy of `Speed.Zval`). -/
noncomputable def ZvalProv (l : ℝ) : ℝ :=
  ∫ p, (p.1 + p.2 - p.1 * p.2) / DfunProv l p.1 p.2
    ∂(escLawProv μ l).prod (escLawProv μ l)

/-- The speed: `N / Z` at nonzero bias and `1` at bias zero (copy of `Speed.speedValue`). -/
noncomputable def speedValueProv (l : ℝ) : ℝ := if l = 0 then 1 else NvalProv μ l / ZvalProv μ l

/-- The sibling factor of the response envelope (copy of `sib`), used to define `RegTree`. -/
noncomputable def sibProv (lPos : ℝ) (T : Tree) (i : Fin (degree T)) : ℝ≥0 :=
  Real.toNNReal (lPos / (lPos + ∑ j ∈ Finset.univ.erase i, escape lPos (child T (j + 1))))

/-- The maximal sibling-factor product along paths (copy of `pathMax`), used to define
`RegTree`. -/
noncomputable def pathMaxProv (lPos : ℝ) : ℕ → Tree → ℝ≥0
  | 0, _ => 1
  | k + 1, T => Finset.univ.sup fun i : Fin (degree T) =>
      sibProv lPos T i * pathMaxProv lPos k (child T (i + 1))

/-- The response envelope (copy of `envelope`), used to define `RegTree`. -/
noncomputable def envelopeProv (lNeg lPos : ℝ) (T : Tree) : ℝ≥0∞ :=
  (ENNReal.ofReal lNeg)⁻¹ * ∑' k, (pathMaxProv lPos (k + 1) T : ℝ≥0∞)

/-! ### Offspring scalars -/
noncomputable def invMean : ℝ := ∫ k, ((k : ℝ))⁻¹ ∂μ
noncomputable def p1 : ℝ := (μ {1}).toReal
noncomputable def pBr : ℝ := (μ (Set.Ici 2)).toReal
noncomputable def splitLaw : Measure Tree :=
  ((GW μ) {T | 2 ≤ degree T})⁻¹ • (GW μ).restrict {T | 2 ≤ degree T}
noncomputable def eJ : ℝ := ∫ T, ((degree T : ℝ))⁻¹ ∂splitLaw μ
noncomputable def meanJ : ℝ := ∫ T, (degree T : ℝ) ∂splitLaw μ
noncomputable def secondMoment : ℝ≥0∞ := ∫⁻ k, (k : ℝ≥0∞) ^ 2 ∂μ

/-! ### Two-copy kernel quantities -/

def tau (b b' : ℝ) : ℝ := b + b' - b * b'
noncomputable def pairE (l : ℝ) (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p, F (escape l p.1) (escape l p.2) ∂(GW μ).prod (GW μ)
noncomputable def resp (l : ℝ) (T : Tree) : ℝ := -l * deriv (fun l' => escape l' T) l
def Pol (l c t : ℝ) : ℝ := t ^ 2 + (l - 1) * (1 + c) * t - (l - 1) * c
noncomputable def Hval (l : ℝ) : ℝ :=
  pairE μ l fun b b' => (b * b' - speedValueProv μ l * tau b b') / DfunProv l b b' ^ 2
noncomputable def Gam (l b : ℝ) : ℝ :=
  ∫ T, Pol l (speedValueProv μ l) (escape l T) / DfunProv l b (escape l T) ^ 2 ∂GW μ
noncomputable def Gam2 (l b : ℝ) : ℝ :=
  ∫ T, escape l T ^ 2 / DfunProv l b (escape l T) ^ 2 ∂GW μ
noncomputable def RW (l : ℝ) : ℝ :=
  pairE μ l fun b b' => b * b' * (1 - b') / DfunProv l b b' ^ 2
noncomputable def K0 (l : ℝ) : ℝ := pairE μ l fun b b' => 1 / DfunProv l b b'
noncomputable def K1 (l : ℝ) : ℝ := pairE μ l fun b b' => b / DfunProv l b b'
noncomputable def cost (l : ℝ) : ℝ := -l * ZvalProv μ l * deriv (speedValueProv μ) l
noncomputable def aidE (l : ℝ) (g : ℕ → ℝ) : ℝ :=
  ∫ p, g (degree p.1) * escape l p.2 / (l - 1 + escape l p.2 + childSum l p.1)
    ∂(GW μ).prod (GW μ)

/-! ### Above one -/

noncomputable def Yt (l : ℝ) (T : Tree) : ℝ := escape l T / (l - 1 + escape l T)
noncomputable def Ylaw (l : ℝ) : Measure ℝ := (GW μ).map (Yt l)
noncomputable def muY (l : ℝ) : ℝ := ∫ T, Yt l T ∂GW μ
noncomputable def momY (l : ℝ) (n : ℕ) : ℝ := ∫ T, Yt l T ^ n ∂GW μ
noncomputable def peff (l : ℝ) : ℝ := (l - 1) * muY μ l / (1 - muY μ l)
noncomputable def rr (l : ℝ) : ℝ := speedValueProv μ l / (l - 1)
def Qgeo (l : ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, l ^ i
noncomputable def Sgeo (l q : ℝ) : ℝ := ∑' j : ℕ, (j + 1) * q ^ j / Qgeo l (j + 1)
noncomputable def geomY (l b : ℝ) : Measure ℝ :=
  Measure.sum fun g : ℕ => ENNReal.ofReal (b * (1 - b) ^ g) • Measure.dirac (l ^ (-((g : ℤ) + 1)))
noncomputable def NY (l : ℝ) (ρ ρ' : Measure ℝ) : ℝ :=
  ∫ p, (l - 1) * p.1 * p.2 / (1 - l * p.1 * p.2) ∂ρ.prod ρ'
noncomputable def ZY (l : ℝ) (ρ ρ' : Measure ℝ) : ℝ :=
  ∫ p, (p.1 * (1 - p.2) + p.2 * (1 - l * p.1)) / (1 - l * p.1 * p.2) ∂ρ.prod ρ'
def Bw (l w t : ℝ) : ℝ := (l - 1) * t - w * (1 - t) * (1 - l * t)
noncomputable def Hw (l w y t : ℝ) : ℝ :=
  ((l - 1) * y * t - w * (y + t - (1 + l) * y * t)) / (1 - l * y * t)
def fθ (l r θ y : ℝ) : ℝ := y - θ * y ^ 2 - r * (1 - y) * (1 - l * y)
def gθ (l r θ y : ℝ) : ℝ :=
  l * y * (1 - y) + 2 * θ * y * (1 - l * y) - l * r * (1 - y) * (2 - (1 + l) * y)
noncomputable def Admissible (l θ : ℝ) : Prop := θ ≤ 1 ∧ 0 ≤ ∫ T, fθ l (rr μ l) θ (Yt l T) ∂GW μ

/-! ### First split -/

noncomputable def prefixLen (T : Tree) : ℕ :=
  sInf {n | degree (subtree T (List.replicate n 1)) ≠ 1}
noncomputable def Gt (T : Tree) : ℕ := prefixLen T + 1
noncomputable def splitTree (T : Tree) : Tree := subtree T (List.replicate (prefixLen T) 1)
noncomputable def Wt (l : ℝ) (T : Tree) : ℝ := childSum l T / (l - 1 + childSum l T)
noncomputable def sS (l : ℝ) : ℝ := (l - 1) / pBr μ
noncomputable def xS (l : ℝ) : ℝ := pBr μ / (l - 1)
noncomputable def kS (l : ℝ) : ℝ := Real.sqrt l
noncomputable def iota (l : ℝ) (n : ℕ) : ℝ := (xS μ l + Qgeo l n)⁻¹
noncomputable def Acoef (l : ℝ) (n : ℕ) : ℝ := kS l ^ (n - 1) * iota μ l n
noncomputable def etaW (l : ℝ) (n : ℕ) : ℝ := ∫ T, Wt l T ^ n ∂splitLaw μ
noncomputable def wbar (l : ℝ) : ℝ := etaW μ l 1
noncomputable def tW (l : ℝ) : ℝ := etaW μ l 2 / wbar μ l
noncomputable def dW (l : ℝ) : ℝ := 1 - wbar μ l
noncomputable def etaD (l : ℝ) : ℝ := (∫ T, (1 - Wt l T) ^ 2 ∂splitLaw μ) / dW μ l
noncomputable def mMom (l : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else Acoef μ l n * etaW μ l n
noncomputable def Ssc (l : ℝ) : ℝ := ∑' n : ℕ, mMom μ l (n + 1) ^ 2
noncomputable def Tsc (l : ℝ) : ℝ := ∑' n : ℕ, mMom μ l (n + 1) * mMom μ l (n + 2)
noncomputable def hsc (l : ℝ) : ℝ :=
  mMom μ l 1 - xS μ l * ((1 + l) * Ssc μ l / 2 - kS l * Tsc μ l)
noncomputable def gamS (l : ℝ) : ℝ := (1 + l) / (2 * kS l)
noncomputable def Ccoef (l : ℝ) (n : ℕ) : ℝ :=
  (if n = 1 then 1 else 0) + xS μ l *
    (kS l * (mMom μ l (n - 1) + mMom μ l (n + 1)) - (1 + l) * mMom μ l n)
noncomputable def Vsc (l : ℝ) : ℝ := speedValueProv μ l / pBr μ
noncomputable def Dcoef (l : ℝ) (n : ℕ) : ℝ := mMom μ l n - Vsc μ l * Ccoef μ l n
noncomputable def dx (f : ℝ → ℝ) (l : ℝ) : ℝ := -((l - 1) ^ 2 / pBr μ) * deriv f l
noncomputable def deltaChild (l : ℝ) (T : Tree) (i : ℕ) : ℝ :=
  (l - 1) / (l - 1 + childSum l T - escape l (child T i))
noncomputable def Mstar (l : ℝ) : ℝ :=
  ∫ T, ∑ i : Fin (degree T), deltaChild l T (i + 1) ^ 2 ∂splitLaw μ
noncomputable def Mtwo (l : ℝ) : ℝ := 2 * ∫ T, (1 - Wt l T) ^ 2 ∂splitLaw μ
noncomputable def Bresp (l : ℝ) (T : Tree) : ℝ := -(l - 1) * deriv (fun l' => Wt l' T) l
noncomputable def Bn (l : ℝ) (n : ℕ) : ℝ := ∫ T, Wt l T ^ (n - 1) * Bresp l T ∂splitLaw μ
noncomputable def cn (l : ℝ) (n : ℕ) : ℝ :=
  (l - 1) ^ 2 * n * (n ^ 2 - 1) / (12 * xS μ l * l ^ (3 / 2 : ℝ))
noncomputable def phiResp (l b : ℝ) : ℝ :=
  (1 - b) * ((l - 1) / Real.log l) *
    ∫ t in (0 : ℝ)..1, (1 - t) / ((1 + (l - 1) * t) * (1 + (l - 1) * t / b))

/-! ### Ranks -/

noncomputable def muJ (l : ℝ) (j : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ T, (kS l * Yt l T) ^ j * f (Yt l T) ∂GW μ
noncomputable def PJ (l : ℝ) (j : ℕ) : ℝ := muJ μ l j fun y => y * (1 - y)
noncomputable def FJ (l : ℝ) (j : ℕ) : ℝ :=
  kS l ^ j * xS μ l * iota μ l (j + 1) * ∫ T, Wt l T ^ (j + 1) *
    (p1 μ * l ^ (j + 1) * iota μ l (j + 1) * iota μ l (j + 2) +
      ((l - 1) / (l + 1) + p1 μ * iota μ l (j + 2)) * (1 - Wt l T) +
      (1 - Wt l T) ^ 2 / 2) ∂splitLaw μ

/-! ### Good events -/

/-- Leafless, and every present subtree has positive escape at every transient bias. -/
def GoodTree0 (T : Tree) : Prop :=
  (∀ v, Present T v → 1 ≤ T.val v) ∧
  ∀ l ∈ Set.Ioo 0 (mean μ), ∀ v, Present T v → 0 < escape l (subtree T v)

/-- `GoodTree0`, plus finiteness at every present subtree of the response envelope of the
proof of Proposition 2.5 (`prop:regularity`), on all rational bias intervals. -/
def RegTree (T : Tree) : Prop := GoodTree0 μ T ∧
  ∀ qNeg qPos : ℚ, 0 < qNeg → qNeg ≤ qPos → (qPos : ℝ) < mean μ → ∀ v, Present T v →
    envelopeProv (qNeg : ℝ) (qPos : ℝ) (subtree T v) < ⊤

/-! ### Measurability of the defined tree integrands -/

theorem measurable_Yt (l : ℝ) : Measurable (Yt l) := by
  exact (measurable_escape l).div (measurable_const.add (measurable_escape l))

theorem measurable_Wt (l : ℝ) : Measurable (Wt l) := by
  exact (measurable_childSum l).div (measurable_const.add (measurable_childSum l))

theorem measurable_deltaChild (l : ℝ) (i : ℕ) : Measurable (fun T => deltaChild l T i) := by
  have hc : Measurable (fun T : Tree => escape l (child T i)) :=
    (measurable_escape l).comp (continuous_child i).measurable
  exact measurable_const.div
    ((measurable_const.add (measurable_childSum l)).sub hc)

private theorem measurableSet_prefixBad (n : ℕ) :
    MeasurableSet {T : Tree | degree (subtree T (List.replicate n 1)) ≠ 1} := by
  exact ((continuous_degree.measurable.comp (measurable_subtree (List.replicate n 1)))
    (measurableSet_singleton 1)).compl

private theorem sInf_eq_succ_iff (S : Set ℕ) (n : ℕ) :
    sInf S = n + 1 ↔ n + 1 ∈ S ∧ ∀ j < n + 1, j ∉ S := by
  constructor
  · intro h
    have hne : S.Nonempty := Nat.nonempty_of_sInf_eq_succ h
    constructor
    · have hm := Nat.sInf_mem hne
      rwa [h] at hm
    · intro j hj
      exact Nat.notMem_of_lt_sInf (h ▸ hj)
  · rintro ⟨hn, hlt⟩
    apply le_antisymm (Nat.sInf_le hn)
    by_contra hle
    have hs : sInf S < n + 1 := Nat.lt_of_not_ge hle
    have hmem := Nat.sInf_mem (show S.Nonempty from ⟨n + 1, hn⟩)
    exact hlt (sInf S) hs hmem

/-- The first non-unary address is measurable, including the all-unary case
where `Nat.sInf ∅ = 0`. -/
theorem measurable_prefixLen : Measurable (prefixLen) := by
  apply measurable_to_countable'
  intro n
  cases n with
  | zero =>
      have heq : prefixLen ⁻¹' {0} =
          {T : Tree | degree (subtree T (List.replicate 0 1)) ≠ 1} ∪
            ⋂ n : ℕ, {T : Tree | degree (subtree T (List.replicate n 1)) ≠ 1}ᶜ := by
        ext T
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_ofPred_eq,
          Set.mem_iInter, Set.mem_compl_iff, prefixLen]
        rw [Nat.sInf_eq_zero]
        simp only [Set.mem_ofPred_eq, Set.eq_empty_iff_forall_notMem]
      rw [heq]
      exact (measurableSet_prefixBad 0).union
        (MeasurableSet.iInter fun n => (measurableSet_prefixBad n).compl)
  | succ n =>
      have heq : prefixLen ⁻¹' {n + 1} =
          {T : Tree | degree (subtree T (List.replicate (n + 1) 1)) ≠ 1} ∩
            ⋂ j ∈ Set.Iio (n + 1),
              {T : Tree | degree (subtree T (List.replicate j 1)) ≠ 1}ᶜ := by
        ext T
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, Set.mem_Iio, prefixLen]
        exact sInf_eq_succ_iff _ _
      rw [heq]
      exact (measurableSet_prefixBad (n + 1)).inter
        (MeasurableSet.biInter (Set.to_countable _)
          (fun j _ => (measurableSet_prefixBad j).compl))

/-- The split tree is measurable although its address depends on the input tree. -/
theorem measurable_splitTree : Measurable (splitTree) := by
  intro s hs
  have heq : splitTree ⁻¹' s = ⋃ n : ℕ,
      (prefixLen ⁻¹' {n}) ∩
        ((fun T : Tree => subtree T (List.replicate n 1)) ⁻¹' s) := by
    ext T
    simp [splitTree]
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    ((measurable_prefixLen (measurableSet_singleton n))).inter ((measurable_subtree _) hs)

end LPPMonotonicityProof.Analytic
