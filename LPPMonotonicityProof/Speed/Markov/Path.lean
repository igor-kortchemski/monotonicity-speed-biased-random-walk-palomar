module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Time-homogeneous trajectory measures

General Markov-chain infrastructure for the proof of the speed formula.  No topology or
countability is assumed on the state space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Preorder Filtration
open scoped ENNReal BigOperators

namespace LPPMonotonicityProof.Speed

variable {S : Type*} [MeasurableSpace S]

/-- A time-homogeneous transition kernel, viewed as a history kernel that reads
only the last state of a trajectory of length `n + 1`. -/
noncomputable def homKernel (K : Kernel S S) (n : ℕ) :
    Kernel (Π _ : Finset.Iic n, S) S :=
  K.comap (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance (K : Kernel S S) [IsMarkovKernel K] (n : ℕ) : IsMarkovKernel (homKernel K n) := by
  unfold homKernel
  infer_instance

/-- The law of a time-homogeneous Markov path started at a point. -/
noncomputable def path (K : Kernel S S) [IsMarkovKernel K] : Kernel S (ℕ → S) :=
  (Kernel.traj (X := fun _ => S) (homKernel K) 0).comap (fun s _ => s) (by fun_prop)

instance (K : Kernel S S) [IsMarkovKernel K] : IsMarkovKernel (path K) := by
  unfold path
  infer_instance

/-- The path measure associated with an arbitrary initial law. -/
noncomputable def pathMeasure (K : Kernel S S) [IsMarkovKernel K] (μ : Measure S) :
    Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ => S) μ (homKernel K)

/-- A point-started path has its prescribed initial state almost surely.
Singleton measurability is automatic on a standard Borel state space. -/
theorem path_zero (K : Kernel S S) [IsMarkovKernel K] [MeasurableSingletonClass S] [MeasurableEq S]
    (x : S) : ∀ᵐ ω ∂path K x, ω 0 = x := by
  have h : path K x {ω : ℕ → S | ω 0 ≠ x} = 0 := by
    change (Kernel.traj (homKernel K) 0 (fun _ => x)) {ω : ℕ → S | ω 0 ≠ x} = 0
    have hs : MeasurableSet {ω : ℕ → S | ω 0 ≠ x} :=
      (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).compl
    rw [← lintegral_indicator_one hs,
      Kernel.lintegral_traj (κ := homKernel K) (fun _ => x)
        (f := {ω : ℕ → S | ω 0 ≠ x}.indicator 1)
        (measurable_const.indicator hs)]
    simp [Set.indicator, Function.updateFinset]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h] with ω hω
  exact not_not.mp hω

/-- The path measure with Dirac initial law is the point-started path law.
Singleton measurability is automatic on a standard Borel state space. -/
theorem trajMeasure_dirac (K : Kernel S S) [IsMarkovKernel K] [MeasurableSingletonClass S]
    (x : S) :
    pathMeasure K (Measure.dirac x) = path K x := by
  rw [pathMeasure, Kernel.trajMeasure, Measure.map_dirac,
    Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- Drop the first entry of a prefix of length `n + 2`. -/
def tailPrefix (n : ℕ) (z : Π _ : Finset.Iic (n + 1), S) : Π _ : Finset.Iic n, S :=
  fun i => z ⟨i.1 + 1, Finset.mem_Iic.mpr (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩

/-- The final entry of a nonempty finite prefix. -/
def lastPrefix (n : ℕ) (z : Π _ : Finset.Iic n, S) : S :=
  z ⟨n, Finset.mem_Iic.mpr le_rfl⟩

/-- Append a state to a finite prefix. -/
def snocPrefix (n : ℕ) (z : Π _ : Finset.Iic n, S) (x : S) : Π _ : Finset.Iic (n + 1), S :=
  IicProdIoc (X := fun _ => S) n (n + 1) (z, MeasurableEquiv.piSingleton (X := fun _ => S) n x)

@[simp] lemma piSingleton_apply (n : ℕ) (x : S)
    (i : Finset.Ioc n (n + 1)) :
    MeasurableEquiv.piSingleton (X := fun _ => S) n x i = x := by
  cases Nat.mem_Ioc_succ' i
  rfl

lemma measurable_tailPrefix (n : ℕ) : Measurable (fun z : (Π _ : Finset.Iic (n + 1), S) =>
    tailPrefix n z) := by
  unfold tailPrefix
  fun_prop

lemma measurable_lastPrefix (n : ℕ) : Measurable (fun z : (Π _ : Finset.Iic n, S) =>
    lastPrefix n z) := by
  unfold lastPrefix
  fun_prop

lemma measurable_snocPrefix (n : ℕ) : Measurable (fun p : (Π _ : Finset.Iic n, S) × S =>
    snocPrefix n p.1 p.2) := by
  exact measurable_IicProdIoc.comp (measurable_fst.prodMk
    ((MeasurableEquiv.piSingleton (X := fun _ => S) n).measurable.comp measurable_snd))

lemma tailPrefix_snocPrefix (n : ℕ) (z : Π _ : Finset.Iic (n + 1), S) (x : S) :
    tailPrefix (n + 1) (snocPrefix (n + 1) z x) = snocPrefix n (tailPrefix n z) x := by
  ext i
  by_cases hi : i.1 ≤ n
  · have hi' : i.1 + 1 ≤ n + 1 := Nat.succ_le_succ hi
    simp [tailPrefix, snocPrefix, _root_.IicProdIoc, hi, hi']
  · have hi' : i.1 = n + 1 := by
      have := Finset.mem_Iic.mp i.2
      omega
    have hii : i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hi'
    subst i
    simp only [tailPrefix, snocPrefix, _root_.IicProdIoc,
      hi, ↓reduceDIte]
    simp [piSingleton_apply]

omit [MeasurableSpace S] in
lemma lastPrefix_tailPrefix (n : ℕ) (z : Π _ : Finset.Iic (n + 1), S) :
    lastPrefix n (tailPrefix n z) = lastPrefix (n + 1) z := by
  rfl

lemma lintegral_partialTraj_succ_homKernel (K : Kernel S S) [IsMarkovKernel K]
    (n : ℕ) (z : Π _ : Finset.Iic n, S) {f : (Π _ : Finset.Iic (n + 1), S) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ u, f u ∂Kernel.partialTraj (X := fun _ => S) (homKernel K) n (n + 1) z =
      ∫⁻ x, f (snocPrefix n z x) ∂K (lastPrefix n z) := by
  rw [Kernel.partialTraj_succ_self,
    Kernel.lintegral_map
      (Kernel.id ×ₖ (homKernel K n).map
        (MeasurableEquiv.piSingleton (X := fun _ => S) n))
      (measurable_IicProdIoc (X := fun _ => S)) z hf,
    Kernel.lintegral_id_prod
      (f := fun p : (Π _ : Finset.Iic n, S) × (Π _ : Finset.Ioc n (n + 1), S) =>
        f (IicProdIoc (X := fun _ => S) n (n + 1) p)) (hf.comp (measurable_IicProdIoc (X := fun _ => S)))
      ((homKernel K n).map (MeasurableEquiv.piSingleton (X := fun _ => S) n)) z,
    Kernel.lintegral_map (homKernel K n)
      (MeasurableEquiv.piSingleton (X := fun _ => S) n).measurable z
      (g' := fun b : (Π _ : Finset.Ioc n (n + 1), S) =>
        f (IicProdIoc (X := fun _ => S) n (n + 1) (z, b)))
      (hf.comp ((measurable_IicProdIoc (X := fun _ => S)).comp
        (measurable_const.prodMk measurable_id)))]
  rfl

lemma map_tailPrefix_partialTraj (K : Kernel S S) [IsMarkovKernel K]
    (n : ℕ) (z : Π _ : Finset.Iic 1, S) :
    (Kernel.partialTraj (X := fun _ => S) (homKernel K) 1 (n + 1) z).map (tailPrefix n) =
      Kernel.partialTraj (X := fun _ => S) (homKernel K) 0 n (fun _ => z ⟨1, by simp⟩) := by
  apply Measure.ext_of_lintegral
  induction n with
  | zero =>
      intro f hf
      rw [lintegral_map hf (measurable_tailPrefix 0)]
      simp only [Kernel.partialTraj_self, Kernel.id_apply]
      rw [lintegral_dirac' z (f := fun a => f (tailPrefix 0 a))
        (hf.comp (measurable_tailPrefix 0)),
        lintegral_dirac' _ hf]
      have hz : tailPrefix 0 z = (fun _ : Finset.Iic 0 => z ⟨1, by simp⟩) := by
        funext i
        apply congrArg z
        apply Subtype.ext
        have hi0 : i.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
        simp [hi0]
      exact congrArg f hz
  | succ n ih =>
      intro f hf
      rw [lintegral_map hf (measurable_tailPrefix (n + 1)),
        Kernel.partialTraj_succ_eq_comp (show 1 ≤ n + 1 by omega),
        Kernel.lintegral_comp _ _ z (g := fun a => f (tailPrefix (n + 1) a))
          (hf.comp (measurable_tailPrefix (n + 1)))]
      simp_rw [lintegral_partialTraj_succ_homKernel K (n + 1) _
        (f := fun c => f (tailPrefix (n + 1) c))
        (hf.comp (measurable_tailPrefix (n + 1)))]
      rw [show (fun z' : (Π _ : Finset.Iic (n + 1), S) =>
          ∫⁻ x, f (tailPrefix (n + 1) (snocPrefix (n + 1) z' x))
            ∂K (lastPrefix (n + 1) z')) =
        (fun z' => ∫⁻ x, f (snocPrefix n (tailPrefix n z') x)
            ∂K (lastPrefix n (tailPrefix n z'))) by
          funext z'
          simp only [tailPrefix_snocPrefix, lastPrefix_tailPrefix]]
      have hg : Measurable (fun u : (Π _ : Finset.Iic n, S) =>
          ∫⁻ x, f (snocPrefix n u x) ∂K (lastPrefix n u)) := by
        let κ : Kernel (Π _ : Finset.Iic n, S) S :=
          K.comap (lastPrefix n) (measurable_lastPrefix n)
        change Measurable (fun u : (Π _ : Finset.Iic n, S) =>
          ∫⁻ x, f (snocPrefix n u x) ∂κ u)
        exact (hf.comp (measurable_snocPrefix n)).lintegral_kernel_prod_right'
      rw [← lintegral_map hg (measurable_tailPrefix n), ih _ hg, Kernel.partialTraj_succ_eq_comp (Nat.zero_le n),
        Kernel.lintegral_comp _ _ _ hf]
      simp_rw [lintegral_partialTraj_succ_homKernel K n _ (f := f) hf]

/-- Shift a path one time step to the left. -/
def shiftPath (ω : ℕ → S) : ℕ → S := fun n => ω (n + 1)

/-- Prepend a state to a path. -/
def pcons (x : S) (ω : ℕ → S) : ℕ → S
  | 0 => x
  | n + 1 => ω n

lemma measurable_shiftPath : Measurable (fun ω : ℕ → S => shiftPath ω) := by
  refine .of_eval fun n => measurable_pi_apply (n + 1)

lemma measurable_pcons (x : S) : Measurable (fun ω : ℕ → S => pcons x ω) := by
  refine .of_eval fun n => ?_
  cases n with
  | zero => exact measurable_const
  | succ n => exact measurable_pi_apply n

set_option maxHeartbeats 800000 in
-- Dependent finite-prefix types make projective-limit elaboration unusually expensive.
lemma map_shiftPath_traj_one (K : Kernel S S) [IsMarkovKernel K]
    (z : Π _ : Finset.Iic 1, S) :
    (Kernel.traj (X := fun _ => S) (homKernel K) 1 z).map shiftPath =
      path K (z ⟨1, by simp⟩) := by
  let z₀ : Π _ : Finset.Iic 0, S := fun _ => z ⟨1, by simp⟩
  let P : (I : Finset ℕ) → Measure ((i : I) → S) := MeasureTheory.inducedFamily (X := fun _ => S) (fun n =>
    Kernel.partialTraj (X := fun _ => S) (homKernel K) 0 n z₀)
  let _ : ∀ I, IsProbabilityMeasure (P I) := by
    intro I
    dsimp [P]
    rw [MeasureTheory.inducedFamily]
    infer_instance
  have hP : IsProjectiveMeasureFamily (α := fun _ : ℕ => S) P := by
    dsimp [P]
    exact Kernel.isProjectiveMeasureFamily_partialTraj (X := fun _ => S) (homKernel K) z₀
  have h₀ : IsProjectiveLimit (α := fun _ : ℕ => S) (Kernel.trajFun (homKernel K) 0 z₀) P :=
    Kernel.isProjectiveLimit_trajFun (X := fun _ => S) (homKernel K) 0 z₀
  have h₁ : IsProjectiveLimit ((Kernel.trajFun (homKernel K) 1 z).map shiftPath) P := by
    rw [isProjectiveLimit_nat_iff hP]
    intro n
    have hPn : P (Finset.Iic n) = Kernel.partialTraj (X := fun _ => S) (homKernel K) 0 n z₀ := by
      dsimp [P]
      exact MeasureTheory.inducedFamily_Iic _ n
    rw [hPn]
    rw [Measure.map_map (measurable_frestrictLe n) measurable_shiftPath]
    have hcomp : (Preorder.frestrictLe (π := fun _ : ℕ => S) n) ∘
        (fun ω : ℕ → S => shiftPath ω) =
        (fun z : (Π _ : Finset.Iic (n + 1), S) => tailPrefix n z) ∘
          (Preorder.frestrictLe (π := fun _ : ℕ => S) (n + 1)) := by
      rfl
    rw [hcomp, ← Measure.map_map (measurable_tailPrefix n) (measurable_frestrictLe (n + 1)),
      ← Kernel.traj_apply, Kernel.traj_map_frestrictLe_apply, map_tailPrefix_partialTraj]
  change (Kernel.trajFun (homKernel K) 1 z).map shiftPath =
    Kernel.trajFun (homKernel K) 0 z₀
  exact (h₀.unique h₁).symm

lemma snocPrefix_zero_apply_zero (z : Π _ : Finset.Iic 0, S) (y : S) :
    snocPrefix 0 z y ⟨0, by simp⟩ = z ⟨0, by simp⟩ := by
  simp [snocPrefix, _root_.IicProdIoc]

lemma snocPrefix_zero_apply_one (z : Π _ : Finset.Iic 0, S) (y : S) :
    snocPrefix 0 z y ⟨1, by simp⟩ = y := by
  simp [snocPrefix, _root_.IicProdIoc]

lemma partialTraj_zero_one_homKernel (K : Kernel S S) [IsMarkovKernel K]
    (z : Π _ : Finset.Iic 0, S) :
    Kernel.partialTraj (X := fun _ => S) (homKernel K) 0 1 z =
      (K (z ⟨0, by simp⟩)).map (snocPrefix 0 z) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_partialTraj_succ_homKernel K 0 z hf]
  rw [lintegral_map (g := snocPrefix 0 z) hf ((measurable_snocPrefix 0).comp
    (measurable_const.prodMk measurable_id))]
  rfl

/-- The shifted path has the mixture of path laws given by the first transition. -/
theorem path_shift (K : Kernel S S) [IsMarkovKernel K] (x : S) :
    (path K x).map shiftPath = (path K) ∘ₘ K x := by
  let z : Π _ : Finset.Iic 0, S := fun _ => x
  change (Kernel.traj (X := fun _ => S) (homKernel K) 0 z).map shiftPath = _
  rw [← Kernel.traj_comp_partialTraj (show 0 ≤ 1 by omega), Kernel.comp_apply,
    Measure.map_bind (Kernel.measurable _).aemeasurable measurable_shiftPath.aemeasurable]
  simp_rw [map_shiftPath_traj_one]
  rw [partialTraj_zero_one_homKernel,
    Measure.bind_map (f := snocPrefix 0 z) (g := fun a => path K (a ⟨1, by simp⟩))
      ((measurable_snocPrefix 0).comp
        (measurable_const.prodMk measurable_id)).aemeasurable
      ((Kernel.measurable (path K)).comp (by fun_prop)).aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [] with y
  rw [snocPrefix_zero_apply_one]

omit [MeasurableSpace S] in
lemma pcons_comp_shiftPath (x : S) :
    pcons x ∘ shiftPath = fun ω => Function.updateFinset ω (Finset.Iic 0) (fun _ => x) := by
  funext ω n
  cases n with
  | zero => simp [pcons, Function.updateFinset]
  | succ n => simp [pcons, shiftPath, Function.updateFinset]

/-- First-step decomposition of a homogeneous path law. -/
theorem path_firstStep (K : Kernel S S) [IsMarkovKernel K] (x : S) :
    path K x = (Kernel.map (path K) (pcons x)) ∘ₘ K x := by
  have h := congrArg (Measure.map (pcons x)) (path_shift K x)
  rw [Measure.map_map (measurable_pcons x) measurable_shiftPath,
    pcons_comp_shiftPath, Measure.map_bind (Kernel.measurable _).aemeasurable
      (measurable_pcons x).aemeasurable] at h
  let z : Π _ : Finset.Iic 0, S := fun _ => x
  have hupdate : (path K x).map
      (fun ω => Function.updateFinset ω (Finset.Iic 0) (fun _ => x)) = path K x := by
    change (Kernel.traj (X := fun _ => S) (homKernel K) 0 z).map
      (Function.updateFinset · (Finset.Iic 0) z) = _
    exact Kernel.traj_map_updateFinset (X := fun _ => S) z
  rw [hupdate] at h
  refine h.trans (Measure.bind_congr_right ?_)
  filter_upwards [] with y
  exact (Kernel.map_apply (path K) (measurable_pcons x) y).symm


/-- Prepend a state to a finite path prefix. -/
def consPrefix (n : ℕ) (x : S) (z : Π _ : Finset.Iic n, S) : Π _ : Finset.Iic (n + 1), S
  | ⟨0, _⟩ => x
  | ⟨j + 1, hj⟩ => z ⟨j, Finset.mem_Iic.mpr (Nat.succ_le_succ_iff.mp (Finset.mem_Iic.mp hj))⟩

lemma measurable_consPrefix (n : ℕ) : Measurable (fun p : S × (Π _ : Finset.Iic n, S) =>
    consPrefix n p.1 p.2) := by
  refine .of_eval fun i => ?_
  obtain ⟨(_ | j), hj⟩ := i
  · change Measurable (fun p : S × (Π _ : Finset.Iic n, S) => p.1)
    exact measurable_fst
  · change Measurable (fun p : S × (Π _ : Finset.Iic n, S) => p.2
      ⟨j, Finset.mem_Iic.mpr (Nat.succ_le_succ_iff.mp (Finset.mem_Iic.mp hj))⟩)
    exact (measurable_pi_apply (⟨j, Finset.mem_Iic.mpr
      (Nat.succ_le_succ_iff.mp (Finset.mem_Iic.mp hj))⟩ : Finset.Iic n)).comp measurable_snd

omit [MeasurableSpace S] in
lemma frestrictLe_zero_pcons (x : S) :
    (Preorder.frestrictLe (π := fun _ : ℕ => S) 0) ∘ pcons x =
      fun _ : ℕ → S => (fun _ : Finset.Iic 0 => x) := by
  funext ω i
  have hi : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := by
    apply Subtype.ext
    exact Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
  subst i
  rfl

omit [MeasurableSpace S] in
lemma frestrictLe_succ_pcons (n : ℕ) (x : S) :
    (Preorder.frestrictLe (π := fun _ : ℕ => S) (n + 1)) ∘ pcons x =
      (fun z : (Π _ : Finset.Iic n, S) => consPrefix n x z) ∘
        (Preorder.frestrictLe (π := fun _ : ℕ => S) n) := by
  funext ω i
  obtain ⟨(_ | j), hj⟩ := i
  · rfl
  · rfl

set_option maxHeartbeats 800000 in
-- Kernel map/bind extensionality needs additional definitional equality work.
lemma map_frestrictLe_zero_firstStep (K : Kernel S S) [IsMarkovKernel K]
    (η : Kernel S (ℕ → S)) [IsMarkovKernel η] (x : S) :
    ((Kernel.map η (pcons x)) ∘ₘ K x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ : Finset.Iic 0 => x) := by
  rw [Measure.map_bind (Kernel.aemeasurable (Kernel.map η (pcons x)))
    (measurable_frestrictLe 0).aemeasurable]
  calc
    _ = (fun _ : S => Measure.dirac (fun _ : Finset.Iic 0 => x)) ∘ₘ K x := by
      apply Measure.bind_congr_right
      filter_upwards [] with y
      rw [Kernel.map_apply _ (measurable_pcons x),
        Measure.map_map (measurable_frestrictLe 0) (measurable_pcons x), frestrictLe_zero_pcons]
      rw [Measure.map_const, measure_univ, one_smul]
    _ = _ := by rw [Measure.bind_const, measure_univ, one_smul]

lemma map_frestrictLe_succ_firstStep (K : Kernel S S) [IsMarkovKernel K]
    (η : Kernel S (ℕ → S)) [IsMarkovKernel η] (x : S) (n : ℕ) :
    ((Kernel.map η (pcons x)) ∘ₘ K x).map (Preorder.frestrictLe (n + 1)) =
      (fun y => ((η y).map (Preorder.frestrictLe n)).map (consPrefix n x)) ∘ₘ K x := by
  rw [Measure.map_bind (Kernel.aemeasurable (Kernel.map η (pcons x)))
    (measurable_frestrictLe (n + 1)).aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [] with y
  rw [Kernel.map_apply _ (measurable_pcons x),
    Measure.map_map (measurable_frestrictLe (n + 1)) (measurable_pcons x),
    frestrictLe_succ_pcons, ← Measure.map_map
      (μ := η y) (g := fun z => consPrefix n x z)
      ((measurable_consPrefix n).comp (measurable_const.prodMk measurable_id))
      (measurable_frestrictLe n)]

lemma map_frestrictLe_path_zero (K : Kernel S S) [IsMarkovKernel K]
    (z : Π _ : Finset.Iic 0, S) (n : ℕ) :
    (path K (z ⟨0, by simp⟩)).map (Preorder.frestrictLe n) =
      Kernel.partialTraj (X := fun _ => S) (homKernel K) 0 n z := by
  have hz : z = (fun _ => z ⟨0, by simp⟩) := by
    funext i
    apply congrArg z
    apply Subtype.ext
    exact Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
  rw [hz, path, Kernel.comap_apply, Kernel.traj_map_frestrictLe_apply]

set_option maxHeartbeats 800000 in
-- The dependent singleton-prefix family is expensive to unify with `traj`.
lemma comap_zero_eq_traj_of_forall_map_frestrictLe (K : Kernel S S) [IsMarkovKernel K]
    (η : Kernel S (ℕ → S)) [IsMarkovKernel η]
    (h : ∀ n x, (η x).map (Preorder.frestrictLe n) =
      (path K x).map (Preorder.frestrictLe n)) :
    η.comap (fun z : (Π _ : Finset.Iic 0, S) => z ⟨0, by simp⟩) (measurable_pi_apply _) =
      Kernel.traj (X := fun _ => S) (homKernel K) 0 := by
  let η₀ : Kernel (Π _ : Finset.Iic 0, S) (ℕ → S) :=
    η.comap (fun z : (Π _ : Finset.Iic 0, S) => z ⟨0, by simp⟩) (measurable_pi_apply _)
  change η₀ = _
  apply Kernel.eq_traj (X := fun _ => S) (homKernel K) η₀
  intro n
  ext z' : 1
  have hz : z' = (fun _ => z' ⟨0, by simp⟩) := by
    funext i
    apply congrArg z'
    apply Subtype.ext
    exact Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
  rw [hz, Kernel.map_apply _ (measurable_frestrictLe n)]
  simp only [η₀, Kernel.comap_apply]
  change (η (z' ⟨0, by simp⟩)).map (Preorder.frestrictLe n) = _
  rw [h, map_frestrictLe_path_zero, ← hz]

set_option maxHeartbeats 800000 in
-- The induction and final dependent-kernel comaps share a large elaboration cost.
/-- A Markov family of path measures is determined by its first-step equation. -/
theorem eq_path_of_firstStep (K : Kernel S S) [IsMarkovKernel K]
    (η : Kernel S (ℕ → S)) [IsMarkovKernel η]
    (h : ∀ x, η x = (Kernel.map η (pcons x)) ∘ₘ K x) : η = path K := by
  have hfinite : ∀ n x, (η x).map (Preorder.frestrictLe n) =
      (path K x).map (Preorder.frestrictLe n) := by
    intro n
    induction n with
    | zero =>
        intro x
        rw [h x, path_firstStep, map_frestrictLe_zero_firstStep,
          map_frestrictLe_zero_firstStep]
    | succ n ih =>
        intro x
        rw [h x, path_firstStep, map_frestrictLe_succ_firstStep,
          map_frestrictLe_succ_firstStep]
        apply Measure.bind_congr_right
        filter_upwards [] with y
        rw [ih y]
  let η₀ : Kernel (Π _ : Finset.Iic 0, S) (ℕ → S) :=
    η.comap (fun z : (Π _ : Finset.Iic 0, S) => z ⟨0, by simp⟩) (measurable_pi_apply _)
  have htraj : η₀ = Kernel.traj (X := fun _ => S) (homKernel K) 0 :=
    comap_zero_eq_traj_of_forall_map_frestrictLe K η hfinite
  let init : S → (Π _ : Finset.Iic 0, S) := fun s _ => s
  have hi : Measurable init := by fun_prop
  have hcom := congrArg (fun κ : Kernel (Π _ : Finset.Iic 0, S) (ℕ → S) =>
    κ.comap init hi) htraj
  calc
    η = η₀.comap init hi := by
      ext x : 1
      rfl
    _ = (Kernel.traj (X := fun _ => S) (homKernel K) 0).comap init hi := hcom
    _ = path K := rfl


/-- The path shifted by `t` steps. -/
def shiftN (t : ℕ) (ω : ℕ → S) : ℕ → S := fun n => ω (n + t)

lemma measurable_shiftN (t : ℕ) : Measurable (fun ω : ℕ → S => shiftN t ω) := by
  refine .of_eval fun n => measurable_pi_apply (n + t)

omit [MeasurableSpace S] in
lemma shiftN_zero (ω : ℕ → S) : shiftN 0 ω = ω := by
  funext n
  rfl

omit [MeasurableSpace S] in
lemma shiftN_succ_pcons (t : ℕ) (x : S) (ω : ℕ → S) :
    shiftN (t + 1) (pcons x ω) = shiftN t ω := by
  rfl

lemma measurableSet_preimage_pcons_of_piLE_succ (x : S) {B : Set (ℕ → S)} (t : ℕ)
    (hB : MeasurableSet[piLE (t + 1)] B) : MeasurableSet[piLE t] (pcons x ⁻¹' B) := by
  rw [piLE_eq_comap_frestrictLe] at hB ⊢
  rcases hB with ⟨C, hC, rfl⟩
  refine ⟨consPrefix t x ⁻¹' C, hC.preimage
    ((measurable_consPrefix t).comp (measurable_const.prodMk measurable_id)), ?_⟩
  rw [← Set.preimage_comp, ← Set.preimage_comp, frestrictLe_succ_pcons]

lemma mem_pcons_iff_of_piLE_zero {B : Set (ℕ → S)}
    (hB : MeasurableSet[piLE 0] B) (x : S) (ω : ℕ → S) :
    pcons x ω ∈ B ↔ (fun _ : ℕ => x) ∈ B := by
  rw [piLE_eq_comap_frestrictLe] at hB
  rcases hB with ⟨C, hC, rfl⟩
  change Preorder.frestrictLe 0 (pcons x ω) ∈ C ↔ Preorder.frestrictLe 0 (fun _ => x) ∈ C
  have heq : Preorder.frestrictLe 0 (pcons x ω) =
      Preorder.frestrictLe 0 (fun _ : ℕ => x) := by
    rw [show Preorder.frestrictLe 0 (pcons x ω) = (fun _ : Finset.Iic 0 => x) from
      congrFun (frestrictLe_zero_pcons x) ω]
    funext i
    rfl
  rw [heq]

set_option maxHeartbeats 800000 in
-- Measurability through measure-valued binds is elaboration-intensive here.
lemma setLIntegral_bind {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] (μ : Measure α) {B : Set β} (hB : MeasurableSet B)
    {F : β → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in B, F x ∂(κ ∘ₘ μ) = ∫⁻ a, ∫⁻ x in B, F x ∂κ a ∂μ := by
  rw [← lintegral_indicator hB, Measure.lintegral_bind (Kernel.measurable κ).aemeasurable
    (hF.indicator hB).aemeasurable]
  apply lintegral_congr
  intro a
  rw [lintegral_indicator hB]

lemma path_apply_firstStep (K : Kernel S S) [IsMarkovKernel K] (x : S)
    {C : Set (ℕ → S)} (hC : MeasurableSet C) :
    path K x C = ∫⁻ y, path K y (pcons x ⁻¹' C) ∂K x := by
  rw [path_firstStep, Measure.bind_apply hC (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro y
  rw [Kernel.map_apply _ (measurable_pcons x), Measure.map_apply (measurable_pcons x) hC]

lemma setLIntegral_path_firstStep (K : Kernel S S) [IsMarkovKernel K] (x : S)
    {B : Set (ℕ → S)} (hB : MeasurableSet B) {F : (ℕ → S) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω in B, F ω ∂path K x =
      ∫⁻ y, ∫⁻ ω in pcons x ⁻¹' B, F (pcons x ω) ∂path K y ∂K x := by
  let _ : IsMarkovKernel ((path K).map (pcons x)) := Kernel.IsMarkovKernel.map _ (measurable_pcons x)
  rw [path_firstStep, setLIntegral_bind _ _ hB hF]
  apply lintegral_congr
  intro y
  rw [Kernel.map_apply _ (measurable_pcons x), setLIntegral_map hB hF (measurable_pcons x)]

set_option maxHeartbeats 800000 in
-- The induction repeatedly rewrites mapped, restrained kernel measures.
/-- The fixed-time Markov property for the cylinder filtration. -/
theorem path_markov (K : Kernel S S) [IsMarkovKernel K] (t : ℕ) (x : S)
    {B : Set (ℕ → S)} (hB : MeasurableSet[piLE t] B)
    {A : Set (ℕ → S)} (hA : MeasurableSet A) :
    path K x (B ∩ shiftN t ⁻¹' A) = ∫⁻ ω in B, path K (ω t) A ∂path K x := by
  induction t generalizing x B with
  | zero =>
      have hshift : (shiftN 0 : (ℕ → S) → ℕ → S) = id := by
        funext ω
        exact shiftN_zero ω
      rw [hshift, Set.preimage_id]
      have hBm : MeasurableSet B := (piLE.le 0) B hB
      have hF : Measurable (fun ω : ℕ → S => path K (ω 0) A) :=
        ((path K).measurable_coe hA).comp (measurable_pi_apply 0)
      by_cases hc : (fun _ : ℕ => x) ∈ B
      · have hpre : pcons x ⁻¹' B = Set.univ := by
          apply Set.eq_univ_of_forall
          intro ω
          exact (mem_pcons_iff_of_piLE_zero hB x ω).2 hc
        have hL : path K x (B ∩ A) = path K x A := by
          rw [path_apply_firstStep K x (hBm.inter hA)]
          rw [path_apply_firstStep K x hA]
          congr 1 with y
          rw [Set.preimage_inter, hpre, Set.univ_inter]
        rw [hL]
        have hR : (∫⁻ ω in B, path K (ω 0) A ∂path K x) =
            ∫⁻ y, ∫⁻ _ω in pcons x ⁻¹' B, path K x A ∂path K y ∂K x := by
          rw [setLIntegral_path_firstStep K x hBm hF]
          rfl
        rw [hR]
        simp [hpre]
      · have hpre : pcons x ⁻¹' B = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro ω hω
          exact hc ((mem_pcons_iff_of_piLE_zero hB x ω).1 hω)
        have hL : path K x (B ∩ A) = 0 := by
          rw [path_apply_firstStep K x (hBm.inter hA)]
          simp [Set.preimage_inter, hpre]
        rw [hL]
        have hR : (∫⁻ ω in B, path K (ω 0) A ∂path K x) =
            ∫⁻ y, ∫⁻ _ω in pcons x ⁻¹' B, path K x A ∂path K y ∂K x := by
          rw [setLIntegral_path_firstStep K x hBm hF]
          rfl
        rw [hR]
        simp [hpre]
  | succ t ih =>
      have hBm : MeasurableSet B := (piLE.le (t + 1)) B hB
      have hF : Measurable (fun ω : ℕ → S => path K (ω (t + 1)) A) :=
        ((path K).measurable_coe hA).comp (measurable_pi_apply (t + 1))
      have hC : MeasurableSet (B ∩ shiftN (t + 1) ⁻¹' A) :=
        hBm.inter (hA.preimage (measurable_shiftN (t + 1)))
      have hpre : pcons x ⁻¹' (B ∩ shiftN (t + 1) ⁻¹' A) =
          (pcons x ⁻¹' B) ∩ shiftN t ⁻¹' A := by
        rw [Set.preimage_inter]
        congr 1
      calc
        path K x (B ∩ shiftN (t + 1) ⁻¹' A) =
            ∫⁻ y, path K y ((pcons x ⁻¹' B) ∩ shiftN t ⁻¹' A) ∂K x := by
          rw [path_apply_firstStep K x hC, hpre]
        _ = ∫⁻ y, ∫⁻ ω in pcons x ⁻¹' B, path K (ω t) A ∂path K y ∂K x := by
          apply lintegral_congr
          intro y
          exact ih y (measurableSet_preimage_pcons_of_piLE_succ x t hB)
        _ = ∫⁻ ω in B, path K (ω (t + 1)) A ∂path K x := by
          rw [setLIntegral_path_firstStep K x hBm hF]
          rfl


/-- The trajectory measure with initial law `μ` is the mixture of point-started paths. -/
theorem pathMeasure_eq_bind (K : Kernel S S) [IsMarkovKernel K] (μ : Measure S) :
    pathMeasure K μ = (path K) ∘ₘ μ := by
  rw [pathMeasure, Kernel.trajMeasure,
    Measure.bind_map (f := (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => S)).symm)
      (g := Kernel.traj (X := fun _ => S) (homKernel K) 0)
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => S)).symm.measurable.aemeasurable
      (Kernel.measurable (Kernel.traj (X := fun _ => S) (homKernel K) 0)).aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [] with x
  rw [path, Kernel.comap_apply]
  congr 1

/-- Shift stationarity follows from invariance of the initial law. -/
theorem measurePreserving_shiftPath (K : Kernel S S) [IsMarkovKernel K] (π : Measure S)
    (hπ : K ∘ₘ π = π) : MeasurePreserving shiftPath (pathMeasure K π) (pathMeasure K π) := by
  refine ⟨measurable_shiftPath, ?_⟩
  rw [pathMeasure_eq_bind,
    Measure.map_bind (Kernel.measurable (path K)).aemeasurable measurable_shiftPath.aemeasurable]
  simp_rw [path_shift]
  rw [← Measure.bind_bind (Kernel.measurable K).aemeasurable
    (Kernel.measurable (path K)).aemeasurable, hπ]



end LPPMonotonicityProof.Speed
