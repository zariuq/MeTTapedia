import Mettapedia.CategoryTheory.DeFinettiGlobalFinitaryDiagram
import Mettapedia.CategoryTheory.DeFinettiKernelInterface
import Mettapedia.CategoryTheory.DeFinettiSequenceKernelCone
import Exchangeability.Core
import Exchangeability.Probability.InfiniteProduct
import Mathlib.CategoryTheory.Monad.Kleisli
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Kleisli(Giry) Global Diagram and IID Cone Data

This file provides the categorical spine for the global de Finetti target:
- ambient category `Kleisli(MeasCat.Giry)`,
- a true global finitary-permutation diagram functor on `Bool^ℕ`,
- and cone data wrappers for an iid candidate arrow.

The universal-property payload is currently tracked through the existing
kernel-level mediator API (`KernelLatentThetaUniversalMediator`), which this
file still packages as `IsLimitLikeForIIDConeSkeleton`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

open CategoryTheory
open MeasureTheory

variable {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Ambient category for the Giry-Kleisli formulation. -/
abbrev KleisliGiry : Type 1 := CategoryTheory.Kleisli (C := MeasCat) MeasCat.Giry

instance : CategoryTheory.Category KleisliGiry :=
  CategoryTheory.Kleisli.category (T := MeasCat.Giry)

/-- Canonical sequence object `Bool^ℕ` in `Kleisli(MeasCat.Giry)`. -/
abbrev KleisliBinarySeqObj : KleisliGiry :=
  (MeasCat.of GlobalBinarySeq : CategoryTheory.Kleisli (C := MeasCat) MeasCat.Giry)

/-- Canonical parameter object `P Bool` in `Kleisli(MeasCat.Giry)`. -/
abbrev KleisliProbBoolObj : KleisliGiry :=
  (MeasCat.of (ProbabilityMeasure Bool) : CategoryTheory.Kleisli (C := MeasCat) MeasCat.Giry)

/-- Measurability of the finitary-permutation action on binary sequences. -/
lemma measurable_finSuppPermuteSeq (τ : FinSuppPermNat) :
    Measurable (finSuppPermuteSeq τ) := by
  refine measurable_pi_lambda _ ?_
  intro i
  simpa [finSuppPermuteSeq] using (measurable_pi_apply (a := (τ.1.symm i)))

/-- Identity action law for finitary permutation action on sequences. -/
lemma finSuppPermuteSeq_one (ω : GlobalBinarySeq) :
    finSuppPermuteSeq (1 : FinSuppPermNat) ω = ω := by
  funext i
  simp [finSuppPermuteSeq]

/-- Composition law for finitary permutation action on sequences. -/
lemma finSuppPermuteSeq_mul (τ υ : FinSuppPermNat) (ω : GlobalBinarySeq) :
    finSuppPermuteSeq (τ * υ) ω = finSuppPermuteSeq τ (finSuppPermuteSeq υ ω) := by
  funext i
  change ω (((τ * υ : FinSuppPermNat).1).symm i) = ω ((υ.1).symm ((τ.1).symm i))
  have harg : ((τ * υ : FinSuppPermNat).1).symm i = (υ.1).symm ((τ.1).symm i) := by
    apply (τ * υ).1.injective
    simp [Equiv.Perm.mul_apply]
  exact congrArg ω harg

/-- Deterministic Kleisli morphism induced by a global finitary permutation. -/
def finSuppPermKleisliHom (τ : FinSuppPermNat) :
    KleisliBinarySeqObj ⟶ KleisliBinarySeqObj :=
  ⟨fun ω => Measure.dirac (finSuppPermuteSeq τ ω),
    Measure.measurable_dirac.comp (measurable_finSuppPermuteSeq τ)⟩

/-- Deterministic Kleisli hom for identity permutation is the Kleisli identity. -/
lemma finSuppPermKleisliHom_one :
    finSuppPermKleisliHom (1 : FinSuppPermNat) =
      CategoryTheory.CategoryStruct.id KleisliBinarySeqObj := by
  apply Subtype.ext
  funext ω
  change Measure.dirac (finSuppPermuteSeq (1 : FinSuppPermNat) ω) = Measure.dirac ω
  simp [finSuppPermuteSeq_one]

/-- Deterministic Kleisli hom composition law for finitary permutations. -/
lemma finSuppPermKleisliHom_comp (τ υ : FinSuppPermNat) :
    CategoryTheory.CategoryStruct.comp (finSuppPermKleisliHom υ) (finSuppPermKleisliHom τ) =
      finSuppPermKleisliHom (τ * υ) := by
  apply Subtype.ext
  funext ω
  change
    Measure.bind (Measure.dirac (finSuppPermuteSeq υ ω))
        (fun x => Measure.dirac (finSuppPermuteSeq τ x)) =
      Measure.dirac (finSuppPermuteSeq (τ * υ) ω)
  simpa [finSuppPermuteSeq_mul] using
    (Measure.dirac_bind
      (hf := Measure.measurable_dirac.comp (measurable_finSuppPermuteSeq τ))
      (a := finSuppPermuteSeq υ ω))

/-- Monoid action into endomorphisms of `Bool^ℕ` in `Kleisli(MeasCat.Giry)`. -/
def finSuppPermKleisliEndMonoidHom :
    FinSuppPermNat →* CategoryTheory.End KleisliBinarySeqObj where
  toFun := finSuppPermKleisliHom
  map_one' := finSuppPermKleisliHom_one
  map_mul' τ υ := by
    simpa [CategoryTheory.End.mul_def] using (finSuppPermKleisliHom_comp τ υ).symm

/-- True global finitary-permutation diagram functor in `Kleisli(MeasCat.Giry)`. -/
def kleisliGiryGlobalDiagramFunctor :
    CategoryTheory.Functor GlobalFinSuppPermIndex KleisliGiry :=
  CategoryTheory.SingleObj.functor
    (M := FinSuppPermNat) (X := KleisliBinarySeqObj) finSuppPermKleisliEndMonoidHom

@[simp] theorem kleisliGiryGlobalDiagramFunctor_obj :
    (kleisliGiryGlobalDiagramFunctor).obj globalFinSuppPermStar = KleisliBinarySeqObj := rfl

@[simp] theorem kleisliGiryGlobalDiagramFunctor_map (τ : FinSuppPermNat) :
    (kleisliGiryGlobalDiagramFunctor).map
        (X := globalFinSuppPermStar) (Y := globalFinSuppPermStar) τ =
      finSuppPermKleisliHom τ := rfl

/-! ## Strong IID Construction (Theta-Parametric) -/

abbrev LatentTheta : Type := Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta

/-- Time-indexed type family carrying the latent parameter at time `0` and Boolean
samples afterward. -/
def ThetaBoolTimeline : ℕ → Type
  | 0 => LatentTheta
  | _ + 1 => Bool

instance thetaBoolTimelineMeasurableSpace : ∀ n : ℕ, MeasurableSpace (ThetaBoolTimeline n)
  | 0 => by
      simpa [ThetaBoolTimeline] using (inferInstance : MeasurableSpace LatentTheta)
  | _ + 1 => by
      simpa [ThetaBoolTimeline] using (inferInstance : MeasurableSpace Bool)

abbrev ThetaBoolPrefix (n : ℕ) : Type := Π i : Finset.Iic n, ThetaBoolTimeline i

def thetaPrefixZeroIdx (n : ℕ) : Finset.Iic n :=
  ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩

/-- Extract the latent `Theta` value from a trajectory prefix. -/
def thetaFromPrefix {n : ℕ} (x : ThetaBoolPrefix n) : LatentTheta :=
  by
    simpa [thetaPrefixZeroIdx, ThetaBoolTimeline] using x (thetaPrefixZeroIdx n)

lemma measurable_thetaFromPrefix {n : ℕ} :
    Measurable (thetaFromPrefix (n := n)) := by
  simpa [thetaFromPrefix, thetaPrefixZeroIdx, ThetaBoolTimeline] using
    (measurable_pi_apply (a := (thetaPrefixZeroIdx n)))

/-- Read the unique coordinate of a `Fin 1 → Bool` tuple. -/
def fin1TupleToBool (x : Fin 1 → Bool) : Bool :=
  x ⟨0, by decide⟩

lemma measurable_fin1TupleToBool : Measurable fin1TupleToBool := by
  simpa [fin1TupleToBool] using (measurable_pi_apply (a := (⟨0, by decide⟩ : Fin 1)))

/-- One-step Bernoulli kernel on `Bool` parameterized by `Theta`. -/
def thetaBernoulliKernel : ProbabilityTheory.Kernel LatentTheta Bool :=
  ProbabilityTheory.Kernel.map
    (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel (n := 1))
    fin1TupleToBool

instance thetaBernoulliKernel_isMarkov : ProbabilityTheory.IsMarkovKernel thetaBernoulliKernel := by
  simpa [thetaBernoulliKernel] using
    (ProbabilityTheory.Kernel.IsMarkovKernel.map
      (κ := Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel (n := 1))
      (f := fin1TupleToBool)
      measurable_fin1TupleToBool)

/-- Convert `Theta` into the corresponding Bernoulli law on `Bool`. -/
def thetaToProbBool (θ : LatentTheta) : ProbabilityMeasure Bool :=
  ⟨thetaBernoulliKernel θ, by infer_instance⟩

lemma measurable_thetaToProbBool : Measurable thetaToProbBool := by
  refine Measurable.subtype_mk ?_
  simpa [thetaToProbBool] using
    (thetaBernoulliKernel.measurable :
      Measurable fun θ : LatentTheta => (thetaBernoulliKernel θ : Measure Bool))

/-- Time-homogeneous IID transition kernel family indexed by trajectory prefixes:
the next Boolean sample depends only on the latent `Theta` coordinate. -/
def thetaIidStep (n : ℕ) :
    ProbabilityTheory.Kernel (ThetaBoolPrefix n) (ThetaBoolTimeline (n + 1)) where
  toFun := fun x => by
    simpa [ThetaBoolTimeline] using (thetaBernoulliKernel (thetaFromPrefix x))
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ ?_
    intro s hs
    simpa [ThetaBoolTimeline] using
      (thetaBernoulliKernel.measurable_coe (s := s) hs).comp measurable_thetaFromPrefix

instance thetaIidStep_isMarkov (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel (thetaIidStep n) := by
  refine ⟨?_⟩
  intro x
  simpa [thetaIidStep, ThetaBoolTimeline] using
    (show IsProbabilityMeasure (thetaBernoulliKernel (thetaFromPrefix x)) from inferInstance)

/-- Deterministic embedding of `Theta` into prefixes of length `0`. -/
noncomputable def thetaToPrefix0 : LatentTheta → ThetaBoolPrefix 0 :=
  fun θ i => by
    rcases i with ⟨j, hj⟩
    have hj0 : j = 0 := Nat.le_antisymm (Finset.mem_Iic.1 hj) (Nat.zero_le _)
    subst hj0
    simpa [ThetaBoolTimeline] using θ

lemma measurable_thetaToPrefix0 : Measurable thetaToPrefix0 := by
  refine measurable_pi_lambda _ ?_
  intro i
  rcases i with ⟨j, hj⟩
  have hj0 : j = 0 := Nat.le_antisymm (Finset.mem_Iic.1 hj) (Nat.zero_le _)
  subst hj0
  simpa [thetaToPrefix0, ThetaBoolTimeline] using
    (measurable_id : Measurable fun θ : LatentTheta => θ)

/-- Trajectory kernel on the augmented timeline (`Theta` at index `0`, then IID booleans). -/
abbrev thetaIidTrajPrefix0 :
    ProbabilityTheory.Kernel (ThetaBoolPrefix 0) (Π n, ThetaBoolTimeline n) :=
  ProbabilityTheory.Kernel.traj thetaIidStep 0

/-- Same trajectory kernel with direct `Theta` input (via deterministic prefix injection). -/
def thetaIidAugmentedKernel :
    ProbabilityTheory.Kernel LatentTheta (Π n, ThetaBoolTimeline n) :=
  ProbabilityTheory.Kernel.comp
    thetaIidTrajPrefix0
    (ProbabilityTheory.Kernel.deterministic thetaToPrefix0 measurable_thetaToPrefix0)

instance thetaIidAugmentedKernel_isMarkov : ProbabilityTheory.IsMarkovKernel thetaIidAugmentedKernel := by
  dsimp [thetaIidAugmentedKernel]
  infer_instance

/-- Forget the latent coordinate and keep the Boolean sample stream. -/
def dropThetaHead (x : Π n, ThetaBoolTimeline n) : GlobalBinarySeq :=
  fun n => x (n + 1)

lemma measurable_dropThetaHead : Measurable dropThetaHead := by
  refine measurable_pi_lambda _ ?_
  intro n
  simpa [dropThetaHead] using (measurable_pi_apply (a := (n + 1)))

/-- Strong IID sequence kernel parameterized by `Theta`. -/
def iidSequenceKernelTheta : ProbabilityTheory.Kernel LatentTheta GlobalBinarySeq :=
  ProbabilityTheory.Kernel.map thetaIidAugmentedKernel dropThetaHead

instance iidSequenceKernelTheta_isMarkov : ProbabilityTheory.IsMarkovKernel iidSequenceKernelTheta := by
  simpa [iidSequenceKernelTheta] using
    (ProbabilityTheory.Kernel.IsMarkovKernel.map
      (κ := thetaIidAugmentedKernel)
      (f := dropThetaHead)
      measurable_dropThetaHead)

/-- Coordinate projection keeping the first `n` Boolean samples of a sequence. -/
def seqPrefixProj (n : ℕ) : GlobalBinarySeq → (Fin n → Bool) :=
  fun ω i => ω i

lemma measurable_seqPrefixProj (n : ℕ) : Measurable (seqPrefixProj n) := by
  unfold seqPrefixProj
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply (a := i.1))

/-- Drop the latent head coordinate from a `Theta`-augmented prefix of length `n`. -/
def dropThetaPrefix (n : ℕ) (x : ThetaBoolPrefix n) : Fin n → Bool :=
  fun i => by
    have hi : i.1 + 1 ≤ n := Nat.succ_le_of_lt i.2
    exact cast (by simp [ThetaBoolTimeline]) (x ⟨i.1 + 1, Finset.mem_Iic.2 hi⟩)

lemma measurable_dropThetaPrefix (n : ℕ) : Measurable (dropThetaPrefix n) := by
  unfold dropThetaPrefix
  refine measurable_pi_lambda _ ?_
  intro i
  have hi : i.1 + 1 ≤ n := Nat.succ_le_of_lt i.2
  simpa using
    (measurable_pi_apply (a := (⟨i.1 + 1, Finset.mem_Iic.2 hi⟩ : Finset.Iic n)))

lemma seqPrefixProj_comp_dropThetaHead_eq_dropThetaPrefix_frestrictLe (n : ℕ) :
    seqPrefixProj n ∘ dropThetaHead = dropThetaPrefix n ∘ (Preorder.frestrictLe n) := by
  funext x
  funext i
  unfold seqPrefixProj dropThetaHead dropThetaPrefix
  simp [Preorder.frestrictLe]

lemma thetaIidAugmentedKernel_apply (θ : LatentTheta) :
    thetaIidAugmentedKernel θ = thetaIidTrajPrefix0 (thetaToPrefix0 θ) := by
  ext s hs
  rw [thetaIidAugmentedKernel, ProbabilityTheory.Kernel.comp_apply' _ _ _ hs,
    ProbabilityTheory.Kernel.deterministic_apply]
  simpa using (lintegral_dirac'
    (a := thetaToPrefix0 θ)
    (f := fun p : ThetaBoolPrefix 0 => thetaIidTrajPrefix0 p s)
    (thetaIidTrajPrefix0.measurable_coe hs))

/-- Strong horizon-`n` prefix law reduction for `iidSequenceKernelTheta`:
the pushed-forward prefix law equals the corresponding `partialTraj` law with the
latent head removed. -/
theorem iidSequenceKernelTheta_map_seqPrefixProj
    (θ : LatentTheta) (n : ℕ) :
    (iidSequenceKernelTheta θ).map (seqPrefixProj n) =
      ((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
        (dropThetaPrefix n) := by
  have hmapKernel :
      iidSequenceKernelTheta.map (seqPrefixProj n) =
        thetaIidAugmentedKernel.map (seqPrefixProj n ∘ dropThetaHead) := by
    simpa [iidSequenceKernelTheta] using
      (ProbabilityTheory.Kernel.map_comp_right thetaIidAugmentedKernel measurable_dropThetaHead
        (measurable_seqPrefixProj n)).symm
  have hmapθ :
      (iidSequenceKernelTheta.map (seqPrefixProj n)) θ =
        (thetaIidAugmentedKernel.map (seqPrefixProj n ∘ dropThetaHead)) θ := by
    simpa using
      congrArg (fun κ : ProbabilityTheory.Kernel LatentTheta (Fin n → Bool) => κ θ) hmapKernel
  have hmapθ' :
      Measure.map (seqPrefixProj n) (iidSequenceKernelTheta θ) =
        Measure.map (seqPrefixProj n ∘ dropThetaHead) (thetaIidAugmentedKernel θ) := by
    calc
      Measure.map (seqPrefixProj n) (iidSequenceKernelTheta θ)
          = (iidSequenceKernelTheta.map (seqPrefixProj n)) θ := by
              symm
              exact ProbabilityTheory.Kernel.map_apply _ (measurable_seqPrefixProj n) θ
      _ = (thetaIidAugmentedKernel.map (seqPrefixProj n ∘ dropThetaHead)) θ := hmapθ
      _ = Measure.map (seqPrefixProj n ∘ dropThetaHead) (thetaIidAugmentedKernel θ) := by
            exact ProbabilityTheory.Kernel.map_apply _
              ((measurable_seqPrefixProj n).comp measurable_dropThetaHead) θ
  have hcompose :
      seqPrefixProj n ∘ dropThetaHead = dropThetaPrefix n ∘ (Preorder.frestrictLe n) :=
    seqPrefixProj_comp_dropThetaHead_eq_dropThetaPrefix_frestrictLe n
  calc
    (iidSequenceKernelTheta θ).map (seqPrefixProj n)
        = Measure.map (seqPrefixProj n) (iidSequenceKernelTheta θ) := by
            simp
    _ = Measure.map (seqPrefixProj n ∘ dropThetaHead) (thetaIidAugmentedKernel θ) := hmapθ'
    _ = Measure.map (dropThetaPrefix n ∘ (Preorder.frestrictLe n)) (thetaIidAugmentedKernel θ) := by
            simp [hcompose]
    _ = (Measure.map (dropThetaPrefix n)
          (Measure.map (Preorder.frestrictLe n) (thetaIidAugmentedKernel θ))) := by
            rw [MeasureTheory.Measure.map_map
              (μ := thetaIidAugmentedKernel θ)
              (g := dropThetaPrefix n)
              (f := Preorder.frestrictLe n)
              (hg := measurable_dropThetaPrefix n)
              (hf := by fun_prop)]
    _ = ((thetaIidTrajPrefix0 (thetaToPrefix0 θ)).map (Preorder.frestrictLe n)).map
          (dropThetaPrefix n) := by
            simp [thetaIidAugmentedKernel_apply]
    _ = ((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
          (dropThetaPrefix n) := by
            simpa using congrArg (fun μ => μ.map (dropThetaPrefix n))
              (ProbabilityTheory.Kernel.traj_map_frestrictLe_apply
                (κ := thetaIidStep) (a := 0) (b := n) (x := thetaToPrefix0 θ))

/-- Horizon-`n` singleton-cylinder evaluation in terms of the strong trajectory
construction of `iidSequenceKernelTheta`. -/
theorem iidSequenceKernelTheta_seqPrefixEvent_eq_partialTraj
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
        (dropThetaPrefix n)) ({xs} : Set (Fin n → Bool)) := by
  have hmap := iidSequenceKernelTheta_map_seqPrefixProj θ n
  have hs : MeasurableSet ({xs} : Set (Fin n → Bool)) := MeasurableSet.singleton xs
  have hset :
      seqPrefixEvent n xs = (seqPrefixProj n) ⁻¹' ({xs} : Set (Fin n → Bool)) := by
    ext ω
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      exact congrArg (fun f : Fin n → Bool => f i) h
  calc
    iidSequenceKernelTheta θ (seqPrefixEvent n xs)
        = iidSequenceKernelTheta θ ((seqPrefixProj n) ⁻¹' ({xs} : Set (Fin n → Bool))) := by
            simp [hset]
    _ = ((iidSequenceKernelTheta.map (seqPrefixProj n)) θ) ({xs} : Set (Fin n → Bool)) := by
          exact (ProbabilityTheory.Kernel.map_apply'
            (κ := iidSequenceKernelTheta) (hf := measurable_seqPrefixProj n)
            (a := θ) (hs := hs)).symm
    _ = (Measure.map (seqPrefixProj n) (iidSequenceKernelTheta θ)) ({xs} : Set (Fin n → Bool)) := by
          simpa using congrArg (fun μ : Measure (Fin n → Bool) => μ ({xs} : Set (Fin n → Bool)))
            (ProbabilityTheory.Kernel.map_apply (κ := iidSequenceKernelTheta)
              (hf := measurable_seqPrefixProj n) (a := θ))
    _ = (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
          (dropThetaPrefix n)) ({xs} : Set (Fin n → Bool)) := by
          simp [hmap]

/-- Singleton mass for the `Theta`-parameterized Bernoulli kernel. -/
theorem thetaBernoulliKernel_singleton_apply
    (θ : LatentTheta) (b : Bool) :
    thetaBernoulliKernel θ ({b} : Set Bool) =
      ENNReal.ofReal (Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) b) := by
  have hs : MeasurableSet ({b} : Set Bool) := MeasurableSet.singleton b
  rw [thetaBernoulliKernel,
    ProbabilityTheory.Kernel.map_apply'
      (κ := Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel (n := 1))
      (hf := measurable_fin1TupleToBool) (a := θ) (hs := hs)]
  have hpre : fin1TupleToBool ⁻¹' ({b} : Set Bool) = ({(fun _ : Fin 1 => b)} : Set (Fin 1 → Bool)) := by
    ext x
    constructor
    · intro hx
      ext i
      have hi : i = 0 := Fin.eq_zero i
      simpa [hi] using hx
    · intro hx
      simpa [fin1TupleToBool] using congrArg (fun f : Fin 1 → Bool => f 0) hx
  rw [hpre]
  simp [Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel,
    Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight,
    Mettapedia.Logic.DeFinetti.bernoulliProductPMF, Mettapedia.Logic.DeFinetti.bernoulliPMF]

/-- Singleton mass comparison: the finite product measure generated by
`thetaBernoulliKernel θ` matches the `iidPrefixKernel` singleton law. -/
theorem iidPrefixKernel_singleton_eq_pi_thetaBernoulli
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    (Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ)) ({xs} : Set (Fin n → Bool)) =
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
  have hnonneg : ∀ i : Fin n, 0 ≤ Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (xs i) := by
    intro i
    cases xs i <;> simp [Mettapedia.Logic.DeFinetti.bernoulliPMF, sub_nonneg.2 θ.2.2, θ.2.1]
  calc
    (Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ)) ({xs} : Set (Fin n → Bool))
        = ∏ i : Fin n, thetaBernoulliKernel θ ({xs i} : Set Bool) := by
            simp
    _ = ∏ i : Fin n, ENNReal.ofReal (Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (xs i)) := by
          simp [thetaBernoulliKernel_singleton_apply]
    _ = ENNReal.ofReal (∏ i : Fin n, Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (xs i)) := by
          symm
          exact ENNReal.ofReal_prod_of_nonneg (fun i _ => hnonneg i)
    _ = ENNReal.ofReal (Mettapedia.Logic.DeFinetti.bernoulliProductPMF (θ : ℝ) xs) := by
          simp [Mettapedia.Logic.DeFinetti.bernoulliProductPMF]
    _ = (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
          simp [iidPrefixKernel,
            Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel,
            Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight]

/-- Full finite-prefix law equality: `iidPrefixKernel` is exactly the finite product
measure generated by `thetaBernoulliKernel`. -/
theorem iidPrefixKernel_eq_pi_thetaBernoulli
    (θ : LatentTheta) (n : ℕ) :
    iidPrefixKernel n θ = Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ) := by
  apply Measure.ext_of_singleton
  intro xs
  exact (iidPrefixKernel_singleton_eq_pi_thetaBernoulli θ n xs).symm

/-- Path-B reduction lemma:
to identify `iidSequenceKernelTheta` with `iidProduct`, it suffices to show that
all finite-prefix marginals are the expected finite products. -/
theorem iidSequenceKernelTheta_eq_iidProduct_of_prefix_pi_marginals
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ),
        (iidSequenceKernelTheta θ).map (seqPrefixProj n) =
          Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ)) :
    ∀ θ : LatentTheta,
      iidSequenceKernelTheta θ =
        Exchangeability.Probability.iidProduct (thetaBernoulliKernel θ) := by
  intro θ
  let μ : ℕ → Measure Bool := fun _ => thetaBernoulliKernel θ
  have hμprob : ∀ i : ℕ, IsProbabilityMeasure (μ i) := by
    intro i
    simpa [μ] using (inferInstance : IsProbabilityMeasure (thetaBernoulliKernel θ))
  letI : ∀ i : ℕ, IsProbabilityMeasure (μ i) := hμprob
  change iidSequenceKernelTheta θ = Measure.infinitePi μ
  refine Measure.eq_infinitePi (μ := μ) ?_
  intro s t ht
  let n : ℕ := s.sup id + 1
  let u : Fin n → Set Bool := fun i => if i.1 ∈ s then t i.1 else Set.univ
  have hs_lt : ∀ i ∈ s, i < n := by
    intro i hi
    exact lt_of_le_of_lt (by simpa using (Finset.le_sup (f := id) hi)) (Nat.lt_succ_self _)
  have hs_sub : s ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.2 (hs_lt i hi)
  have hpre :
      Set.pi s t = (seqPrefixProj n) ⁻¹' (Set.univ.pi u) := by
    ext ω
    constructor
    · intro h j hj
      by_cases hjs : (j : ℕ) ∈ s
      · have hω : ω j ∈ t j := h j hjs
        simpa [seqPrefixProj, u, hjs] using hω
      · simp [seqPrefixProj, u, hjs]
    · intro h i hi
      have hin : i < n := hs_lt i hi
      have hω : (seqPrefixProj n ω) ⟨i, hin⟩ ∈ u ⟨i, hin⟩ := h ⟨i, hin⟩ (by simp)
      have hiFin : (((⟨i, hin⟩ : Fin n) : ℕ) ∈ s) := hi
      simpa [seqPrefixProj, u, hiFin] using hω
  have hu_meas : ∀ i : Fin n, MeasurableSet (u i) := by
    intro i
    by_cases hi : i.1 ∈ s
    · simp [u, hi]
    · simp [u, hi]
  let fNat : ℕ → ENNReal :=
    fun i => if h : i < n then thetaBernoulliKernel θ (u ⟨i, h⟩) else 1
  have hprod_range :
      (∏ i : Fin n, thetaBernoulliKernel θ (u i))
        = Finset.prod (Finset.range n)
            (fun i => if i ∈ s then thetaBernoulliKernel θ (t i) else 1) := by
    calc
      (∏ i : Fin n, thetaBernoulliKernel θ (u i))
          = Finset.prod (Finset.range n) fNat := by
              simpa [fNat] using (Fin.prod_univ_eq_prod_range (n := n) (f := fNat))
      _ = Finset.prod (Finset.range n)
            (fun i => if i ∈ s then thetaBernoulliKernel θ (t i) else 1) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            have hin : i < n := Finset.mem_range.1 hi
            by_cases his : i ∈ s
            · simp [fNat, u, hin, his]
            · simpa [fNat, u, hin, his] using
                (measure_univ : thetaBernoulliKernel θ Set.univ = 1)
  have hprod_inter :
      Finset.prod (Finset.range n)
          (fun i => if i ∈ s then thetaBernoulliKernel θ (t i) else 1)
        = Finset.prod (Finset.range n ∩ s) (fun i => thetaBernoulliKernel θ (t i)) := by
    exact
      (Finset.prod_ite_mem (s := Finset.range n) (t := s)
        (f := fun i => thetaBernoulliKernel θ (t i)))
  calc
    iidSequenceKernelTheta θ (Set.pi s t)
        = iidSequenceKernelTheta θ ((seqPrefixProj n) ⁻¹' (Set.univ.pi u)) := by
            simp [hpre]
    _ = ((iidSequenceKernelTheta θ).map (seqPrefixProj n)) (Set.univ.pi u) := by
          rw [Measure.map_apply (measurable_seqPrefixProj n) (MeasurableSet.univ_pi hu_meas)]
    _ = (Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ)) (Set.univ.pi u) := by
          simpa using
            congrArg (fun μ : Measure (Fin n → Bool) => μ (Set.univ.pi u)) (hprefix θ n)
    _ = ∏ i : Fin n, thetaBernoulliKernel θ (u i) := by
          rw [Measure.pi_pi]
    _ = Finset.prod (Finset.range n)
          (fun i => if i ∈ s then thetaBernoulliKernel θ (t i) else 1) := hprod_range
    _ = Finset.prod (Finset.range n ∩ s) (fun i => thetaBernoulliKernel θ (t i)) := hprod_inter
    _ = Finset.prod s (fun i => thetaBernoulliKernel θ (t i)) := by
          rw [Finset.inter_eq_right.2 hs_sub]
    _ = Finset.prod s (fun i => μ i (t i)) := by
          simp [μ]

/-- Prefix-event law for the external IID product measure with Bernoulli base
`thetaBernoulliKernel θ`: it matches `iidPrefixKernel` on singleton prefixes. -/
theorem iidProduct_thetaBernoulli_seqPrefixEvent_eq_iidPrefixKernel
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    Exchangeability.Probability.iidProduct (thetaBernoulliKernel θ) (seqPrefixEvent n xs) =
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
  have hs : MeasurableSet ({xs} : Set (Fin n → Bool)) := MeasurableSet.singleton xs
  have hset :
      seqPrefixEvent n xs = (seqPrefixProj n) ⁻¹' ({xs} : Set (Fin n → Bool)) := by
    ext ω
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      exact congrArg (fun f : Fin n → Bool => f i) h
  have hmap :
      (Exchangeability.Probability.iidProduct (thetaBernoulliKernel θ)).map
          (seqPrefixProj n)
        = Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ) := by
    simpa [seqPrefixProj] using
      (Exchangeability.Probability.iidProduct.cylinder_fintype
        (ν := thetaBernoulliKernel θ) (n := n))
  calc
    Exchangeability.Probability.iidProduct (thetaBernoulliKernel θ) (seqPrefixEvent n xs)
        = Exchangeability.Probability.iidProduct (thetaBernoulliKernel θ)
            ((seqPrefixProj n) ⁻¹' ({xs} : Set (Fin n → Bool))) := by
              simp [hset]
    _ = ((Exchangeability.Probability.iidProduct (thetaBernoulliKernel θ)).map
          (seqPrefixProj n)) ({xs} : Set (Fin n → Bool)) := by
          exact (Measure.map_apply (measurable_seqPrefixProj n) hs).symm
    _ = (Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ)) ({xs} : Set (Fin n → Bool)) := by
          simpa using congrArg (fun μ : Measure (Fin n → Bool) => μ ({xs} : Set (Fin n → Bool))) hmap
    _ = (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
          exact iidPrefixKernel_singleton_eq_pi_thetaBernoulli θ n xs

/-- Path-B bridge: under pointwise identification with `iidProduct`, horizon-`n`
prefix singleton probabilities of `iidSequenceKernelTheta` match `iidPrefixKernel`
exactly (no latent-mediator hypothesis needed). -/
theorem iidSequenceKernelTheta_prefix_apply_of_iidProduct_bridge
    (hbridge :
      ∀ θ : LatentTheta,
        iidSequenceKernelTheta θ =
          Exchangeability.Probability.iidProduct (thetaBernoulliKernel θ))
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
  rw [hbridge θ]
  exact iidProduct_thetaBernoulli_seqPrefixEvent_eq_iidPrefixKernel θ n xs

def firstCoord (ω : GlobalBinarySeq) : Bool := ω 0

lemma measurable_firstCoord : Measurable firstCoord := by
  simpa [firstCoord] using (measurable_pi_apply (a := (0 : ℕ)))

lemma thetaFromPrefix_thetaToPrefix0 (θ : LatentTheta) :
    thetaFromPrefix (thetaToPrefix0 θ) = θ := by
  change thetaToPrefix0 θ (thetaPrefixZeroIdx 0) = θ
  unfold thetaToPrefix0 thetaPrefixZeroIdx
  simp [ThetaBoolTimeline]

/-- Cylinder-evaluation bridge at horizon `1`: pushing `iidSequenceKernelTheta`
through the first coordinate recovers the one-step Bernoulli kernel. -/
theorem iidSequenceKernelTheta_map_firstCoord :
    iidSequenceKernelTheta.map firstCoord = thetaBernoulliKernel := by
  rw [iidSequenceKernelTheta, ← ProbabilityTheory.Kernel.map_comp_right _ measurable_dropThetaHead
    measurable_firstCoord]
  change thetaIidAugmentedKernel.map (fun x => x (0 + 1)) = thetaBernoulliKernel
  rw [thetaIidAugmentedKernel, ProbabilityTheory.Kernel.map_comp]
  have htraj :
      thetaIidTrajPrefix0.map (fun x => x (0 + 1)) = thetaIidStep 0 := by
    simpa [thetaIidTrajPrefix0] using
      (ProbabilityTheory.Kernel.map_traj_succ_self (κ := thetaIidStep) (a := 0))
  rw [htraj]
  ext θ s hs
  rw [ProbabilityTheory.Kernel.comp_apply' _ _ _ hs, ProbabilityTheory.Kernel.deterministic_apply]
  simpa [thetaIidStep, thetaFromPrefix_thetaToPrefix0, hs, ThetaBoolTimeline] using
    (lintegral_dirac'
      (a := thetaToPrefix0 θ)
      (f := fun b : ThetaBoolPrefix 0 => (thetaIidStep 0 b) s)
      ((thetaIidStep 0).measurable_coe hs))

/-- First-coordinate cylinder evaluation for measurable sets. -/
theorem iidSequenceKernelTheta_firstCoord_apply
    (θ : LatentTheta) (s : Set Bool) (hs : MeasurableSet s) :
    iidSequenceKernelTheta θ {ω | firstCoord ω ∈ s} = thetaBernoulliKernel θ s := by
  have hmap := congrArg (fun κ => κ θ s) iidSequenceKernelTheta_map_firstCoord
  simpa [firstCoord, ProbabilityTheory.Kernel.map_apply' _ measurable_firstCoord _ hs] using hmap

/-- First-coordinate singleton-cylinder evaluation. -/
theorem iidSequenceKernelTheta_firstCoord_singleton
    (θ : LatentTheta) (b : Bool) :
    iidSequenceKernelTheta θ {ω | ω 0 = b} = thetaBernoulliKernel θ ({b} : Set Bool) := by
  simpa [firstCoord] using
    iidSequenceKernelTheta_firstCoord_apply θ ({b} : Set Bool) (by simp)

/-- Horizon-`n` cylinder evaluation for `iidSequenceKernelTheta`, assuming the
canonical latent-`Theta` mediator is the Dirac family. -/
theorem iidSequenceKernelTheta_prefix_apply_of_latentDirac
    (hrep :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
  have hfac :=
    kernelRepresentsLatentTheta_coord_prefix_eq_iidPrefixKernel
      (κ := iidSequenceKernelTheta)
      (L := fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta))
      hrep θ n xs
  have hdirac :
      (∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool))
          ∂(Measure.dirac θ : Measure LatentTheta)) =
        (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
    simp [lintegral_dirac'
      (a := θ)
      (f := fun θ' : LatentTheta => (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)))
      ((iidPrefixKernel n).measurable_coe (s := ({xs} : Set (Fin n → Bool)))
        (MeasurableSet.singleton xs))]
  exact hfac.trans hdirac

/-- Under a Dirac latent-representation witness, the finite-prefix marginal of
`iidSequenceKernelTheta` is exactly `iidPrefixKernel`. -/
theorem iidSequenceKernelTheta_map_seqPrefixProj_eq_iidPrefixKernel_of_latentDirac
    (hrep :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (θ : LatentTheta) (n : ℕ) :
    (iidSequenceKernelTheta θ).map (seqPrefixProj n) = iidPrefixKernel n θ := by
  apply Measure.ext_of_singleton
  intro xs
  have hs : MeasurableSet ({xs} : Set (Fin n → Bool)) := MeasurableSet.singleton xs
  have hset :
      seqPrefixEvent n xs = (seqPrefixProj n) ⁻¹' ({xs} : Set (Fin n → Bool)) := by
    ext ω
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      exact congrArg (fun f : Fin n → Bool => f i) h
  calc
    ((iidSequenceKernelTheta θ).map (seqPrefixProj n)) ({xs} : Set (Fin n → Bool))
        = iidSequenceKernelTheta θ ((seqPrefixProj n) ⁻¹' ({xs} : Set (Fin n → Bool))) := by
            exact Measure.map_apply (measurable_seqPrefixProj n) hs
    _ = iidSequenceKernelTheta θ (seqPrefixEvent n xs) := by
          simp [hset]
    _ = iidPrefixKernel n θ ({xs} : Set (Fin n → Bool)) :=
          iidSequenceKernelTheta_prefix_apply_of_latentDirac hrep θ n xs

/-- Under a Dirac latent-representation witness, all finite-prefix marginals of
`iidSequenceKernelTheta` are Bernoulli product measures. -/
theorem iidSequenceKernelTheta_prefix_pi_marginals_of_latentDirac
    (hrep :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (θ : LatentTheta) (n : ℕ) :
    (iidSequenceKernelTheta θ).map (seqPrefixProj n) =
      Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ) := by
  calc
    (iidSequenceKernelTheta θ).map (seqPrefixProj n) = iidPrefixKernel n θ :=
      iidSequenceKernelTheta_map_seqPrefixProj_eq_iidPrefixKernel_of_latentDirac hrep θ n
    _ = Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ) :=
      iidPrefixKernel_eq_pi_thetaBernoulli θ n

/-- Path-B bridge from the strong construction:
if the Dirac latent-representation witness is available, then
`iidSequenceKernelTheta` is pointwise equal to external `iidProduct`. -/
theorem iidSequenceKernelTheta_eq_iidProduct_of_latentDirac
    (hrep :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta))) :
    ∀ θ : LatentTheta,
      iidSequenceKernelTheta θ =
        Exchangeability.Probability.iidProduct (thetaBernoulliKernel θ) :=
  iidSequenceKernelTheta_eq_iidProduct_of_prefix_pi_marginals
    (fun θ n => iidSequenceKernelTheta_prefix_pi_marginals_of_latentDirac hrep θ n)

/-- A Dirac latent representation witness yields coordinate-prefix cone laws for
`iidSequenceKernelTheta`. -/
theorem iidSequenceKernelTheta_kernelPrefixCone_coord_of_latentDirac
    (hrep :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta))) :
    KernelPrefixCone (X := coordProcess) (κ := iidSequenceKernelTheta) := by
  have hseq : KernelSequencePrefixCone (κ := iidSequenceKernelTheta) := by
    intro θ n σ xs
    calc
      iidSequenceKernelTheta θ (seqPrefixEvent n xs)
          = (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) :=
            iidSequenceKernelTheta_prefix_apply_of_latentDirac hrep θ n xs
      _ = (iidPrefixKernel n θ) ({xs ∘ σ.symm} : Set (Fin n → Bool)) :=
            iidPrefixKernel_perm_singleton n σ θ xs
      _ = iidSequenceKernelTheta θ (seqPrefixEvent n (permutePrefixTuple σ xs)) := by
            simpa [permutePrefixTuple] using
              (iidSequenceKernelTheta_prefix_apply_of_latentDirac hrep θ n (xs ∘ σ.symm)).symm
  exact (kernelSequencePrefixCone_iff_kernelPrefixCone_coord (κ := iidSequenceKernelTheta)).1 hseq

/-! ## Global Finitary Commutation => Coordinate Prefix Invariance -/

/-- Global finitary cone commutation on sequence laws (all `τ : FinSuppPermNat`). -/
def GlobalFinitarySeqConeCommutes (μ : Measure GlobalBinarySeq) : Prop :=
  ∀ τ : FinSuppPermNat, μ.map (finSuppPermuteSeq τ) = μ

/-- The external i.i.d. product law is globally finitary-permutation invariant. -/
theorem iidProduct_globalFinitarySeqConeCommutes
    (ν : Measure Bool) [IsProbabilityMeasure ν] :
    GlobalFinitarySeqConeCommutes (Exchangeability.Probability.iidProduct ν) := by
  intro τ
  simpa [GlobalFinitarySeqConeCommutes, finSuppPermuteSeq, Function.comp] using
    (Exchangeability.Probability.iidProduct.perm_eq (ν := ν) (σ := τ.1.symm))

/-- Path-B bridge: if the strong IID kernel is identified pointwise with the
external `iidProduct` law, then global finitary commutation follows immediately. -/
theorem iidSequenceKernelTheta_globalFinitaryInvariance_of_iidProduct_bridge
    (hbridge :
      ∀ θ : LatentTheta,
        iidSequenceKernelTheta θ =
          Exchangeability.Probability.iidProduct (thetaBernoulliKernel θ)) :
    ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ) := by
  intro θ
  rw [hbridge θ]
  exact iidProduct_globalFinitarySeqConeCommutes (thetaBernoulliKernel θ)

/-- Converse bridge (probability-law version):
coordinate-process prefix invariance implies global finitary commutation. -/
theorem coordPrefixInvariance_imp_globalFinitarySeqConeCommutes
    (μ : Measure GlobalBinarySeq) [IsProbabilityMeasure μ]
    (hprefix : IsPrefixLawCone (Ω := GlobalBinarySeq) (fun i ω => ω i) μ) :
    GlobalFinitarySeqConeCommutes μ := by
  have hcone : ExchangeablePrefixCone (fun i ω => ω i) μ :=
    (isPrefixLawCone_iff_exchangeablePrefixCone
      (Ω := GlobalBinarySeq) (X := fun i ω => ω i) (μ := μ)).1 hprefix
  have hexchLocal :
      Mettapedia.Logic.Exchangeability.InfiniteExchangeable (fun i ω => ω i) μ :=
    infiniteExchangeable_of_exchangeablePrefixCone (X := fun i ω => ω i) (μ := μ) hcone
  have hexchExt : Exchangeability.Exchangeable μ (fun i ω => ω i) := by
    intro n σ
    apply Measure.ext_of_singleton
    intro xs
    have hseg :
        Mettapedia.Logic.Exchangeability.FiniteExchangeable n
          (fun i : Fin n => fun ω : GlobalBinarySeq => ω i) μ :=
      hexchLocal.finite_segments n
    have hleft :
        (Measure.map (fun ω : GlobalBinarySeq => fun i : Fin n => ω (σ i)) μ)
          ({xs} : Set (Fin n → Bool)) =
        μ {ω : GlobalBinarySeq | ∀ i : Fin n, ω (σ i) = xs i} := by
      have hmeas :
          Measurable (fun ω : GlobalBinarySeq => fun i : Fin n => ω (σ i)) :=
        measurable_pi_lambda _ (fun i => measurable_pi_apply (a := (σ i).1))
      have hpre :
          (fun ω : GlobalBinarySeq => fun i : Fin n => ω (σ i)) ⁻¹'
              ({xs} : Set (Fin n → Bool)) =
            {ω : GlobalBinarySeq | ∀ i : Fin n, ω (σ i) = xs i} := by
        ext ω
        constructor
        · intro h i
          exact congrArg (fun f : Fin n → Bool => f i) h
        · intro h
          funext i
          exact h i
      rw [Measure.map_apply hmeas (MeasurableSet.singleton xs)]
      simp [hpre]
    have hright :
        (Measure.map (fun ω : GlobalBinarySeq => fun i : Fin n => ω i) μ)
          ({xs} : Set (Fin n → Bool)) =
        μ {ω : GlobalBinarySeq | ∀ i : Fin n, ω i = xs i} := by
      have hmeas :
          Measurable (fun ω : GlobalBinarySeq => fun i : Fin n => ω i) :=
        measurable_pi_lambda _ (fun i => measurable_pi_apply (a := i.1))
      have hpre :
          (fun ω : GlobalBinarySeq => fun i : Fin n => ω i) ⁻¹'
              ({xs} : Set (Fin n → Bool)) =
            {ω : GlobalBinarySeq | ∀ i : Fin n, ω i = xs i} := by
        ext ω
        constructor
        · intro h i
          exact congrArg (fun f : Fin n → Bool => f i) h
        · intro h
          funext i
          exact h i
      rw [Measure.map_apply hmeas (MeasurableSet.singleton xs)]
      simp [hpre]
    calc
      (Measure.map (fun ω : GlobalBinarySeq => fun i : Fin n => ω (σ i)) μ)
          ({xs} : Set (Fin n → Bool))
          = μ {ω : GlobalBinarySeq | ∀ i : Fin n, ω (σ i) = xs i} := hleft
      _ = μ {ω : GlobalBinarySeq | ∀ i : Fin n, ω i = xs i} := by
            simpa using (hseg.perm_invariant σ xs).symm
      _ = (Measure.map (fun ω : GlobalBinarySeq => fun i : Fin n => ω i) μ)
            ({xs} : Set (Fin n → Bool)) := hright.symm
  have hcoordMeas : ∀ i : ℕ, Measurable (fun ω : GlobalBinarySeq => ω i) := by
    intro i
    simpa using (measurable_pi_apply (a := i))
  have hfull : Exchangeability.FullyExchangeable μ (fun i ω => ω i) :=
    (Exchangeability.exchangeable_iff_fullyExchangeable
      (μ := μ) (X := fun i ω => ω i) hcoordMeas).1 hexchExt
  intro τ
  have hτ := hfull (τ.1.symm)
  have hid :
      Measure.map (fun ω : GlobalBinarySeq => fun i : ℕ => ω i) μ = μ := by
    simp
  calc
    μ.map (finSuppPermuteSeq τ)
        = Measure.map (fun ω : GlobalBinarySeq => fun i : ℕ => ω ((τ.1).symm i)) μ := by
            rfl
    _ = Measure.map (fun ω : GlobalBinarySeq => fun i : ℕ => ω i) μ := by
          simpa [Function.comp] using hτ
    _ = μ := hid

lemma measurableSet_globalSeqPrefixEvent (n : ℕ) (xs : Fin n → Bool) :
    MeasurableSet (globalSeqPrefixEvent n xs) := by
  classical
  have hrepr :
      globalSeqPrefixEvent n xs =
        ⋂ i : Fin n, (fun ω : GlobalBinarySeq => ω i.1) ⁻¹' ({xs i} : Set Bool) := by
    ext ω
    simp [globalSeqPrefixEvent]
  have hmeas : ∀ i : Fin n, MeasurableSet ((fun ω : GlobalBinarySeq => ω i.1) ⁻¹' ({xs i} : Set Bool)) := by
    intro i
    exact measurableSet_preimage (measurable_pi_apply (a := i.1)) (measurableSet_singleton (xs i))
  simpa [hrepr] using MeasurableSet.iInter hmeas

/-- Bridge lemma: global commutation under all finitary permutations implies
coordinate-process prefix invariance. -/
theorem globalFinitarySeqConeCommutes_imp_coordPrefixInvariance
    (μ : Measure GlobalBinarySeq)
    (hτ : GlobalFinitarySeqConeCommutes μ) :
    IsPrefixLawCone (Ω := GlobalBinarySeq) (fun i ω => ω i) μ := by
  have hglobal :
      GlobalLiftedPrefixLawConeCommutes (Ω := GlobalBinarySeq) (fun i ω => ω i) μ := by
    intro n σ
    let L : GlobalBinarySeqLawObj := fun A => μ A
    have haction :
        globalPrefixLawActionFromSeqLaw (finPermToFinSuppPermNat σ) L n =
          prefixLawObjOfSeqLaw L n := by
      funext xs
      unfold globalPrefixLawActionFromSeqLaw prefixLawObjOfSeqLaw finSuppPermActionOnSeqLaw
      have hmeas : MeasurableSet (globalSeqPrefixEvent n xs) :=
        measurableSet_globalSeqPrefixEvent n xs
      have hmap :
          (μ.map (finSuppPermuteSeq (finPermToFinSuppPermNat σ)))
            (globalSeqPrefixEvent n xs) =
          μ (globalSeqPrefixEvent n xs) := by
        exact congrArg (fun m => m (globalSeqPrefixEvent n xs)) (hτ (finPermToFinSuppPermNat σ))
      simpa [Measure.map_apply (measurable_finSuppPermuteSeq (finPermToFinSuppPermNat σ)) hmeas]
        using hmap
    have hcompat :=
      globalPrefixLawActionFromSeqLaw_compatible_with_lift (L := L) n σ
    have hperm :
        perNPrefixDiagramMap n σ (prefixLawObjOfSeqLaw L n) = prefixLawObjOfSeqLaw L n := by
      calc
        perNPrefixDiagramMap n σ (prefixLawObjOfSeqLaw L n)
            = globalPrefixLawActionFromSeqLaw (finPermToFinSuppPermNat σ) L n := by
                symm
                exact hcompat
        _ = prefixLawObjOfSeqLaw L n := haction
    simpa [GlobalLiftedPrefixLawConeCommutes, perNPrefixDiagramMapFromGlobalLift,
      prefixLawObjOfSeqLaw, prefixLaw, globalSeqPrefixEvent, L] using hperm
  exact
    (isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes
      (Ω := GlobalBinarySeq) (X := fun i ω => ω i) (μ := μ)).2 hglobal

/-- Kernel-level corollary of the bridge lemma. -/
def KernelGlobalFinitarySeqConeCommutes
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop :=
  ∀ y : Y, GlobalFinitarySeqConeCommutes (κ y)

theorem kernelGlobalFinitarySeqConeCommutes_imp_kernelPrefixCone_coord
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hτ : KernelGlobalFinitarySeqConeCommutes (Y := Y) κ) :
    KernelPrefixCone (X := (fun i ω => ω i)) κ := by
  intro y
  have hprefix :
      IsPrefixLawCone (Ω := GlobalBinarySeq) (fun i ω => ω i) (κ y) :=
    globalFinitarySeqConeCommutes_imp_coordPrefixInvariance (μ := κ y) (hτ y)
  exact
    (isPrefixLawCone_iff_exchangeablePrefixCone
      (Ω := GlobalBinarySeq) (X := fun i ω => ω i) (μ := κ y)).1 hprefix

/-- Converse bridge (kernel version):
coordinate-process prefix-cone laws imply global finitary commutation fiberwise. -/
theorem kernelPrefixCone_coord_imp_kernelGlobalFinitarySeqConeCommutes
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hprefix : KernelPrefixCone (X := (fun i ω => ω i)) κ) :
    KernelGlobalFinitarySeqConeCommutes (Y := Y) κ := by
  intro y
  haveI : IsProbabilityMeasure (κ y) := by infer_instance
  have hpre :
      IsPrefixLawCone (Ω := GlobalBinarySeq) (fun i ω => ω i) (κ y) :=
    (isPrefixLawCone_iff_exchangeablePrefixCone
      (Ω := GlobalBinarySeq) (X := fun i ω => ω i) (μ := κ y)).2 (hprefix y)
  exact coordPrefixInvariance_imp_globalFinitarySeqConeCommutes (μ := κ y) hpre

/-- Fiberwise equivalence between global finitary commutation and
coordinate-process prefix-cone laws. -/
theorem kernelGlobalFinitarySeqConeCommutes_iff_kernelPrefixCone_coord
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    KernelGlobalFinitarySeqConeCommutes (Y := Y) κ ↔
      KernelPrefixCone (X := (fun i ω => ω i)) κ := by
  constructor
  · exact kernelGlobalFinitarySeqConeCommutes_imp_kernelPrefixCone_coord (κ := κ)
  · exact kernelPrefixCone_coord_imp_kernelGlobalFinitarySeqConeCommutes (κ := κ)

/-- A Dirac latent representation witness yields global finitary commutation for
all fibers of `iidSequenceKernelTheta`. -/
theorem iidSequenceKernelTheta_globalFinitaryInvariance_of_latentDirac
    (hrep :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta))) :
    ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ) := by
  have hprefix :
      KernelPrefixCone (X := coordProcess) (κ := iidSequenceKernelTheta) :=
    iidSequenceKernelTheta_kernelPrefixCone_coord_of_latentDirac hrep
  exact kernelPrefixCone_coord_imp_kernelGlobalFinitarySeqConeCommutes
    (κ := iidSequenceKernelTheta) hprefix

/-- Canonical `Kleisli(Giry)` object for the latent parameter space. -/
abbrev KleisliLatentThetaObj : KleisliGiry :=
  (MeasCat.of LatentTheta : CategoryTheory.Kleisli (C := MeasCat) MeasCat.Giry)

/-- `iidSequenceKernelTheta` viewed as a Kleisli morphism. -/
def iidSequenceKleisliHomTheta : KleisliLatentThetaObj ⟶ KleisliBinarySeqObj :=
  ⟨fun θ => iidSequenceKernelTheta θ, iidSequenceKernelTheta.measurable⟩

/-- Commutation of `iidSequenceKleisliHomTheta` with the global finitary
permutation action, derived from pointwise global finitary invariance of the
sequence laws. -/
theorem iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta := by
  intro τ
  apply Subtype.ext
  funext θ
  change
    Measure.bind (iidSequenceKernelTheta θ) (fun x => Measure.dirac (finSuppPermuteSeq τ x)) =
      iidSequenceKernelTheta θ
  calc
    Measure.bind (iidSequenceKernelTheta θ) (fun x => Measure.dirac (finSuppPermuteSeq τ x))
        = (iidSequenceKernelTheta θ).map (finSuppPermuteSeq τ) := by
            simpa using
              (Measure.bind_dirac_eq_map
                (m := iidSequenceKernelTheta θ)
                (hf := measurable_finSuppPermuteSeq τ))
    _ = iidSequenceKernelTheta θ := hglobal θ τ

/-- Path-B bridge: pointwise identification with `iidProduct` yields commutation
of `iidSequenceKleisliHomTheta` with all global finitary permutation arrows. -/
theorem iidSequenceKleisliHomTheta_commutes_of_iidProduct_bridge
    (hbridge :
      ∀ θ : LatentTheta,
        iidSequenceKernelTheta θ =
          Exchangeability.Probability.iidProduct (thetaBernoulliKernel θ)) :
    ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta := by
  exact iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance
    (iidSequenceKernelTheta_globalFinitaryInvariance_of_iidProduct_bridge hbridge)

/-- Reverse bridge: if `iidSequenceKleisliHomTheta` commutes with all global
finitary permutation arrows in Kleisli(Giry), then each fiber law of
`iidSequenceKernelTheta` is globally finitary-invariant. -/
theorem iidSequenceKernelTheta_globalFinitaryInvariance_of_iidSequenceKleisliHomTheta_commutes
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta) :
    ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ) := by
  intro θ τ
  have hbind :
      Measure.bind (iidSequenceKernelTheta θ) (fun x => Measure.dirac (finSuppPermuteSeq τ x)) =
        iidSequenceKernelTheta θ := by
    simpa [iidSequenceKleisliHomTheta] using
      congrArg
        (fun h :
          KleisliLatentThetaObj ⟶ KleisliBinarySeqObj => h.1 θ)
        (hcommutes τ)
  calc
    (iidSequenceKernelTheta θ).map (finSuppPermuteSeq τ)
        = Measure.bind (iidSequenceKernelTheta θ) (fun x => Measure.dirac (finSuppPermuteSeq τ x)) := by
            simpa using
              (Measure.bind_dirac_eq_map
                (m := iidSequenceKernelTheta θ)
                (hf := measurable_finSuppPermuteSeq τ)).symm
    _ = iidSequenceKernelTheta θ := hbind

/-- Global finitary invariance of `iidSequenceKernelTheta` implies a kernel-level
prefix-cone law for the coordinate process. -/
theorem iidSequenceKernelTheta_kernelPrefixCone_coord_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    KernelPrefixCone (X := coordProcess) (κ := iidSequenceKernelTheta) :=
  kernelGlobalFinitarySeqConeCommutes_imp_kernelPrefixCone_coord
    (κ := iidSequenceKernelTheta) hglobal

/-- Unconditional finite-prefix iid-factorization payload for
`iidSequenceKernelTheta`, derived from global finitary invariance and the
existing latent-mediator chain. -/
theorem exists_latentKernel_prefixFactorization_of_iidSequenceKernelTheta_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    ∃ L : LatentTheta → Measure LatentTheta,
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta) L ∧
      (∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂(L θ)) := by
  have hX : ∀ i : ℕ, Measurable (coordProcess i) := by
    intro i
    simpa [coordProcess] using (measurable_pi_apply (a := i))
  have hprefix :
      KernelPrefixCone (X := coordProcess) (κ := iidSequenceKernelTheta) :=
    iidSequenceKernelTheta_kernelPrefixCone_coord_of_globalFinitaryInvariance hglobal
  have hexch :
      KernelExchangeable (X := coordProcess) (κ := iidSequenceKernelTheta) :=
    (kernelExchangeable_iff_kernelPrefixCone
      (X := coordProcess) (κ := iidSequenceKernelTheta)).2 hprefix
  rcases existsUnique_latentThetaKernel_of_kernelExchangeable
      (X := coordProcess) (κ := iidSequenceKernelTheta) hX hexch with
    ⟨L, hL, _⟩
  refine ⟨L, hL, ?_⟩
  exact kernelRepresentsLatentTheta_coord_prefix_eq_iidPrefixKernel
    (κ := iidSequenceKernelTheta) (L := L) hL

/-- Canonical latent-kernel choice extracted from global finitary invariance of
`iidSequenceKernelTheta`. -/
noncomputable def iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    LatentTheta → Measure LatentTheta :=
  Classical.choose
    (exists_latentKernel_prefixFactorization_of_iidSequenceKernelTheta_globalFinitaryInvariance
      hglobal)

/-- Under global finitary invariance, if the Dirac family is a latent-`Theta`
representation witness for `iidSequenceKernelTheta`, then the canonical mediator
chosen by `Classical.choose` is exactly that Dirac family. -/
theorem iidSequenceKernelTheta_canonicalLatentKernel_eq_dirac_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta))) :
    iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal =
      (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)) := by
  have hprefix :
      KernelPrefixCone (X := coordProcess) (κ := iidSequenceKernelTheta) :=
    iidSequenceKernelTheta_kernelPrefixCone_coord_of_globalFinitaryInvariance hglobal
  have hexch :
      KernelExchangeable (X := coordProcess) (κ := iidSequenceKernelTheta) :=
    (kernelExchangeable_iff_kernelPrefixCone
      (X := coordProcess) (κ := iidSequenceKernelTheta)).2 hprefix
  have hX : ∀ i : ℕ, Measurable (coordProcess i) := by
    intro i
    simpa [coordProcess] using (measurable_pi_apply (a := i))
  rcases existsUnique_latentThetaKernel_of_kernelExchangeable
      (X := coordProcess) (κ := iidSequenceKernelTheta) hX hexch with
    ⟨L0, hL0, huniq⟩
  have hcanonRep :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal) :=
    (Classical.choose_spec
      (exists_latentKernel_prefixFactorization_of_iidSequenceKernelTheta_globalFinitaryInvariance
        hglobal)).1
  have hcanonEq : iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal = L0 :=
    huniq _ hcanonRep
  have hdiracEq : (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)) = L0 :=
    huniq _ hrepDirac
  exact hcanonEq.trans hdiracEq.symm

/-- Unconditional horizon-`n` prefix evaluation for `iidSequenceKernelTheta`,
derived from global finitary invariance through the existing mediator chain. -/
theorem iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
        (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal θ) := by
  exact
    (Classical.choose_spec
      (exists_latentKernel_prefixFactorization_of_iidSequenceKernelTheta_globalFinitaryInvariance
        hglobal)).2 θ n xs

/-- Prefix-law equation family obtained directly from the Kleisli commutation
hypothesis for `iidSequenceKleisliHomTheta`, via the existing mediator chain. -/
theorem iidSequenceKernelTheta_prefix_apply_of_iidSequenceKleisliHomTheta_commutes
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
        (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance
          (iidSequenceKernelTheta_globalFinitaryInvariance_of_iidSequenceKleisliHomTheta_commutes
            hcommutes) θ) := by
  exact iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance
    (iidSequenceKernelTheta_globalFinitaryInvariance_of_iidSequenceKleisliHomTheta_commutes
      hcommutes) θ n xs

/-- Direct horizon-`n` cylinder law for `iidSequenceKernelTheta` when global
finitary invariance holds and the Dirac family is the latent mediator. -/
theorem iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance_dirac
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
  have hbase :=
    iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance hglobal θ n xs
  have hcanon :
      iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal θ =
        (Measure.dirac θ : Measure LatentTheta) := by
    simpa using congrArg (fun L : LatentTheta → Measure LatentTheta => L θ)
      (iidSequenceKernelTheta_canonicalLatentKernel_eq_dirac_of_globalFinitaryInvariance
        hglobal hrepDirac)
  calc
    iidSequenceKernelTheta θ (seqPrefixEvent n xs)
        = ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
            (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal θ) :=
          hbase
    _ = ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
          (Measure.dirac θ : Measure LatentTheta) := by
            simp [hcanon]
    _ = (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
          exact
            (lintegral_dirac'
              (a := θ)
              (f := fun θ' : LatentTheta => (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)))
              ((iidPrefixKernel n).measurable_coe (s := ({xs} : Set (Fin n → Bool)))
                (MeasurableSet.singleton xs)))

/-- Cone-data wrapper over the true global Kleisli(Giry) diagram. -/
structure KleisliGiryIIDConeSkeleton where
  apexObj : KleisliGiry
  iidHom : apexObj ⟶ KleisliBinarySeqObj
  commutes : ∀ τ : FinSuppPermNat,
    CategoryTheory.CategoryStruct.comp iidHom (finSuppPermKleisliHom τ) = iidHom

/-- Build a true categorical cone from iid-cone data. -/
def KleisliGiryIIDConeSkeleton.toCone
    (cone : KleisliGiryIIDConeSkeleton) :
    CategoryTheory.Limits.Cone kleisliGiryGlobalDiagramFunctor where
  pt := cone.apexObj
  π :=
    { app := fun _ => cone.iidHom
      naturality := by
        intro j j' τ
        cases j
        cases j'
        simpa using (cone.commutes τ).symm }

/-- IID cone-data specialized to the canonical apex `P Bool`. -/
structure KleisliGiryProbBoolIIDCone where
  iidHom : KleisliProbBoolObj ⟶ KleisliBinarySeqObj
  commutes : ∀ τ : FinSuppPermNat,
    CategoryTheory.CategoryStruct.comp iidHom (finSuppPermKleisliHom τ) = iidHom

/-- Convert specialized `P Bool` iid-cone data into a true categorical cone. -/
def KleisliGiryProbBoolIIDCone.toCone
    (cone : KleisliGiryProbBoolIIDCone) :
    CategoryTheory.Limits.Cone kleisliGiryGlobalDiagramFunctor :=
  (KleisliGiryIIDConeSkeleton.toCone
    ⟨KleisliProbBoolObj, cone.iidHom, cone.commutes⟩)

/-! ## True `IsLimit` Packaging for the Global Kleisli(Giry) Diagram -/

/-- Universal mediator property for a global iid-cone skeleton:
every cone into the global permutation diagram has a unique mediating morphism
to the cone apex, witnessed on the unique index object. -/
def GlobalIIDConeMediatorUnique
    (cone : KleisliGiryIIDConeSkeleton) : Prop :=
  ∀ s : CategoryTheory.Limits.Cone kleisliGiryGlobalDiagramFunctor,
    ∃! m : s.pt ⟶ cone.apexObj,
      CategoryTheory.CategoryStruct.comp m cone.iidHom = s.π.app globalFinSuppPermStar

/-- A Kleisli morphism is Markov when all fibers are probability measures. -/
def KleisliIsMarkov
    {A B : KleisliGiry} (f : A ⟶ B) : Prop :=
  ∀ a : A.1, IsProbabilityMeasure (f.1 a)

/-- A cone over the global finitary diagram is Markov when its leg at the unique
index object is Markov. -/
def ConeIsMarkov
    (s : CategoryTheory.Limits.Cone kleisliGiryGlobalDiagramFunctor) : Prop :=
  KleisliIsMarkov (s.π.app globalFinSuppPermStar)

/-- Markov-only universal mediator property for a global iid-cone skeleton. -/
def GlobalIIDConeMediatorUnique_markovOnly
    (cone : KleisliGiryIIDConeSkeleton) : Prop :=
  ∀ s : CategoryTheory.Limits.Cone kleisliGiryGlobalDiagramFunctor,
    ConeIsMarkov s →
      ∃! m : s.pt ⟶ cone.apexObj,
        CategoryTheory.CategoryStruct.comp m cone.iidHom = s.π.app globalFinSuppPermStar

/-- Convert the universal mediator property into a true `IsLimit` witness. -/
noncomputable def KleisliGiryIIDConeSkeleton.isLimitOfMediatorUnique
    (cone : KleisliGiryIIDConeSkeleton)
    (hmed : GlobalIIDConeMediatorUnique cone) :
    CategoryTheory.Limits.IsLimit (cone.toCone) := by
  refine CategoryTheory.Limits.IsLimit.ofExistsUnique ?_
  intro s
  rcases hmed s with ⟨m, hm, huniq⟩
  refine ⟨m, ?_, ?_⟩
  · intro j
    cases j
    simpa [KleisliGiryIIDConeSkeleton.toCone] using hm
  · intro m' hm'
    apply huniq
    have hm0 := hm' globalFinSuppPermStar
    simpa [KleisliGiryIIDConeSkeleton.toCone] using hm0

/-- Any true `IsLimit` witness yields the universal mediator property. -/
theorem globalIIDConeMediatorUnique_of_isLimit
    (cone : KleisliGiryIIDConeSkeleton)
    (hlim : CategoryTheory.Limits.IsLimit (cone.toCone)) :
    GlobalIIDConeMediatorUnique cone := by
  intro s
  rcases hlim.existsUnique s with ⟨m, hm, huniq⟩
  refine ⟨m, ?_, ?_⟩
  · simpa [KleisliGiryIIDConeSkeleton.toCone] using hm globalFinSuppPermStar
  · intro m' hm'
    apply huniq
    intro j
    cases j
    simpa [KleisliGiryIIDConeSkeleton.toCone] using hm'

/-- Any global mediator-uniqueness witness restricts to the Markov-only form. -/
theorem globalIIDConeMediatorUnique_markovOnly_of_globalIIDConeMediatorUnique
    (cone : KleisliGiryIIDConeSkeleton)
    (hmed : GlobalIIDConeMediatorUnique cone) :
    GlobalIIDConeMediatorUnique_markovOnly cone := by
  intro s _hsMarkov
  exact hmed s

/-- Any true `IsLimit` witness yields Markov-only mediator uniqueness. -/
theorem isLimit_implies_globalIIDConeMediatorUnique_markovOnly
    (cone : KleisliGiryIIDConeSkeleton)
    (hlim : CategoryTheory.Limits.IsLimit (cone.toCone)) :
    GlobalIIDConeMediatorUnique_markovOnly cone :=
  globalIIDConeMediatorUnique_markovOnly_of_globalIIDConeMediatorUnique
    cone (globalIIDConeMediatorUnique_of_isLimit cone hlim)

/-- True equivalence: global mediator uniqueness is exactly `IsLimit` for the
global Kleisli(Giry) iid-cone skeleton. -/
theorem isLimit_iff_globalIIDConeMediatorUnique
    (cone : KleisliGiryIIDConeSkeleton) :
    Nonempty (CategoryTheory.Limits.IsLimit (cone.toCone)) ↔ GlobalIIDConeMediatorUnique cone := by
  constructor
  · intro hlim
    rcases hlim with ⟨hlim⟩
    exact globalIIDConeMediatorUnique_of_isLimit cone hlim
  · intro hmed
    exact ⟨cone.isLimitOfMediatorUnique hmed⟩

/-- Specialized `P Bool` form of mediator uniqueness for the global diagram. -/
def GlobalIIDConeMediatorUniqueProbBool
    (cone : KleisliGiryProbBoolIIDCone) : Prop :=
  GlobalIIDConeMediatorUnique
    (⟨KleisliProbBoolObj, cone.iidHom, cone.commutes⟩ : KleisliGiryIIDConeSkeleton)

/-- Specialized `P Bool` form of the `IsLimit` equivalence. -/
theorem isLimit_iff_globalIIDConeMediatorUniqueProbBool
    (cone : KleisliGiryProbBoolIIDCone) :
    Nonempty (CategoryTheory.Limits.IsLimit (cone.toCone)) ↔
      GlobalIIDConeMediatorUniqueProbBool cone := by
  exact isLimit_iff_globalIIDConeMediatorUnique
    (⟨KleisliProbBoolObj, cone.iidHom, cone.commutes⟩ : KleisliGiryIIDConeSkeleton)

/-- Cone skeleton induced by `iidSequenceKernelTheta` once global finitary
commutation is supplied. -/
def iidSequenceKleisliConeSkeleton
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta) :
    KleisliGiryIIDConeSkeleton :=
  ⟨KleisliLatentThetaObj, iidSequenceKleisliHomTheta, hcommutes⟩

/-- Bridge theorem: for the cone built from `iidSequenceKernelTheta`, true
`IsLimit` is equivalent to global mediator uniqueness. -/
theorem isLimit_iff_globalIIDConeMediatorUnique_iidSequenceKernelTheta
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta) :
    Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
      GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes) :=
  isLimit_iff_globalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)

/-- No-extra-hypothesis (beyond global finitary invariance) IsLimit-ready entry:
it bundles
1. the derived commutation witness for `iidSequenceKleisliHomTheta`,
2. the unconditional finite-prefix iid-factorization equation family, and
3. the true `IsLimit`/mediator-uniqueness equivalence for the induced cone. -/
theorem iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    ∃ hcommutes : ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
          iidSequenceKleisliHomTheta,
      (∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
            (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal θ)) ∧
      (Nonempty (CategoryTheory.Limits.IsLimit ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
        GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)) := by
  let hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta :=
    iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal
  refine ⟨hcommutes, ?_⟩
  refine ⟨?_, ?_⟩
  · intro θ n xs
    exact iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance hglobal θ n xs
  · exact isLimit_iff_globalIIDConeMediatorUnique_iidSequenceKernelTheta
      (hcommutes := hcommutes)

/-- Path-B one-hop packaging: once `iidSequenceKernelTheta` is pointwise identified
with `iidProduct (thetaBernoulliKernel θ)`, the full IsLimit-ready payload follows. -/
theorem iidSequenceKernelTheta_isLimitReady_of_iidProduct_bridge
    (hbridge :
      ∀ θ : LatentTheta,
        iidSequenceKernelTheta θ =
          Exchangeability.Probability.iidProduct (thetaBernoulliKernel θ)) :
    ∃ hcommutes : ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
          iidSequenceKleisliHomTheta,
      (∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
            (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance
              (iidSequenceKernelTheta_globalFinitaryInvariance_of_iidProduct_bridge hbridge) θ)) ∧
      (Nonempty (CategoryTheory.Limits.IsLimit ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
        GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)) := by
  exact iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance
    (iidSequenceKernelTheta_globalFinitaryInvariance_of_iidProduct_bridge hbridge)

/-- Path-B canonical wrapper:
finite-prefix product marginals imply the full pointwise `iidProduct` bridge,
hence the complete IsLimit-ready payload. -/
theorem iidSequenceKernelTheta_isLimitReady_of_prefix_pi_marginals
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ),
        (iidSequenceKernelTheta θ).map (seqPrefixProj n) =
          Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ)) :
    ∃ hcommutes : ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
          iidSequenceKleisliHomTheta,
      (∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
            (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance
              (iidSequenceKernelTheta_globalFinitaryInvariance_of_iidProduct_bridge
                (iidSequenceKernelTheta_eq_iidProduct_of_prefix_pi_marginals hprefix)) θ)) ∧
      (Nonempty (CategoryTheory.Limits.IsLimit ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
        GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)) := by
  exact iidSequenceKernelTheta_isLimitReady_of_iidProduct_bridge
    (iidSequenceKernelTheta_eq_iidProduct_of_prefix_pi_marginals hprefix)

/-- `IsLimit`-like payload currently tracked in the existing kernel interface.
This is the bridge point from cone data to the established universal mediator
API. -/
def IsLimitLikeForIIDConeSkeleton
    (X : ℕ → Ω → Bool) (_cone : KleisliGiryIIDConeSkeleton) : Prop :=
  KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X

/-- Bridge: the existing kernel universal mediator API supplies the
`IsLimit`-like payload for any iid-cone skeleton. -/
theorem isLimitLikeForIIDConeSkeleton_of_kernelUniversalMediator
    (X : ℕ → Ω → Bool) (cone : KleisliGiryIIDConeSkeleton)
    (h : KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X) :
    IsLimitLikeForIIDConeSkeleton (Y := Y) (Ω := Ω) X cone := h

end Mettapedia.CategoryTheory
