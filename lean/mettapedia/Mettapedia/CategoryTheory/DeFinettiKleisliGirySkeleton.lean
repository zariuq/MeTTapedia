import Mettapedia.CategoryTheory.DeFinettiGlobalFinitaryDiagram
import Mettapedia.CategoryTheory.DeFinettiKernelInterface
import Mettapedia.CategoryTheory.DeFinettiSequenceKernelCone
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

/-! ## Global Finitary Commutation => Coordinate Prefix Invariance -/

/-- Global finitary cone commutation on sequence laws (all `τ : FinSuppPermNat`). -/
def GlobalFinitarySeqConeCommutes (μ : Measure GlobalBinarySeq) : Prop :=
  ∀ τ : FinSuppPermNat, μ.map (finSuppPermuteSeq τ) = μ

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
