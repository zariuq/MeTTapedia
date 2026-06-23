import Mettapedia.CategoryTheory.DeFinettiGlobalFinitaryDiagram
import Mettapedia.CategoryTheory.DeFinettiKernelInterface
import Mettapedia.CategoryTheory.DeFinettiSequenceKernelCone
import Mettapedia.ProbabilityTheory.HigherOrderProbability.ProbabilityMeasureBorelBridge
import Exchangeability.Core
import Exchangeability.Probability.InfiniteProduct
import Mathlib.CategoryTheory.Monad.Kleisli
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.MetricSpace.Polish

/-!
# Kleisli(Giry) Global Diagram and IID Cone Data

This file provides the categorical spine for the global de Finetti target:
- ambient category `Kleisli(MeasCat.Giry)`,
- a true global finitary-permutation diagram functor on `Bool^ℕ`,
- and cone data wrappers for an iid candidate arrow.

The universal-property payload is currently tracked through the existing
kernel-level mediator API (`KernelLatentThetaUniversalMediator`) and its
all-sources Kleisli bridges.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

open CategoryTheory
open MeasureTheory
open Mettapedia.Logic.DeFinetti
open Mettapedia.ProbabilityTheory.HigherOrderProbability.ProbabilityMeasureBorelBridge

variable {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Ambient category for the Giry-Kleisli formulation. -/
abbrev KleisliGiry : Type 1 := CategoryTheory.Kleisli (C := MeasCat) MeasCat.Giry

instance : CategoryTheory.Category KleisliGiry :=
  CategoryTheory.Kleisli.category (T := MeasCat.Giry)

/-- Extensionality for Kleisli(Giry) morphisms via their underlying kernel
functions. In Lean v4.31 a `Kleisli` morphism is bundled as a `Kleisli.Hom`
whose `.of` field is a `MeasCat` morphism (itself a `Measurable`-subtype), so the
underlying function is reached through `.1.1`. -/
theorem kleisliHom_ext {A B : KleisliGiry} {f g : A ⟶ B}
    (h : ∀ a : A.of.carrier, f.1.1 a = g.1.1 a) : f = g := by
  apply CategoryTheory.Kleisli.Hom.ext
  apply Subtype.ext
  funext a
  exact h a

/-- Pointwise application of an equation between Kleisli(Giry) morphisms. -/
theorem kleisliHom_congr_fun {A B : KleisliGiry} {f g : A ⟶ B}
    (h : f = g) (a : A.of.carrier) : f.1.1 a = g.1.1 a :=
  congrFun (congrArg (fun k : A ⟶ B => k.1.1) h) a

/-- Canonical sequence object `Bool^ℕ` in `Kleisli(MeasCat.Giry)`. -/
abbrev KleisliBinarySeqObj : KleisliGiry :=
  CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of GlobalBinarySeq)

/-- Canonical parameter object `P Bool` in `Kleisli(MeasCat.Giry)`. -/
abbrev KleisliProbBoolObj : KleisliGiry :=
  CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of (ProbabilityMeasure Bool))

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
  show ω (((1 : FinSuppPermNat).1).symm i) = ω i
  rw [OneMemClass.coe_one]
  rfl

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
  ⟨⟨fun ω => Measure.dirac (finSuppPermuteSeq τ ω),
    Measure.measurable_dirac.comp (measurable_finSuppPermuteSeq τ)⟩⟩

/-- Deterministic Kleisli hom for identity permutation is the Kleisli identity. -/
lemma finSuppPermKleisliHom_one :
    finSuppPermKleisliHom (1 : FinSuppPermNat) =
      CategoryTheory.CategoryStruct.id KleisliBinarySeqObj := by
  apply kleisliHom_ext
  intro ω
  change Measure.dirac (finSuppPermuteSeq (1 : FinSuppPermNat) ω) = Measure.dirac ω
  simp [finSuppPermuteSeq_one]

/-- Deterministic Kleisli hom composition law for finitary permutations. -/
lemma finSuppPermKleisliHom_comp (τ υ : FinSuppPermNat) :
    CategoryTheory.CategoryStruct.comp (finSuppPermKleisliHom υ) (finSuppPermKleisliHom τ) =
      finSuppPermKleisliHom (τ * υ) := by
  apply kleisliHom_ext
  intro ω
  change
    Measure.bind (Measure.dirac (finSuppPermuteSeq υ ω))
        (fun x => Measure.dirac (finSuppPermuteSeq τ x)) =
      Measure.dirac (finSuppPermuteSeq (τ * υ) ω)
  rw [Measure.bind_dirac_eq_map _ (measurable_finSuppPermuteSeq τ)]
  simp [measurable_finSuppPermuteSeq τ, finSuppPermuteSeq_mul]

/-- Monoid action into endomorphisms of `Bool^ℕ` in `Kleisli(MeasCat.Giry)`. -/
def finSuppPermKleisliEndMonoidHom :
    FinSuppPermNat →* CategoryTheory.End KleisliBinarySeqObj where
  toFun := finSuppPermKleisliHom
  map_one' := finSuppPermKleisliHom_one
  map_mul' τ υ := by
    exact (finSuppPermKleisliHom_comp τ υ).symm

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
  exact measurable_pi_apply (a := (thetaPrefixZeroIdx n))

/-- Read the unique coordinate of a `Fin 1 → Bool` tuple. -/
def fin1TupleToBool (x : Fin 1 → Bool) : Bool :=
  x ⟨0, by decide⟩

lemma measurable_fin1TupleToBool : Measurable fin1TupleToBool := by
  exact measurable_pi_apply (a := (⟨0, by decide⟩ : Fin 1))

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

/-- Time-homogeneous IID transition kernel family indexed by trajectory prefixes:
the next Boolean sample depends only on the latent `Theta` coordinate. -/
def thetaIidStep (n : ℕ) :
    ProbabilityTheory.Kernel (ThetaBoolPrefix n) (ThetaBoolTimeline (n + 1)) where
  toFun := fun x => by
    exact thetaBernoulliKernel (thetaFromPrefix x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ ?_
    intro s hs
    exact (thetaBernoulliKernel.measurable_coe (s := s) hs).comp measurable_thetaFromPrefix

instance thetaIidStep_isMarkov (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel (thetaIidStep n) := by
  refine ⟨?_⟩
  intro x
  exact (show IsProbabilityMeasure (thetaBernoulliKernel (thetaFromPrefix x)) from inferInstance)

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
  exact (measurable_id : Measurable fun θ : LatentTheta => θ)

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
  exact measurable_pi_apply (a := (n + 1))

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
  exact measurable_pi_apply (a := (⟨i.1 + 1, Finset.mem_Iic.2 hi⟩ : Finset.Iic n))

lemma seqPrefixProj_comp_dropThetaHead_eq_dropThetaPrefix_frestrictLe (n : ℕ) :
    seqPrefixProj n ∘ dropThetaHead = dropThetaPrefix n ∘ (Preorder.frestrictLe n) := by
  funext x
  funext i
  unfold seqPrefixProj dropThetaHead dropThetaPrefix
  simp only [Preorder.frestrictLe]
  rfl

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
      rw [hi]; exact hx
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

/-- Prefix-event decomposition for a tuple built with `Fin.snoc`: horizon `n+1`
splits into the first `n` coordinates and the final coordinate. -/
theorem seqPrefixEvent_snoc
    (n : ℕ) (xs : Fin n → Bool) (b : Bool) :
    seqPrefixEvent (n + 1) (Fin.snoc xs b) =
      {ω : GlobalBinarySeq | (∀ i : Fin n, ω i = xs i) ∧ ω n = b} := by
  ext ω
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      simpa [Fin.snoc_castSucc] using h i.castSucc
    · simpa [Fin.snoc_last] using h (Fin.last n)
  · intro h i
    cases i using Fin.lastCases with
    | last =>
        simpa [Fin.snoc_last] using h.2
    | cast j =>
        simpa [Fin.snoc_castSucc] using h.1 j

private theorem seqPrefixEvent_eq_preimage_seqPrefixProj_singleton
    (n : ℕ) (xs : Fin n → Bool) :
    seqPrefixEvent n xs = (seqPrefixProj n) ⁻¹' ({xs} : Set (Fin n → Bool)) := by
  ext ω
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrArg (fun f : Fin n → Bool => f i) h

/-- Pullback of a singleton `Fin.snoc` prefix through the `IicProdIoc`-split of
`dropThetaPrefix` at horizon `n+1`. -/
private theorem dropThetaPrefix_IicProdIoc_preimage_snoc
    (n : ℕ) (xs : Fin n → Bool) (b : Bool) :
    (fun z : ThetaBoolPrefix n × ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i) =>
      dropThetaPrefix (n + 1) (IicProdIoc n (n + 1) z)) ⁻¹'
        ({Fin.snoc xs b} : Set (Fin (n + 1) → Bool))
      =
    {z : ThetaBoolPrefix n × ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i) |
      dropThetaPrefix n z.1 = xs ∧
        cast (by simp [ThetaBoolTimeline]) (z.2 ⟨n + 1, by simp⟩) = b} := by
  ext z
  constructor
  · intro hz
    have hz0 :
        dropThetaPrefix (n + 1) (IicProdIoc n (n + 1) z) = Fin.snoc xs b := by
      simpa using hz
    refine ⟨?_, ?_⟩
    · funext i
      have hcomp := congrArg (fun f : Fin (n + 1) → Bool => f i.castSucc) hz0
      simpa [dropThetaPrefix, IicProdIoc, Fin.snoc_castSucc] using hcomp
    · have hlast := congrArg (fun f : Fin (n + 1) → Bool => f (Fin.last n)) hz0
      simpa [dropThetaPrefix, IicProdIoc, Fin.snoc_last] using hlast
  · intro hz
    have hinit :
        ∀ i : Fin n,
          dropThetaPrefix (n + 1) (IicProdIoc n (n + 1) z) i.castSucc = xs i := by
      intro i
      have hi := congrArg (fun f : Fin n → Bool => f i) hz.1
      simpa [dropThetaPrefix, IicProdIoc] using hi
    have hlast :
        dropThetaPrefix (n + 1) (IicProdIoc n (n + 1) z) (Fin.last n) = b := by
      simpa [dropThetaPrefix, IicProdIoc] using hz.2
    have hfun :
        dropThetaPrefix (n + 1) (IicProdIoc n (n + 1) z) = Fin.snoc xs b := by
      funext i
      cases i using Fin.lastCases with
      | last =>
          simpa [Fin.snoc_last] using hlast
      | cast j =>
          simpa [Fin.snoc_castSucc] using hinit j
    simp [hfun]

/-- Measurability of `dropThetaPrefix (n+1)` after splitting `Iic (n+1)` into
`Iic n × Ioc n (n+1)`. -/
private theorem measurable_dropThetaPrefix_IicProdIoc (n : ℕ) :
    Measurable (fun z : ThetaBoolPrefix n ×
      ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i) =>
      dropThetaPrefix (n + 1) (IicProdIoc n (n + 1) z)) := by
  exact (measurable_dropThetaPrefix (n + 1)).comp (measurable_IicProdIoc (m := n) (n := n + 1))

/-- The singleton `Fin.snoc` pullback set through the split map is measurable. -/
private theorem measurableSet_dropThetaPrefix_IicProdIoc_preimage_snoc
    (n : ℕ) (xs : Fin n → Bool) (b : Bool) :
    MeasurableSet
      ((fun z : ThetaBoolPrefix n ×
        ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i) =>
        dropThetaPrefix (n + 1) (IicProdIoc n (n + 1) z)) ⁻¹'
          ({Fin.snoc xs b} : Set (Fin (n + 1) → Bool))) := by
  simpa using
    (measurable_dropThetaPrefix_IicProdIoc n)
      (MeasurableSet.singleton (Fin.snoc xs b))

/-- The one-step tail event selecting value `b` on the unique coordinate in
`Ioc n (n+1)`. -/
private def snocTailEvent (n : ℕ) (b : Bool) :
    Set ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i) :=
  (fun y : ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i) =>
      y ⟨n + 1, by simp⟩) ⁻¹'
    ({cast (by simp [ThetaBoolTimeline]) b} :
      Set (ThetaBoolTimeline (⟨n + 1, by simp⟩ : Finset.Ioc n (n + 1))))

private theorem snocTailEvent_eq_singleton (n : ℕ) (b : Bool) :
    snocTailEvent n b =
      ({MeasurableEquiv.piSingleton n (cast (by simp [ThetaBoolTimeline]) b)} :
        Set ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i)) := by
  let b' : ThetaBoolTimeline (n + 1) := cast (by simp [ThetaBoolTimeline]) b
  ext y
  constructor
  · intro hy
    apply Set.mem_singleton_iff.2
    funext i
    rcases Nat.mem_Ioc_succ' i with rfl
    have hy' :
        cast (by simp [ThetaBoolTimeline])
          (y ⟨n + 1, by simp⟩) = b := by
      exact hy
    have hy'' : y ⟨n + 1, by simp⟩ = b' := by
      exact hy'
    rw [hy'']; rfl
  · intro hy
    rcases Set.mem_singleton_iff.1 hy with rfl
    simp only [snocTailEvent, Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.piSingleton]
    rfl

private theorem measurableSet_snocTailEvent (n : ℕ) (b : Bool) :
    MeasurableSet (snocTailEvent n b) := by
  let b' : ThetaBoolTimeline (n + 1) := cast (by simp [ThetaBoolTimeline]) b
  have hpre :
      snocTailEvent n b =
        ((MeasurableEquiv.piSingleton n).symm ⁻¹' ({b'} : Set (ThetaBoolTimeline (n + 1)))) := by
    ext y
    rfl
  rw [hpre]
  haveI : MeasurableSingletonClass (ThetaBoolTimeline (n + 1)) :=
    (inferInstance : MeasurableSingletonClass Bool)
  exact (MeasurableEquiv.piSingleton n).symm.measurable (MeasurableSet.singleton b')

private theorem snocTailEvent_preimage_piSingleton
    (n : ℕ) (b : Bool) :
    (MeasurableEquiv.piSingleton n) ⁻¹' (snocTailEvent n b) = ({b} : Set Bool) := by
  let b' : ThetaBoolTimeline (n + 1) := cast (by simp [ThetaBoolTimeline]) b
  rw [snocTailEvent_eq_singleton]
  ext t
  constructor
  · intro ht
    have hEq : MeasurableEquiv.piSingleton n t = MeasurableEquiv.piSingleton n b' := by
      simpa [b'] using ht
    have ht' : t = b' := (MeasurableEquiv.piSingleton n).injective hEq
    exact ht'
  · intro ht
    have ht' : t = b' := ht
    simp [ht', b']

private theorem thetaIidStep_map_piSingleton_snocTailEvent
    (n : ℕ) (x : ThetaBoolPrefix n) (b : Bool) :
    (((thetaIidStep n).map (MeasurableEquiv.piSingleton n)) x) (snocTailEvent n b) =
      thetaIidStep n x ({b} : Set Bool) := by
  calc
    (((thetaIidStep n).map (MeasurableEquiv.piSingleton n)) x) (snocTailEvent n b)
        = (Measure.map (MeasurableEquiv.piSingleton n) ((thetaIidStep n) x))
            (snocTailEvent n b) := by
              exact congrArg (fun μ => μ (snocTailEvent n b))
                (ProbabilityTheory.Kernel.map_apply (thetaIidStep n)
                  ((MeasurableEquiv.piSingleton n).measurable) x)
    _ = thetaIidStep n x ({b} : Set Bool) := by
          rw [Measure.map_apply
            (MeasurableEquiv.piSingleton n).measurable (measurableSet_snocTailEvent n b)]
          simp [snocTailEvent_preimage_piSingleton]

private theorem dropThetaPrefix_IicProdIoc_preimage_snoc_tail
    (n : ℕ) (xs : Fin n → Bool) (b : Bool) :
    (fun z : ThetaBoolPrefix n × ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i) =>
      dropThetaPrefix (n + 1) (IicProdIoc n (n + 1) z)) ⁻¹'
        ({Fin.snoc xs b} : Set (Fin (n + 1) → Bool))
      =
    {z : ThetaBoolPrefix n × ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i) |
      dropThetaPrefix n z.1 = xs ∧ z.2 ∈ snocTailEvent n b} := by
  ext z
  rw [dropThetaPrefix_IicProdIoc_preimage_snoc]; rfl

private theorem snocTailCarrier_preimage_prodMk
    (n : ℕ) (xs : Fin n → Bool) (b : Bool) (x : ThetaBoolPrefix n) :
    Prod.mk x ⁻¹'
        ({z : ThetaBoolPrefix n × ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i) |
          dropThetaPrefix n z.1 = xs ∧ z.2 ∈ snocTailEvent n b})
      = if dropThetaPrefix n x = xs then snocTailEvent n b else ∅ := by
  ext y
  by_cases hx : dropThetaPrefix n x = xs
  · simp [hx]
  · simp [hx]

private theorem partialTraj_dropThetaPrefix_map_snoc_integral
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) (b : Bool) :
    (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 (n + 1)) (thetaToPrefix0 θ)).map
      (dropThetaPrefix (n + 1))) ({Fin.snoc xs b} : Set (Fin (n + 1) → Bool))
      =
    ∫⁻ x : ThetaBoolPrefix n,
      (if dropThetaPrefix n x = xs then thetaIidStep n x ({b} : Set Bool) else 0)
      ∂((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)) := by
  let sn : Fin (n + 1) → Bool := Fin.snoc xs b
  let A : Set (ThetaBoolPrefix n × ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i)) :=
    {z | dropThetaPrefix n z.1 = xs ∧ z.2 ∈ snocTailEvent n b}
  let Kstep : ProbabilityTheory.Kernel (ThetaBoolPrefix n)
      (ThetaBoolPrefix n × ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i)) :=
    ProbabilityTheory.Kernel.prod ProbabilityTheory.Kernel.id
      ((thetaIidStep n).map (MeasurableEquiv.piSingleton n))
  let Kcomp : ProbabilityTheory.Kernel (ThetaBoolPrefix 0)
      (ThetaBoolPrefix n × ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i)) :=
    ProbabilityTheory.Kernel.comp Kstep (ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n)
  have hAeq :
      (fun z : ThetaBoolPrefix n × ((i : Finset.Ioc n (n + 1)) → ThetaBoolTimeline i) =>
        dropThetaPrefix (n + 1) (IicProdIoc n (n + 1) z)) ⁻¹'
          ({sn} : Set (Fin (n + 1) → Bool))
        = A := by
    simpa [A] using dropThetaPrefix_IicProdIoc_preimage_snoc_tail n xs b
  have hAmeas : MeasurableSet A := by
    rw [← hAeq]
    exact measurableSet_dropThetaPrefix_IicProdIoc_preimage_snoc n xs b
  have hsucc :
      ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 (n + 1)
        =
      Kcomp.map
          (IicProdIoc n (n + 1)) := by
    simpa [Kcomp, Kstep, ProbabilityTheory.Kernel.comp] using
      (ProbabilityTheory.Kernel.partialTraj_succ_of_le
        (κ := thetaIidStep) (a := 0) (b := n) (hab := Nat.zero_le n))
  have hsuccθ :
      (ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 (n + 1)) (thetaToPrefix0 θ)
        =
      (Kcomp.map (IicProdIoc n (n + 1)) (thetaToPrefix0 θ)) := by
    simpa using congrArg
      (fun κ : ProbabilityTheory.Kernel (ThetaBoolPrefix 0) (ThetaBoolPrefix (n + 1)) =>
        κ (thetaToPrefix0 θ)) hsucc
  have hSmeas :
      MeasurableSet
        ((dropThetaPrefix (n + 1)) ⁻¹' ({sn} : Set (Fin (n + 1) → Bool))) := by
    exact (measurable_dropThetaPrefix (n + 1)) (MeasurableSet.singleton sn)
  have hprecomp :
      ((IicProdIoc n (n + 1)) ⁻¹' ((dropThetaPrefix (n + 1)) ⁻¹' ({sn} : Set (Fin (n + 1) → Bool)))
        = A) := by
    exact hAeq
  calc
    (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 (n + 1)) (thetaToPrefix0 θ)).map
      (dropThetaPrefix (n + 1))) ({sn} : Set (Fin (n + 1) → Bool))
        = (ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 (n + 1) (thetaToPrefix0 θ))
            ((dropThetaPrefix (n + 1)) ⁻¹' ({sn} : Set (Fin (n + 1) → Bool))) := by
              exact Measure.map_apply (measurable_dropThetaPrefix (n + 1))
                (MeasurableSet.singleton sn)
    _ = (Kcomp.map (IicProdIoc n (n + 1)) (thetaToPrefix0 θ))
          ((dropThetaPrefix (n + 1)) ⁻¹' ({sn} : Set (Fin (n + 1) → Bool))) := by
            simp [hsuccθ]
    _ = (Measure.map (IicProdIoc n (n + 1)) (Kcomp (thetaToPrefix0 θ)))
          ((dropThetaPrefix (n + 1)) ⁻¹' ({sn} : Set (Fin (n + 1) → Bool))) := by
            exact congrArg (fun μ => μ ((dropThetaPrefix (n + 1)) ⁻¹' ({sn} : Set (Fin (n + 1) → Bool))))
              (ProbabilityTheory.Kernel.map_apply Kcomp
                (measurable_IicProdIoc (m := n) (n := n + 1)) (thetaToPrefix0 θ))
    _ = (Kcomp (thetaToPrefix0 θ))
          ((IicProdIoc n (n + 1)) ⁻¹'
            ((dropThetaPrefix (n + 1)) ⁻¹' ({sn} : Set (Fin (n + 1) → Bool)))) := by
            exact
              (Measure.map_apply (measurable_IicProdIoc (m := n) (n := n + 1)) hSmeas)
    _ = (Kcomp (thetaToPrefix0 θ)) A := by
            simp [hprecomp]
    _ = ∫⁻ x : ThetaBoolPrefix n,
          (Kstep x) A
            ∂((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)) := by
            exact
              (ProbabilityTheory.Kernel.comp_apply'
                Kstep
                (ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n)
                (thetaToPrefix0 θ) hAmeas)
    _ = ∫⁻ x : ThetaBoolPrefix n,
          (if dropThetaPrefix n x = xs then thetaIidStep n x ({b} : Set Bool) else 0)
            ∂((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)) := by
            refine lintegral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            by_cases hx : dropThetaPrefix n x = xs
            · have hpre :
                Prod.mk x ⁻¹' A = snocTailEvent n b := by
                  ext y
                  simp [A, hx]
              calc
                (Kstep x) A
                    = ((thetaIidStep n).map (MeasurableEquiv.piSingleton n)) x
                        (Prod.mk x ⁻¹' A) := by
                          simpa [Kstep] using
                            (ProbabilityTheory.Kernel.id_prod_apply'
                              ((thetaIidStep n).map (MeasurableEquiv.piSingleton n)) x hAmeas)
                _ = ((thetaIidStep n).map (MeasurableEquiv.piSingleton n)) x
                      (snocTailEvent n b) := by simp [hpre]
                _ = thetaIidStep n x ({b} : Set Bool) := by
                      exact thetaIidStep_map_piSingleton_snocTailEvent n x b
                _ = (if dropThetaPrefix n x = xs then thetaIidStep n x ({b} : Set Bool) else 0) := by
                      simp [hx]
            · have hpre :
                Prod.mk x ⁻¹' A = ∅ := by
                  ext y
                  simp [A, hx]
              calc
                (Kstep x) A
                    = ((thetaIidStep n).map (MeasurableEquiv.piSingleton n)) x
                        (Prod.mk x ⁻¹' A) := by
                          simpa [Kstep] using
                            (ProbabilityTheory.Kernel.id_prod_apply'
                              ((thetaIidStep n).map (MeasurableEquiv.piSingleton n)) x hAmeas)
                _ = ((thetaIidStep n).map (MeasurableEquiv.piSingleton n)) x ∅ := by simp [hpre]
                _ = 0 := by simp
                _ = (if dropThetaPrefix n x = xs then thetaIidStep n x ({b} : Set Bool) else 0) := by
                      simp [hx]

/-- Singleton recursion for `iidPrefixKernel`: appending one final bit multiplies
the singleton mass by the one-step Bernoulli factor. -/
theorem iidPrefixKernel_singleton_snoc
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) (b : Bool) :
    (iidPrefixKernel (n + 1) θ) ({Fin.snoc xs b} : Set (Fin (n + 1) → Bool)) =
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) *
        thetaBernoulliKernel θ ({b} : Set Bool) := by
  let fs : Fin (n + 1) → Bool := Fin.snoc xs b
  have hprod_snoc :
      (∏ i : Fin (n + 1), Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (fs i)) =
        (∏ i : Fin n, Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (xs i)) *
          Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) b := by
    calc
      (∏ i : Fin (n + 1), Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (fs i))
          = (∏ i : Fin n, Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (fs i.castSucc)) *
              Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (fs (Fin.last n)) := by
                simpa using (Fin.prod_univ_castSucc
                  (f := fun i : Fin (n + 1) =>
                    Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (fs i)))
      _ = (∏ i : Fin n, Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (xs i)) *
            Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) b := by
              simp [fs, Fin.snoc_castSucc, Fin.snoc_last]
  have hnonnegProd :
      0 ≤ (∏ i : Fin n, Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (xs i)) := by
    exact Finset.prod_nonneg (fun i _ => by
      cases xs i <;>
        simp [Mettapedia.Logic.DeFinetti.bernoulliPMF, sub_nonneg.2 θ.2.2, θ.2.1])
  calc
    (iidPrefixKernel (n + 1) θ) ({Fin.snoc xs b} : Set (Fin (n + 1) → Bool))
        = ENNReal.ofReal
            (∏ i : Fin (n + 1), Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (fs i)) := by
              simp [iidPrefixKernel,
                Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel,
                Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight,
                Mettapedia.Logic.DeFinetti.bernoulliProductPMF, fs]
    _ = ENNReal.ofReal
          ((∏ i : Fin n, Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (xs i)) *
            Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) b) := by
              simp [hprod_snoc]
    _ = ENNReal.ofReal
          (∏ i : Fin n, Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (xs i)) *
        ENNReal.ofReal (Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) b) := by
          simpa using (ENNReal.ofReal_mul
            (p := (∏ i : Fin n, Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) (xs i)))
            (q := Mettapedia.Logic.DeFinetti.bernoulliPMF (θ : ℝ) b) hnonnegProd)
    _ = (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) *
          thetaBernoulliKernel θ ({b} : Set Bool) := by
            simp [iidPrefixKernel,
              Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel,
              Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight,
              Mettapedia.Logic.DeFinetti.bernoulliProductPMF,
              thetaBernoulliKernel_singleton_apply, mul_comm]

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
    exact Exchangeability.Probability.iidProduct.cylinder_fintype
      (thetaBernoulliKernel θ) (n := n)
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
  exact measurable_pi_apply (a := (0 : ℕ))

lemma thetaFromPrefix_thetaToPrefix0 (θ : LatentTheta) :
    thetaFromPrefix (thetaToPrefix0 θ) = θ := by
  change thetaToPrefix0 θ (thetaPrefixZeroIdx 0) = θ
  unfold thetaToPrefix0 thetaPrefixZeroIdx
  simp [ThetaBoolTimeline]

/-- Along the partial trajectory started from `thetaToPrefix0 θ`, the extracted
latent coordinate is deterministic and equal to `θ`. -/
lemma partialTraj_thetaIidStep_map_thetaFromPrefix_eq_dirac
    (θ : LatentTheta) (n : ℕ) :
    (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
      (fun x : ThetaBoolPrefix n => thetaFromPrefix x)) = Measure.dirac θ := by
  have hmap0 :
      (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
        (Preorder.frestrictLe₂ (Nat.zero_le n))) =
      (ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 0 (thetaToPrefix0 θ)) := by
    simpa using
      (ProbabilityTheory.Kernel.partialTraj_map_frestrictLe₂_apply
        (κ := thetaIidStep) (a := 0) (b := 0) (c := n)
        (x₀ := thetaToPrefix0 θ) (hbc := Nat.zero_le n))
  have hmapTheta :
      (fun x : ThetaBoolPrefix n => thetaFromPrefix x) =
        (fun x0 : ThetaBoolPrefix 0 => thetaFromPrefix x0) ∘
          (Preorder.frestrictLe₂ (Nat.zero_le n)) := by
    funext x
    unfold thetaFromPrefix
    simp [thetaPrefixZeroIdx]
  have hmapmap :
      (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
        (fun x : ThetaBoolPrefix n => thetaFromPrefix x)) =
      ((((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
          (Preorder.frestrictLe₂ (Nat.zero_le n))).map
        (fun x0 : ThetaBoolPrefix 0 => thetaFromPrefix x0)) := by
    rw [hmapTheta]
    have htmp :=
      (Measure.map_map
        (μ := (ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ))
        (g := (fun x0 : ThetaBoolPrefix 0 => thetaFromPrefix x0))
        (f := (Preorder.frestrictLe₂ (Nat.zero_le n)))
        (hg := by
          simpa using (Mettapedia.CategoryTheory.measurable_thetaFromPrefix (n := 0)))
        (hf := by fun_prop))
    simpa using htmp.symm
  calc
    (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
      (fun x : ThetaBoolPrefix n => thetaFromPrefix x))
        = ((((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
            (Preorder.frestrictLe₂ (Nat.zero_le n))).map
            (fun x0 : ThetaBoolPrefix 0 => thetaFromPrefix x0)) := hmapmap
    _ = ((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 0 (thetaToPrefix0 θ)).map
          (fun x0 : ThetaBoolPrefix 0 => thetaFromPrefix x0)) := by
            simp [hmap0]
    _ = Measure.dirac (thetaFromPrefix (thetaToPrefix0 θ)) := by
          simp [ProbabilityTheory.Kernel.partialTraj_self, ProbabilityTheory.Kernel.id_apply,
            Measure.map_dirac, Mettapedia.CategoryTheory.measurable_thetaFromPrefix]
    _ = Measure.dirac θ := by
          simp [thetaFromPrefix_thetaToPrefix0]

/-- One-step composition of `partialTraj thetaIidStep 0 n` with `thetaIidStep n`
evaluated at `thetaToPrefix0 θ` equals the Bernoulli kernel at `θ`. -/
lemma partialTraj_thetaIidStep_comp_eval_eq_thetaBernoulli
    (θ : LatentTheta) (n : ℕ) (s : Set Bool) (hs : MeasurableSet s) :
    (ProbabilityTheory.Kernel.comp (thetaIidStep n)
      (ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)) s
      = thetaBernoulliKernel θ s := by
  have hmap :
      (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
        (fun x : ThetaBoolPrefix n => thetaFromPrefix x)) = Measure.dirac θ :=
    partialTraj_thetaIidStep_map_thetaFromPrefix_eq_dirac θ n
  have hlin :
      ∫⁻ t : LatentTheta, (thetaBernoulliKernel t) s
          ∂((((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
            (fun x : ThetaBoolPrefix n => thetaFromPrefix x)))
        =
      ∫⁻ x : ThetaBoolPrefix n, (thetaBernoulliKernel (thetaFromPrefix x)) s
        ∂((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)) := by
    simpa using
      (MeasureTheory.lintegral_map
        (μ := ((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)))
        (f := fun t : LatentTheta => (thetaBernoulliKernel t) s)
        (g := fun x : ThetaBoolPrefix n => thetaFromPrefix x)
        (hf := (thetaBernoulliKernel.measurable_coe (s := s) hs))
        (hg := Mettapedia.CategoryTheory.measurable_thetaFromPrefix (n := n)))
  calc
    (ProbabilityTheory.Kernel.comp (thetaIidStep n)
      (ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)) s
        = ∫⁻ x : ThetaBoolPrefix n, (thetaIidStep n x) s
            ∂((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)) := by
              simpa using (ProbabilityTheory.Kernel.comp_apply' (thetaIidStep n)
                (ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n)
                (thetaToPrefix0 θ) hs)
    _ = ∫⁻ x : ThetaBoolPrefix n, (thetaBernoulliKernel (thetaFromPrefix x)) s
          ∂((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)) := by
            rfl
    _ = ∫⁻ t : LatentTheta, (thetaBernoulliKernel t) s
          ∂((((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
            (fun x : ThetaBoolPrefix n => thetaFromPrefix x))) := by
            exact hlin.symm
    _ = ∫⁻ t : LatentTheta, (thetaBernoulliKernel t) s ∂(Measure.dirac θ) := by
          simp [hmap]
    _ = thetaBernoulliKernel θ s := by
          simp [lintegral_dirac'
            (a := θ)
            (f := fun t : LatentTheta => (thetaBernoulliKernel t) s)
            ((thetaBernoulliKernel.measurable_coe (s := s) hs))]

/-- Under the partial trajectory started from `thetaToPrefix0 θ`, the latent
coordinate extracted by `thetaFromPrefix` is almost surely equal to `θ`. -/
lemma ae_thetaFromPrefix_eq_of_partialTraj_thetaIidStep
    (θ : LatentTheta) (n : ℕ) :
    ∀ᵐ x ∂((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)),
      thetaFromPrefix x = θ := by
  let μ : Measure (ThetaBoolPrefix n) :=
    (ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)
  have hmap :
      μ.map (fun x : ThetaBoolPrefix n => thetaFromPrefix x) = Measure.dirac θ := by
    simpa [μ] using partialTraj_thetaIidStep_map_thetaFromPrefix_eq_dirac θ n
  have hpre :
      (fun x : ThetaBoolPrefix n => thetaFromPrefix x) ⁻¹' ({θ} : Set LatentTheta) =
        {x : ThetaBoolPrefix n | thetaFromPrefix x = θ} := by
    ext x
    simp
  have hone : μ {x : ThetaBoolPrefix n | thetaFromPrefix x = θ} = 1 := by
    calc
      μ {x : ThetaBoolPrefix n | thetaFromPrefix x = θ}
          = μ ((fun x : ThetaBoolPrefix n => thetaFromPrefix x) ⁻¹' ({θ} : Set LatentTheta)) := by
              simp [hpre]
      _ = (μ.map (fun x : ThetaBoolPrefix n => thetaFromPrefix x)) ({θ} : Set LatentTheta) := by
            symm
            exact Measure.map_apply (Mettapedia.CategoryTheory.measurable_thetaFromPrefix (n := n))
              (MeasurableSet.singleton θ)
      _ = (Measure.dirac θ) ({θ} : Set LatentTheta) := by
            simp [hmap]
      _ = 1 := by
            simp
  have hmeasEq : MeasurableSet {x : ThetaBoolPrefix n | thetaFromPrefix x = θ} := by
    simpa [hpre] using
      (Mettapedia.CategoryTheory.measurable_thetaFromPrefix (n := n)) (MeasurableSet.singleton θ)
  have hzero : μ {x : ThetaBoolPrefix n | thetaFromPrefix x ≠ θ} = 0 := by
    have hcompl :
        {x : ThetaBoolPrefix n | thetaFromPrefix x ≠ θ} =
          ({x : ThetaBoolPrefix n | thetaFromPrefix x = θ})ᶜ := by
      ext x
      simp
    have hadd :
        μ {x : ThetaBoolPrefix n | thetaFromPrefix x = θ} +
          μ ({x : ThetaBoolPrefix n | thetaFromPrefix x = θ})ᶜ =
        μ Set.univ := MeasureTheory.measure_add_measure_compl hmeasEq
    have hprob : μ Set.univ = 1 := by
      have hprobI : IsProbabilityMeasure μ := by
        change IsProbabilityMeasure
          ((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ))
        infer_instance
      exact (measure_univ : μ Set.univ = 1)
    have hcomp0 : μ ({x : ThetaBoolPrefix n | thetaFromPrefix x = θ})ᶜ = 0 := by
      simpa [hone, hprob] using hadd
    simpa [hcompl] using hcomp0
  have haeμ : ∀ᵐ x ∂μ, thetaFromPrefix x = θ := by
    refine (ae_iff).2 ?_
    simpa using hzero
  simpa [μ] using haeμ

/-- Along the partial trajectory started from `thetaToPrefix0 θ`, the one-step
kernel `thetaIidStep n` agrees almost surely with the constant Bernoulli kernel
at parameter `θ`. -/
lemma ae_thetaIidStep_eq_thetaBernoulli_under_partialTraj
    (θ : LatentTheta) (n : ℕ) :
    ∀ᵐ x ∂((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)),
      thetaIidStep n x = thetaBernoulliKernel θ := by
  filter_upwards [ae_thetaFromPrefix_eq_of_partialTraj_thetaIidStep θ n] with x hx
  ext s hs
  show thetaBernoulliKernel (thetaFromPrefix x) s = thetaBernoulliKernel θ s
  rw [hx]

/-- Composing the one-step kernel `thetaIidStep n` with the partial trajectory
started from `thetaToPrefix0 θ` yields exactly the Bernoulli law at `θ`. -/
lemma partialTraj_thetaIidStep_nextLaw_eq_thetaBernoulli
    (θ : LatentTheta) (n : ℕ) :
    ((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).bind
        (thetaIidStep n) =
      thetaBernoulliKernel θ := by
  let μ : Measure (ThetaBoolPrefix n) :=
    (ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)
  have hcongr :
      μ.bind (thetaIidStep n) =
        μ.bind (ProbabilityTheory.Kernel.const (ThetaBoolPrefix n) (thetaBernoulliKernel θ)) := by
    exact MeasureTheory.Measure.comp_congr
      (ae_thetaIidStep_eq_thetaBernoulli_under_partialTraj θ n)
  have hprob : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure
      ((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ))
    infer_instance
  calc
    ((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).bind
        (thetaIidStep n)
        = μ.bind (thetaIidStep n) := by
            rfl
    _ = μ.bind (ProbabilityTheory.Kernel.const (ThetaBoolPrefix n) (thetaBernoulliKernel θ)) := hcongr
    _ = μ Set.univ • (thetaBernoulliKernel θ) := by
          exact (MeasureTheory.Measure.const_comp (μ := μ) (ν := (thetaBernoulliKernel θ)))
    _ = thetaBernoulliKernel θ := by
          simp [measure_univ]

private theorem partialTraj_dropThetaPrefix_map_snoc
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) (b : Bool) :
    (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 (n + 1)) (thetaToPrefix0 θ)).map
      (dropThetaPrefix (n + 1))) ({Fin.snoc xs b} : Set (Fin (n + 1) → Bool)) =
      (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
        (dropThetaPrefix n)) ({xs} : Set (Fin n → Bool)) *
        thetaBernoulliKernel θ ({b} : Set Bool) := by
  let μn : Measure (ThetaBoolPrefix n) :=
    (ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)
  let S : Set (ThetaBoolPrefix n) := {x | dropThetaPrefix n x = xs}
  let c : ENNReal := thetaBernoulliKernel θ ({b} : Set Bool)
  have hmain :=
    partialTraj_dropThetaPrefix_map_snoc_integral θ n xs b
  have hstepKernel :
      ∀ᵐ x ∂μn, thetaIidStep n x = thetaBernoulliKernel θ := by
    simpa [μn] using ae_thetaIidStep_eq_thetaBernoulli_under_partialTraj θ n
  have hstep :
      ∀ᵐ x ∂μn, thetaIidStep n x ({b} : Set Bool) = c := by
    filter_upwards [hstepKernel] with x hx
    show thetaIidStep n x ({b} : Set Bool) = c
    rw [hx]; rfl
  have hcongr :
      (∫⁻ x : ThetaBoolPrefix n,
          (if dropThetaPrefix n x = xs then thetaIidStep n x ({b} : Set Bool) else 0) ∂μn)
        =
      (∫⁻ x : ThetaBoolPrefix n,
          (if dropThetaPrefix n x = xs then c else 0) ∂μn) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hstep] with x hx
    by_cases hxs : dropThetaPrefix n x = xs
    · simp [hxs, hx]
    · simp [hxs]
  have hSmeas : MeasurableSet S := by
    exact (measurable_dropThetaPrefix n) (MeasurableSet.singleton xs)
  have hindicator :
      (fun x : ThetaBoolPrefix n => if dropThetaPrefix n x = xs then c else 0)
        = Set.indicator S (fun _ : ThetaBoolPrefix n => c) := by
    funext x
    by_cases hxs : dropThetaPrefix n x = xs
    · simp [S, hxs]
    · simp [S, hxs]
  have hind :
      (∫⁻ x : ThetaBoolPrefix n, (if dropThetaPrefix n x = xs then c else 0) ∂μn)
        = c * μn S := by
    rw [hindicator, lintegral_indicator hSmeas]
    simp [S, lintegral_const]
  have hmapS :
      (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
        (dropThetaPrefix n)) ({xs} : Set (Fin n → Bool)) = μn S := by
    have hpreS :
        (dropThetaPrefix n) ⁻¹' ({xs} : Set (Fin n → Bool)) = S := by
      ext x
      simp [S]
    calc
      (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
        (dropThetaPrefix n)) ({xs} : Set (Fin n → Bool))
          = μn ((dropThetaPrefix n) ⁻¹' ({xs} : Set (Fin n → Bool))) := by
              change Measure.map (dropThetaPrefix n) μn ({xs} : Set (Fin n → Bool)) =
                  μn ((dropThetaPrefix n) ⁻¹' ({xs} : Set (Fin n → Bool))
                )
              exact Measure.map_apply (measurable_dropThetaPrefix n) (MeasurableSet.singleton xs)
      _ = μn S := by
            simp [hpreS]
  calc
    (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 (n + 1)) (thetaToPrefix0 θ)).map
      (dropThetaPrefix (n + 1))) ({Fin.snoc xs b} : Set (Fin (n + 1) → Bool))
        = (∫⁻ x : ThetaBoolPrefix n,
            (if dropThetaPrefix n x = xs then thetaIidStep n x ({b} : Set Bool) else 0) ∂μn) := by
              simpa [μn] using hmain
    _ = (∫⁻ x : ThetaBoolPrefix n, (if dropThetaPrefix n x = xs then c else 0) ∂μn) := hcongr
    _ = c * μn S := hind
    _ = μn S * c := by simp [mul_comm]
    _ = (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
          (dropThetaPrefix n)) ({xs} : Set (Fin n → Bool)) * c := by
            simp [hmapS]
    _ = (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
          (dropThetaPrefix n)) ({xs} : Set (Fin n → Bool)) * thetaBernoulliKernel θ ({b} : Set Bool) := by
            rfl

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
  rw [lintegral_dirac' (a := thetaToPrefix0 θ) (hf := (thetaIidStep 0).measurable_coe hs)]
  show thetaBernoulliKernel (thetaFromPrefix (thetaToPrefix0 θ)) s = thetaBernoulliKernel θ s
  rw [thetaFromPrefix_thetaToPrefix0]

/-- First-coordinate cylinder evaluation for measurable sets. -/
theorem iidSequenceKernelTheta_firstCoord_apply
    (θ : LatentTheta) (s : Set Bool) (hs : MeasurableSet s) :
    iidSequenceKernelTheta θ {ω | firstCoord ω ∈ s} = thetaBernoulliKernel θ s := by
  have hmap := congrArg (fun κ => κ θ s) iidSequenceKernelTheta_map_firstCoord
  rw [ProbabilityTheory.Kernel.map_apply' _ measurable_firstCoord _ hs] at hmap
  exact hmap

/-- First-coordinate singleton-cylinder evaluation. -/
theorem iidSequenceKernelTheta_firstCoord_singleton
    (θ : LatentTheta) (b : Bool) :
    iidSequenceKernelTheta θ {ω | ω 0 = b} = thetaBernoulliKernel θ ({b} : Set Bool) := by
  simpa [firstCoord] using
    iidSequenceKernelTheta_firstCoord_apply θ ({b} : Set Bool) (by simp)

/-- Unconditional horizon-`0` prefix singleton law for `iidSequenceKernelTheta`. -/
theorem iidSequenceKernelTheta_prefix_apply_zero
    (θ : LatentTheta) (xs : Fin 0 → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent 0 xs) =
      (iidPrefixKernel 0 θ) ({xs} : Set (Fin 0 → Bool)) := by
  have hleft : iidSequenceKernelTheta θ (seqPrefixEvent 0 xs) = 1 := by
    simp [seqPrefixEvent]
  have huniv : ({xs} : Set (Fin 0 → Bool)) = Set.univ := by
    ext f
    constructor
    · intro _
      simp
    · intro _
      have hf : f = xs := by
        funext i
        exact Fin.elim0 i
      simp [hf]
  have hright : (iidPrefixKernel 0 θ) ({xs} : Set (Fin 0 → Bool)) = 1 := by
    rw [huniv]
    simp
  exact hleft.trans hright.symm

/-- Unconditional horizon-`1` prefix singleton law for `iidSequenceKernelTheta`. -/
theorem iidSequenceKernelTheta_prefix_apply_one
    (θ : LatentTheta) (xs : Fin 1 → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent 1 xs) =
      (iidPrefixKernel 1 θ) ({xs} : Set (Fin 1 → Bool)) := by
  have hset :
      seqPrefixEvent 1 xs = {ω : GlobalBinarySeq | ω 0 = xs 0} := by
    ext ω
    constructor
    · intro h
      exact h 0
    · intro h i
      have hi : i = 0 := Fin.eq_zero i
      simpa [hi] using h
  have hleft :
      iidSequenceKernelTheta θ (seqPrefixEvent 1 xs) =
        thetaBernoulliKernel θ ({xs 0} : Set Bool) := by
    rw [hset]
    simpa using iidSequenceKernelTheta_firstCoord_singleton θ (xs 0)
  have hright :
      (iidPrefixKernel 1 θ) ({xs} : Set (Fin 1 → Bool)) =
        thetaBernoulliKernel θ ({xs 0} : Set Bool) := by
    calc
      (iidPrefixKernel 1 θ) ({xs} : Set (Fin 1 → Bool))
          = (Measure.pi (fun _ : Fin 1 => thetaBernoulliKernel θ))
              ({xs} : Set (Fin 1 → Bool)) := by
                exact (iidPrefixKernel_singleton_eq_pi_thetaBernoulli θ 1 xs).symm
      _ = thetaBernoulliKernel θ ({xs 0} : Set Bool) := by
            simp
  exact hleft.trans hright.symm

/-- Recursion step for `iidSequenceKernelTheta` on singleton prefix cylinders:
appending one bit multiplies by the one-step Bernoulli factor. -/
theorem iidSequenceKernelTheta_prefix_apply_snoc
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) (b : Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent (n + 1) (Fin.snoc xs b)) =
      iidSequenceKernelTheta θ (seqPrefixEvent n xs) *
        thetaBernoulliKernel θ ({b} : Set Bool) := by
  let sn : Fin (n + 1) → Bool := Fin.snoc xs b
  have hsSucc : MeasurableSet ({sn} : Set (Fin (n + 1) → Bool)) :=
    MeasurableSet.singleton sn
  have hsPrev : MeasurableSet ({xs} : Set (Fin n → Bool)) :=
    MeasurableSet.singleton xs
  have hsetSucc :
      seqPrefixEvent (n + 1) (Fin.snoc xs b) =
        (seqPrefixProj (n + 1)) ⁻¹' ({sn} : Set (Fin (n + 1) → Bool)) := by
    simpa [sn] using seqPrefixEvent_eq_preimage_seqPrefixProj_singleton (n + 1) (Fin.snoc xs b)
  have hsetPrev :
      seqPrefixEvent n xs = (seqPrefixProj n) ⁻¹' ({xs} : Set (Fin n → Bool)) :=
    seqPrefixEvent_eq_preimage_seqPrefixProj_singleton n xs
  have hmapSucc :
      ((iidSequenceKernelTheta θ).map (seqPrefixProj (n + 1)))
          ({sn} : Set (Fin (n + 1) → Bool)) =
        (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 (n + 1)) (thetaToPrefix0 θ)).map
          (dropThetaPrefix (n + 1))) ({sn} : Set (Fin (n + 1) → Bool)) := by
    exact congrArg (fun μ : Measure (Fin (n + 1) → Bool) =>
      μ ({sn} : Set (Fin (n + 1) → Bool)))
      (iidSequenceKernelTheta_map_seqPrefixProj θ (n + 1))
  have hmapPrev :
      ((iidSequenceKernelTheta θ).map (seqPrefixProj n)) ({xs} : Set (Fin n → Bool)) =
        (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
          (dropThetaPrefix n)) ({xs} : Set (Fin n → Bool)) := by
    exact congrArg (fun μ : Measure (Fin n → Bool) => μ ({xs} : Set (Fin n → Bool)))
      (iidSequenceKernelTheta_map_seqPrefixProj θ n)
  have hprevMapApply :
      ((iidSequenceKernelTheta θ).map (seqPrefixProj n)) ({xs} : Set (Fin n → Bool)) =
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) := by
    calc
      ((iidSequenceKernelTheta θ).map (seqPrefixProj n)) ({xs} : Set (Fin n → Bool))
          = iidSequenceKernelTheta θ ((seqPrefixProj n) ⁻¹' ({xs} : Set (Fin n → Bool))) := by
              exact Measure.map_apply (measurable_seqPrefixProj n) hsPrev
      _ = iidSequenceKernelTheta θ (seqPrefixEvent n xs) := by
            simp [hsetPrev]
  calc
    iidSequenceKernelTheta θ (seqPrefixEvent (n + 1) (Fin.snoc xs b))
        = iidSequenceKernelTheta θ
            ((seqPrefixProj (n + 1)) ⁻¹' ({sn} : Set (Fin (n + 1) → Bool))) := by
              simp [hsetSucc]
    _ = ((iidSequenceKernelTheta θ).map (seqPrefixProj (n + 1)))
          ({sn} : Set (Fin (n + 1) → Bool)) := by
            symm
            exact Measure.map_apply (measurable_seqPrefixProj (n + 1)) hsSucc
    _ = (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 (n + 1)) (thetaToPrefix0 θ)).map
          (dropThetaPrefix (n + 1))) ({sn} : Set (Fin (n + 1) → Bool)) := hmapSucc
    _ = (((ProbabilityTheory.Kernel.partialTraj thetaIidStep 0 n) (thetaToPrefix0 θ)).map
          (dropThetaPrefix n)) ({xs} : Set (Fin n → Bool)) *
            thetaBernoulliKernel θ ({b} : Set Bool) := by
          simpa [sn] using partialTraj_dropThetaPrefix_map_snoc θ n xs b
    _ = ((iidSequenceKernelTheta θ).map (seqPrefixProj n)) ({xs} : Set (Fin n → Bool)) *
          thetaBernoulliKernel θ ({b} : Set Bool) := by
            rw [hmapPrev]
    _ = iidSequenceKernelTheta θ (seqPrefixEvent n xs) *
          thetaBernoulliKernel θ ({b} : Set Bool) := by
            simp [hprevMapApply]

/-- Unconditional strict prefix singleton law for `iidSequenceKernelTheta` at all
horizons. -/
theorem iidSequenceKernelTheta_prefix_apply_unconditional
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
  induction n with
  | zero =>
      exact iidSequenceKernelTheta_prefix_apply_zero θ xs
  | succ n ih =>
      let xsInit : Fin n → Bool := fun i => xs i.castSucc
      let bLast : Bool := xs (Fin.last n)
      have hsnoc : Fin.snoc xsInit bLast = xs := by
        ext i
        cases i using Fin.lastCases with
        | last =>
            simp [xsInit, bLast, Fin.snoc_last]
        | cast j =>
            simp [xsInit, bLast, Fin.snoc_castSucc]
      calc
        iidSequenceKernelTheta θ (seqPrefixEvent (n + 1) xs)
            = iidSequenceKernelTheta θ (seqPrefixEvent (n + 1) (Fin.snoc xsInit bLast)) := by
                simp [hsnoc]
        _ = iidSequenceKernelTheta θ (seqPrefixEvent n xsInit) *
              thetaBernoulliKernel θ ({bLast} : Set Bool) := by
                exact iidSequenceKernelTheta_prefix_apply_snoc θ n xsInit bLast
        _ = (iidPrefixKernel n θ) ({xsInit} : Set (Fin n → Bool)) *
              thetaBernoulliKernel θ ({bLast} : Set Bool) := by
                simpa using
                  congrArg
                    (fun t : ENNReal => t * thetaBernoulliKernel θ ({bLast} : Set Bool))
                    (ih xsInit)
        _ = (iidPrefixKernel (n + 1) θ) ({Fin.snoc xsInit bLast} : Set (Fin (n + 1) → Bool)) := by
              symm
              exact iidPrefixKernel_singleton_snoc θ n xsInit bLast
        _ = (iidPrefixKernel (n + 1) θ) ({xs} : Set (Fin (n + 1) → Bool)) := by
              simp [hsnoc]

/-- Unconditional horizon-`0` finite-prefix marginal identity. -/
theorem iidSequenceKernelTheta_map_seqPrefixProj_eq_iidPrefixKernel_zero
    (θ : LatentTheta) :
    (iidSequenceKernelTheta θ).map (seqPrefixProj 0) = iidPrefixKernel 0 θ := by
  apply Measure.ext_of_singleton
  intro xs
  have hs : MeasurableSet ({xs} : Set (Fin 0 → Bool)) := MeasurableSet.singleton xs
  have hset : seqPrefixEvent 0 xs = (seqPrefixProj 0) ⁻¹' ({xs} : Set (Fin 0 → Bool)) := by
    ext ω
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      exact congrArg (fun f : Fin 0 → Bool => f i) h
  calc
    ((iidSequenceKernelTheta θ).map (seqPrefixProj 0)) ({xs} : Set (Fin 0 → Bool))
        = iidSequenceKernelTheta θ ((seqPrefixProj 0) ⁻¹' ({xs} : Set (Fin 0 → Bool))) := by
            exact Measure.map_apply (measurable_seqPrefixProj 0) hs
    _ = iidSequenceKernelTheta θ (seqPrefixEvent 0 xs) := by simp [hset]
    _ = iidPrefixKernel 0 θ ({xs} : Set (Fin 0 → Bool)) :=
          iidSequenceKernelTheta_prefix_apply_zero θ xs

/-- Unconditional horizon-`1` finite-prefix marginal identity. -/
theorem iidSequenceKernelTheta_map_seqPrefixProj_eq_iidPrefixKernel_one
    (θ : LatentTheta) :
    (iidSequenceKernelTheta θ).map (seqPrefixProj 1) = iidPrefixKernel 1 θ := by
  apply Measure.ext_of_singleton
  intro xs
  have hs : MeasurableSet ({xs} : Set (Fin 1 → Bool)) := MeasurableSet.singleton xs
  have hset : seqPrefixEvent 1 xs = (seqPrefixProj 1) ⁻¹' ({xs} : Set (Fin 1 → Bool)) := by
    ext ω
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      exact congrArg (fun f : Fin 1 → Bool => f i) h
  calc
    ((iidSequenceKernelTheta θ).map (seqPrefixProj 1)) ({xs} : Set (Fin 1 → Bool))
        = iidSequenceKernelTheta θ ((seqPrefixProj 1) ⁻¹' ({xs} : Set (Fin 1 → Bool))) := by
            exact Measure.map_apply (measurable_seqPrefixProj 1) hs
    _ = iidSequenceKernelTheta θ (seqPrefixEvent 1 xs) := by simp [hset]
    _ = iidPrefixKernel 1 θ ({xs} : Set (Fin 1 → Bool)) :=
          iidSequenceKernelTheta_prefix_apply_one θ xs

/-- Unconditional horizon-`0` prefix-`π` marginal identity. -/
theorem iidSequenceKernelTheta_prefix_pi_marginals_zero
    (θ : LatentTheta) :
    (iidSequenceKernelTheta θ).map (seqPrefixProj 0) =
      Measure.pi (fun _ : Fin 0 => thetaBernoulliKernel θ) := by
  calc
    (iidSequenceKernelTheta θ).map (seqPrefixProj 0) = iidPrefixKernel 0 θ :=
      iidSequenceKernelTheta_map_seqPrefixProj_eq_iidPrefixKernel_zero θ
    _ = Measure.pi (fun _ : Fin 0 => thetaBernoulliKernel θ) :=
      iidPrefixKernel_eq_pi_thetaBernoulli θ 0

/-- Unconditional horizon-`1` prefix-`π` marginal identity. -/
theorem iidSequenceKernelTheta_prefix_pi_marginals_one
    (θ : LatentTheta) :
    (iidSequenceKernelTheta θ).map (seqPrefixProj 1) =
      Measure.pi (fun _ : Fin 1 => thetaBernoulliKernel θ) := by
  calc
    (iidSequenceKernelTheta θ).map (seqPrefixProj 1) = iidPrefixKernel 1 θ :=
      iidSequenceKernelTheta_map_seqPrefixProj_eq_iidPrefixKernel_one θ
    _ = Measure.pi (fun _ : Fin 1 => thetaBernoulliKernel θ) :=
      iidPrefixKernel_eq_pi_thetaBernoulli θ 1

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
  show Measure.map (finSuppPermuteSeq τ) (Exchangeability.Probability.iidProduct ν) =
    Exchangeability.Probability.iidProduct ν
  exact Exchangeability.Probability.iidProduct.perm_eq (ν := ν) (σ := τ.1.symm)

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
      rw [Measure.map_apply (measurable_finSuppPermuteSeq (finPermToFinSuppPermNat σ)) hmeas] at hmap
      exact hmap
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
    have h2 : perNPrefixDiagramMapFromGlobalLift n σ (prefixLaw (fun i ω => ω i) μ n) =
        perNPrefixDiagramMap n σ (prefixLawObjOfSeqLaw L n) := rfl
    rw [h2]; exact hperm
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
  CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of LatentTheta)

/-- `iidSequenceKernelTheta` viewed as a Kleisli morphism. -/
def iidSequenceKleisliHomTheta : KleisliLatentThetaObj ⟶ KleisliBinarySeqObj :=
  ⟨⟨fun θ => iidSequenceKernelTheta θ, iidSequenceKernelTheta.measurable⟩⟩

/-- Commutation of `iidSequenceKleisliHomTheta` with the global finitary
permutation action, derived from pointwise global finitary invariance of the
sequence laws. -/
theorem iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta := by
  intro τ
  apply kleisliHom_ext
  intro θ
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
    exact
      congrArg
        (fun h :
          KleisliLatentThetaObj ⟶ KleisliBinarySeqObj => h.1.1 θ)
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
    exact measurable_pi_apply (a := i)
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
    exact measurable_pi_apply (a := i)
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

/-- Horizon-`n` prefix evaluation for `iidSequenceKernelTheta` as a latent
integral against the canonical mediator extracted from global finitary
invariance. -/
theorem iidSequenceKernelTheta_prefix_apply_integral_of_globalFinitaryInvariance
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
hypothesis for `iidSequenceKleisliHomTheta`, via the existing mediator chain
and canonical latent-integral payload. -/
theorem iidSequenceKernelTheta_prefix_apply_integral_of_iidSequenceKleisliHomTheta_commutes
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
        (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance
          (iidSequenceKernelTheta_globalFinitaryInvariance_of_iidSequenceKleisliHomTheta_commutes
            hcommutes) θ) := by
  exact iidSequenceKernelTheta_prefix_apply_integral_of_globalFinitaryInvariance
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
    iidSequenceKernelTheta_prefix_apply_integral_of_globalFinitaryInvariance hglobal θ n xs
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

/-- Strict horizon-`n` cylinder law for `iidSequenceKernelTheta` under global
finitary invariance, with the Dirac latent representation supplied explicitly. -/
theorem iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
  exact iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance_dirac
    hglobal hrepDirac θ n xs

/-- Cone-data wrapper over the true global Kleisli(Giry) diagram. -/
structure KleisliGiryIIDConeSkeleton where
  apexObj : KleisliGiry
  iidHom : apexObj ⟶ KleisliBinarySeqObj
  commutes : ∀ τ : FinSuppPermNat,
    CategoryTheory.CategoryStruct.comp iidHom (finSuppPermKleisliHom τ) = iidHom

/-- Build a true categorical cone from iid-cone data. -/
noncomputable def KleisliGiryIIDConeSkeleton.toCone
    (cone : KleisliGiryIIDConeSkeleton) :
    CategoryTheory.Limits.Cone kleisliGiryGlobalDiagramFunctor where
  pt := cone.apexObj
  π :=
    { app := fun _ => cone.iidHom
      naturality := by
        intro j j' τ
        cases j
        cases j'
        exact (CategoryTheory.Category.id_comp _).trans (cone.commutes τ).symm }

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
  ∀ a : A.of.carrier, IsProbabilityMeasure (f.1.1 a)

/-- A cone over the global finitary diagram is Markov when its leg at the unique
index object is Markov. -/
def ConeIsMarkov
    (s : CategoryTheory.Limits.Cone kleisliGiryGlobalDiagramFunctor) : Prop :=
  KleisliIsMarkov (s.π.app globalFinSuppPermStar)

/-- View a kernel as a Kleisli(Giry) morphism. -/
def kernelToKleisliHom
    {A B : KleisliGiry}
    (κ : ProbabilityTheory.Kernel A.of.carrier B.of.carrier) :
    A ⟶ B :=
  ⟨⟨fun a => κ a, κ.measurable⟩⟩

/-- View a Kleisli(Giry) morphism as a kernel. -/
def kleisliHomToKernel
    {A B : KleisliGiry} (f : A ⟶ B) :
    ProbabilityTheory.Kernel A.of.carrier B.of.carrier where
  toFun := f.1.1
  measurable' := f.1.2

/-- A latent-kernel representation witness forces the latent kernel to be
Markov (fiberwise probability-valued). -/
theorem isMarkovKernel_of_kernelRepresentsLatentTheta
    {Y : Type} [MeasurableSpace Y]
    {κ : ProbabilityTheory.Kernel Y GlobalBinarySeq}
    [ProbabilityTheory.IsMarkovKernel κ]
    {L : ProbabilityTheory.Kernel Y LatentTheta}
    (hL : KernelRepresentsLatentTheta (X := coordProcess) κ (fun y => L y)) :
    ProbabilityTheory.IsMarkovKernel L := by
  refine ⟨?_⟩
  intro y
  rcases hL y with ⟨M, _hrep, hLy⟩
  simpa [hLy] using
    (inferInstance :
      IsProbabilityMeasure
        (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.mixingMeasureTheta M))

/-- Core bridge:
if a measurable latent kernel `L` represents `κ` and the strong IID kernel
`iidSequenceKernelTheta` has the expected horizon-prefix cylinder law, then the
Kleisli factorization equation `kernelToKleisliHom L ≫ iid = kernelToKleisliHom κ`
holds exactly. -/
theorem kernelToKleisliHom_comp_iidSequenceKleisliHomTheta_eq_of_prefixLaw_and_represents
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (L : ProbabilityTheory.Kernel Y LatentTheta)
    (hL : KernelRepresentsLatentTheta (X := coordProcess) κ (fun y => L y)) :
    CategoryTheory.CategoryStruct.comp
        (kernelToKleisliHom (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliLatentThetaObj) L)
        iidSequenceKleisliHomTheta =
      kernelToKleisliHom (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ := by
  haveI : ProbabilityTheory.IsMarkovKernel L :=
    isMarkovKernel_of_kernelRepresentsLatentTheta (κ := κ) (L := L) hL
  let κmix : ProbabilityTheory.Kernel Y GlobalBinarySeq :=
    ProbabilityTheory.Kernel.comp iidSequenceKernelTheta L
  haveI : ProbabilityTheory.IsMarkovKernel κmix := by
    dsimp [κmix]
    infer_instance
  have hμeq : ∀ y : Y, κmix y = κ y := by
    intro y
    have hfin :
        ∀ n (S : Set (Fin n → Bool)) (_hS : MeasurableSet S),
          Measure.map (Exchangeability.prefixProj (α := Bool) n) (κmix y) S =
            Measure.map (Exchangeability.prefixProj (α := Bool) n) (κ y) S := by
      intro n S hS
      have hmapEq :
          Measure.map (Exchangeability.prefixProj (α := Bool) n) (κmix y) =
            Measure.map (Exchangeability.prefixProj (α := Bool) n) (κ y) := by
        apply Measure.ext_of_singleton
        intro xs
        have hsx : MeasurableSet ({xs} : Set (Fin n → Bool)) := MeasurableSet.singleton xs
        have hset :
            seqPrefixEvent n xs =
              (Exchangeability.prefixProj (α := Bool) n) ⁻¹' ({xs} : Set (Fin n → Bool)) := by
          ext ω
          constructor
          · intro hω
            funext i
            exact hω i
          · intro hω i
            exact congrArg (fun f : Fin n → Bool => f i) hω
        have hseqMeas : MeasurableSet (seqPrefixEvent n xs) := by
          simpa [hset] using
            (Exchangeability.measurable_prefixProj (α := Bool) (n := n)) hsx
        calc
          Measure.map (Exchangeability.prefixProj (α := Bool) n) (κmix y) ({xs} : Set (Fin n → Bool))
              = κmix y ((Exchangeability.prefixProj (α := Bool) n) ⁻¹' ({xs} : Set (Fin n → Bool))) := by
                  exact Measure.map_apply
                    (Exchangeability.measurable_prefixProj (α := Bool) (n := n)) hsx
          _ = κmix y (seqPrefixEvent n xs) := by simp [hset]
          _ = ∫⁻ θ : LatentTheta, iidSequenceKernelTheta θ (seqPrefixEvent n xs) ∂(L y) := by
                simpa [κmix] using
                  (ProbabilityTheory.Kernel.comp_apply'
                    iidSequenceKernelTheta L y (s := seqPrefixEvent n xs) hseqMeas)
          _ = ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L y) := by
                refine lintegral_congr_ae ?_
                exact Filter.Eventually.of_forall (fun θ => hprefix θ n xs)
          _ = κ y (seqPrefixEvent n xs) := by
                exact (kernelRepresentsLatentTheta_coord_prefix_eq_iidPrefixKernel
                  (κ := κ) (L := fun y => L y) hL y n xs).symm
          _ = κ y ((Exchangeability.prefixProj (α := Bool) n) ⁻¹' ({xs} : Set (Fin n → Bool))) := by
                simp [hset]
          _ = Measure.map (Exchangeability.prefixProj (α := Bool) n) (κ y) ({xs} : Set (Fin n → Bool)) := by
                exact (Measure.map_apply
                  (Exchangeability.measurable_prefixProj (α := Bool) (n := n)) hsx).symm
      exact congrArg (fun μ : Measure (Fin n → Bool) => μ S) hmapEq
    exact Exchangeability.measure_eq_of_fin_marginals_eq_prob (α := Bool) hfin
  apply kleisliHom_ext
  intro y
  change Measure.bind (L y) (fun θ => iidSequenceKernelTheta θ) = κ y
  exact hμeq y

/-- Specialization of the previous bridge using a Dirac latent representation
for `iidSequenceKernelTheta`. -/
theorem kernelToKleisliHom_comp_iidSequenceKleisliHomTheta_eq_of_latentDirac_and_represents
    (hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (L : ProbabilityTheory.Kernel Y LatentTheta)
    (hL : KernelRepresentsLatentTheta (X := coordProcess) κ (fun y => L y)) :
    CategoryTheory.CategoryStruct.comp
        (kernelToKleisliHom (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliLatentThetaObj) L)
        iidSequenceKleisliHomTheta =
      kernelToKleisliHom (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ := by
  refine kernelToKleisliHom_comp_iidSequenceKleisliHomTheta_eq_of_prefixLaw_and_represents
    (κ := κ) (L := L) (hL := hL) ?_
  intro θ n xs
  exact iidSequenceKernelTheta_prefix_apply_of_latentDirac hrepDirac θ n xs

/-- Kernel-level consequence of Kleisli factorization:
for each source value and horizon, prefix-cylinder probabilities are given by
the latent integral of `iidSequenceKernelTheta`. -/
theorem kernel_prefixLaw_of_kleisliFactorization
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    (L : ProbabilityTheory.Kernel Y LatentTheta)
    (hfac :
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliLatentThetaObj) L)
          iidSequenceKleisliHomTheta =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ) :
    ∀ (y : Y) (n : ℕ) (xs : Fin n → Bool),
      κ y (seqPrefixEvent n xs) =
        ∫⁻ θ : LatentTheta, iidSequenceKernelTheta θ (seqPrefixEvent n xs) ∂(L y) := by
  intro y n xs
  have hset :
      seqPrefixEvent n xs =
        (Exchangeability.prefixProj (α := Bool) n) ⁻¹' ({xs} : Set (Fin n → Bool)) := by
    ext ω
    constructor
    · intro hω
      funext i
      exact hω i
    · intro hω i
      exact congrArg (fun f : Fin n → Bool => f i) hω
  have hseqMeas : MeasurableSet (seqPrefixEvent n xs) := by
    simpa [hset] using
      (Exchangeability.measurable_prefixProj (α := Bool) (n := n))
        (MeasurableSet.singleton xs)
  have hcomp' := congrArg (fun f => f.1.1 y) hfac
  have hbindEq : Measure.bind (L y) (fun θ => iidSequenceKernelTheta θ) = κ y := by
    exact hcomp'
  rw [← hbindEq]
  simpa using
    (Measure.bind_apply hseqMeas (ProbabilityTheory.Kernel.aemeasurable _))

/-- Factorization-to-prefix bridge at the iid-prefix layer:
if `κ = L ≫ iidSequenceKernelTheta` and `iidSequenceKernelTheta` has the
expected horizon-prefix singleton law, then `κ` satisfies the iid-prefix
mixture equations. -/
theorem kernel_prefixLaw_iidPrefix_of_kleisliFactorization
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    (L : ProbabilityTheory.Kernel Y LatentTheta)
    (hfac :
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliLatentThetaObj) L)
          iidSequenceKleisliHomTheta =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ) :
    ∀ (y : Y) (n : ℕ) (xs : Fin n → Bool),
      κ y (seqPrefixEvent n xs) =
        ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L y) := by
  intro y n xs
  calc
    κ y (seqPrefixEvent n xs)
        = ∫⁻ θ : LatentTheta, iidSequenceKernelTheta θ (seqPrefixEvent n xs) ∂(L y) :=
          kernel_prefixLaw_of_kleisliFactorization (κ := κ) (L := L) hfac y n xs
    _ = ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L y) := by
          refine lintegral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun θ => hprefix θ n xs)

/-- Bernoulli-mixture object canonically induced by a probability measure on
`Theta`. -/
noncomputable def bernoulliMixtureOfThetaMeasure
    (ν : Measure LatentTheta) [IsProbabilityMeasure ν] : BernoulliMixture where
  mixingMeasure := Measure.map (fun θ : LatentTheta => (θ : ℝ)) ν
  isProbability := by
    refine ⟨?_⟩
    rw [Measure.map_apply (by
      simpa using (measurable_subtype_coe : Measurable (fun θ : LatentTheta => (θ : ℝ))))
      MeasurableSet.univ]
    simp
  support_unit := by
    have hpre :
        (fun θ : LatentTheta => (θ : ℝ)) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ = (∅ : Set LatentTheta) := by
      ext θ
      simp [LatentTheta]
    rw [Measure.map_apply (by
      simpa using (measurable_subtype_coe : Measurable (fun θ : LatentTheta => (θ : ℝ))))
      (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.measurableSet_Icc.compl)]
    simp [hpre]

/-- The canonical Bernoulli-mixture induced by `ν : Measure Theta` recovers `ν`
after pulling back to `Theta`. -/
theorem mixingMeasureTheta_bernoulliMixtureOfThetaMeasure
    (ν : Measure LatentTheta) [IsProbabilityMeasure ν] :
    Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.mixingMeasureTheta
      (bernoulliMixtureOfThetaMeasure ν) = ν := by
  simpa [bernoulliMixtureOfThetaMeasure,
    Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.mixingMeasureTheta]
    using
      (MeasurableEmbedding.subtype_coe
        Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.measurableSet_Icc).comap_map ν

/-- For the canonical Bernoulli mixture induced by `ν : Measure Theta`,
singleton prefix masses are exactly the iid-prefix kernel integrals under `ν`. -/
theorem lintegral_iidPrefixKernel_eq_ofReal_prob_bernoulliMixtureOfThetaMeasure
    (ν : Measure LatentTheta) [IsProbabilityMeasure ν]
    (n : ℕ) (xs : Fin n → Bool) :
    ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂ν =
      ENNReal.ofReal ((bernoulliMixtureOfThetaMeasure ν).prob xs) := by
  let M : BernoulliMixture := bernoulliMixtureOfThetaMeasure ν
  have hs : MeasurableSet ({xs} : Set (Fin n → Bool)) := MeasurableSet.singleton xs
  have hflat :
      (Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten
        (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.pd M n))
          ({xs} : Set (Fin n → Bool)) =
        ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool))
          ∂(Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.mixingMeasureTheta M) := by
    simpa [iidPrefixKernel, Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.pd] using
      (Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten_apply
        (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.pd M n)
        ({xs} : Set (Fin n → Bool)) hs)
  have hsingle :
      (Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten
        (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.pd M n))
          ({xs} : Set (Fin n → Bool)) =
        ENNReal.ofReal (M.prob xs) :=
    Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.flatten_apply_singleton
      M n xs
  calc
    ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂ν
        = ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool))
            ∂(Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.mixingMeasureTheta M) := by
              simpa [M] using
                (congrArg
                  (fun μ : Measure LatentTheta =>
                    ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂μ)
                  (mixingMeasureTheta_bernoulliMixtureOfThetaMeasure (ν := ν)).symm)
    _ = (Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten
          (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.pd M n))
          ({xs} : Set (Fin n → Bool)) := hflat.symm
    _ = ENNReal.ofReal (M.prob xs) := hsingle
    _ = ENNReal.ofReal ((bernoulliMixtureOfThetaMeasure ν).prob xs) := by rfl

/-- Strict horizon-prefix equations imply that the Dirac family is a valid
latent-`Theta` representation witness for `iidSequenceKernelTheta`. -/
theorem iidSequenceKernelTheta_represents_latentDirac
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool))) :
    KernelRepresentsLatentTheta
      (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
      (κ := iidSequenceKernelTheta)
      (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)) := by
  intro θ
  let M : BernoulliMixture := bernoulliMixtureOfThetaMeasure (Measure.dirac θ)
  refine ⟨M, ?_, ?_⟩
  · intro n xs
    calc
      iidSequenceKernelTheta θ (seqPrefixEvent n xs)
          = (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) :=
            hprefix θ n xs
      _ = ENNReal.ofReal (M.prob xs) := by
            simpa [M] using
              lintegral_iidPrefixKernel_eq_ofReal_prob_bernoulliMixtureOfThetaMeasure
                (ν := (Measure.dirac θ : Measure LatentTheta)) n xs
  · simpa [M] using
      (mixingMeasureTheta_bernoulliMixtureOfThetaMeasure
        (ν := (Measure.dirac θ : Measure LatentTheta))).symm

/-- Unconditional latent-Dirac representation witness for `iidSequenceKernelTheta`
from the internally proved strict prefix law. -/
theorem iidSequenceKernelTheta_represents_latentDirac_unconditional :
    KernelRepresentsLatentTheta
      (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
      (κ := iidSequenceKernelTheta)
      (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)) := by
  exact
    iidSequenceKernelTheta_represents_latentDirac
      (hprefix := iidSequenceKernelTheta_prefix_apply_unconditional)

/-- If `iidSequenceKernelTheta` is identified pointwise with the external
`iidProduct` Bernoulli law, then the latent-Dirac family is a valid
`KernelRepresentsLatentTheta` witness. -/
theorem iidSequenceKernelTheta_represents_latentDirac_of_iidProduct_bridge
    (hbridge :
      ∀ θ : LatentTheta,
        iidSequenceKernelTheta θ =
          Exchangeability.Probability.iidProduct (thetaBernoulliKernel θ)) :
    KernelRepresentsLatentTheta
      (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
      (κ := iidSequenceKernelTheta)
      (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)) := by
  have hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
    intro θ n xs
    exact iidSequenceKernelTheta_prefix_apply_of_iidProduct_bridge hbridge θ n xs
  exact iidSequenceKernelTheta_represents_latentDirac (hprefix := hprefix)

/-- If all finite-prefix marginals of `iidSequenceKernelTheta` are Bernoulli
product measures, then the latent-Dirac family is a valid
`KernelRepresentsLatentTheta` witness. -/
theorem iidSequenceKernelTheta_represents_latentDirac_of_prefix_pi_marginals
    (hprefixPi :
      ∀ (θ : LatentTheta) (n : ℕ),
        (iidSequenceKernelTheta θ).map (seqPrefixProj n) =
          Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ)) :
    KernelRepresentsLatentTheta
      (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
      (κ := iidSequenceKernelTheta)
      (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)) := by
  exact
    iidSequenceKernelTheta_represents_latentDirac_of_iidProduct_bridge
      (iidSequenceKernelTheta_eq_iidProduct_of_prefix_pi_marginals
        (hprefix := hprefixPi))

/-- Prefix iid-mixture equations at all horizons induce a
`KernelRepresentsLatentTheta` witness. -/
theorem kernelRepresentsLatentTheta_of_kernelPrefixLaw_iidPrefix
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (L : ProbabilityTheory.Kernel Y LatentTheta)
    [ProbabilityTheory.IsMarkovKernel L]
    (hprefixLaw :
      ∀ (y : Y) (n : ℕ) (xs : Fin n → Bool),
        κ y (seqPrefixEvent n xs) =
          ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L y)) :
    KernelRepresentsLatentTheta (X := coordProcess) κ (fun y => L y) := by
  intro y
  let M : BernoulliMixture := bernoulliMixtureOfThetaMeasure (L y)
  refine ⟨M, ?_, ?_⟩
  · intro n xs
    calc
      κ y (seqPrefixEvent n xs)
          = ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L y) :=
            hprefixLaw y n xs
      _ = ENNReal.ofReal (M.prob xs) := by
            simpa [M] using
              lintegral_iidPrefixKernel_eq_ofReal_prob_bernoulliMixtureOfThetaMeasure
                (ν := L y) n xs
  · simpa [M] using
      (mixingMeasureTheta_bernoulliMixtureOfThetaMeasure (ν := L y)).symm

/-- If `κ` is Markov and factorizes through `iidSequenceKleisliHomTheta`, then
the latent kernel in the factorization is also Markov. -/
theorem isMarkovKernel_of_kleisliFactorization_targetMarkov
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (L : ProbabilityTheory.Kernel Y LatentTheta)
    (hfac :
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliLatentThetaObj) L)
          iidSequenceKleisliHomTheta =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ) :
    ProbabilityTheory.IsMarkovKernel L := by
  refine ⟨?_⟩
  intro y
  have hcomp' := congrArg (fun f => f.1.1 y) hfac
  have hbindEq : Measure.bind (L y) (fun θ => iidSequenceKernelTheta θ) = κ y := by
    exact hcomp'
  have hbind :
      (Measure.bind (L y) (fun θ => iidSequenceKernelTheta θ)) Set.univ = (L y) Set.univ := by
    calc
      (Measure.bind (L y) (fun θ => iidSequenceKernelTheta θ)) Set.univ
          = ∫⁻ θ : LatentTheta, iidSequenceKernelTheta θ Set.univ ∂(L y) := by
              exact Measure.bind_apply MeasurableSet.univ (ProbabilityTheory.Kernel.aemeasurable _)
      _ = ∫⁻ _ : LatentTheta, (1 : ENNReal) ∂(L y) := by
            refine lintegral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun θ => by simp)
      _ = (L y) Set.univ := by
            simp
  have hκ : κ y Set.univ = 1 := measure_univ
  refine ⟨?_⟩
  calc
    (L y) Set.univ = (Measure.bind (L y) (fun θ => iidSequenceKernelTheta θ)) Set.univ := hbind.symm
    _ = κ y Set.univ := by simp [hbindEq]
    _ = 1 := hκ

/-- All-sources kernel-level mediator property with measurable latent mediator
kernel output. -/
def KernelLatentThetaUniversalMediator_allSourcesKernel : Prop :=
  ∀ (Y : Type) [MeasurableSpace Y],
    ∀ (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
      [ProbabilityTheory.IsMarkovKernel κ],
      KernelExchangeable (X := coordProcess) κ →
        ∃! L : ProbabilityTheory.Kernel Y LatentTheta,
          KernelRepresentsLatentTheta (X := coordProcess) (κ := κ) (fun y => L y)

/-- All-sources kernel-level mediator property in categorical factorization
form. -/
def KernelLatentThetaUniversalMediator_allSourcesFactorization : Prop :=
  ∀ (Y : Type) [MeasurableSpace Y],
    ∀ (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
      [ProbabilityTheory.IsMarkovKernel κ],
      KernelExchangeable (X := coordProcess) κ →
        ∃! L : ProbabilityTheory.Kernel Y LatentTheta,
          CategoryTheory.CategoryStruct.comp
              (kernelToKleisliHom
                (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliLatentThetaObj) L)
              iidSequenceKleisliHomTheta =
            kernelToKleisliHom
              (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ

/-- Unrestricted all-sources kernel-level universal mediator property in
factorization form:
for every source type and every kernel whose Kleisli leg commutes with all
global finitary permutation arrows, there is a unique latent kernel whose
composition with `iidSequenceKleisliHomTheta` recovers the original leg. -/
def KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted : Prop :=
  ∀ (Y : Type) [MeasurableSpace Y],
    ∀ (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq),
      (∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp
            (kernelToKleisliHom
              (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
            (finSuppPermKleisliHom τ) =
          kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ) →
        ∃! L : ProbabilityTheory.Kernel Y LatentTheta,
          CategoryTheory.CategoryStruct.comp
              (kernelToKleisliHom
                (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliLatentThetaObj) L)
              iidSequenceKleisliHomTheta =
            kernelToKleisliHom
              (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ

/-- Commutation API for sequence-law kernels in the global finitary diagram:
package Markov-ness and full finitary-permutation commutation together. -/
def KernelCommutationAPI
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq) : Prop :=
  ProbabilityTheory.IsMarkovKernel κ ∧
    (∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
          (finSuppPermKleisliHom τ) =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)

/-- Extract Markov-ness from the packaged commutation API. -/
theorem isMarkovKernel_of_kernelCommutationAPI
    {Y : Type} [MeasurableSpace Y]
    {κ : ProbabilityTheory.Kernel Y GlobalBinarySeq}
    (hκapi : KernelCommutationAPI κ) :
    ProbabilityTheory.IsMarkovKernel κ :=
  hκapi.1

/-- Extract the raw commutation equations from the packaged commutation API. -/
theorem kernelCommutes_of_kernelCommutationAPI
    {Y : Type} [MeasurableSpace Y]
    {κ : ProbabilityTheory.Kernel Y GlobalBinarySeq}
    (hκapi : KernelCommutationAPI κ) :
    ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
          (finSuppPermKleisliHom τ) =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ :=
  hκapi.2

/-- Build the packaged commutation API from a local Markov instance plus raw
commutation equations. -/
theorem kernelCommutationAPI_of_commutes_and_isMarkov
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hcomm : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
          (finSuppPermKleisliHom τ) =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ) :
    KernelCommutationAPI (Y := Y) κ := by
  exact ⟨inferInstance, hcomm⟩

/-- Counterexample witness: the zero kernel on `PUnit` commutes with every
global finitary permutation in Kleisli(Giry). -/
theorem zeroKernel_punit_commutes_all_finsupp :
    ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of PUnit) : KleisliGiry)) (B := KleisliBinarySeqObj)
            (0 : ProbabilityTheory.Kernel PUnit GlobalBinarySeq))
          (finSuppPermKleisliHom τ) =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of PUnit) : KleisliGiry)) (B := KleisliBinarySeqObj)
          (0 : ProbabilityTheory.Kernel PUnit GlobalBinarySeq) := by
  intro τ
  apply kleisliHom_ext
  intro y
  change
    Measure.bind
      ((0 : ProbabilityTheory.Kernel PUnit GlobalBinarySeq) y)
      (fun x => Measure.dirac (finSuppPermuteSeq τ x)) =
      (0 : ProbabilityTheory.Kernel PUnit GlobalBinarySeq) y
  simp

/-- Counterexample witness: the zero kernel on `PUnit` is not Markov. -/
theorem not_isMarkovKernel_zeroKernel_punit :
    ¬ ProbabilityTheory.IsMarkovKernel
      (0 : ProbabilityTheory.Kernel PUnit GlobalBinarySeq) := by
  let κ0 : ProbabilityTheory.Kernel PUnit GlobalBinarySeq := 0
  intro hmk
  have hzero : κ0 PUnit.unit Set.univ = 0 := by simp [κ0]
  have hone : κ0 PUnit.unit Set.univ = 1 := by
    letI : ProbabilityTheory.IsMarkovKernel κ0 := by simpa [κ0] using hmk
    simpa [κ0] using (measure_univ : κ0 PUnit.unit Set.univ = 1)
  have hone' : (0 : ENNReal) = 1 := by
    rw [← hzero]
    exact hone
  exact zero_ne_one hone'

/-- `commutes ⇒ IsMarkovKernel` is false for unrestricted source kernels in
`Kleisli(MeasCat.Giry)` (measure monad): the zero-kernel commutes but is not
Markov. -/
theorem not_commutes_implies_isMarkovKernel_for_all_sources :
    ¬ (
      ∀ (Y : Type) [MeasurableSpace Y]
        (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq),
        (∀ τ : FinSuppPermNat,
          CategoryTheory.CategoryStruct.comp
              (kernelToKleisliHom
                (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
              (finSuppPermKleisliHom τ) =
            kernelToKleisliHom
              (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ) →
          ProbabilityTheory.IsMarkovKernel κ) := by
  intro hall
  let κ0 : ProbabilityTheory.Kernel PUnit GlobalBinarySeq := 0
  have hcomm :
      ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp
            (kernelToKleisliHom
              (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of PUnit) : KleisliGiry)) (B := KleisliBinarySeqObj) κ0)
            (finSuppPermKleisliHom τ) =
          kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of PUnit) : KleisliGiry)) (B := KleisliBinarySeqObj) κ0 := by
    intro τ
    apply kleisliHom_ext
    intro y
    change Measure.bind (κ0 y) (fun x => Measure.dirac (finSuppPermuteSeq τ x)) = κ0 y
    simp [κ0]
  have hmk : ProbabilityTheory.IsMarkovKernel κ0 := hall PUnit κ0 hcomm
  exact not_isMarkovKernel_zeroKernel_punit (by simpa [κ0] using hmk)

/-- Explicit strengthening used by unrestricted Giry/Kleisli export routes:
every source kernel whose Kleisli leg commutes with all global finitary
permutation arrows is required to be Markov. -/
def CommutesToMarkovBridge : Prop :=
  ∀ (Y : Type) [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq),
    (∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
          (finSuppPermKleisliHom τ) =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ) →
      ProbabilityTheory.IsMarkovKernel κ

/-- The unrestricted commutation-to-Markov bridge is refuted in
`Kleisli(MeasCat.Giry)` by the zero-kernel counterexample. -/
theorem not_commutesToMarkovBridge_unrestricted :
    ¬ CommutesToMarkovBridge := by
  simpa [CommutesToMarkovBridge] using
    not_commutes_implies_isMarkovKernel_for_all_sources

/-- Measurability-upgrade crux:
upgrade a pointwise latent mediator family `Y → Measure Theta` satisfying
`KernelRepresentsLatentTheta` to a genuine measurable kernel `Y →ₖ Theta`. -/
def KernelLatentThetaMediatorMeasurabilityUpgrade : Prop :=
  ∀ (Y : Type) [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (Lfun : Y → Measure LatentTheta),
      KernelRepresentsLatentTheta (X := coordProcess) (κ := κ) Lfun →
        ∃ L : ProbabilityTheory.Kernel Y LatentTheta, ∀ y : Y, L y = Lfun y

/-- The all-`true` finite prefix tuple. -/
private def allTruePrefix (n : ℕ) : Fin n → Bool := fun _ => true

/-- The count of `false` entries in `allTruePrefix` is `0`. -/
private lemma countFalse_allTrue (n : ℕ) :
    Mettapedia.Logic.Exchangeability.countFalse (allTruePrefix n) = 0 := by
  simp [Mettapedia.Logic.Exchangeability.countFalse, allTruePrefix]

/-- On singleton all-`true` prefixes, `iidPrefixKernel` is exactly the
`n`-th Bernoulli monomial weight. -/
private lemma iidPrefixKernel_allTrue_apply (n : ℕ) (θ : LatentTheta) :
    (iidPrefixKernel n θ) ({allTruePrefix n} : Set (Fin n → Bool)) =
      ENNReal.ofReal ((θ : ℝ) ^ n) := by
  have hfalse : Mettapedia.Logic.Exchangeability.countFalse (allTruePrefix n) = 0 :=
    countFalse_allTrue n
  have htrue : Mettapedia.Logic.Exchangeability.countTrue (allTruePrefix n) = n := by
    simp [Mettapedia.Logic.Exchangeability.countTrue, allTruePrefix]
  simp [iidPrefixKernel,
    Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel,
    Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight,
    bernoulliProductPMF_eq_power, htrue, hfalse]

/-- Countable ENNReal moment embedding candidate on latent probability measures. -/
private def thetaMomentSeq (ν : ProbabilityMeasure LatentTheta) : ℕ → ENNReal :=
  fun n => ∫⁻ θ : LatentTheta, ENNReal.ofReal ((θ : ℝ) ^ n) ∂((ν : Measure LatentTheta))

/-- Public alias of the latent ENNReal moment embedding map used in the
measurability-upgrade crux. -/
def latentThetaMomentSeq : ProbabilityMeasure LatentTheta → ℕ → ENNReal :=
  thetaMomentSeq

/-- Measurability of the countable latent moment map. -/
private theorem measurable_thetaMomentSeq : Measurable thetaMomentSeq := by
  refine measurable_pi_iff.2 (fun n => ?_)
  change Measurable (fun ν : ProbabilityMeasure LatentTheta =>
      ∫⁻ θ : LatentTheta, ENNReal.ofReal ((θ : ℝ) ^ n) ∂((ν : Measure LatentTheta)))
  refine
    (Measure.measurable_lintegral
      (f := fun θ : LatentTheta => ENNReal.ofReal ((θ : ℝ) ^ n))
      ?_).comp measurable_subtype_coe
  exact
    Measurable.ennreal_ofReal
      ((measurable_subtype_coe : Measurable (fun θ : LatentTheta => (θ : ℝ))).pow_const n)

/-- Bounded-continuous NNReal test function giving the `n`-th latent moment coordinate. -/
private def thetaMomentBCNN (n : ℕ) : BoundedContinuousFunction LatentTheta NNReal :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun θ : LatentTheta => Real.toNNReal ((θ : ℝ) ^ n),
      continuous_real_toNNReal.comp
        ((continuous_subtype_val : Continuous fun θ : LatentTheta => (θ : ℝ)).pow n)⟩

/-- The ENNReal moment coordinate agrees with integration of `thetaMomentBCNN`. -/
private lemma thetaMomentSeq_eq_lintegral_thetaMomentBCNN
    (ν : ProbabilityMeasure LatentTheta) (n : ℕ) :
    thetaMomentSeq ν n =
      ∫⁻ θ : LatentTheta, (thetaMomentBCNN n θ : ENNReal) ∂((ν : Measure LatentTheta)) := by
  unfold thetaMomentSeq thetaMomentBCNN
  apply lintegral_congr_ae
  refine Filter.Eventually.of_forall (fun θ => ?_)
  have hnonneg : 0 ≤ (θ : ℝ) ^ n := pow_nonneg θ.2.1 n
  simpa [Real.toNNReal_of_nonneg hnonneg] using (ENNReal.ofReal_eq_coe_nnreal hnonneg)

/-- Continuity of the countable latent moment map for weak convergence on
`ProbabilityMeasure LatentTheta`. -/
private theorem continuous_thetaMomentSeq :
    Continuous (fun ν : ProbabilityMeasure LatentTheta => (thetaMomentSeq ν : ℕ → ENNReal)) := by
  refine continuous_pi fun n => ?_
  have hcont :
      Continuous (fun ν : ProbabilityMeasure LatentTheta =>
        ∫⁻ θ : LatentTheta, (thetaMomentBCNN n θ : ENNReal) ∂((ν : Measure LatentTheta))) :=
    ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction (f := thetaMomentBCNN n)
  simpa [thetaMomentSeq_eq_lintegral_thetaMomentBCNN] using hcont

/-- Real moments are the `toReal` image of `thetaMomentSeq`. -/
private lemma integral_pow_eq_toReal_thetaMomentSeq
    (ν : ProbabilityMeasure LatentTheta) (n : ℕ) :
    ∫ θ : LatentTheta, (θ : ℝ) ^ n ∂((ν : Measure LatentTheta)) =
      (thetaMomentSeq ν n).toReal := by
  refine integral_eq_lintegral_of_nonneg_ae ?hf ?hfm
  · exact Filter.Eventually.of_forall (fun θ : LatentTheta => pow_nonneg θ.2.1 n)
  ·
    have hpow :
        Measurable (fun θ : LatentTheta => (θ : ℝ) ^ n) :=
      (measurable_subtype_coe : Measurable (fun θ : LatentTheta => (θ : ℝ))).pow_const n
    exact hpow.aestronglyMeasurable

/-- Hausdorff-moment injectivity of `thetaMomentSeq` on `ProbabilityMeasure Theta`. -/
private theorem thetaMomentSeq_injective : Function.Injective thetaMomentSeq := by
  intro ν1 ν2 h
  apply Subtype.ext
  change (ν1 : Measure LatentTheta) = (ν2 : Measure LatentTheta)
  apply Mettapedia.Logic.HausdorffMoment.probMeasure_unitInterval_eq_of_moments_eq
  intro n
  have hcoord : thetaMomentSeq ν1 n = thetaMomentSeq ν2 n := congrArg (fun f => f n) h
  have hcoordR : (thetaMomentSeq ν1 n).toReal = (thetaMomentSeq ν2 n).toReal :=
    congrArg ENNReal.toReal hcoord
  calc
    ∫ θ : LatentTheta, (θ : ℝ) ^ n ∂((ν1 : Measure LatentTheta))
        = (thetaMomentSeq ν1 n).toReal := integral_pow_eq_toReal_thetaMomentSeq ν1 n
    _ = (thetaMomentSeq ν2 n).toReal := hcoordR
    _ = ∫ θ : LatentTheta, (θ : ℝ) ^ n ∂((ν2 : Measure LatentTheta)) :=
          (integral_pow_eq_toReal_thetaMomentSeq ν2 n).symm

/-- Latent-theta specialization of
`borel_le_of_continuous_injective_compact_t2_measurable`: the weak Borel
σ-algebra on `ProbabilityMeasure LatentTheta` is contained in the Giry
measurable structure via the countable moment embedding. -/
theorem borel_le_inst_probabilityMeasureLatentTheta_of_moments :
    borel (ProbabilityMeasure LatentTheta) ≤
      (inferInstance : MeasurableSpace (ProbabilityMeasure LatentTheta)) := by
  exact
    borel_le_of_continuous_injective_compact_t2_measurable
      (f := fun ν : ProbabilityMeasure LatentTheta => (thetaMomentSeq ν : ℕ → ENNReal))
      continuous_thetaMomentSeq thetaMomentSeq_injective measurable_thetaMomentSeq

/-- Canonical latent-theta Borel structure on probability measures from the
moment embedding plus Portmanteau/closed-set inclusion. -/
instance latentTheta_borelSpace_probabilityMeasure_fromMoments :
    BorelSpace (ProbabilityMeasure LatentTheta) := by
  refine ⟨le_antisymm ?_ ?_⟩
  · exact instMeasurable_le_borel_probabilityMeasure (Ω := LatentTheta)
  · exact borel_le_inst_probabilityMeasureLatentTheta_of_moments

/-- If `ProbabilityMeasure LatentTheta` is standard Borel, the latent moment map is a
measurable embedding into a countable ENNReal product. -/
private theorem measurableEmbedding_thetaMomentSeq_of_standardBorel
    [StandardBorelSpace (ProbabilityMeasure LatentTheta)] :
    MeasurableEmbedding thetaMomentSeq :=
  Measurable.measurableEmbedding measurable_thetaMomentSeq thetaMomentSeq_injective

/-- Standard-Borel specialization of the public latent moment embedding alias. -/
theorem measurableEmbedding_latentThetaMomentSeq_of_standardBorel
    [StandardBorelSpace (ProbabilityMeasure LatentTheta)] :
    MeasurableEmbedding latentThetaMomentSeq := by
  simpa [latentThetaMomentSeq] using measurableEmbedding_thetaMomentSeq_of_standardBorel

/-- Local Polish structure on `ProbabilityMeasure LatentTheta` from compactness and
the Lévy-Prokhorov metrization machinery. -/
private theorem polishSpace_probabilityMeasureLatentTheta :
    PolishSpace (ProbabilityMeasure LatentTheta) := by
  -- Use the Lévy–Prokhorov metrization on a compact latent space.
  haveI : TopologicalSpace.PseudoMetrizableSpace LatentTheta := inferInstance
  haveI : TopologicalSpace.SeparableSpace LatentTheta := inferInstance
  haveI : BorelSpace LatentTheta := inferInstance
  haveI : OpensMeasurableSpace LatentTheta := inferInstance
  haveI : TopologicalSpace.MetrizableSpace (ProbabilityMeasure LatentTheta) := inferInstance
  letI : MetricSpace (ProbabilityMeasure LatentTheta) :=
    TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure LatentTheta)
  -- Compactness gives properness and hence second-countability and completeness.
  haveI : CompactSpace (ProbabilityMeasure LatentTheta) := inferInstance
  haveI : ProperSpace (ProbabilityMeasure LatentTheta) := inferInstance
  haveI : SecondCountableTopology (ProbabilityMeasure LatentTheta) := inferInstance
  haveI : CompleteSpace (ProbabilityMeasure LatentTheta) := inferInstance
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace (ProbabilityMeasure LatentTheta) := inferInstance
  infer_instance

/-- If the measurable structure on `ProbabilityMeasure LatentTheta` is Borel for the
convergence-in-distribution topology, then it is standard Borel. -/
private theorem standardBorelSpace_probabilityMeasureLatentTheta_of_borel
    [BorelSpace (ProbabilityMeasure LatentTheta)] :
    StandardBorelSpace (ProbabilityMeasure LatentTheta) := by
  letI : PolishSpace (ProbabilityMeasure LatentTheta) :=
    polishSpace_probabilityMeasureLatentTheta
  infer_instance

/-- Canonical latent-theta standard-Borel structure on probability measures,
discharged via the local moment-induced Borel instance. -/
private theorem standardBorelSpace_probabilityMeasureLatentTheta_fromMoments :
    StandardBorelSpace (ProbabilityMeasure LatentTheta) := by
  letI : BorelSpace (ProbabilityMeasure LatentTheta) :=
    latentTheta_borelSpace_probabilityMeasure_fromMoments
  exact standardBorelSpace_probabilityMeasureLatentTheta_of_borel

/-- Canonical measurable embedding of the latent moment map (no extra Borel
assumption at call sites). -/
theorem measurableEmbedding_latentThetaMomentSeq :
    MeasurableEmbedding latentThetaMomentSeq := by
  letI : StandardBorelSpace (ProbabilityMeasure LatentTheta) :=
    standardBorelSpace_probabilityMeasureLatentTheta_fromMoments
  simpa [latentThetaMomentSeq] using measurableEmbedding_thetaMomentSeq_of_standardBorel

/-- Legacy compatibility wrapper for the latent moment embedding under an explicit
`BorelSpace (ProbabilityMeasure LatentTheta)` assumption.

Migration: prefer `measurableEmbedding_latentThetaMomentSeq`, which now
discharges the required Borel/standard-Borel infrastructure canonically. -/
theorem measurableEmbedding_latentThetaMomentSeq_of_borel
    [BorelSpace (ProbabilityMeasure LatentTheta)] :
    MeasurableEmbedding latentThetaMomentSeq := by
  exact measurableEmbedding_latentThetaMomentSeq

/-- Legacy compatibility wrapper for the latent moment embedding under an explicit
`BorelSpace (FiniteMeasure LatentTheta)` bridge assumption.

Migration: prefer `measurableEmbedding_latentThetaMomentSeq`. -/
theorem measurableEmbedding_latentThetaMomentSeq_of_finiteMeasureBorel
    [BorelSpace (FiniteMeasure LatentTheta)] :
    MeasurableEmbedding latentThetaMomentSeq := by
  exact measurableEmbedding_latentThetaMomentSeq

/-- `KernelRepresentsLatentTheta` implies each latent fiber measure is a probability
measure. -/
private theorem isProbabilityMeasure_latent_of_kernelRepresents
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (Lfun : Y → Measure LatentTheta)
    (hL : KernelRepresentsLatentTheta (X := coordProcess) (κ := κ) Lfun) :
    ∀ y : Y, IsProbabilityMeasure (Lfun y) := by
  intro y
  rcases hL y with ⟨M, _hrep, hν⟩
  rw [hν]
  infer_instance

/-- Measurable kernel-derived all-`true` prefix coordinates. -/
private def kernelAllTrueMomentSeq
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq) : Y → ℕ → ENNReal :=
  fun y n => κ y (seqPrefixEvent n (allTruePrefix n))

/-- Measurability of the kernel-derived all-`true` prefix coordinates. -/
private theorem measurable_kernelAllTrueMomentSeq
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq) :
    Measurable (kernelAllTrueMomentSeq κ) := by
  refine measurable_pi_iff.2 (fun n => ?_)
  refine κ.measurable_coe ?_
  have hset :
      seqPrefixEvent n (allTruePrefix n) =
        (Exchangeability.prefixProj (α := Bool) n) ⁻¹'
          ({allTruePrefix n} : Set (Fin n → Bool)) := by
    ext ω
    constructor
    · intro hω
      funext i
      exact hω i
    · intro hω i
      exact congrArg (fun f : Fin n → Bool => f i) hω
  simpa [hset] using
    (Exchangeability.measurable_prefixProj (α := Bool) (n := n))
      (MeasurableSet.singleton (allTruePrefix n))

/-- Pointwise identification: latent moments from `Lfun` coincide with measurable
kernel-derived all-`true` prefix coordinates. -/
private theorem thetaMomentSeq_eq_kernelAllTrueMomentSeq_of_kernelRepresents
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (Lfun : Y → Measure LatentTheta)
    (hL : KernelRepresentsLatentTheta (X := coordProcess) (κ := κ) Lfun) :
    ∀ y : Y,
      thetaMomentSeq
          (⟨Lfun y,
            isProbabilityMeasure_latent_of_kernelRepresents
              (κ := κ) (Lfun := Lfun) hL y⟩ : ProbabilityMeasure LatentTheta) =
        kernelAllTrueMomentSeq κ y := by
  classical
  intro y
  funext n
  have hprefix :
      κ y (seqPrefixEvent n (allTruePrefix n)) =
        ∫⁻ θ : LatentTheta,
          (iidPrefixKernel n θ) ({allTruePrefix n} : Set (Fin n → Bool)) ∂(Lfun y) :=
    kernelRepresentsLatentTheta_coord_prefix_eq_iidPrefixKernel
      (κ := κ) (L := Lfun) hL y n (allTruePrefix n)
  calc
    thetaMomentSeq
        (⟨Lfun y,
          isProbabilityMeasure_latent_of_kernelRepresents
            (κ := κ) (Lfun := Lfun) hL y⟩ : ProbabilityMeasure LatentTheta) n
        = ∫⁻ θ : LatentTheta,
            (iidPrefixKernel n θ) ({allTruePrefix n} : Set (Fin n → Bool)) ∂(Lfun y) := by
              refine lintegral_congr_ae ?_
              exact Filter.Eventually.of_forall (fun θ => (iidPrefixKernel_allTrue_apply n θ).symm)
    _ = κ y (seqPrefixEvent n (allTruePrefix n)) := hprefix.symm
    _ = kernelAllTrueMomentSeq κ y n := rfl

/-- Measurability upgrade from a measurable latent moment embedding:
if the countable latent moment map is a measurable embedding, then any
pointwise latent mediator family `Lfun` is automatically measurable. -/
theorem kernelLatentThetaMediatorMeasurabilityUpgrade_of_thetaMomentEmbedding
    (hEmb : MeasurableEmbedding thetaMomentSeq) :
    KernelLatentThetaMediatorMeasurabilityUpgrade := by
  intro Y _ κ _ Lfun hL
  let θ0 : LatentTheta := ⟨0, by constructor <;> simp⟩
  haveI : Nonempty (ProbabilityMeasure LatentTheta) :=
    ⟨⟨Measure.dirac θ0, inferInstance⟩⟩
  letI : ∀ y : Y, IsProbabilityMeasure (Lfun y) :=
    isProbabilityMeasure_latent_of_kernelRepresents (κ := κ) (Lfun := Lfun) hL
  let Lprob : Y → ProbabilityMeasure LatentTheta := fun y => ⟨Lfun y, inferInstance⟩
  let mκ : Y → ℕ → ENNReal := kernelAllTrueMomentSeq κ
  have hmκ : Measurable mκ := measurable_kernelAllTrueMomentSeq (κ := κ)
  have hIdMom : ∀ y : Y, thetaMomentSeq (Lprob y) = mκ y := by
    intro y
    simpa [Lprob, mκ] using
      thetaMomentSeq_eq_kernelAllTrueMomentSeq_of_kernelRepresents
        (κ := κ) (Lfun := Lfun) hL y
  have hLprobEq : Lprob = fun y => hEmb.invFun (mκ y) := by
    funext y
    calc
      Lprob y = hEmb.invFun (thetaMomentSeq (Lprob y)) := (hEmb.leftInverse_invFun (Lprob y)).symm
      _ = hEmb.invFun (mκ y) := by rw [hIdMom y]
  have hLprobMeas : Measurable Lprob := by
    rw [hLprobEq]
    exact hEmb.measurable_invFun.comp hmκ
  have hLfunMeas : Measurable Lfun := measurable_subtype_coe.comp hLprobMeas
  refine ⟨⟨Lfun, hLfunMeas⟩, ?_⟩
  intro y
  rfl

/-- Standard-Borel corollary: if `ProbabilityMeasure LatentTheta` is standard Borel,
the measurable-upgrade crux follows via the latent moment embedding. -/
theorem kernelLatentThetaMediatorMeasurabilityUpgrade_of_standardBorel
    [StandardBorelSpace (ProbabilityMeasure LatentTheta)] :
    KernelLatentThetaMediatorMeasurabilityUpgrade :=
  kernelLatentThetaMediatorMeasurabilityUpgrade_of_thetaMomentEmbedding
    (hEmb := measurableEmbedding_thetaMomentSeq_of_standardBorel)

/-- Discrete-source measurable-upgrade lemma:
on a discrete source measurable space, any function `Y → Measure Theta` is
measurable, hence any pointwise latent mediator family upgrades to a kernel. -/
theorem kernelLatentThetaMediatorMeasurabilityUpgrade_of_discrete
    (Y : Type) [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (Lfun : Y → Measure LatentTheta)
    (_hL : KernelRepresentsLatentTheta (X := coordProcess) (κ := κ) Lfun) :
    ∃ L : ProbabilityTheory.Kernel Y LatentTheta, ∀ y : Y, L y = Lfun y := by
  refine ⟨⟨Lfun, ?_⟩, ?_⟩
  · simpa using (Measurable.of_discrete (f := Lfun))
  · intro y
    rfl

/-- Discrete-source all-sources kernel mediator bridge:
from the default qualitative all-sources witness, recover measurable latent
kernels on any discrete source measurable space. -/
theorem allSourcesKernel_discrete_of_allSourcesDefault
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (Y : Type) [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hκexch : KernelExchangeable (X := coordProcess) κ) :
    ∃! L : ProbabilityTheory.Kernel Y LatentTheta,
      KernelRepresentsLatentTheta (X := coordProcess) (κ := κ) (fun y => L y) := by
  have hX : ∀ i : ℕ, Measurable (coordProcess i) := by
    intro i
    exact measurable_pi_apply (a := i)
  rcases (hunivDefault Y) hX κ hκexch with ⟨Lfun, hLfunRep, hLfunUniq⟩
  rcases
      kernelLatentThetaMediatorMeasurabilityUpgrade_of_discrete
        Y κ Lfun hLfunRep with ⟨L, hLeq⟩
  refine ⟨L, ?_, ?_⟩
  · intro y
    simpa [hLeq y] using hLfunRep y
  · intro L' hL'rep
    have hEqFun : (fun y => L' y) = Lfun :=
      hLfunUniq (fun y => L' y) (by intro y; exact hL'rep y)
    apply ProbabilityTheory.Kernel.ext
    intro y
    simpa [hLeq y] using congrArg (fun F => F y) hEqFun

/-- Lift the default all-sources qualitative de Finetti witness to the measurable
kernel-level all-sources mediator API, assuming the measurability-upgrade crux. -/
theorem allSourcesKernel_of_allSourcesDefault_and_measurabilityUpgrade
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hupgrade : KernelLatentThetaMediatorMeasurabilityUpgrade) :
    KernelLatentThetaUniversalMediator_allSourcesKernel := by
  intro (Y : Type) _ κ _ hκexch
  have hX : ∀ i : ℕ, Measurable (coordProcess i) := by
    intro i
    exact measurable_pi_apply (a := i)
  have hunivY := hunivDefault Y
  rcases hunivY hX κ hκexch with ⟨Lfun, hLfunRep, hLfunUniq⟩
  rcases hupgrade Y κ Lfun hLfunRep with ⟨L, hLeq⟩
  refine ⟨L, ?_, ?_⟩
  · intro y
    simpa [hLeq y] using hLfunRep y
  · intro L' hL'rep
    have hEqFun : (fun y => L' y) = Lfun :=
      hLfunUniq (fun y => L' y) (by intro y; exact hL'rep y)
    apply ProbabilityTheory.Kernel.ext
    intro y
    simpa [hLeq y] using congrArg (fun F => F y) hEqFun

/-- The default all-sources qualitative de Finetti witness, specialized as a
`Type`-indexed family usable by kernel-level bridge theorems in this file. -/
theorem kernelLatentThetaUniversalMediator_default_typeFamily
    (Y' : Type) [MeasurableSpace Y'] :
    KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess := by
  exact
    kernelLatentThetaUniversalMediator_allSources_default
      (Ω := GlobalBinarySeq) coordProcess (Y' := Y')

/-- Markov-only universal mediator property for a global iid-cone skeleton. -/
def GlobalIIDConeMediatorUnique_markovOnly
    (cone : KleisliGiryIIDConeSkeleton) : Prop :=
  ∀ s : CategoryTheory.Limits.Cone kleisliGiryGlobalDiagramFunctor,
    ConeIsMarkov s →
      ∃! m : s.pt ⟶ cone.apexObj,
        CategoryTheory.CategoryStruct.comp m cone.iidHom = s.π.app globalFinSuppPermStar

/-- All-sources Kleisli mediator property (Markov-only):
for every source object and every Markov cone-leg into `Bool^ℕ` that commutes
with all finitary permutation arrows, there exists a unique Kleisli mediator
through `iidSequenceKleisliHomTheta`. -/
def KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly : Prop :=
  ∀ (A : KleisliGiry),
    ∀ (κhom : A ⟶ KleisliBinarySeqObj),
      KleisliIsMarkov κhom →
      (∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp κhom (finSuppPermKleisliHom τ) = κhom) →
      ∃! m : A ⟶ KleisliLatentThetaObj,
        CategoryTheory.CategoryStruct.comp m iidSequenceKleisliHomTheta = κhom

/-- All-sources Kleisli mediator property (unrestricted):
for every source object and every commuting cone-leg into `Bool^ℕ`, there exists
a unique Kleisli mediator through `iidSequenceKleisliHomTheta`.

This is exactly the shape needed to derive full `GlobalIIDConeMediatorUnique`
and hence `Nonempty IsLimit` for the iid cone skeleton. -/
def KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted : Prop :=
  ∀ (A : KleisliGiry),
    ∀ (κhom : A ⟶ KleisliBinarySeqObj),
      (∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp κhom (finSuppPermKleisliHom τ) = κhom) →
      ∃! m : A ⟶ KleisliLatentThetaObj,
        CategoryTheory.CategoryStruct.comp m iidSequenceKleisliHomTheta = κhom

/-- Hard-step target strengthening candidate:
derive unrestricted all-sources Kleisli universality directly from global
finitary invariance and the default all-sources qualitative witness, without an
explicit `CommutesToMarkovBridge` assumption. -/
def DefaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening : Prop :=
  ∀ (_hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess),
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted

/-- A Kleisli morphism has finite mass when all fibers have finite total mass. -/
def KleisliIsFiniteMass {A B : KleisliGiry} (f : A ⟶ B) : Prop :=
  ∀ a : A.of.carrier, (kleisliHomToKernel f) a Set.univ < ⊤

/-- All-sources Kleisli mediator property (finite-mass):
for every source object and every finite-mass cone-leg into `Bool^ℕ` that commutes
with all finitary permutation arrows, there exists a unique Kleisli mediator
through `iidSequenceKleisliHomTheta`.

This is the corrected strengthening target: the unrestricted version
(`KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted`) is false
(counting-measure counterexample), but the finite-mass restriction is equivalent
to the fully-proven Markov-only version. -/
def KernelLatentThetaUniversalMediator_allSourcesKleisli_finiteMass : Prop :=
  ∀ (A : KleisliGiry),
    ∀ (κhom : A ⟶ KleisliBinarySeqObj),
      KleisliIsFiniteMass κhom →
      (∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp κhom (finSuppPermKleisliHom τ) = κhom) →
      ∃! m : A ⟶ KleisliLatentThetaObj,
        CategoryTheory.CategoryStruct.comp m iidSequenceKleisliHomTheta = κhom

theorem kleisliIsFiniteMass_of_kleisliIsMarkov
    {A B : KleisliGiry} (f : A ⟶ B) (hm : KleisliIsMarkov f) :
    KleisliIsFiniteMass f := by
  intro a; have := hm a; simp [kleisliHomToKernel]

/-- Markov-only universality trivially implies finite-mass universality
(every Markov morphism has finite mass). -/
theorem allSourcesKleisli_markovOnly_of_finiteMass
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_finiteMass) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly := by
  intro A κhom hmarkov hcomm
  exact huniv A κhom (kleisliIsFiniteMass_of_kleisliIsMarkov κhom hmarkov) hcomm

private theorem bind_iidSequenceKernelTheta_totalMass_eq
    (μ : Measure LatentTheta) :
    (Measure.bind μ (fun θ => iidSequenceKernelTheta θ)) Set.univ = μ Set.univ := by
  by_cases hμ : μ = 0
  · simp [hμ, Measure.bind_zero_left]
  · rw [Measure.bind_apply MeasurableSet.univ
      (ProbabilityTheory.Kernel.aemeasurable iidSequenceKernelTheta)]
    calc
      ∫⁻ θ : LatentTheta, iidSequenceKernelTheta θ Set.univ ∂μ
          = ∫⁻ _ : LatentTheta, (1 : ENNReal) ∂μ := by
            refine lintegral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun θ => by simp)
      _ = μ Set.univ := by simp

private theorem smul_inv_smul_measure' {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : ENNReal) (hc_pos : c ≠ 0) (hc_fin : c ≠ ⊤) :
    c • (c⁻¹ • μ) = μ := by
  ext s _
  simp [Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hc_pos hc_fin]

private theorem measurable_piecewise_measure {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (f g : α → Measure β) (p : α → Prop) [DecidablePred p]
    (hp : MeasurableSet {a | p a})
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => if p a then f a else g a) := by
  rw [Measure.measurable_measure]
  intro s hs
  have : (fun a => (if p a then f a else g a) s)
      = fun a => if p a then (f a) s else (g a) s := by
    ext a; split <;> rfl
  rw [this]
  exact Measurable.ite hp
    ((Measure.measurable_measure.mp hf) s hs)
    ((Measure.measurable_measure.mp hg) s hs)

private theorem measurable_smul_measure {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (f : α → Measure β) (g : α → ENNReal)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => g a • f a) := by
  rw [Measure.measurable_measure]
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul]
  exact hg.mul ((Measure.measurable_measure.mp hf) s hs)

/-- Factorization equation at a point for Kleisli composition through iid. -/
private theorem kleisli_iid_fac_at {A : KleisliGiry}
    (f : A ⟶ KleisliLatentThetaObj) (a : A.of.carrier) :
    (CategoryTheory.CategoryStruct.comp f iidSequenceKleisliHomTheta).1.1 a =
      ((kleisliHomToKernel f) a).bind (fun θ => iidSequenceKernelTheta θ) := by
  rfl

/-- Finite-mass universality follows from Markov-only universality by
pointwise scaling: normalize each fiber to probability, apply the Markov-only
chain, and scale the mediator back up. -/
theorem allSourcesKleisli_finiteMass_of_allSourcesKleisli_markovOnly
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_finiteMass := by
  intro A κhom hfin hκcomm
  -- ===== Setup =====
  let κ := kleisliHomToKernel κhom
  let θ₀ : LatentTheta := ⟨1/2, by norm_num, by norm_num⟩
  let c : A.of.carrier → ENNReal := fun a => κ a Set.univ
  have hc_fin : ∀ a, c a < ⊤ := hfin
  have hc_ne_top : ∀ a, c a ≠ ⊤ := fun a => ne_top_of_lt (hc_fin a)
  have hc_meas : Measurable c :=
    (Measure.measurable_measure.mp κ.measurable) Set.univ MeasurableSet.univ
  have hp_zero : MeasurableSet {a : A.of.carrier | c a = 0} :=
    hc_meas (measurableSet_singleton 0)
  -- Fiber permutation invariance
  have hfiber_perm : ∀ a τ, (κ a).map (finSuppPermuteSeq τ) = κ a := by
    intro a τ
    have ha : (CategoryTheory.CategoryStruct.comp κhom (finSuppPermKleisliHom τ)).1 a = κhom.1 a :=
      congrFun (congrArg (fun k => k.1.1) (hκcomm τ)) a
    simp only [κ, kleisliHomToKernel]
    change (κhom.1 a).map (finSuppPermuteSeq τ) = κhom.1 a
    have : (CategoryTheory.CategoryStruct.comp κhom (finSuppPermKleisliHom τ)).1 a =
        (κhom.1 a).bind (fun ω => Measure.dirac (finSuppPermuteSeq τ ω)) := rfl
    rw [this, Measure.bind_dirac_eq_map _ (measurable_finSuppPermuteSeq τ)] at ha
    exact ha
  -- ===== Normalized morphism =====
  haveI hdec_c : DecidablePred (fun a : A.of.carrier => c a = 0) := fun a => Classical.dec _
  let κ_norm_fn : A.of.carrier → Measure GlobalBinarySeq :=
    fun a => if c a = 0 then iidSequenceKernelTheta θ₀ else (c a)⁻¹ • κ a
  have hκ_norm_meas : Measurable κ_norm_fn :=
    measurable_piecewise_measure _ _ (fun a => c a = 0) hp_zero
      measurable_const (measurable_smul_measure _ _ κ.measurable hc_meas.inv)
  have hκ_norm_prob : ∀ a, IsProbabilityMeasure (κ_norm_fn a) := by
    intro a; simp only [κ_norm_fn]; split
    · exact ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure
        (κ := iidSequenceKernelTheta) θ₀
    · rename_i h
      exact ⟨by simp only [Measure.smul_apply, smul_eq_mul]
              ; exact ENNReal.inv_mul_cancel h (hc_ne_top a)⟩
  let κ_norm_hom : A ⟶ KleisliBinarySeqObj := ⟨⟨κ_norm_fn, hκ_norm_meas⟩⟩
  have hκ_norm_comm : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp κ_norm_hom (finSuppPermKleisliHom τ) = κ_norm_hom := by
    intro τ; apply kleisliHom_ext; intro a
    show (κ_norm_fn a).bind (fun ω => Measure.dirac (finSuppPermuteSeq τ ω)) = κ_norm_fn a
    rw [Measure.bind_dirac_eq_map _ (measurable_finSuppPermuteSeq τ)]
    simp only [κ_norm_fn]; split
    · exact hglobal θ₀ τ
    · rw [Measure.map_smul, hfiber_perm a τ]
  -- ===== Apply Markov universality =====
  rcases huniv A κ_norm_hom (fun a => hκ_norm_prob a) hκ_norm_comm with
    ⟨m_norm, hm_norm_fac, hm_norm_uniq⟩
  let L_norm := kleisliHomToKernel m_norm
  have hm_norm_fac_pt : ∀ a,
      (L_norm a).bind (fun θ => iidSequenceKernelTheta θ) = κ_norm_fn a := by
    intro a
    have := congrFun (congrArg (fun k => k.1.1) hm_norm_fac) a
    exact this
  -- ===== Scaled mediator =====
  have hm_meas : Measurable (fun a => c a • L_norm a) :=
    measurable_smul_measure _ _ L_norm.measurable hc_meas
  let m : A ⟶ KleisliLatentThetaObj :=
    kernelToKleisliHom
      { toFun := fun a => c a • L_norm a
        measurable' := hm_meas }
  -- ===== Factorization =====
  have hm_fac : CategoryTheory.CategoryStruct.comp m iidSequenceKleisliHomTheta = κhom := by
    apply kleisliHom_ext; intro a
    -- LHS: bind (c a • L_norm a) iid
    have hlhs : (CategoryTheory.CategoryStruct.comp m iidSequenceKleisliHomTheta).1.1 a =
        (c a • L_norm a).bind (fun θ => iidSequenceKernelTheta θ) :=
      kleisli_iid_fac_at m a
    rw [hlhs]
    -- = c a • bind (L_norm a) iid
    rw [Measure.comp_smul .., hm_norm_fac_pt a]
    -- = c a • κ_norm_fn a = κhom.1 a
    simp only [κ_norm_fn]
    split
    · -- c a = 0
      rename_i hca0
      have hκ_zero : κ a = 0 := Measure.measure_univ_eq_zero.mp hca0
      simp only [hca0, zero_smul]
      exact hκ_zero.symm
    · -- c a > 0: c • c⁻¹ • μ = μ
      rename_i hca_ne0
      show c a • ((c a)⁻¹ • κ a) = κhom.1.1 a
      have : c a • ((c a)⁻¹ • κ a) = κ a :=
        smul_inv_smul_measure' (κ a) (c a) hca_ne0 (hc_ne_top a)
      rw [this]; rfl
  -- ===== Uniqueness =====
  have hm_uniq : ∀ m' : A ⟶ KleisliLatentThetaObj,
      CategoryTheory.CategoryStruct.comp m' iidSequenceKleisliHomTheta = κhom → m' = m := by
    intro m' hm'_fac
    let L' := kleisliHomToKernel m'
    -- Pointwise bind factorization
    have hm'_bind : ∀ a,
        (L' a).bind (fun θ => iidSequenceKernelTheta θ) = κ a := by
      intro a
      have := congrFun (congrArg (fun k => k.1.1) hm'_fac) a
      exact this
    -- Total mass transfer
    have hm'_mass : ∀ a, (L' a) Set.univ = c a := by
      intro a
      rw [← bind_iidSequenceKernelTheta_totalMass_eq (L' a), hm'_bind a]
    -- Construct normalized m'
    let m'_norm_fn : A.of.carrier → Measure LatentTheta :=
      fun b => if c b = 0 then L_norm b else (c b)⁻¹ • L' b
    have hm'_norm_meas : Measurable m'_norm_fn :=
      measurable_piecewise_measure _ _ (fun b => c b = 0) hp_zero
        L_norm.measurable (measurable_smul_measure _ _ L'.measurable hc_meas.inv)
    let m'_norm : A ⟶ KleisliLatentThetaObj :=
      kernelToKleisliHom ⟨m'_norm_fn, hm'_norm_meas⟩
    -- m'_norm factors κ_norm_hom
    have hm'_norm_fac : CategoryTheory.CategoryStruct.comp m'_norm
        iidSequenceKleisliHomTheta = κ_norm_hom := by
      apply kleisliHom_ext; intro b
      have hlhs : (CategoryTheory.CategoryStruct.comp m'_norm iidSequenceKleisliHomTheta).1.1 b =
          (m'_norm_fn b).bind (fun θ => iidSequenceKernelTheta θ) :=
        kleisli_iid_fac_at m'_norm b
      rw [hlhs]
      show (m'_norm_fn b).bind (fun θ => iidSequenceKernelTheta θ) = κ_norm_fn b
      simp only [m'_norm_fn]; split
      · exact hm_norm_fac_pt b
      · rename_i hcb_ne0
        rw [Measure.comp_smul .., hm'_bind b]
        show (c b)⁻¹ • κ b = κ_norm_fn b
        simp only [κ_norm_fn, hcb_ne0, ↓reduceIte]
    -- Uniqueness: m'_norm = m_norm
    have h_eq : m'_norm = m_norm := hm_norm_uniq m'_norm hm'_norm_fac
    -- Extract pointwise equality
    apply kleisliHom_ext; intro a
    by_cases hca0 : c a = 0
    · -- c a = 0: L' a = 0 and c a • L_norm a = 0
      have hL'_zero : L' a = 0 :=
        Measure.measure_univ_eq_zero.mp (by rw [hm'_mass a, hca0])
      show m'.1.1 a = m.1.1 a
      have hm_a : m.1.1 a = (0 : Measure LatentTheta) := by
        show c a • L_norm a = 0; rw [hca0, zero_smul]
      rw [hm_a]
      change L' a = 0
      exact hL'_zero
    · -- c a > 0: from m'_norm = m_norm, extract (c a)⁻¹ • L' a = L_norm a
      have h_eq_a : m'_norm_fn a = L_norm a := by
        have h := congrFun (congrArg (fun k => k.1.1) h_eq) a
        exact h
      -- m'_norm_fn a = (c a)⁻¹ • L' a (since c a ≠ 0)
      have h_m'_norm_val : m'_norm_fn a = (c a)⁻¹ • L' a := by
        simp [m'_norm_fn, hca0]
      rw [h_m'_norm_val] at h_eq_a
      -- L' a = c a • L_norm a
      show m'.1.1 a = m.1.1 a
      have hL'_eq : L' a = c a • L_norm a := by
        calc L' a = c a • ((c a)⁻¹ • L' a) :=
              (smul_inv_smul_measure' (L' a) (c a) hca0 (hc_ne_top a)).symm
          _ = c a • L_norm a := by rw [h_eq_a]
      simp only [m, kernelToKleisliHom, L', kleisliHomToKernel] at hL'_eq ⊢
      exact hL'_eq
  exact ⟨m, hm_fac, hm_uniq⟩

/-- Finite-mass universality is equivalent to Markov-only universality
(given global finitary invariance of iid). -/
theorem allSourcesKleisli_finiteMass_iff_markovOnly
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_finiteMass ↔
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly :=
  ⟨allSourcesKleisli_markovOnly_of_finiteMass,
   fun h => allSourcesKleisli_finiteMass_of_allSourcesKleisli_markovOnly h hglobal⟩

/-- A cone in the global finitary diagram has finite mass when its canonical
leg into `Bool^ℕ` is a finite-mass Kleisli morphism. -/
def ConeIsFiniteMass
    (s : CategoryTheory.Limits.Cone kleisliGiryGlobalDiagramFunctor) : Prop :=
  KleisliIsFiniteMass (s.π.app globalFinSuppPermStar)

/-- Markov cones have finite mass. -/
theorem coneIsFiniteMass_of_coneIsMarkov
    (s : CategoryTheory.Limits.Cone kleisliGiryGlobalDiagramFunctor)
    (hm : ConeIsMarkov s) : ConeIsFiniteMass s :=
  kleisliIsFiniteMass_of_kleisliIsMarkov _ hm

/-- Finite-mass cone-level mediator uniqueness for a global iid-cone skeleton. -/
def GlobalIIDConeMediatorUnique_finiteMass
    (cone : KleisliGiryIIDConeSkeleton) : Prop :=
  ∀ s : CategoryTheory.Limits.Cone kleisliGiryGlobalDiagramFunctor,
    ConeIsFiniteMass s →
      ∃! m : s.pt ⟶ cone.apexObj,
        CategoryTheory.CategoryStruct.comp m cone.iidHom = s.π.app globalFinSuppPermStar

/-- Markov-only cone universality implies finite-mass cone universality. -/
theorem globalIIDConeMediatorUnique_markovOnly_of_finiteMass
    (cone : KleisliGiryIIDConeSkeleton)
    (hfm : GlobalIIDConeMediatorUnique_finiteMass cone) :
    GlobalIIDConeMediatorUnique_markovOnly cone := by
  intro s hs
  exact hfm s (coneIsFiniteMass_of_coneIsMarkov s hs)

-- Specialized cone-level finite-mass ↔ Markov-only theorems are defined later
-- (after `iidSequenceKleisliConeSkeleton`) as:
-- `globalIIDConeMediatorUnique_finiteMass_of_allSourcesKleisli_finiteMass`
-- `globalIIDConeMediatorUnique_finiteMass_iff_markovOnly`

/-- Canonical measurable latent-kernel constructor from unrestricted
all-sources kernel-level factorization witnesses. -/
noncomputable def latentKernelOf_allSourcesKernelFactorization_unrestricted
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted)
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    (hcomm : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
          (finSuppPermKleisliHom τ) =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ) :
    ProbabilityTheory.Kernel Y LatentTheta :=
  Classical.choose (huniv Y κ hcomm)

/-- Factorization equation satisfied by the canonical latent-kernel constructor. -/
theorem latentKernelOf_allSourcesKernelFactorization_unrestricted_factorizes
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted)
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    (hcomm : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
          (finSuppPermKleisliHom τ) =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ) :
    CategoryTheory.CategoryStruct.comp
        (kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliLatentThetaObj)
          (latentKernelOf_allSourcesKernelFactorization_unrestricted
            (huniv := huniv) (κ := κ) hcomm))
        iidSequenceKleisliHomTheta =
      kernelToKleisliHom
        (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ :=
  (Classical.choose_spec (huniv Y κ hcomm)).1

/-- Uniqueness of the canonical latent-kernel constructor among kernels with the
same Kleisli factorization equation. -/
theorem latentKernelOf_allSourcesKernelFactorization_unrestricted_unique
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted)
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    (hcomm : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
          (finSuppPermKleisliHom τ) =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
    (L : ProbabilityTheory.Kernel Y LatentTheta)
    (hL :
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliLatentThetaObj) L)
          iidSequenceKleisliHomTheta =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ) :
    L =
      latentKernelOf_allSourcesKernelFactorization_unrestricted
        (huniv := huniv) (κ := κ) hcomm :=
  (Classical.choose_spec (huniv Y κ hcomm)).2 L hL

/-- Bridge: unrestricted all-sources kernel-level factorization implies
unrestricted all-sources Kleisli universality. -/
theorem allSourcesKleisli_unrestricted_of_allSourcesKernelFactorization_unrestricted
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  intro A κhom hκcomm
  let κ : ProbabilityTheory.Kernel A.of.carrier GlobalBinarySeq := kleisliHomToKernel κhom
  have hκcomm' :
      ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp
            (kernelToKleisliHom (A := A) (B := KleisliBinarySeqObj) κ)
            (finSuppPermKleisliHom τ) =
          kernelToKleisliHom (A := A) (B := KleisliBinarySeqObj) κ := by
    intro τ
    exact hκcomm τ
  let L : ProbabilityTheory.Kernel A.of.carrier LatentTheta :=
    latentKernelOf_allSourcesKernelFactorization_unrestricted
      (huniv := huniv) (Y := A.of.carrier) (κ := κ) hκcomm'
  refine ⟨kernelToKleisliHom (A := A) (B := KleisliLatentThetaObj) L, ?_, ?_⟩
  · have hfac :
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom (A := A) (B := KleisliLatentThetaObj) L)
          iidSequenceKleisliHomTheta =
        kernelToKleisliHom (A := A) (B := KleisliBinarySeqObj) κ := by
      simpa [L] using
        latentKernelOf_allSourcesKernelFactorization_unrestricted_factorizes
          (huniv := huniv) (Y := A.of.carrier) (κ := κ) hκcomm'
    exact hfac
  · intro m hm
    let K : ProbabilityTheory.Kernel A.of.carrier LatentTheta := kleisliHomToKernel m
    have hfacK :
        CategoryTheory.CategoryStruct.comp
            (kernelToKleisliHom (A := A) (B := KleisliLatentThetaObj) K)
            iidSequenceKleisliHomTheta =
          kernelToKleisliHom (A := A) (B := KleisliBinarySeqObj) κ := by
      exact hm
    have hKL : K = L := by
      exact
        latentKernelOf_allSourcesKernelFactorization_unrestricted_unique
          (huniv := huniv) (Y := A.of.carrier) (κ := κ) hκcomm' K hfacK
    apply kleisliHom_ext
    intro y
    exact congrArg (fun K' => K' y) hKL

/-- A commuting Kleisli arrow into `Bool^ℕ` induces a kernel-level coordinate
exchangeability witness. -/
theorem kernelExchangeable_coord_of_kleisliCommutes
    {Y : Type} [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hcomm : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp
          (kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
          (finSuppPermKleisliHom τ) =
        kernelToKleisliHom
          (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ) :
    KernelExchangeable (X := coordProcess) κ := by
  have hglob : KernelGlobalFinitarySeqConeCommutes (Y := Y) κ := by
    intro y τ
    have hbind :
        Measure.bind (κ y) (fun x => Measure.dirac (finSuppPermuteSeq τ x)) = κ y := by
      have hcomp := hcomm τ
      have hcomp' := congrArg (fun f => f.1.1 y) hcomp
      exact hcomp'
    calc
      (κ y).map (finSuppPermuteSeq τ) =
          Measure.bind (κ y) (fun x => Measure.dirac (finSuppPermuteSeq τ x)) := by
            simpa using
              (Measure.bind_dirac_eq_map
                (m := κ y)
                (hf := measurable_finSuppPermuteSeq τ)).symm
      _ = κ y := hbind
  have hprefix : KernelPrefixCone (X := coordProcess) κ :=
    kernelGlobalFinitarySeqConeCommutes_imp_kernelPrefixCone_coord (κ := κ) hglob
  exact (kernelExchangeable_iff_kernelPrefixCone (X := coordProcess) (κ := κ)).2 hprefix

/-- Main all-sources bridge:
if commuting legs are known Markov, and one has all-sources kernel-level
latent representation witnesses together with the iid-prefix law for
`iidSequenceKernelTheta`, then unrestricted all-sources kernel factorization
follows. -/
theorem allSourcesKernelFactorization_unrestricted_of_allSourcesKernel_and_prefixLaw
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted := by
  intro Y _ κ hcomm
  letI : ProbabilityTheory.IsMarkovKernel κ := hmarkov_of_commutes Y κ hcomm
  have hκapi : KernelCommutationAPI (Y := Y) κ :=
    kernelCommutationAPI_of_commutes_and_isMarkov (Y := Y) κ hcomm
  have hcomm' :
      ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp
            (kernelToKleisliHom
              (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
            (finSuppPermKleisliHom τ) =
          kernelToKleisliHom
            (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of Y) : KleisliGiry)) (B := KleisliBinarySeqObj) κ :=
    kernelCommutes_of_kernelCommutationAPI hκapi
  have hκexch : KernelExchangeable (X := coordProcess) κ :=
    kernelExchangeable_coord_of_kleisliCommutes (κ := κ) hcomm'
  rcases huniv Y κ hκexch with ⟨L, hLrep, hLuniqRep⟩
  refine ⟨L, ?_, ?_⟩
  · exact
      kernelToKleisliHom_comp_iidSequenceKleisliHomTheta_eq_of_prefixLaw_and_represents
        (hprefix := hprefix) (κ := κ) (L := L) hLrep
  · intro L' hL'fac
    haveI : ProbabilityTheory.IsMarkovKernel L' :=
      isMarkovKernel_of_kleisliFactorization_targetMarkov
        (κ := κ) (L := L') hL'fac
    have hL'prefix :
        ∀ (y : Y) (n : ℕ) (xs : Fin n → Bool),
          κ y (seqPrefixEvent n xs) =
            ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L' y) :=
      kernel_prefixLaw_iidPrefix_of_kleisliFactorization
        (hprefix := hprefix) (κ := κ) (L := L') hL'fac
    have hL'rep :
        KernelRepresentsLatentTheta (X := coordProcess) κ (fun y => L' y) :=
      kernelRepresentsLatentTheta_of_kernelPrefixLaw_iidPrefix
        (κ := κ) (L := L') hL'prefix
    exact hLuniqRep L' hL'rep

/-- Unconditional all-sources kernel factorization bridge:
the strict iid prefix law is supplied internally by
`iidSequenceKernelTheta_prefix_apply_unconditional`. -/
theorem allSourcesKernelFactorization_unrestricted_of_allSourcesKernel
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted := by
  exact
    allSourcesKernelFactorization_unrestricted_of_allSourcesKernel_and_prefixLaw
      (hprefix := iidSequenceKernelTheta_prefix_apply_unconditional)
      (huniv := huniv)
      (hmarkov_of_commutes := hmarkov_of_commutes)

/-- Corollary: the previous theorem immediately yields unrestricted all-sources
Kleisli mediation. -/
theorem allSourcesKleisli_unrestricted_of_allSourcesKernel_and_prefixLaw
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  exact
    allSourcesKleisli_unrestricted_of_allSourcesKernelFactorization_unrestricted
      (allSourcesKernelFactorization_unrestricted_of_allSourcesKernel_and_prefixLaw
        (hprefix := hprefix) (huniv := huniv)
        (hmarkov_of_commutes := hmarkov_of_commutes))

/-- Unconditional all-sources Kleisli mediation bridge:
strict iid prefix laws are supplied internally. -/
theorem allSourcesKleisli_unrestricted_of_allSourcesKernel
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  exact
    allSourcesKleisli_unrestricted_of_allSourcesKernel_and_prefixLaw
      (hprefix := iidSequenceKernelTheta_prefix_apply_unconditional)
      (huniv := huniv)
      (hmarkov_of_commutes := hmarkov_of_commutes)

/-- One-hop unrestricted bridge from:
1. strict IID prefix-law equations for `iidSequenceKernelTheta`,
2. default all-sources qualitative de Finetti witness,
3. measurable-upgrade crux, and
4. a commutes⇒Markov bridge for source kernels. -/
theorem allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hupgrade : KernelLatentThetaMediatorMeasurabilityUpgrade)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  have hunivKernel : KernelLatentThetaUniversalMediator_allSourcesKernel :=
    allSourcesKernel_of_allSourcesDefault_and_measurabilityUpgrade
      (hunivDefault := hunivDefault)
      (hupgrade := hupgrade)
  exact
    allSourcesKleisli_unrestricted_of_allSourcesKernel_and_prefixLaw
      (hprefix := hprefix)
      (huniv := hunivKernel)
      (hmarkov_of_commutes := hmarkov_of_commutes)

/-- Unconditional one-hop unrestricted bridge from default all-sources witness:
strict iid prefix laws are supplied internally. -/
theorem allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hupgrade : KernelLatentThetaMediatorMeasurabilityUpgrade)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  exact
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw
      (hprefix := iidSequenceKernelTheta_prefix_apply_unconditional)
      (hunivDefault := hunivDefault)
      (hupgrade := hupgrade)
      (hmarkov_of_commutes := hmarkov_of_commutes)

/-- Same one-hop unrestricted bridge as above, but replacing the explicit
`hupgrade` hypothesis with a measurable-embedding hypothesis for the latent
moment map. -/
theorem allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_thetaMomentEmbedding
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hEmb : MeasurableEmbedding thetaMomentSeq)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  exact
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw
      (hprefix := hprefix)
      (hunivDefault := hunivDefault)
      (hupgrade := kernelLatentThetaMediatorMeasurabilityUpgrade_of_thetaMomentEmbedding
        (hEmb := hEmb))
      (hmarkov_of_commutes := hmarkov_of_commutes)

/-- Public-alias variant of the previous theorem using `latentThetaMomentSeq`
instead of the private internal name. -/
theorem allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_latentThetaMomentEmbedding
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hEmb : MeasurableEmbedding latentThetaMomentSeq)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  simpa [latentThetaMomentSeq] using
    (allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_thetaMomentEmbedding
      (hprefix := hprefix)
      (hunivDefault := hunivDefault)
      (hEmb := hEmb)
      (hmarkov_of_commutes := hmarkov_of_commutes))

/-- Canonical one-hop unrestricted bridge:
discharge the measurable-upgrade crux through the built-in latent moment
embedding infrastructure, so no extra embedding/Borel assumptions are required
at call sites. -/
theorem allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  exact
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_latentThetaMomentEmbedding
      (hprefix := hprefix)
      (hunivDefault := hunivDefault)
      (hEmb := measurableEmbedding_latentThetaMomentSeq)
      (hmarkov_of_commutes := hmarkov_of_commutes)

/-- Canonical one-hop unrestricted bridge with no explicit prefix-law input:
derive strict iid-prefix equations from global finitary invariance plus a
Dirac latent representation witness, then dispatch to the canonical moment
embedding route. -/
theorem allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  have hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
    intro θ n xs
    exact iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance
      hglobal hrepDirac θ n xs
  exact
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding
      (hprefix := hprefix)
      (hunivDefault := hunivDefault)
      (hmarkov_of_commutes := hmarkov_of_commutes)

/-- Canonical one-hop unrestricted bridge from finite-prefix product marginals:
if finite-prefix marginals of `iidSequenceKernelTheta` are Bernoulli product
measures, derive the latent-Dirac representation witness internally and dispatch
to the global-finitary-invariance canonical route. -/
theorem allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_prefixPiMarginals_of_canonicalMomentEmbedding
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hprefixPi :
      ∀ (θ : LatentTheta) (n : ℕ),
        (iidSequenceKernelTheta θ).map (seqPrefixProj n) =
          Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  have hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)) :=
    iidSequenceKernelTheta_represents_latentDirac_of_prefix_pi_marginals
      (hprefixPi := hprefixPi)
  exact
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
      (hglobal := hglobal)
      (hrepDirac := hrepDirac)
      (hunivDefault := hunivDefault)
      (hmarkov_of_commutes := hmarkov_of_commutes)

/-- The hard-step strengthening target follows from the explicit unrestricted
commutes-to-Markov bridge plus the canonical latent-Dirac route. -/
theorem defaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening_of_commutesToMarkovBridge
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    DefaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening := by
  intro hglobal hunivDefault
  exact
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
      (hglobal := hglobal)
      (hrepDirac := iidSequenceKernelTheta_represents_latentDirac_unconditional)
      (hunivDefault := hunivDefault)
      (hmarkov_of_commutes := hmarkov_of_commutes)

/-- Legacy compatibility wrapper threading an explicit
`StandardBorelSpace (ProbabilityMeasure LatentTheta)` assumption.

Migration: prefer
`allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding`.
-/
theorem allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_standardBorel
    [StandardBorelSpace (ProbabilityMeasure LatentTheta)]
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  exact
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding
      (hprefix := hprefix)
      (hunivDefault := hunivDefault)
      (hmarkov_of_commutes := hmarkov_of_commutes)

/-- Legacy compatibility wrapper for an explicit finite-measure Borel bridge:
derive `StandardBorelSpace (ProbabilityMeasure LatentTheta)` from finite-measure
Borel via the local bridge, then discharge unrestricted all-sources Kleisli
mediation through the standard-Borel latent embedding path. -/
theorem allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_borel
    [BorelSpace (FiniteMeasure LatentTheta)]
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  exact
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding
      (hprefix := hprefix)
      (hunivDefault := hunivDefault)
      (hmarkov_of_commutes := hmarkov_of_commutes)

/-- Local finite→probability Borel bridge specialization for `LatentTheta`.
Use this to make the fallback route explicit at call sites. -/
theorem borelSpace_probabilityMeasureLatentTheta_of_finiteMeasure
    [BorelSpace (FiniteMeasure LatentTheta)] :
    BorelSpace (ProbabilityMeasure LatentTheta) := by
  infer_instance

/-- Local finite→standard-Borel bridge specialization for `LatentTheta`.
This packages the preferred theorem-level route:
`FiniteMeasure`-Borel → `ProbabilityMeasure`-Borel → standard-Borel. -/
theorem standardBorelSpace_probabilityMeasureLatentTheta_of_finiteMeasure
    [BorelSpace (FiniteMeasure LatentTheta)] :
    StandardBorelSpace (ProbabilityMeasure LatentTheta) := by
  letI : PolishSpace (ProbabilityMeasure LatentTheta) :=
    polishSpace_probabilityMeasureLatentTheta
  exact standardBorelSpace_probabilityMeasure_of_finiteMeasure (Ω := LatentTheta)

/-- Legacy compatibility wrapper for an explicit
`BorelSpace (ProbabilityMeasure LatentTheta)` assumption:
if `ProbabilityMeasure LatentTheta` already carries the Borel measurable
structure, obtain the latent-moment measurable embedding directly and
discharge unrestricted all-sources Kleisli mediation without any
`FiniteMeasure`-Borel bridge assumption. -/
theorem allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_probabilityMeasureBorel
    [BorelSpace (ProbabilityMeasure LatentTheta)]
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  exact
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding
      (hprefix := hprefix)
      (hunivDefault := hunivDefault)
      (hmarkov_of_commutes := hmarkov_of_commutes)

attribute
  [deprecated measurableEmbedding_latentThetaMomentSeq (since := "2026-02-19")]
  measurableEmbedding_latentThetaMomentSeq_of_borel

attribute
  [deprecated measurableEmbedding_latentThetaMomentSeq (since := "2026-02-19")]
  measurableEmbedding_latentThetaMomentSeq_of_finiteMeasureBorel

attribute
  [deprecated
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding
    (since := "2026-02-19")]
  allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_thetaMomentEmbedding

attribute
  [deprecated
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding
    (since := "2026-02-19")]
  allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_latentThetaMomentEmbedding

attribute
  [deprecated
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding
    (since := "2026-02-19")]
  allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_standardBorel

attribute
  [deprecated
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding
    (since := "2026-02-19")]
  allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_borel

attribute
  [deprecated
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding
    (since := "2026-02-19")]
  allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_prefixLaw_of_probabilityMeasureBorel

attribute
  [deprecated iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance (since := "2026-02-19")]
  iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance_dirac

/-- Bridge: all-sources kernel-level factorization implies all-sources
Markov-only Kleisli mediation. -/
theorem allSourcesKleisli_markovOnly_of_allSourcesKernelFactorization
    (huniv : KernelLatentThetaUniversalMediator_allSourcesFactorization) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly := by
  intro A κhom hmarkov hcomm
  let κ : ProbabilityTheory.Kernel A.of.carrier GlobalBinarySeq :=
    kleisliHomToKernel κhom
  haveI : ProbabilityTheory.IsMarkovKernel κ := by
    refine ⟨?_⟩
    intro y
    exact hmarkov y
  have hκcomm :
      ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp
            (kernelToKleisliHom (A := A) (B := KleisliBinarySeqObj) κ)
            (finSuppPermKleisliHom τ) =
          kernelToKleisliHom (A := A) (B := KleisliBinarySeqObj) κ := by
    intro τ
    exact hcomm τ
  have hκexch : KernelExchangeable (X := coordProcess) κ :=
    kernelExchangeable_coord_of_kleisliCommutes (κ := κ) hκcomm
  rcases huniv A.of.carrier κ hκexch with ⟨L, hfacL, huniqL⟩
  refine ⟨kernelToKleisliHom (A := A) (B := KleisliLatentThetaObj) L, ?_, ?_⟩
  · exact hfacL
  · intro m hm
    let K : ProbabilityTheory.Kernel A.of.carrier LatentTheta := kleisliHomToKernel m
    have hfacK :
        CategoryTheory.CategoryStruct.comp
            (kernelToKleisliHom (A := A) (B := KleisliLatentThetaObj) K)
            iidSequenceKleisliHomTheta =
          kernelToKleisliHom (A := A) (B := KleisliBinarySeqObj) κ := by
      exact hm
    have hKL : K = L := huniqL K hfacK
    apply kleisliHom_ext
    intro y
    exact congrArg (fun K' => K' y) hKL

/-- Markov-only bridge with no extra commutation-to-Markov adapter:
strict iid prefix law + all-sources kernel-level latent mediation imply
all-sources Markov-only Kleisli mediation directly. -/
theorem allSourcesKleisli_markovOnly_of_allSourcesKernel_and_prefixLaw
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly := by
  have hunivFac : KernelLatentThetaUniversalMediator_allSourcesFactorization := by
    intro Y _ κ _ hκexch
    rcases huniv Y κ hκexch with ⟨L, hLrep, hLuniqRep⟩
    refine ⟨L, ?_, ?_⟩
    · exact
        kernelToKleisliHom_comp_iidSequenceKleisliHomTheta_eq_of_prefixLaw_and_represents
          (hprefix := hprefix) (κ := κ) (L := L) hLrep
    · intro L' hL'fac
      haveI : ProbabilityTheory.IsMarkovKernel L' :=
        isMarkovKernel_of_kleisliFactorization_targetMarkov
          (κ := κ) (L := L') hL'fac
      have hL'prefix :
          ∀ (y : Y) (n : ℕ) (xs : Fin n → Bool),
            κ y (seqPrefixEvent n xs) =
              ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L' y) :=
        kernel_prefixLaw_iidPrefix_of_kleisliFactorization
          (hprefix := hprefix) (κ := κ) (L := L') hL'fac
      have hL'rep :
          KernelRepresentsLatentTheta (X := coordProcess) κ (fun y => L' y) :=
        kernelRepresentsLatentTheta_of_kernelPrefixLaw_iidPrefix
          (κ := κ) (L := L') hL'prefix
      exact hLuniqRep L' hL'rep
  exact allSourcesKleisli_markovOnly_of_allSourcesKernelFactorization hunivFac

/-- Markov-only one-hop bridge from:
1. strict IID prefix-law equations for `iidSequenceKernelTheta`,
2. default all-sources qualitative de Finetti witness, and
3. a measurable embedding of the latent moment map. -/
theorem allSourcesKleisli_markovOnly_of_defaultAllSourcesKernel_and_prefixLaw_of_thetaMomentEmbedding
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hEmb : MeasurableEmbedding thetaMomentSeq) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly := by
  have hupgrade : KernelLatentThetaMediatorMeasurabilityUpgrade :=
    kernelLatentThetaMediatorMeasurabilityUpgrade_of_thetaMomentEmbedding (hEmb := hEmb)
  have hunivKernel : KernelLatentThetaUniversalMediator_allSourcesKernel :=
    allSourcesKernel_of_allSourcesDefault_and_measurabilityUpgrade
      (hunivDefault := hunivDefault)
      (hupgrade := hupgrade)
  exact
    allSourcesKleisli_markovOnly_of_allSourcesKernel_and_prefixLaw
      (hprefix := hprefix)
      (huniv := hunivKernel)

/-- Canonical Markov-only one-hop bridge with no explicit embedding argument:
use the in-repo latent moment embedding infrastructure. -/
theorem allSourcesKleisli_markovOnly_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly := by
  exact
    allSourcesKleisli_markovOnly_of_defaultAllSourcesKernel_and_prefixLaw_of_thetaMomentEmbedding
      (hprefix := hprefix)
      (hunivDefault := hunivDefault)
      (hEmb := measurableEmbedding_latentThetaMomentSeq)

/-- Canonical Markov-only bridge with no explicit strict prefix-law input:
derive strict iid-prefix equations from global finitary invariance plus a Dirac
latent representation witness, then dispatch to the canonical moment-embedding
route. -/
theorem allSourcesKleisli_markovOnly_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly := by
  have hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) := by
    intro θ n xs
    exact iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance
      hglobal hrepDirac θ n xs
  exact
    allSourcesKleisli_markovOnly_of_defaultAllSourcesKernel_and_prefixLaw_of_canonicalMomentEmbedding
      (hprefix := hprefix)
      (hunivDefault := hunivDefault)

/-- Canonical Markov-only bridge with no explicit strict prefix-law or latent-Dirac
input:
derive the latent-Dirac witness internally from the unconditional iid-prefix
law, then dispatch to the global-finitary-invariance Markov-only bridge. -/
theorem allSourcesKleisli_markovOnly_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_of_canonicalMomentEmbedding
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly := by
  exact
    allSourcesKleisli_markovOnly_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
      (hglobal := hglobal)
      (hrepDirac := iidSequenceKernelTheta_represents_latentDirac_unconditional)
      (hunivDefault := hunivDefault)

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
    exact hm
  · intro m' hm'
    apply huniq
    have hm0 := hm' globalFinSuppPermStar
    exact hm0

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
    exact hm'

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

/-- Bridge: all-sources Markov-only Kleisli mediation implies Markov-only global
mediator uniqueness for the `iidSequenceKernelTheta` cone skeleton. -/
theorem globalIIDConeMediatorUnique_markovOnly_of_allSourcesKleisli
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly) :
    GlobalIIDConeMediatorUnique_markovOnly
      (⟨KleisliLatentThetaObj, iidSequenceKleisliHomTheta, hcommutes⟩ : KleisliGiryIIDConeSkeleton) := by
  intro s hsMarkov
  let κhom : s.pt ⟶ KleisliBinarySeqObj := s.π.app globalFinSuppPermStar
  have hκcomm :
      ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp κhom (finSuppPermKleisliHom τ) = κhom := by
    intro τ
    have h := (s.π.naturality (X := globalFinSuppPermStar) (Y := globalFinSuppPermStar) τ).symm
    rw [kleisliGiryGlobalDiagramFunctor_map] at h
    exact h.trans (CategoryTheory.Category.id_comp _)
  have hκmarkov : KleisliIsMarkov κhom := by
    exact hsMarkov
  simpa [κhom] using huniv s.pt κhom hκmarkov hκcomm

/-- Bridge: unrestricted all-sources Kleisli mediation implies full global
mediator uniqueness for the `iidSequenceKernelTheta` cone skeleton. -/
theorem globalIIDConeMediatorUnique_of_allSourcesKleisli_unrestricted
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    GlobalIIDConeMediatorUnique
      (⟨KleisliLatentThetaObj, iidSequenceKleisliHomTheta, hcommutes⟩ : KleisliGiryIIDConeSkeleton) := by
  intro s
  let κhom : s.pt ⟶ KleisliBinarySeqObj := s.π.app globalFinSuppPermStar
  have hκcomm :
      ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp κhom (finSuppPermKleisliHom τ) = κhom := by
    intro τ
    have h := (s.π.naturality (X := globalFinSuppPermStar) (Y := globalFinSuppPermStar) τ).symm
    rw [kleisliGiryGlobalDiagramFunctor_map] at h
    exact h.trans (CategoryTheory.Category.id_comp _)
  simpa [κhom] using huniv s.pt κhom hκcomm

/-- Converse bridge: full global mediator uniqueness for the canonical
`iidSequenceKernelTheta` cone implies unrestricted all-sources Kleisli
universality. -/
theorem allSourcesKleisli_unrestricted_of_globalIIDConeMediatorUnique
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (hmed :
      GlobalIIDConeMediatorUnique
        (⟨KleisliLatentThetaObj, iidSequenceKleisliHomTheta, hcommutes⟩ :
          KleisliGiryIIDConeSkeleton)) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  intro A κhom hκcomm
  let s : CategoryTheory.Limits.Cone kleisliGiryGlobalDiagramFunctor :=
    { pt := A
      π :=
        { app := fun _ => κhom
          naturality := by
            intro j j' τ
            cases j
            cases j'
            exact (CategoryTheory.Category.id_comp _).trans (hκcomm τ).symm } }
  rcases hmed s with ⟨m, hm, huniq⟩
  refine ⟨m, ?_, ?_⟩
  · simpa [s] using hm
  · intro m' hm'
    exact huniq m' (by simpa [s] using hm')

/-- Equivalent packaging: unrestricted all-sources Kleisli universality is
exactly full global mediator uniqueness for the canonical
`iidSequenceKernelTheta` cone. -/
theorem allSourcesKleisli_unrestricted_iff_globalIIDConeMediatorUnique
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted ↔
      GlobalIIDConeMediatorUnique
        (⟨KleisliLatentThetaObj, iidSequenceKleisliHomTheta, hcommutes⟩ :
          KleisliGiryIIDConeSkeleton) := by
  constructor
  · exact globalIIDConeMediatorUnique_of_allSourcesKleisli_unrestricted
      (hcommutes := hcommutes)
  · exact allSourcesKleisli_unrestricted_of_globalIIDConeMediatorUnique
      (hcommutes := hcommutes)

/-- Full target packaging: under unrestricted all-sources Kleisli mediation,
the `iidSequenceKernelTheta` cone skeleton has a concrete `IsLimit` witness. -/
theorem deFinetti_iidSequenceKleisliCone_isLimit_of_allSourcesKleisli_unrestricted
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    Nonempty
      (CategoryTheory.Limits.IsLimit
        ((⟨KleisliLatentThetaObj, iidSequenceKleisliHomTheta, hcommutes⟩ : KleisliGiryIIDConeSkeleton).toCone)) := by
  have hmed :
      GlobalIIDConeMediatorUnique
        (⟨KleisliLatentThetaObj, iidSequenceKleisliHomTheta, hcommutes⟩ : KleisliGiryIIDConeSkeleton) :=
    globalIIDConeMediatorUnique_of_allSourcesKleisli_unrestricted
      (hcommutes := hcommutes) huniv
  exact ⟨(⟨KleisliLatentThetaObj, iidSequenceKleisliHomTheta, hcommutes⟩ :
      KleisliGiryIIDConeSkeleton).isLimitOfMediatorUnique hmed⟩

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

/-- One-hop bridge: global finitary invariance plus all-sources Markov-only
Kleisli universality yields Markov-only global mediator uniqueness for the
canonical `iidSequenceKernelTheta` cone. -/
theorem globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_allSourcesKleisli
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly) :
    GlobalIIDConeMediatorUnique_markovOnly
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) := by
  exact globalIIDConeMediatorUnique_markovOnly_of_allSourcesKleisli
    (hcommutes := iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal) huniv

/-- One-hop bridge: global finitary invariance plus unrestricted all-sources
Kleisli universality yields full global mediator uniqueness for the canonical
`iidSequenceKernelTheta` cone. -/
theorem globalIIDConeMediatorUnique_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    GlobalIIDConeMediatorUnique
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) := by
  exact globalIIDConeMediatorUnique_of_allSourcesKleisli_unrestricted
    (hcommutes := iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal) huniv

/-- Finite-mass all-sources Kleisli universality implies finite-mass cone
universality for the canonical `iidSequenceKernelTheta` cone. -/
theorem globalIIDConeMediatorUnique_finiteMass_of_allSourcesKleisli_finiteMass
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_finiteMass) :
    GlobalIIDConeMediatorUnique_finiteMass (iidSequenceKleisliConeSkeleton hcommutes) := by
  intro s hsfm
  let κhom := s.π.app globalFinSuppPermStar
  have hκcomm : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp κhom (finSuppPermKleisliHom τ) = κhom := by
    intro τ
    have h := (s.π.naturality (X := globalFinSuppPermStar) (Y := globalFinSuppPermStar) τ).symm
    rw [kleisliGiryGlobalDiagramFunctor_map] at h
    exact h.trans (CategoryTheory.Category.id_comp _)
  exact huniv s.pt κhom hsfm hκcomm

/-- Finite-mass cone universality follows from the all-sources Markov-only
Kleisli universality (via the finite-mass ↔ Markov-only Kleisli equivalence). -/
theorem globalIIDConeMediatorUnique_finiteMass_of_allSourcesKleisli_markovOnly
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly) :
    GlobalIIDConeMediatorUnique_finiteMass
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) :=
  globalIIDConeMediatorUnique_finiteMass_of_allSourcesKleisli_finiteMass _
    ((allSourcesKleisli_finiteMass_iff_markovOnly hglobal).mpr huniv)

/-- One-hop full-target packaging: global finitary invariance plus unrestricted
all-sources Kleisli universality yields a concrete `IsLimit` witness for the
canonical `iidSequenceKernelTheta` cone. -/
theorem deFinetti_iidSequenceKleisliCone_isLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    Nonempty
      (CategoryTheory.Limits.IsLimit
        ((iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact deFinetti_iidSequenceKleisliCone_isLimit_of_allSourcesKleisli_unrestricted
    (hcommutes := iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal) huniv

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
    exact iidSequenceKernelTheta_prefix_apply_integral_of_globalFinitaryInvariance hglobal θ n xs
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

end Mettapedia.CategoryTheory
