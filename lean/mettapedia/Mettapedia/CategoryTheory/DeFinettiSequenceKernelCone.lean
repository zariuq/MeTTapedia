import Mettapedia.CategoryTheory.DeFinettiKernelInterface
import Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection

/-!
# Sequence-Kernel Permutation Cone and IID Prefix Kernels

This file adds:
1. A sequence-level permutation-cone interface on kernels `κ : Y → (ℕ → Bool)`.
2. An explicit iid prefix-kernel family (in Mathlib's `Kernel` layer) and direct
   permutation commutation on singleton cylinder events.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open MeasureTheory
open ProbabilityTheory
open Mettapedia.Logic.Exchangeability
open Mettapedia.Logic.DeFinetti

variable {Y : Type*} [MeasurableSpace Y]

/-- Canonical binary sequence space `Bool^ℕ`. -/
abbrev BinarySeq : Type := ℕ → Bool

/-- Prefix cylinder event on `Bool^ℕ`. -/
def seqPrefixEvent (n : ℕ) (xs : Fin n → Bool) : Set BinarySeq :=
  {ω | ∀ i : Fin n, ω i = xs i}

/-- Finite-prefix tuple permutation action. -/
def permutePrefixTuple {n : ℕ} (σ : Equiv.Perm (Fin n)) (xs : Fin n → Bool) : Fin n → Bool :=
  xs ∘ σ.symm

/-- Sequence-kernel permutation cone:
for each parameter `y`, finite-prefix laws commute with finite-coordinate
permutations. -/
def KernelSequencePrefixCone
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop :=
  ∀ (y : Y) (n : ℕ) (σ : Equiv.Perm (Fin n)) (xs : Fin n → Bool),
    (κ y) (seqPrefixEvent n xs) = (κ y) (seqPrefixEvent n (permutePrefixTuple σ xs))

/-- Thin cone-object wrapper for sequence-kernel permutation commutation. -/
structure SequenceKernelConeObj
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop where
  commutes :
    ∀ (y : Y) (n : ℕ) (σ : Equiv.Perm (Fin n)) (xs : Fin n → Bool),
      (κ y) (seqPrefixEvent n xs) = (κ y) (seqPrefixEvent n (permutePrefixTuple σ xs))

/-- The thin cone-object wrapper is definitionally equivalent to
`KernelSequencePrefixCone`. -/
theorem sequenceKernelConeObj_iff_kernelSequencePrefixCone
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ ↔ KernelSequencePrefixCone κ := by
  constructor
  · intro h
    exact h.commutes
  · intro h
    exact ⟨h⟩

/-- Coordinate process on sequence space. -/
def coordProcess : ℕ → BinarySeq → Bool :=
  fun i ω => ω i

/-- The new sequence-kernel cone is exactly the old kernel prefix-cone
for the coordinate process `coordProcess`. -/
theorem kernelSequencePrefixCone_iff_kernelPrefixCone_coord
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    KernelSequencePrefixCone κ ↔ KernelPrefixCone (X := coordProcess) κ := by
  constructor
  · intro h y n σ xs
    simpa [KernelSequencePrefixCone, KernelPrefixCone, ExchangeablePrefixCone,
      prefixLaw, seqPrefixEvent, permutePrefixTuple, coordProcess, permuteBoolTuple] using
      h y n σ xs
  · intro h y n σ xs
    simpa [KernelSequencePrefixCone, KernelPrefixCone, ExchangeablePrefixCone,
      prefixLaw, seqPrefixEvent, permutePrefixTuple, coordProcess, permuteBoolTuple] using
      h y n σ xs

/-- Sequence-kernel cone is equivalent to pointwise exchangeability for the
coordinate process. -/
theorem kernelSequencePrefixCone_iff_kernelExchangeable_coord
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    KernelSequencePrefixCone κ ↔ KernelExchangeable (X := coordProcess) κ := by
  rw [kernelSequencePrefixCone_iff_kernelPrefixCone_coord]
  simpa using
    (kernelExchangeable_iff_kernelPrefixCone (X := coordProcess) (κ := κ)).symm

/-- Cone-object API equivalence to coordinate-process exchangeability. -/
theorem sequenceKernelConeObj_iff_kernelExchangeable_coord
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ ↔ KernelExchangeable (X := coordProcess) κ := by
  rw [sequenceKernelConeObj_iff_kernelSequencePrefixCone]
  exact kernelSequencePrefixCone_iff_kernelExchangeable_coord (κ := κ)

/-- Bridge theorem from cone-object form to latent-`Theta` factorization:
a sequence-kernel cone object yields a unique latent `Y → Measure Theta` family
for the coordinate process. -/
theorem sequenceKernelConeObj_existsUnique_latentThetaKernel
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ →
      ∃! L :
        Y →
          Measure
            Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
        KernelRepresentsLatentTheta (X := coordProcess) κ L := by
  intro hcone
  have hexch : KernelExchangeable (X := coordProcess) κ :=
    (sequenceKernelConeObj_iff_kernelExchangeable_coord (κ := κ)).1 hcone
  have hX : ∀ i : ℕ, Measurable (coordProcess i) := by
    intro i
    simpa [coordProcess] using (measurable_pi_apply (a := i))
  exact existsUnique_latentThetaKernel_of_kernelExchangeable
    (X := coordProcess) (κ := κ) hX hexch

/-- Round-trip bridge:
`SequenceKernelConeObj` is equivalent to latent-`Theta` factorization for the coordinate process,
and together with `sequenceKernelConeObj_existsUnique_latentThetaKernel` yields
existence-uniqueness of the mediator map. -/
theorem sequenceKernelConeObj_iff_kernelLatentThetaFactorization_coord
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ ↔ KernelLatentThetaFactorization (X := coordProcess) κ := by
  have hX : ∀ i : ℕ, Measurable (coordProcess i) := by
    intro i
    simpa [coordProcess] using (measurable_pi_apply (a := i))
  calc
    SequenceKernelConeObj κ ↔ KernelExchangeable (X := coordProcess) κ :=
      sequenceKernelConeObj_iff_kernelExchangeable_coord (κ := κ)
    _ ↔ KernelLatentThetaFactorization (X := coordProcess) κ :=
      kernelExchangeable_iff_kernelLatentThetaFactorization (X := coordProcess) (κ := κ) hX

/-- Round-trip package combining cone-object/factorization equivalence with
the cone-object existence-uniqueness theorem for latent-`Theta` mediators. -/
theorem sequenceKernelConeObj_roundTrip_latentThetaMediator
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ ↔
      (KernelLatentThetaFactorization (X := coordProcess) κ ∧
        ∃! L :
          Y →
            Measure
              Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
          KernelRepresentsLatentTheta (X := coordProcess) κ L) := by
  constructor
  · intro hcone
    refine ⟨(sequenceKernelConeObj_iff_kernelLatentThetaFactorization_coord (κ := κ)).1 hcone, ?_⟩
    exact sequenceKernelConeObj_existsUnique_latentThetaKernel (κ := κ) hcone
  · intro h
    exact (sequenceKernelConeObj_iff_kernelLatentThetaFactorization_coord (κ := κ)).2 h.1

/-! ## IID Prefix Kernels in Mathlib's Kernel Layer -/

/-- Parameter space `[0,1]` used by the Bernoulli mixture construction. -/
abbrev Theta : Type :=
  Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta

/-- IID Bernoulli prefix-kernel (horizon `n`) from the higher-order probability
de Finetti connection file. -/
noncomputable abbrev iidPrefixKernel (n : ℕ) : ProbabilityTheory.Kernel Theta (Fin n → Bool) :=
  Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel (n := n)

instance iidPrefixKernel_isMarkov (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel (iidPrefixKernel n) := by
  simpa [iidPrefixKernel] using
    (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel_isMarkov
      (n := n))

/-- Direct permutation commutation on singleton prefix events for the iid prefix-kernel. -/
theorem iidPrefixKernel_perm_singleton
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (θ : Theta) (xs : Fin n → Bool) :
    (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) =
      (iidPrefixKernel n θ) ({xs ∘ σ.symm} : Set (Fin n → Bool)) := by
  have hcountTrue : countTrue (xs ∘ σ.symm) = countTrue xs := countTrue_perm xs σ.symm
  have hcountFalse : countFalse (xs ∘ σ.symm) = countFalse xs := countFalse_perm xs σ.symm
  have hprod :
      bernoulliProductPMF (θ : ℝ) xs =
        bernoulliProductPMF (θ : ℝ) (xs ∘ σ.symm) := by
    simp [bernoulliProductPMF_eq_power, hcountTrue, hcountFalse]
  have hweight :
      Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight
          (n := n) θ xs =
        Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight
          (n := n) θ (xs ∘ σ.symm) := by
    simp [Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight, hprod]
  calc
    (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool))
        =
          Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight
            (n := n) θ xs := by
              simp [iidPrefixKernel,
                Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel]
    _ =
        Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight
          (n := n) θ (xs ∘ σ.symm) := hweight
    _ =
        (iidPrefixKernel n θ) ({xs ∘ σ.symm} : Set (Fin n → Bool)) := by
          simp [iidPrefixKernel,
            Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel]

/-- Cone law for the iid prefix-kernel family:
finite-coordinate permutations preserve singleton prefix-event probabilities. -/
theorem iidPrefixKernel_cone_commutes
    (n : ℕ) :
    ∀ (θ : Theta) (σ : Equiv.Perm (Fin n)) (xs : Fin n → Bool),
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) =
        (iidPrefixKernel n θ) ({xs ∘ σ.symm} : Set (Fin n → Bool)) := by
  intro θ σ xs
  exact iidPrefixKernel_perm_singleton n σ θ xs

/-- Sequence-level mediator packaging the finite-prefix factorization
`k̃ ≫ iid = k` in kernel language. -/
structure KernelIIDPrefixMediator
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] where
  latent : Y → Measure Theta
  fac : ∀ (y : Y) (n : ℕ) (xs : Fin n → Bool),
    (κ y) (seqPrefixEvent n xs) =
      ∫⁻ θ : Theta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(latent y)

/-- If a latent `Theta` family represents every fiber of `κ` for the coordinate
process, then each finite-prefix event law is exactly the corresponding iid-prefix
mixture under that latent family. -/
theorem kernelRepresentsLatentTheta_coord_prefix_eq_iidPrefixKernel
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (L : Y → Measure Theta)
    (hL : KernelRepresentsLatentTheta (X := coordProcess) κ L) :
    ∀ (y : Y) (n : ℕ) (xs : Fin n → Bool),
      (κ y) (seqPrefixEvent n xs) =
        ∫⁻ θ : Theta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L y) := by
  intro y n xs
  rcases hL y with ⟨M, hrep, hLy⟩
  have hrepEq :
      (κ y) (seqPrefixEvent n xs) = ENNReal.ofReal (M.prob xs) := by
    simpa [Represents, coordProcess, seqPrefixEvent] using hrep n xs
  have hflatMix :
      (∫⁻ θ : Theta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool))
          ∂(Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.mixingMeasureTheta M)) =
        ENNReal.ofReal (M.prob xs) := by
    have hflat_apply :
        (Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten
            (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.pd M n))
            ({xs} : Set (Fin n → Bool)) =
          ∫⁻ θ,
            ((Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.pd M n).kernel θ)
              ({xs} : Set (Fin n → Bool))
            ∂((Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.pd M n).mixingMeasure) := by
      exact
        Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten_apply
          (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.pd M n)
          ({xs} : Set (Fin n → Bool)) (by simp)
    have hflat_apply' :
        (Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten
            (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.pd M n))
            ({xs} : Set (Fin n → Bool)) =
          ∫⁻ θ : Theta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool))
            ∂(Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.mixingMeasureTheta M) := by
      simpa [iidPrefixKernel,
        Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.pd] using hflat_apply
    calc
      (∫⁻ θ : Theta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool))
          ∂(Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.mixingMeasureTheta M)) =
        (Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten
            (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.pd M n))
            ({xs} : Set (Fin n → Bool)) := by
          simpa using hflat_apply'.symm
      _ = ENNReal.ofReal (M.prob xs) :=
        Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.flatten_apply_singleton M n xs
  have hflatL :
      (∫⁻ θ : Theta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L y)) =
        ENNReal.ofReal (M.prob xs) := by
    simpa [hLy] using hflatMix
  calc
    (κ y) (seqPrefixEvent n xs) = ENNReal.ofReal (M.prob xs) := hrepEq
    _ =
      ∫⁻ θ : Theta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L y) := by
        simpa using hflatL.symm

/-- Build a sequence-level iid-prefix mediator from a latent-`Theta`
representation witness. -/
def kernelIIDPrefixMediatorOfRepresentsLatentTheta
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (L : Y → Measure Theta)
    (hL : KernelRepresentsLatentTheta (X := coordProcess) κ L) :
    KernelIIDPrefixMediator (κ := κ) where
  latent := L
  fac := kernelRepresentsLatentTheta_coord_prefix_eq_iidPrefixKernel (κ := κ) (L := L) hL

/-- Explicit universal-mediator form for sequence kernels:
under the sequence-prefix cone law, there is a unique latent `Theta` family that
both represents each fiber and satisfies finite-prefix iid-mixture equations. -/
theorem existsUnique_latentThetaKernel_with_iidPrefixFactorization_of_sequenceKernelConeObj
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hcone : SequenceKernelConeObj κ) :
    ∃! L : Y → Measure Theta,
      KernelRepresentsLatentTheta (X := coordProcess) κ L ∧
      (∀ (y : Y) (n : ℕ) (xs : Fin n → Bool),
        (κ y) (seqPrefixEvent n xs) =
          ∫⁻ θ : Theta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L y)) := by
  rcases sequenceKernelConeObj_existsUnique_latentThetaKernel (κ := κ) hcone with
    ⟨L0, hL0, huniq0⟩
  refine ⟨L0, ?_, ?_⟩
  · refine ⟨hL0, ?_⟩
    exact kernelRepresentsLatentTheta_coord_prefix_eq_iidPrefixKernel
      (κ := κ) (L := L0) hL0
  · intro L hL
    exact huniq0 L hL.1

/-- Same explicit universal-mediator form, with exchangeability as hypothesis
for the coordinate process. -/
theorem existsUnique_latentThetaKernel_with_iidPrefixFactorization_of_kernelExchangeable_coord
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hexch : KernelExchangeable (X := coordProcess) κ) :
    ∃! L : Y → Measure Theta,
      KernelRepresentsLatentTheta (X := coordProcess) κ L ∧
      (∀ (y : Y) (n : ℕ) (xs : Fin n → Bool),
        (κ y) (seqPrefixEvent n xs) =
          ∫⁻ θ : Theta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L y)) := by
  have hcone : SequenceKernelConeObj κ :=
    (sequenceKernelConeObj_iff_kernelExchangeable_coord (κ := κ)).2 hexch
  exact
    existsUnique_latentThetaKernel_with_iidPrefixFactorization_of_sequenceKernelConeObj
      (κ := κ) hcone

/-- Equivalent unique-mediator packaging using the `KernelIIDPrefixMediator`
record. -/
theorem existsUnique_kernelIIDPrefixMediator_of_sequenceKernelConeObj
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hcone : SequenceKernelConeObj κ) :
    ∃! M : KernelIIDPrefixMediator (κ := κ),
      KernelRepresentsLatentTheta (X := coordProcess) κ M.latent := by
  rcases sequenceKernelConeObj_existsUnique_latentThetaKernel (κ := κ) hcone with
    ⟨L0, hL0, huniq0⟩
  refine ⟨kernelIIDPrefixMediatorOfRepresentsLatentTheta (κ := κ) L0 hL0, hL0, ?_⟩
  intro M hM
  cases M with
  | mk latent fac =>
      have hLat : latent = L0 := huniq0 latent hM
      cases hLat
      simp [kernelIIDPrefixMediatorOfRepresentsLatentTheta]

end Mettapedia.CategoryTheory
