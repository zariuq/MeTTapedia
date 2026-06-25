import Mettapedia.CategoryTheory.DeFinettiPermutationCone
import Mettapedia.CategoryTheory.DeFinettiHausdorffBridge
import Mathlib.Probability.Kernel.Basic

/-!
# Kernel-Level Interface for Categorical de Finetti

This file lifts the process-level qualitative de Finetti interface to
Markov kernels `κ : Y → Ω` by requiring the interface pointwise in `y : Y`.

No finite-rate quantitative bounds are introduced here.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open MeasureTheory
open ProbabilityTheory
open Mettapedia.ProbabilityTheory.Exchangeability
open Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti
open Mettapedia.ProbabilityTheory.HigherOrderProbability

variable {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Kernel-level exchangeability: each fiber measure `κ y` is exchangeable for `X`. -/
def KernelExchangeable
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop :=
  ∀ y : Y, InfiniteExchangeable X (κ y)

/-- Kernel-level prefix-cone interface: each fiber measure `κ y` satisfies the
finite-prefix permutation cone laws. -/
def KernelPrefixCone
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop :=
  ∀ y : Y, ExchangeablePrefixCone X (κ y)

/-- Kernel-level qualitative categorical factorization: each fiber `κ y`
admits a de Finetti Bernoulli-mixture factorization. -/
def KernelCategoricalDeFinettiFactorization
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop :=
  ∀ y : Y, CategoricalDeFinettiFactorization X (κ y)

/-- Kernel-level iid-factorization alias. -/
def KernelIIDFactorization
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop :=
  KernelCategoricalDeFinettiFactorization X κ

/-- Pointwise equivalence: kernel exchangeability iff kernel prefix-cone laws. -/
theorem kernelExchangeable_iff_kernelPrefixCone
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ] :
    KernelExchangeable X κ ↔ KernelPrefixCone X κ := by
  constructor
  · intro hexch y
    exact (infiniteExchangeable_iff_exchangeablePrefixCone (X := X) (μ := κ y)).1 (hexch y)
  · intro hcone y
    exact (infiniteExchangeable_iff_exchangeablePrefixCone (X := X) (μ := κ y)).2 (hcone y)

/-- Kernel exchangeability implies kernel iid-factorization (qualitative). -/
theorem kernelIIDFactorization_of_kernelExchangeable
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : KernelExchangeable X κ) :
    KernelIIDFactorization X κ := by
  intro y
  exact categoricalDeFinetti_factorization_of_exchangeable
    (X := X) (μ := κ y) hX (hexch y)

/-- Pointwise qualitative de Finetti characterization over kernels. -/
theorem kernelExchangeable_iff_kernelIIDFactorization
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i)) :
    KernelExchangeable X κ ↔ KernelIIDFactorization X κ := by
  constructor
  · intro hexch
    exact kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch
  · intro hfac y
    exact (exchangeable_iff_categoricalDeFinettiFactorization (X := X) (μ := κ y) hX).2 (hfac y)

/-- Kernel-level latent-`Theta` interface:
`L y` is a valid latent `Theta` measure for each fiber law `κ y`. -/
def KernelRepresentsLatentTheta
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (L : Y → Measure DeFinettiConnection.Theta) : Prop :=
  ∀ y : Y, RepresentsLatentTheta (X := X) (μ := κ y) (L y)

/-- Kernel-level latent-`Theta` factorization interface:
there exists a latent measure family `Y → Measure Theta` representing each fiber law. -/
def KernelLatentThetaFactorization
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop :=
  ∃ L : Y → Measure DeFinettiConnection.Theta, KernelRepresentsLatentTheta X κ L

/-- Cone-morphism style packaging for a latent-`Theta` mediator at kernel level. -/
structure KernelLatentThetaConeMorphism
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ] where
  mediator : Y → Measure DeFinettiConnection.Theta
  commutes : KernelRepresentsLatentTheta X κ mediator

/-- A cone-morphism record induces latent-`Theta` factorization. -/
theorem kernelLatentThetaFactorization_of_kernelLatentThetaConeMorphism
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (Φ : KernelLatentThetaConeMorphism X κ) :
    KernelLatentThetaFactorization X κ :=
  ⟨Φ.mediator, Φ.commutes⟩

/-- Latent-`Theta` factorization yields a cone-morphism record. -/
noncomputable def kernelLatentThetaConeMorphism_of_kernelLatentThetaFactorization
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hfacθ : KernelLatentThetaFactorization X κ) :
    KernelLatentThetaConeMorphism X κ :=
  let L := Classical.choose hfacθ
  let hL := Classical.choose_spec hfacθ
  ⟨L, hL⟩

/-- Direct translation theorem between cone-morphism packaging and
existential latent-`Theta` factorization. -/
theorem kernelLatentThetaConeMorphism_iff_kernelLatentThetaFactorization
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ] :
    Nonempty (KernelLatentThetaConeMorphism X κ) ↔ KernelLatentThetaFactorization X κ := by
  constructor
  · intro h
    rcases h with ⟨Φ⟩
    exact kernelLatentThetaFactorization_of_kernelLatentThetaConeMorphism X κ Φ
  · intro hfacθ
    exact ⟨kernelLatentThetaConeMorphism_of_kernelLatentThetaFactorization X κ hfacθ⟩

/-- Extract a kernel-indexed latent Bernoulli-mixture family from a
kernel iid-factorization witness. -/
noncomputable def latentBernoulliMixtureKernelOf
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hfac : KernelIIDFactorization X κ) : Y → BernoulliMixture :=
  fun y => latentBernoulliMixtureOf (hfac y)

/-- Extract the latent `Theta`-measure family from a kernel iid-factorization witness. -/
noncomputable def latentThetaKernelOf
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hfac : KernelIIDFactorization X κ) : Y → Measure DeFinettiConnection.Theta :=
  fun y => DeFinettiConnection.mixingMeasureTheta (latentBernoulliMixtureKernelOf hfac y)

/-- The extracted latent kernel family satisfies the representation equations
on every fiber `κ y`. -/
theorem latentBernoulliMixtureKernelOf_represents
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hfac : KernelIIDFactorization X κ) :
    ∀ y : Y, Represents (latentBernoulliMixtureKernelOf hfac y) X (κ y) := by
  intro y
  exact latentBernoulliMixtureOf_represents (hfac y)

/-- The extracted latent-`Theta` kernel family satisfies the measure-level latent interface
on every fiber `κ y`. -/
theorem latentThetaKernelOf_represents
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hfac : KernelIIDFactorization X κ) :
    KernelRepresentsLatentTheta X κ (latentThetaKernelOf hfac) := by
  intro y
  exact ⟨latentBernoulliMixtureKernelOf hfac y, latentBernoulliMixtureKernelOf_represents hfac y, rfl⟩

/-- Kernel exchangeability implies latent-`Theta` factorization. -/
theorem kernelLatentThetaFactorization_of_kernelExchangeable
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : KernelExchangeable X κ) :
    KernelLatentThetaFactorization X κ := by
  let hfac : KernelIIDFactorization X κ :=
    kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch
  refine ⟨latentThetaKernelOf hfac, ?_⟩
  exact latentThetaKernelOf_represents hfac

/-- Latent-`Theta` factorization implies kernel exchangeability. -/
theorem kernelExchangeable_of_kernelLatentThetaFactorization
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hfacθ : KernelLatentThetaFactorization X κ) :
    KernelExchangeable X κ := by
  intro y
  rcases hfacθ with ⟨L, hL⟩
  rcases hL y with ⟨M, hrep, _⟩
  exact
    (exchangeable_iff_categoricalDeFinettiFactorization (X := X) (μ := κ y) hX).2 ⟨M, hrep⟩

/-- Pointwise qualitative de Finetti characterization over kernels in latent-`Theta` form. -/
theorem kernelExchangeable_iff_kernelLatentThetaFactorization
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i)) :
    KernelExchangeable X κ ↔ KernelLatentThetaFactorization X κ := by
  constructor
  · intro hexch
    exact kernelLatentThetaFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch
  · intro hfacθ
    exact kernelExchangeable_of_kernelLatentThetaFactorization (X := X) (κ := κ) hX hfacθ

/-- Fiberwise identifiability assumption for Bernoulli-mixture representation. -/
def KernelMixtureIdentifiable
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop :=
  ∀ y : Y, ∀ M1 M2 : BernoulliMixture,
    Represents M1 X (κ y) → Represents M2 X (κ y) → M1 = M2

/-- Unconditional identifiability from the Hausdorff bridge:
two Bernoulli-mixture representations of the same fiber law must be equal. -/
theorem kernelMixtureIdentifiable_of_HausdorffBridge
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ] :
    KernelMixtureIdentifiable X κ := by
  intro y M1 M2 hrep1 hrep2
  exact bernoulliMixture_eq_of_represents (X := X) (μ := κ y) (M1 := M1) (M2 := M2) hrep1 hrep2

/-- Conditional uniqueness theorem:
if Bernoulli-mixture representation is identifiable on each fiber, then the
extracted latent kernel family is unique. -/
theorem latentBernoulliMixtureKernel_unique_of_identifiable
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hfac : KernelIIDFactorization X κ)
    (hident : KernelMixtureIdentifiable X κ)
    (L : Y → BernoulliMixture)
    (hL : ∀ y : Y, Represents (L y) X (κ y)) :
    latentBernoulliMixtureKernelOf hfac = L := by
  funext y
  exact hident y _ _ (latentBernoulliMixtureKernelOf_represents hfac y) (hL y)

/-- Conditional existence-uniqueness of a latent Bernoulli-mixture kernel family. -/
theorem existsUnique_latentBernoulliMixtureKernel_of_identifiable
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hfac : KernelIIDFactorization X κ)
    (hident : KernelMixtureIdentifiable X κ) :
    ∃! L : Y → BernoulliMixture, ∀ y : Y, Represents (L y) X (κ y) := by
  refine ⟨latentBernoulliMixtureKernelOf hfac, latentBernoulliMixtureKernelOf_represents hfac, ?_⟩
  intro L hL
  exact (latentBernoulliMixtureKernel_unique_of_identifiable hfac hident L hL).symm

/-- Unconditional uniqueness of the latent Bernoulli-mixture kernel family
from the Hausdorff bridge. -/
theorem latentBernoulliMixtureKernel_unique
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hfac : KernelIIDFactorization X κ)
    (L : Y → BernoulliMixture)
    (hL : ∀ y : Y, Represents (L y) X (κ y)) :
    latentBernoulliMixtureKernelOf hfac = L := by
  exact latentBernoulliMixtureKernel_unique_of_identifiable
    (hfac := hfac)
    (hident := kernelMixtureIdentifiable_of_HausdorffBridge X κ)
    L hL

/-- Unconditional existence-uniqueness of a latent Bernoulli-mixture kernel family
from the Hausdorff bridge. -/
theorem existsUnique_latentBernoulliMixtureKernel
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hfac : KernelIIDFactorization X κ) :
    ∃! L : Y → BernoulliMixture, ∀ y : Y, Represents (L y) X (κ y) := by
  exact existsUnique_latentBernoulliMixtureKernel_of_identifiable
    (hfac := hfac)
    (hident := kernelMixtureIdentifiable_of_HausdorffBridge X κ)

/-- Direct qualitative existence-uniqueness interface:
kernel exchangeability yields a unique latent Bernoulli-mixture family. -/
theorem existsUnique_latentBernoulliMixtureKernel_of_kernelExchangeable
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : KernelExchangeable X κ) :
    ∃! L : Y → BernoulliMixture, ∀ y : Y, Represents (L y) X (κ y) := by
  exact existsUnique_latentBernoulliMixtureKernel
    (hfac := kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch)

/-- Direct qualitative uniqueness interface:
under kernel exchangeability, any representation family equals the canonical latent family. -/
theorem latentBernoulliMixtureKernel_unique_of_kernelExchangeable
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : KernelExchangeable X κ)
    (L : Y → BernoulliMixture)
    (hL : ∀ y : Y, Represents (L y) X (κ y)) :
    latentBernoulliMixtureKernelOf
      (kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch) = L := by
  exact latentBernoulliMixtureKernel_unique
    (hfac := kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch)
    L hL

/-- Direct qualitative uniqueness interface on latent `Theta`-measure kernels:
under kernel exchangeability, any latent-measure family satisfying the representation
interface equals the canonical latent-measure family. -/
theorem latentThetaKernel_unique_of_kernelExchangeable
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : KernelExchangeable X κ)
    (L : Y → Measure DeFinettiConnection.Theta)
    (hL : KernelRepresentsLatentTheta X κ L) :
    latentThetaKernelOf
      (kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch) = L := by
  funext y
  rcases hL y with ⟨M, hrepM, hLM⟩
  have hrepCanon :
      Represents
        (latentBernoulliMixtureKernelOf
          (kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch) y)
        X (κ y) :=
    latentBernoulliMixtureKernelOf_represents
      (kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch) y
  have hΘeq :
      DeFinettiConnection.mixingMeasureTheta
          (latentBernoulliMixtureKernelOf
            (kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch) y) =
        DeFinettiConnection.mixingMeasureTheta M :=
    mixingMeasureTheta_eq_of_represents (X := X) (μ := κ y)
      (M1 := latentBernoulliMixtureKernelOf
        (kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch) y)
      (M2 := M) hrepCanon hrepM
  calc
    latentThetaKernelOf
        (kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch) y
      =
        DeFinettiConnection.mixingMeasureTheta
          (latentBernoulliMixtureKernelOf
            (kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch) y) := rfl
    _ = DeFinettiConnection.mixingMeasureTheta M := hΘeq
    _ = L y := hLM.symm

/-- Direct qualitative existence-uniqueness on latent `Theta`-measure kernels:
kernel exchangeability yields a unique latent `Y → Measure Theta` family. -/
theorem existsUnique_latentThetaKernel_of_kernelExchangeable
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : KernelExchangeable X κ) :
    ∃! L : Y → Measure DeFinettiConnection.Theta, KernelRepresentsLatentTheta X κ L := by
  refine
    ⟨latentThetaKernelOf
      (kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch), ?_, ?_⟩
  · exact latentThetaKernelOf_represents
      (kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch)
  · intro L hL
    exact (latentThetaKernel_unique_of_kernelExchangeable
      (X := X) (κ := κ) hX hexch L hL).symm

/-- Cone-morphism packaging theorem:
for an exchangeable kernel, the latent-`Theta` mediator is unique as a cone-morphism record. -/
theorem existsUnique_kernelLatentThetaConeMorphism_of_kernelExchangeable
    {X : ℕ → Ω → Bool} {κ : ProbabilityTheory.Kernel Y Ω}
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : KernelExchangeable X κ) :
    ∃! Φ : KernelLatentThetaConeMorphism X κ,
      Φ.mediator =
        latentThetaKernelOf
          (kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch) := by
  let hfac : KernelIIDFactorization X κ :=
    kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch
  let Φ0 : KernelLatentThetaConeMorphism X κ :=
    { mediator := latentThetaKernelOf hfac
      commutes := latentThetaKernelOf_represents hfac }
  refine ⟨Φ0, rfl, ?_⟩
  intro Φ hΦ
  cases Φ with
  | mk mediator commutes =>
      dsimp at hΦ
      cases hΦ
      simp [Φ0]

end Mettapedia.CategoryTheory
