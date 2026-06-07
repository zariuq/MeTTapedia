import Mettapedia.CategoryTheory.DeFinettiCategoricalInterface
import Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection
import Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
import Exchangeability.Core
import Exchangeability.Probability.InfiniteProduct

/-!
# de Finetti Projective Credal Bridge

This file adapts the existing de Finetti factorization surface to the shared
projective credal abstraction.

The bridge is intentionally explicit: a de Finetti mixture becomes a compatible
global precise prevision only after the caller supplies the interpretation map
from mixture objects to precise previsions over the chosen global state space.
-/

namespace Mettapedia.Logic.DeFinettiProjectiveCredalBridge

open MeasureTheory
open Mettapedia.Logic.DeFinetti
open Mettapedia.Logic.Exchangeability
open Mettapedia.CategoryTheory
open Mettapedia.ProbabilityTheory.HigherOrderProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

variable {Ω Window Global : Type*} [MeasurableSpace Ω] [LE Window]

/-! ## Concrete Bernoulli-prefix prevision adapters -/

/-- Explicit finite prefix-law obligations for a Bernoulli mixture.  The
analysis theorem that mixture integrals are nonnegative and sum to one is kept
as an explicit gate here; this adapter is the algebraic handoff into Walley
previsions once that gate is available. -/
structure BernoulliMixturePrefixLaw
    (M : BernoulliMixture) (n : ℕ) where
  nonneg : ∀ xs : Fin n → Bool, 0 ≤ M.prob xs
  total : ∑ xs : (Fin n → Bool), M.prob xs = 1

namespace BernoulliMixturePrefixLaw

/-- A proved finite Bernoulli prefix law gives finite probability weights. -/
noncomputable def toFiniteWeights
    {M : BernoulliMixture} {n : ℕ}
    (h : BernoulliMixturePrefixLaw M n) :
    PrecisePrevision.FiniteWeights (Fin n → Bool) where
  weight xs := M.prob xs
  nonneg := h.nonneg
  total := h.total

/-- A proved finite Bernoulli prefix law gives a precise prevision on prefix
gambles. -/
noncomputable def toPrecisePrevision
    {M : BernoulliMixture} {n : ℕ}
    (h : BernoulliMixturePrefixLaw M n) :
    PrecisePrevision (Fin n → Bool) :=
  h.toFiniteWeights.toPrecisePrevision

@[simp] theorem toPrecisePrevision_apply
    {M : BernoulliMixture} {n : ℕ}
    (h : BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    h.toPrecisePrevision X = ∑ xs, M.prob xs * X xs :=
  rfl

theorem toPrecisePrevision_precise
    {M : BernoulliMixture} {n : ℕ}
    (h : BernoulliMixturePrefixLaw M n) :
    h.toPrecisePrevision.toLowerPrevision.isPrecise :=
  PrecisePrevision.FiniteWeights.toPrecisePrevision_precise h.toFiniteWeights

end BernoulliMixturePrefixLaw

/-- Bernoulli mixtures analytically induce finite prefix laws.  Nonnegativity
comes from the nonnegative Bernoulli-product integrand on `[0,1]`; normalization
comes from the finite product PMF and Kyburg flattening. -/
theorem bernoulliMixturePrefixLaw_analytic
    (M : BernoulliMixture) (n : ℕ) :
    BernoulliMixturePrefixLaw M n where
  nonneg := DeFinettiConnection.bernoulliMixture_prob_nonneg M n
  total := DeFinettiConnection.bernoulliMixture_prob_total M n

/-! ## External exchangeability prefix adapters -/

/-- The vendored exchangeability library's `iidProduct` has the expected finite
prefix product marginal.  This is the bridge point from the external
Kolmogorov/i.i.d. construction into the projective-credal prefix surface. -/
theorem externalIIDProductPrefixMeasure_eq_product
    (ν : Measure Bool) [IsProbabilityMeasure ν] (n : ℕ) :
    (Exchangeability.Probability.iidProduct ν).map
        (Exchangeability.prefixProj (α := Bool) n) =
      Measure.pi fun _ : Fin n => ν := by
  simpa [Exchangeability.prefixProj] using
    (Exchangeability.Probability.iidProduct.cylinder_fintype
      (ν := ν) (n := n))

/-- A finite prefix marginal of an external i.i.d. product measure induces a
precise prevision on prefix gambles. -/
noncomputable def externalIIDProductPrefixPrevision
    (ν : Measure Bool) [IsProbabilityMeasure ν] (n : ℕ) :
    PrecisePrevision (Fin n → Bool) :=
  let μprefix : Measure (Fin n → Bool) :=
    (Exchangeability.Probability.iidProduct ν).map
      (Exchangeability.prefixProj (α := Bool) n)
  haveI : IsProbabilityMeasure μprefix :=
    Measure.isProbabilityMeasure_map
      ((Exchangeability.measurable_prefixProj (α := Bool) (n := n)).aemeasurable)
  PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision μprefix

theorem externalIIDProductPrefixPrevision_precise
    (ν : Measure Bool) [IsProbabilityMeasure ν] (n : ℕ) :
    (externalIIDProductPrefixPrevision ν n).toLowerPrevision.isPrecise := by
  let μprefix : Measure (Fin n → Bool) :=
    (Exchangeability.Probability.iidProduct ν).map
      (Exchangeability.prefixProj (α := Bool) n)
  haveI : IsProbabilityMeasure μprefix :=
    Measure.isProbabilityMeasure_map
      ((Exchangeability.measurable_prefixProj (α := Bool) (n := n)).aemeasurable)
  change
    (PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision
      μprefix).toLowerPrevision.isPrecise
  exact
    PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_precise
      μprefix

/-! ## External path-law prefix adapters -/

/-- The vendored exchangeability path-law construction restricts to the
finite-prefix law of the observed process.  Unlike the i.i.d. adapter above,
this works for an arbitrary measurable process. -/
theorem externalPathLawPrefixMeasure_eq_processPrefix
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → Bool)
    (hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ) :
    Measure.map (Exchangeability.prefixProj (α := Bool) n)
        (Exchangeability.pathLaw (α := Bool) μ X) =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ :=
  Exchangeability.pathLaw_map_prefix (α := Bool) μ X hX n

/-- Prefix-cylinder evaluation for the external path-law construction. -/
theorem externalPathLawPrefixCylinder_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → Bool)
    (hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ)
    (S : Set (Fin n → Bool)) (hS : MeasurableSet S) :
    Exchangeability.pathLaw (α := Bool) μ X
        (Exchangeability.prefixCylinder (α := Bool) S) =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ S := by
  have hprefix :=
    externalPathLawPrefixMeasure_eq_processPrefix
      (μ := μ) (X := X) hX n
  have hmap :
      Measure.map (Exchangeability.prefixProj (α := Bool) n)
          (Exchangeability.pathLaw (α := Bool) μ X) S =
        Exchangeability.pathLaw (α := Bool) μ X
          (Exchangeability.prefixCylinder (α := Bool) S) := by
    rw [Measure.map_apply
      (Exchangeability.measurable_prefixProj (α := Bool) (n := n)) hS]
    rfl
  rw [← hmap]
  exact congrArg (fun ν : Measure (Fin n → Bool) => ν S) hprefix

/-- Every finite Boolean prefix gamble is a bounded measurable observable. -/
noncomputable def externalPrefixBoundedMeasurableGamble
    (n : ℕ) (Y : Gamble (Fin n → Bool)) :
    BoundedMeasurableGamble (Fin n → Bool) :=
  BoundedMeasurableGamble.ofFinite Y

@[simp] theorem externalPrefixBoundedMeasurableGamble_apply
    (n : ℕ) (Y : Gamble (Fin n → Bool)) (xs : Fin n → Bool) :
    externalPrefixBoundedMeasurableGamble n Y xs = Y xs :=
  rfl

/-- Pulling a finite prefix gamble back along the external path projection gives
a bounded measurable path-space cylinder observable. -/
noncomputable def externalPathLawPrefixBoundedMeasurableGamble
    (n : ℕ) (Y : Gamble (Fin n → Bool)) :
    BoundedMeasurableGamble (ℕ → Bool) :=
  BoundedMeasurableGamble.pullback
    (Exchangeability.prefixProj (α := Bool) n)
    (Exchangeability.measurable_prefixProj (α := Bool) (n := n))
    (externalPrefixBoundedMeasurableGamble n Y)

@[simp] theorem externalPathLawPrefixBoundedMeasurableGamble_apply
    (n : ℕ) (Y : Gamble (Fin n → Bool)) (ω : ℕ → Bool) :
    externalPathLawPrefixBoundedMeasurableGamble n Y ω =
      Y (Exchangeability.prefixProj (α := Bool) n ω) :=
  rfl

/-- Pulling a finite prefix gamble back along a measurable Boolean process gives
a bounded measurable observable on the process's probability space. -/
noncomputable def externalProcessPrefixBoundedMeasurableGamble
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i))
    (n : ℕ) (Y : Gamble (Fin n → Bool)) :
    BoundedMeasurableGamble Ω :=
  BoundedMeasurableGamble.pullback
    (fun ω => fun i : Fin n => X i ω)
    (measurable_pi_lambda _ fun i => hX i)
    (externalPrefixBoundedMeasurableGamble n Y)

@[simp] theorem externalProcessPrefixBoundedMeasurableGamble_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i))
    (n : ℕ) (Y : Gamble (Fin n → Bool)) (ω : Ω) :
    externalProcessPrefixBoundedMeasurableGamble X hX n Y ω =
      Y (fun i : Fin n => X i ω) :=
  rfl

/-- Any finite prefix of an external path law over a probability space induces
a precise prevision on prefix gambles. -/
noncomputable def externalPathLawPrefixPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ) :
    PrecisePrevision (Fin n → Bool) :=
  let path : Measure (ℕ → Bool) := Exchangeability.pathLaw (α := Bool) μ X
  haveI : IsProbabilityMeasure path := by
    dsimp [path, Exchangeability.pathLaw]
    exact Measure.isProbabilityMeasure_map
      ((measurable_pi_lambda _ fun i => hX i).aemeasurable)
  let μprefix : Measure (Fin n → Bool) :=
    Measure.map (Exchangeability.prefixProj (α := Bool) n) path
  haveI : IsProbabilityMeasure μprefix :=
    Measure.isProbabilityMeasure_map
      ((Exchangeability.measurable_prefixProj (α := Bool) (n := n)).aemeasurable)
  PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision μprefix

theorem externalPathLawPrefixPrevision_precise
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ) :
    (externalPathLawPrefixPrevision μ X hX n).toLowerPrevision.isPrecise := by
  let path : Measure (ℕ → Bool) := Exchangeability.pathLaw (α := Bool) μ X
  haveI : IsProbabilityMeasure path := by
    dsimp [path, Exchangeability.pathLaw]
    exact Measure.isProbabilityMeasure_map
      ((measurable_pi_lambda _ fun i => hX i).aemeasurable)
  let μprefix : Measure (Fin n → Bool) :=
    Measure.map (Exchangeability.prefixProj (α := Bool) n) path
  haveI : IsProbabilityMeasure μprefix :=
    Measure.isProbabilityMeasure_map
      ((Exchangeability.measurable_prefixProj (α := Bool) (n := n)).aemeasurable)
  change
    (PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision
      μprefix).toLowerPrevision.isPrecise
  exact
    PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_precise
      μprefix

/-- For an external path law, σ-additive expectation of a bounded measurable
finite-prefix cylinder observable agrees with the finite-prefix precise
prevision used by the projective credal adapter. -/
theorem externalPathLawPrefixBoundedMeasurablePrevision_eq_prefixPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ)
    (Y : Gamble (Fin n → Bool)) :
    let path : Measure (ℕ → Bool) := Exchangeability.pathLaw (α := Bool) μ X
    haveI : IsProbabilityMeasure path := by
      dsimp [path, Exchangeability.pathLaw]
      exact Measure.isProbabilityMeasure_map
        ((measurable_pi_lambda _ fun i => hX i).aemeasurable)
    BoundedMeasurablePrecisePrevision.ofProbabilityMeasure path
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixPrevision μ X hX n Y := by
  dsimp only
  let path : Measure (ℕ → Bool) := Exchangeability.pathLaw (α := Bool) μ X
  haveI : IsProbabilityMeasure path := by
    dsimp [path, Exchangeability.pathLaw]
    exact Measure.isProbabilityMeasure_map
      ((measurable_pi_lambda _ fun i => hX i).aemeasurable)
  let μprefix : Measure (Fin n → Bool) :=
    Measure.map (Exchangeability.prefixProj (α := Bool) n) path
  haveI : IsProbabilityMeasure μprefix :=
    Measure.isProbabilityMeasure_map
      ((Exchangeability.measurable_prefixProj (α := Bool) (n := n)).aemeasurable)
  unfold externalPathLawPrefixPrevision
    externalPathLawPrefixBoundedMeasurableGamble
    externalPrefixBoundedMeasurableGamble
  have hpush :=
    BoundedMeasurablePrecisePrevision.ofProbabilityMeasure_map_apply
      path (Exchangeability.prefixProj (α := Bool) n)
      (Exchangeability.measurable_prefixProj (α := Bool) (n := n))
      (BoundedMeasurableGamble.ofFinite Y)
  rw [← hpush]
  exact
    PrecisePrevision.FiniteWeights.boundedMeasurablePrevision_ofFinite_eq_finiteProbabilityMeasurePrevision
      μprefix Y

/-! ## External path-law credal sets as projective specs -/

/-- A probability space together with a measurable Boolean process.  This is
the external-exchangeability carrier for finite path-law prefix adapters:
different elements of a credal set may use different underlying probability
spaces, but they all induce precise previsions on the common finite prefix
state space `Fin n → Bool`. -/
structure ExternalBoolProcessLaw (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  prob : IsProbabilityMeasure μ
  X : ℕ → Ω → Bool
  measurable : ∀ i : ℕ, Measurable (X i)

namespace ExternalBoolProcessLaw

/-- The finite-prefix precise prevision induced by an external Boolean process
law through the vendored exchangeability path-law construction. -/
noncomputable def prefixPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (A : ExternalBoolProcessLaw Ω) (n : ℕ) :
    PrecisePrevision (Fin n → Bool) := by
  haveI : IsProbabilityMeasure A.μ := A.prob
  exact externalPathLawPrefixPrevision A.μ A.X A.measurable n

theorem prefixPrevision_precise
    {Ω : Type*} [MeasurableSpace Ω]
    (A : ExternalBoolProcessLaw Ω) (n : ℕ) :
    (A.prefixPrevision n).toLowerPrevision.isPrecise := by
  haveI : IsProbabilityMeasure A.μ := A.prob
  exact externalPathLawPrefixPrevision_precise A.μ A.X A.measurable n

/-- Prefix-cylinder evaluation for the path law carried by an external Boolean
process law. -/
theorem prefixCylinder_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (A : ExternalBoolProcessLaw Ω) (n : ℕ)
    (S : Set (Fin n → Bool)) (hS : MeasurableSet S) :
    Exchangeability.pathLaw (α := Bool) A.μ A.X
        (Exchangeability.prefixCylinder (α := Bool) S) =
      Measure.map (fun ω => fun i : Fin n => A.X i ω) A.μ S := by
  exact externalPathLawPrefixCylinder_apply A.μ A.X A.measurable n S hS

/-- The common infinite-path sigma-additive bounded-observable prevision
induced by an external Boolean process law. -/
noncomputable def pathBoundedMeasurablePrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (A : ExternalBoolProcessLaw Ω) :
    BoundedMeasurablePrecisePrevision (ℕ → Bool) := by
  haveI : IsProbabilityMeasure A.μ := A.prob
  let path : Measure (ℕ → Bool) :=
    Exchangeability.pathLaw (α := Bool) A.μ A.X
  haveI : IsProbabilityMeasure path := by
    dsimp [path, Exchangeability.pathLaw]
    exact Measure.isProbabilityMeasure_map
      ((measurable_pi_lambda _ fun i => A.measurable i).aemeasurable)
  exact BoundedMeasurablePrecisePrevision.ofProbabilityMeasure path

/-- On finite-prefix cylinders, the infinite-path bounded-observable prevision
agrees with the finite-prefix precise prevision already used by the projective
credal adapter. -/
theorem pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (A : ExternalBoolProcessLaw Ω) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    A.pathBoundedMeasurablePrevision
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      A.prefixPrevision n Y := by
  unfold pathBoundedMeasurablePrevision prefixPrevision
  haveI : IsProbabilityMeasure A.μ := A.prob
  exact externalPathLawPrefixBoundedMeasurablePrevision_eq_prefixPrevision
    A.μ A.X A.measurable n Y

end ExternalBoolProcessLaw

/-- A credal set of external Boolean process laws induces a finite-prefix
credal set of precise previsions on `Fin n → Bool`. -/
noncomputable def externalPathLawPrefixCredalSet
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    CredalPrevisionSet (Fin n → Bool) :=
  {P | ∃ A : ExternalBoolProcessLaw Ω, A ∈ C ∧
    P = A.prefixPrevision n}

theorem externalPathLawPrefixCredalSet_nonempty
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty) :
    (externalPathLawPrefixCredalSet C n).Nonempty := by
  rcases hC with ⟨A, hA⟩
  exact ⟨A.prefixPrevision n, A, hA, rfl⟩

/-- A credal set of external Boolean process laws induces a bounded-measurable
credal set on the common infinite Boolean path space. -/
noncomputable def externalPathLawBoundedMeasurableCredalSet
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) :
    BoundedMeasurableCredalSet (ℕ → Bool) :=
  {P | ∃ A : ExternalBoolProcessLaw Ω, A ∈ C ∧
    P = A.pathBoundedMeasurablePrevision}

@[simp] theorem mem_externalPathLawBoundedMeasurableCredalSet
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C) :
    A.pathBoundedMeasurablePrevision ∈
      externalPathLawBoundedMeasurableCredalSet C :=
  ⟨A, hA, rfl⟩

/-- Nonempty external process-law credal sets induce nonempty bounded
path-space credal sets. -/
theorem externalPathLawBoundedMeasurableCredalSet_nonempty
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) :
    (externalPathLawBoundedMeasurableCredalSet C).Nonempty := by
  rcases hC with ⟨A, hA⟩
  exact ⟨A.pathBoundedMeasurablePrevision,
    mem_externalPathLawBoundedMeasurableCredalSet C hA⟩

/-- The bounded-measurable natural extension generated by external path laws
has an exact dominating-precise-completion envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCredalSet_hasExactDominatingPreciseEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) :
    boundedMeasurableHasExactDominatingPreciseEnvelope
      (boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)) :=
  boundedMeasurableNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)

/-- The bounded-measurable external path-law natural extension is below every
actual process-law prevision on every bounded path observable. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCredalSet_le_processPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty)
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C)
    (X : BoundedMeasurableGamble (ℕ → Bool)) :
    boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X ≤
      A.pathBoundedMeasurablePrevision X :=
  boundedMeasurableNaturalExtensionPrevision_le_completion
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
    (mem_externalPathLawBoundedMeasurableCredalSet C hA) X

/-- The bounded-measurable external path-law natural extension is the greatest
bounded lower prevision dominated by every actual process-law prevision. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCredalSet_greatest_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty)
    (L : BoundedMeasurableLowerPrevision (ℕ → Bool))
    (hL : ∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        L X ≤ A.pathBoundedMeasurablePrevision X)
    (X : BoundedMeasurableGamble (ℕ → Bool)) :
    L X ≤
      boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X := by
  apply boundedMeasurableNaturalExtensionPrevision_greatest_lower_bound
  intro P hP Y
  rcases hP with ⟨A, hA, rfl⟩
  exact hL A hA Y

/-- Every actual process-law prevision lies below the bounded-measurable
external path-law natural upper envelope on every bounded path observable. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCredalSet_processPrevision_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty)
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C)
    (X : BoundedMeasurableGamble (ℕ → Bool)) :
    A.pathBoundedMeasurablePrevision X ≤
      boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X :=
  boundedMeasurableNaturalUpperEnvelopePrevision_completion_le
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
    (mem_externalPathLawBoundedMeasurableCredalSet C hA) X

/-- The bounded-measurable external path-law natural upper envelope is the
least bounded upper prevision dominating every actual process-law prevision. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCredalSet_least_upper_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty)
    (U : BoundedMeasurableUpperPrevision (ℕ → Bool))
    (hU : ∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        A.pathBoundedMeasurablePrevision X ≤ U X)
    (X : BoundedMeasurableGamble (ℕ → Bool)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X ≤
      U X := by
  apply boundedMeasurableNaturalUpperEnvelopePrevision_least_upper_bound
  intro P hP Y
  rcases hP with ⟨A, hA, rfl⟩
  exact hU A hA Y

/-- Compact evaluation-closure carrier generated by a credal set of external
Boolean process laws on the common infinite path space. -/
noncomputable def externalPathLawBoundedMeasurableCompactCredalSet
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) :
    BoundedMeasurableCredalSet (ℕ → Bool) :=
  boundedMeasurableCredalSetEvaluationClosure
    (externalPathLawBoundedMeasurableCredalSet C)

/-- Every external path-law prevision belongs to the compact carrier generated
by its credal set. -/
theorem mem_externalPathLawBoundedMeasurableCompactCredalSet
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C) :
    A.pathBoundedMeasurablePrevision ∈
      externalPathLawBoundedMeasurableCompactCredalSet C :=
  boundedMeasurableCredalSet_subset_evaluationClosure
    (externalPathLawBoundedMeasurableCredalSet C)
    (mem_externalPathLawBoundedMeasurableCredalSet C hA)

/-- The compact external path-law bounded-measurable credal carrier is closed in
the evaluation topology. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_isClosed
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) :
    @IsClosed (BoundedMeasurablePrecisePrevision (ℕ → Bool))
      (BoundedMeasurablePrecisePrevision.evaluationTopology
        (Ω := ℕ → Bool))
      (externalPathLawBoundedMeasurableCompactCredalSet C) :=
  boundedMeasurableCredalSetEvaluationClosure_isClosed
    (externalPathLawBoundedMeasurableCredalSet C)

/-- The compact external path-law bounded-measurable credal carrier is compact
in the evaluation topology. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_isCompact
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) :
    @IsCompact (BoundedMeasurablePrecisePrevision (ℕ → Bool))
      (BoundedMeasurablePrecisePrevision.evaluationTopology
        (Ω := ℕ → Bool))
      (externalPathLawBoundedMeasurableCompactCredalSet C) :=
  boundedMeasurableCredalSetEvaluationClosure_isCompact
    (externalPathLawBoundedMeasurableCredalSet C)

/-- Nonempty external process-law credal sets induce nonempty compact
path-space credal carriers. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_nonempty
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) :
    (externalPathLawBoundedMeasurableCompactCredalSet C).Nonempty :=
  boundedMeasurableCredalSetEvaluationClosure_nonempty
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)

/-- Compactifying the external path-law bounded-measurable credal carrier
preserves the dominating precise completions of the generated natural
extension. -/
theorem boundedMeasurableDominatingPreciseCompletions_externalPathLawCompactCredalSet_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) :
    boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision
          (externalPathLawBoundedMeasurableCompactCredalSet C)
          (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)) =
      boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision
          (externalPathLawBoundedMeasurableCredalSet C)
          (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)) := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  exact
    boundedMeasurableDominatingPreciseCompletions_naturalExtension_evaluationClosure_eq
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)

/-- The compact external path-law natural extension has an exact
dominating-precise-completion envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_hasExactDominatingPreciseEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) :
    boundedMeasurableHasExactDominatingPreciseEnvelope
      (boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)) :=
  boundedMeasurableNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (externalPathLawBoundedMeasurableCompactCredalSet C)
    (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)

/-- The compact external path-law natural extension is below every actual
process-law prevision on every bounded path observable. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_le_processPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty)
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C)
    (X : BoundedMeasurableGamble (ℕ → Bool)) :
    boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC) X ≤
      A.pathBoundedMeasurablePrevision X :=
  boundedMeasurableNaturalExtensionPrevision_le_completion
    (externalPathLawBoundedMeasurableCompactCredalSet C)
    (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
    (mem_externalPathLawBoundedMeasurableCompactCredalSet C hA) X

/-- Every actual process-law prevision lies below the compact external path-law
natural upper envelope on every bounded path observable. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_processPrevision_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty)
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C)
    (X : BoundedMeasurableGamble (ℕ → Bool)) :
    A.pathBoundedMeasurablePrevision X ≤
      boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC) X :=
  boundedMeasurableNaturalUpperEnvelopePrevision_completion_le
    (externalPathLawBoundedMeasurableCompactCredalSet C)
    (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
    (mem_externalPathLawBoundedMeasurableCompactCredalSet C hA) X

/-- Evaluating finite-prefix cylinder observables over the infinite-path
bounded-measurable credal set gives exactly the same value set as evaluating
the existing finite-prefix credal set. -/
theorem externalPathLawBoundedMeasurableCredalSet_prefix_value_image_eq_finitePrefix
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    ((fun P : BoundedMeasurablePrecisePrevision (ℕ → Bool) =>
      P (externalPathLawPrefixBoundedMeasurableGamble n Y)) ''
        externalPathLawBoundedMeasurableCredalSet C) =
      ((fun P : PrecisePrevision (Fin n → Bool) => P Y) ''
        externalPathLawPrefixCredalSet C n) := by
  ext z
  constructor
  · rintro ⟨P, hP, rfl⟩
    rcases hP with ⟨A, hA, rfl⟩
    exact ⟨A.prefixPrevision n, ⟨A, hA, rfl⟩,
      (ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision
        A n Y).symm⟩
  · rintro ⟨P, hP, rfl⟩
    rcases hP with ⟨A, hA, rfl⟩
    exact ⟨A.pathBoundedMeasurablePrevision,
      mem_externalPathLawBoundedMeasurableCredalSet C hA,
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision
        A n Y⟩

/-- The lower envelope over a credal set of external path-law prefix
previsions. -/
noncomputable def externalPathLawPrefixLowerEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  lowerEnvelope (externalPathLawPrefixCredalSet C n)

/-- The external path-law prefix lower envelope is below every admissible
process-law prefix prevision. -/
theorem externalPathLawPrefixLowerEnvelope_le_processPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    externalPathLawPrefixLowerEnvelope C n X ≤ A.prefixPrevision n X := by
  simpa [externalPathLawPrefixLowerEnvelope] using
    finiteLowerEnvelopePrevision_le_completion
      (externalPathLawPrefixCredalSet C n)
      (externalPathLawPrefixCredalSet_nonempty C n ⟨A, hA⟩)
      (P := A.prefixPrevision n)
      (by exact ⟨A, hA, rfl⟩) X

/-- The external path-law prefix lower envelope is the greatest lower prevision
dominated by every admissible process-law prefix prevision. -/
theorem externalPathLawPrefixLowerEnvelope_greatest_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty)
    (L : LowerPrevision (Fin n → Bool))
    (hL : ∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool), L X ≤ A.prefixPrevision n X)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    L X ≤ externalPathLawPrefixLowerEnvelope C n X := by
  simpa [externalPathLawPrefixLowerEnvelope] using
    finiteLowerEnvelopePrevision_greatest_lower_bound
      (externalPathLawPrefixCredalSet C n)
      (externalPathLawPrefixCredalSet_nonempty C n hC) L
      (by
        intro P hP Y
        rcases hP with ⟨A, hA, rfl⟩
        exact hL A hA Y)
      X

/-- The upper envelope over a credal set of external path-law prefix
previsions. -/
noncomputable def externalPathLawPrefixUpperEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  upperEnvelope (externalPathLawPrefixCredalSet C n)

/-- The finite-prefix credal width induced by external path laws. -/
noncomputable def externalPathLawPrefixEnvelopeWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  credalEnvelopeWidth (externalPathLawPrefixCredalSet C n)

/-- The finite-prefix width-complement induced by external path laws, used as
the PLN-style confidence coordinate of the prefix credal projection. -/
noncomputable def externalPathLawPrefixEnvelopeWidthComplement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  credalEnvelopeWidthComplement (externalPathLawPrefixCredalSet C n)

/-- The finite-prefix midpoint induced by external path laws, used as the
PLN-style strength coordinate of the prefix credal projection. -/
noncomputable def externalPathLawPrefixEnvelopeMidpoint
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  credalEnvelopeMidpoint (externalPathLawPrefixCredalSet C n)

/-- The infinite-path bounded-measurable lower envelope, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix lower
envelope. -/
theorem boundedMeasurableLowerEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixLower
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableLowerEnvelope
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixLowerEnvelope C n Y := by
  unfold boundedMeasurableLowerEnvelope externalPathLawPrefixLowerEnvelope
    lowerEnvelope
  rw [externalPathLawBoundedMeasurableCredalSet_prefix_value_image_eq_finitePrefix]

/-- The bounded-measurable natural extension generated by external path laws,
restricted to a finite-prefix cylinder observable, is the existing finite-prefix
lower envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCredalSet_prefix_eq_finitePrefixLower
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    (hC : (externalPathLawBoundedMeasurableCredalSet C).Nonempty)
    (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCredalSet C) hC
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixLowerEnvelope C n Y := by
  rw [boundedMeasurableNaturalExtensionPrevision_apply,
    boundedMeasurableLowerEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixLower]

/-- The infinite-path bounded-measurable upper envelope, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix upper
envelope. -/
theorem boundedMeasurableUpperEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixUpper
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableUpperEnvelope
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixUpperEnvelope C n Y := by
  unfold boundedMeasurableUpperEnvelope externalPathLawPrefixUpperEnvelope
    upperEnvelope
  rw [externalPathLawBoundedMeasurableCredalSet_prefix_value_image_eq_finitePrefix]

/-- The bounded-measurable natural upper envelope generated by external path
laws, restricted to a finite-prefix cylinder observable, is the existing
finite-prefix upper envelope. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCredalSet_prefix_eq_finitePrefixUpper
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    (hC : (externalPathLawBoundedMeasurableCredalSet C).Nonempty)
    (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCredalSet C) hC
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixUpperEnvelope C n Y := by
  rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply,
    boundedMeasurableUpperEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixUpper]

/-- The infinite-path bounded-measurable envelope width, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix width. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCredalSet_prefix_eq_finitePrefixWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixEnvelopeWidth C n Y := by
  unfold boundedMeasurableEnvelopeWidth externalPathLawPrefixEnvelopeWidth
    credalEnvelopeWidth
  rw [
    boundedMeasurableLowerEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixLower,
    boundedMeasurableUpperEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixUpper]
  rfl

/-- The infinite-path bounded-measurable width-complement, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix confidence-like
coordinate. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCredalSet_prefix_eq_finitePrefixComplement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixEnvelopeWidthComplement C n Y := by
  unfold boundedMeasurableEnvelopeWidthComplement
    externalPathLawPrefixEnvelopeWidthComplement
    credalEnvelopeWidthComplement
  rw [
    boundedMeasurableEnvelopeWidth_externalPathLawCredalSet_prefix_eq_finitePrefixWidth]
  rfl

/-- The infinite-path bounded-measurable midpoint, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix strength-like
coordinate. -/
theorem boundedMeasurableEnvelopeMidpoint_externalPathLawCredalSet_prefix_eq_finitePrefixMidpoint
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixEnvelopeMidpoint C n Y := by
  unfold boundedMeasurableEnvelopeMidpoint externalPathLawPrefixEnvelopeMidpoint
    credalEnvelopeMidpoint
  rw [
    boundedMeasurableLowerEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixLower,
    boundedMeasurableUpperEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixUpper]
  rfl

/-- Compactifying the external path-law bounded-measurable credal carrier does
not change finite-prefix lower envelopes. -/
theorem boundedMeasurableLowerEnvelope_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableLowerEnvelope
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixLowerEnvelope C n Y := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableLowerEnvelope_evaluationClosure_eq
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
      (externalPathLawPrefixBoundedMeasurableGamble n Y),
    boundedMeasurableLowerEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixLower]

/-- Compactifying the external path-law bounded-measurable credal carrier does
not change finite-prefix upper envelopes. -/
theorem boundedMeasurableUpperEnvelope_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableUpperEnvelope
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixUpperEnvelope C n Y := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableUpperEnvelope_evaluationClosure_eq
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
      (externalPathLawPrefixBoundedMeasurableGamble n Y),
    boundedMeasurableUpperEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixUpper]

/-- The compact external path-law carrier has the same finite-prefix envelope
width as the raw external path-law carrier. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_finitePrefixWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixEnvelopeWidth C n Y := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableEnvelopeWidth_evaluationClosure_eq
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
      (externalPathLawPrefixBoundedMeasurableGamble n Y),
    boundedMeasurableEnvelopeWidth_externalPathLawCredalSet_prefix_eq_finitePrefixWidth]

/-- The compact external path-law carrier has the same finite-prefix
width-complement confidence coordinate as the raw external path-law carrier. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_finitePrefixComplement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixEnvelopeWidthComplement C n Y := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableEnvelopeWidthComplement_evaluationClosure_eq
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
      (externalPathLawPrefixBoundedMeasurableGamble n Y),
    boundedMeasurableEnvelopeWidthComplement_externalPathLawCredalSet_prefix_eq_finitePrefixComplement]

/-- The compact external path-law carrier has the same finite-prefix midpoint
strength coordinate as the raw external path-law carrier. -/
theorem boundedMeasurableEnvelopeMidpoint_externalPathLawCompactCredalSet_prefix_eq_finitePrefixMidpoint
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixEnvelopeMidpoint C n Y := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableEnvelopeMidpoint_evaluationClosure_eq
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
      (externalPathLawPrefixBoundedMeasurableGamble n Y),
    boundedMeasurableEnvelopeMidpoint_externalPathLawCredalSet_prefix_eq_finitePrefixMidpoint]

/-- The compact external path-law natural extension, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix lower
envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixLowerEnvelope C n Y := by
  rw [boundedMeasurableNaturalExtensionPrevision_apply,
    boundedMeasurableLowerEnvelope_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
      C hC n Y]

/-- The compact external path-law natural upper envelope, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix upper
envelope. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixUpperEnvelope C n Y := by
  rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply,
    boundedMeasurableUpperEnvelope_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
      C hC n Y]

/-- If an external path-law finite-prefix gamble spans the full unit interval,
then the compact bounded-measurable path-law carrier reads midpoint strength
one half on the corresponding prefix cylinder observable. -/
theorem boundedMeasurableEnvelopeMidpoint_externalPathLawCompactCredalSet_prefix_eq_half_of_prefixUnitInterval
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hL : externalPathLawPrefixLowerEnvelope C n Y = 0)
    (hU : externalPathLawPrefixUpperEnvelope C n Y = 1) :
    boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) = (1 / 2 : ℝ) := by
  apply boundedMeasurableEnvelopeMidpoint_eq_half_of_natural_interval
    (C := externalPathLawBoundedMeasurableCompactCredalSet C)
    (hC := externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
  · rw [
      boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
        C hC n Y]
    exact hL
  · rw [
      boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
        C hC n Y]
    exact hU

/-- If an external path-law finite-prefix gamble spans the full unit interval,
then the compact bounded-measurable path-law carrier has maximal prefix-cylinder
width. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_one_of_prefixUnitInterval
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hL : externalPathLawPrefixLowerEnvelope C n Y = 0)
    (hU : externalPathLawPrefixUpperEnvelope C n Y = 1) :
    boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) = 1 := by
  apply boundedMeasurableEnvelopeWidth_eq_one_of_natural_interval
    (C := externalPathLawBoundedMeasurableCompactCredalSet C)
    (hC := externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
  · rw [
      boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
        C hC n Y]
    exact hL
  · rw [
      boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
        C hC n Y]
    exact hU

/-- If an external path-law finite-prefix gamble spans the full unit interval,
then the compact bounded-measurable path-law carrier has zero width-complement
confidence on the corresponding prefix cylinder observable. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_zero_of_prefixUnitInterval
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hL : externalPathLawPrefixLowerEnvelope C n Y = 0)
    (hU : externalPathLawPrefixUpperEnvelope C n Y = 1) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) = 0 := by
  apply boundedMeasurableEnvelopeWidthComplement_eq_zero_of_natural_interval
    (C := externalPathLawBoundedMeasurableCompactCredalSet C)
    (hC := externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
  · rw [
      boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
        C hC n Y]
    exact hL
  · rw [
      boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
        C hC n Y]
    exact hU

/-- Unit-valued finite-prefix observables have bounded path-space envelope
width in `[0,1]`. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCredalSet_prefix_in_unit_of_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    (hC : (externalPathLawBoundedMeasurableCredalSet C).Nonempty)
    (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hY : ∀ xs, Y xs ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) ∈
      Set.Icc (0 : ℝ) 1 :=
  boundedMeasurableEnvelopeWidth_in_unit_of_unit
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawPrefixBoundedMeasurableGamble n Y) hC
    (by intro ω; exact hY (fun i : Fin n => ω i))

/-- Unit-valued finite-prefix observables have bounded path-space
width-complement confidence coordinate in `[0,1]`. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCredalSet_prefix_in_unit_of_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    (hC : (externalPathLawBoundedMeasurableCredalSet C).Nonempty)
    (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hY : ∀ xs, Y xs ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) ∈
      Set.Icc (0 : ℝ) 1 :=
  boundedMeasurableEnvelopeWidthComplement_in_unit_of_unit
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawPrefixBoundedMeasurableGamble n Y) hC
    (by intro ω; exact hY (fun i : Fin n => ω i))

/-- Unit-valued finite-prefix observables have bounded path-space midpoint
strength coordinate in `[0,1]`. -/
theorem boundedMeasurableEnvelopeMidpoint_externalPathLawCredalSet_prefix_in_unit_of_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    (hC : (externalPathLawBoundedMeasurableCredalSet C).Nonempty)
    (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hY : ∀ xs, Y xs ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) ∈
      Set.Icc (0 : ℝ) 1 :=
  boundedMeasurableEnvelopeMidpoint_in_unit_of_unit
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawPrefixBoundedMeasurableGamble n Y) hC
    (by intro ω; exact hY (fun i : Fin n => ω i))

/-- Every admissible external process-law prefix prevision is below the prefix
upper envelope. -/
theorem externalPathLawPrefixPrevision_le_upperEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    A.prefixPrevision n X ≤ externalPathLawPrefixUpperEnvelope C n X := by
  simpa [externalPathLawPrefixUpperEnvelope] using
    finiteCompletion_le_upperEnvelopePrevision
      (externalPathLawPrefixCredalSet C n)
      (externalPathLawPrefixCredalSet_nonempty C n ⟨A, hA⟩)
      (P := A.prefixPrevision n)
      (by exact ⟨A, hA, rfl⟩) X

/-- The external path-law prefix upper envelope is the least upper prevision
dominating every admissible process-law prefix prevision. -/
theorem externalPathLawPrefixUpperEnvelope_least_upper_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty)
    (U : UpperPrevision (Fin n → Bool))
    (hU : ∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool), A.prefixPrevision n X ≤ U X)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    externalPathLawPrefixUpperEnvelope C n X ≤ U X := by
  simpa [externalPathLawPrefixUpperEnvelope] using
    finiteUpperEnvelopePrevision_least_upper_bound
      (externalPathLawPrefixCredalSet C n)
      (externalPathLawPrefixCredalSet_nonempty C n hC) U
      (by
        intro P hP Y
        rcases hP with ⟨A, hA, rfl⟩
        exact hU A hA Y)
      X

/-- The finite-prefix credal set induced by external Boolean process laws as a
one-window projective local-credal specification. -/
noncomputable def externalPathLawPrefixProjectiveSpec
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    ProjectiveLocalCredalSpec PUnit.{1} (Fin n → Bool) :=
  identityCredalProjectiveSpec (externalPathLawPrefixCredalSet C n)

@[simp] theorem externalPathLawPrefixProjectiveSpec_projectiveLimitCredalSet
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    (externalPathLawPrefixProjectiveSpec C n).projectiveLimitCredalSet =
      externalPathLawPrefixCredalSet C n := by
  simp [externalPathLawPrefixProjectiveSpec]

theorem externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty) :
    (externalPathLawPrefixProjectiveSpec C n).hasCompatibleCompletion := by
  rw [externalPathLawPrefixProjectiveSpec,
    identityCredalProjectiveSpec_hasCompatibleCompletion_iff]
  exact externalPathLawPrefixCredalSet_nonempty C n hC

/-- A finite external path-law prefix natural extension is Walley-coherent as a
finite lower envelope of precise process-prefix previsions. -/
theorem externalPathLawPrefixProjectiveSpec_finiteGlobalNaturalExtensionPrevision_isCoherent
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty) :
    ((externalPathLawPrefixProjectiveSpec C n).finiteGlobalNaturalExtensionPrevision
      (externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion C n hC)).isCoherent :=
  ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_isCoherent
    (S := externalPathLawPrefixProjectiveSpec C n)
    (externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion C n hC)

/-- A finite external path-law prefix natural extension is exactly the lower
envelope of the precise previsions dominating it. -/
theorem externalPathLawPrefixProjectiveSpec_finiteGlobalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty) :
    hasExactDominatingPreciseEnvelope
      ((externalPathLawPrefixProjectiveSpec C n).finiteGlobalNaturalExtensionPrevision
        (externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion C n hC)) :=
  ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (S := externalPathLawPrefixProjectiveSpec C n)
    (externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion C n hC)

/-- The projective natural extension of an external path-law prefix credal set
is exactly its lower envelope. -/
@[simp] theorem externalPathLawPrefixProjectiveSpec_globalNaturalExtension
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (externalPathLawPrefixProjectiveSpec C n).globalNaturalExtension X =
      externalPathLawPrefixLowerEnvelope C n X := by
  simp [externalPathLawPrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalNaturalExtension,
    externalPathLawPrefixLowerEnvelope]

/-- The projective upper envelope of an external path-law prefix credal set is
exactly its upper envelope. -/
@[simp] theorem externalPathLawPrefixProjectiveSpec_upperEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    upperEnvelope
        (externalPathLawPrefixProjectiveSpec C n).projectiveLimitCredalSet X =
      externalPathLawPrefixUpperEnvelope C n X := by
  simp [externalPathLawPrefixProjectiveSpec, externalPathLawPrefixUpperEnvelope]

/-- The projective global width of an external path-law prefix credal set is
exactly its prefix envelope width. -/
@[simp] theorem externalPathLawPrefixProjectiveSpec_globalEnvelopeWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeWidth X =
      externalPathLawPrefixEnvelopeWidth C n X := by
  simp [externalPathLawPrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeWidth,
    externalPathLawPrefixEnvelopeWidth]

/-- The projective global width-complement of an external path-law prefix
credal set is exactly its prefix width-complement. -/
@[simp] theorem externalPathLawPrefixProjectiveSpec_globalEnvelopeWidthComplement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeWidthComplement X =
      externalPathLawPrefixEnvelopeWidthComplement C n X := by
  simp [externalPathLawPrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement,
    externalPathLawPrefixEnvelopeWidthComplement]

/-- The projective global midpoint of an external path-law prefix credal set is
exactly its prefix midpoint. -/
@[simp] theorem externalPathLawPrefixProjectiveSpec_globalEnvelopeMidpoint
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeMidpoint X =
      externalPathLawPrefixEnvelopeMidpoint C n X := by
  simp [externalPathLawPrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeMidpoint,
    externalPathLawPrefixEnvelopeMidpoint]

/-- The compact external path-law natural extension agrees on finite-prefix
cylinder observables with the finite projective Walley natural extension of
the corresponding prefix credal set. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_projectiveNaturalExtensionPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      ((externalPathLawPrefixProjectiveSpec C n).finiteGlobalNaturalExtensionPrevision
        (externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion C n hC)) Y := by
  rw [
    boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
      C hC n Y]
  rw [ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_apply]
  rw [externalPathLawPrefixProjectiveSpec_globalNaturalExtension]

/-- The compact external path-law natural upper envelope agrees on
finite-prefix cylinder observables with the finite projective Walley upper
envelope of the corresponding prefix credal set. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_projectiveUpperEnvelopePrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      ((externalPathLawPrefixProjectiveSpec C n).finiteGlobalUpperEnvelopePrevision
        (externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion C n hC)) Y := by
  rw [
    boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
      C hC n Y]
  rw [ProjectiveLocalCredalSpec.finiteGlobalUpperEnvelopePrevision_apply]
  rw [externalPathLawPrefixProjectiveSpec_upperEnvelope]

/-- The compact external path-law carrier and the finite projective prefix
Walley interface compute the same PLN-facing interval width. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_projectiveEnvelopeWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeWidth Y := by
  rw [
    boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_finitePrefixWidth
      C hC n Y,
    externalPathLawPrefixProjectiveSpec_globalEnvelopeWidth]

/-- The compact external path-law carrier and the finite projective prefix
Walley interface compute the same PLN-facing width-complement confidence
coordinate. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_projectiveEnvelopeWidthComplement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeWidthComplement Y := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_finitePrefixComplement
      C hC n Y,
    externalPathLawPrefixProjectiveSpec_globalEnvelopeWidthComplement]

/-- The compact external path-law carrier and the finite projective prefix
Walley interface compute the same PLN-facing midpoint strength coordinate. -/
theorem boundedMeasurableEnvelopeMidpoint_externalPathLawCompactCredalSet_prefix_eq_projectiveEnvelopeMidpoint
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeMidpoint Y := by
  rw [
    boundedMeasurableEnvelopeMidpoint_externalPathLawCompactCredalSet_prefix_eq_finitePrefixMidpoint
      C hC n Y,
    externalPathLawPrefixProjectiveSpec_globalEnvelopeMidpoint]

/-- Agreement of all admissible external process laws on a finite-prefix gamble
makes that gamble determined by the projective credal set. -/
theorem externalPathLawPrefixProjectiveSpec_determinesGlobalGamble_of_processAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
      ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
        A.prefixPrevision n X = B.prefixPrevision n X) :
    (externalPathLawPrefixProjectiveSpec C n).determinesGlobalGamble X := by
  rw [externalPathLawPrefixProjectiveSpec,
    identityCredalProjectiveSpec_determinesGlobalGamble_iff]
  intro P hP Q hQ
  rcases hP with ⟨A, hA, rfl⟩
  rcases hQ with ⟨B, hB, rfl⟩
  exact hAgree A hA B hB

/-- Disagreement between two admissible external process laws on a finite-prefix
gamble gives strict projective credal width. -/
theorem externalPathLawPrefixProjectiveSpec_hasStrictGlobalWidth_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n X < B.prefixPrevision n X) :
    (externalPathLawPrefixProjectiveSpec C n).hasStrictGlobalWidth X := by
  rw [externalPathLawPrefixProjectiveSpec,
    identityCredalProjectiveSpec_hasStrictGlobalWidth_iff]
  refine ⟨A.prefixPrevision n, ?_, B.prefixPrevision n, ?_, hlt⟩
  · exact ⟨A, hA, rfl⟩
  · exact ⟨B, hB, rfl⟩

/-- External process-law disagreement produces a nontrivial finite-prefix
lower/upper envelope. -/
theorem externalPathLawPrefixCredalSet_lowerUpperEnvelope_nontrivial_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n X < B.prefixPrevision n X) :
    lowerEnvelope (externalPathLawPrefixCredalSet C n) X <
      upperEnvelope (externalPathLawPrefixCredalSet C n) X := by
  exact
    lower_upperEnvelope_nontrivial_of_strictWidth
      (externalPathLawPrefixCredalSet C n) X
      (finite_credalRange_bddBelow (externalPathLawPrefixCredalSet C n) X)
      (finite_credalRange_bddAbove (externalPathLawPrefixCredalSet C n) X)
      (by
        refine ⟨A.prefixPrevision n, ?_, B.prefixPrevision n, ?_, hlt⟩
        · exact ⟨A, hA, rfl⟩
        · exact ⟨B, hB, rfl⟩)

/-- External process-law disagreement gives positive finite-prefix credal
envelope width. -/
theorem externalPathLawPrefixCredalSet_envelopeWidth_pos_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n X < B.prefixPrevision n X) :
    0 < credalEnvelopeWidth (externalPathLawPrefixCredalSet C n) X := by
  exact
    credalEnvelopeWidth_pos_of_strictWidth
      (externalPathLawPrefixCredalSet C n) X
      (finite_credalRange_bddBelow (externalPathLawPrefixCredalSet C n) X)
      (finite_credalRange_bddAbove (externalPathLawPrefixCredalSet C n) X)
      (by
        refine ⟨A.prefixPrevision n, ?_, B.prefixPrevision n, ?_, hlt⟩
        · exact ⟨A, hA, rfl⟩
        · exact ⟨B, hB, rfl⟩)

/-- If all admissible external process laws agree on a finite-prefix gamble,
then the PLN-style width-complement confidence coordinate is maximal. -/
theorem externalPathLawPrefixEnvelopeWidthComplement_eq_one_of_processAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
      ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
        A.prefixPrevision n X = B.prefixPrevision n X) :
    externalPathLawPrefixEnvelopeWidthComplement C n X = 1 := by
  rcases hC with ⟨A, hA⟩
  unfold externalPathLawPrefixEnvelopeWidthComplement
  exact
    credalEnvelopeWidthComplement_eq_one_of_credalSetDetermines
      (externalPathLawPrefixCredalSet C n) X
      (externalPathLawPrefixCredalSet_nonempty C n ⟨A, hA⟩)
      (finite_credalRange_bddBelow (externalPathLawPrefixCredalSet C n) X)
      (finite_credalRange_bddAbove (externalPathLawPrefixCredalSet C n) X)
      (P := A.prefixPrevision n)
      (by exact ⟨A, hA, rfl⟩)
      (by
        intro P hP Q hQ
        rcases hP with ⟨B, hB, rfl⟩
        rcases hQ with ⟨D, hD, rfl⟩
        exact hAgree B hB D hD)

/-- If two admissible external process laws disagree on a finite-prefix gamble,
then the PLN-style width-complement confidence coordinate is strictly below
one. -/
theorem externalPathLawPrefixEnvelopeWidthComplement_lt_one_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n X < B.prefixPrevision n X) :
    externalPathLawPrefixEnvelopeWidthComplement C n X < 1 := by
  unfold externalPathLawPrefixEnvelopeWidthComplement
  exact
    credalEnvelopeWidthComplement_lt_one_of_strictWidth
      (externalPathLawPrefixCredalSet C n) X
      (finite_credalRange_bddBelow (externalPathLawPrefixCredalSet C n) X)
      (finite_credalRange_bddAbove (externalPathLawPrefixCredalSet C n) X)
      (by
        refine ⟨A.prefixPrevision n, ?_, B.prefixPrevision n, ?_, hlt⟩
        · exact ⟨A, hA, rfl⟩
        · exact ⟨B, hB, rfl⟩)

/-- If all admissible external process laws agree on a finite-prefix gamble,
then the compact path-space credal carrier determines the corresponding
bounded-measurable cylinder observable. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_determines_prefix_of_processAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
      ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
        A.prefixPrevision n Y = B.prefixPrevision n Y) :
    boundedMeasurableCredalSetDetermines
      (externalPathLawBoundedMeasurableCompactCredalSet C)
      (externalPathLawPrefixBoundedMeasurableGamble n Y) := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  exact boundedMeasurableCredalSetDetermines_evaluationClosure_of_determines
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
    (externalPathLawPrefixBoundedMeasurableGamble n Y)
    (by
      intro P hP Q hQ
      rcases hP with ⟨A, hA, rfl⟩
      rcases hQ with ⟨B, hB, rfl⟩
      rw [
        ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision,
        ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision]
      exact hAgree A hA B hB)

/-- If two admissible external process laws disagree on a finite-prefix gamble,
then the compact path-space credal carrier has strict width on the corresponding
bounded-measurable cylinder observable. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_hasStrictWidth_prefix_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n Y < B.prefixPrevision n Y) :
    boundedMeasurableCredalSetHasStrictWidth
      (externalPathLawBoundedMeasurableCompactCredalSet C)
      (externalPathLawPrefixBoundedMeasurableGamble n Y) := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  exact boundedMeasurableCredalSetHasStrictWidth_evaluationClosure_of_strictWidth
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawPrefixBoundedMeasurableGamble n Y)
    (by
      refine ⟨A.pathBoundedMeasurablePrevision,
        mem_externalPathLawBoundedMeasurableCredalSet C hA,
        B.pathBoundedMeasurablePrevision,
        mem_externalPathLawBoundedMeasurableCredalSet C hB, ?_⟩
      rw [
        ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision,
        ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision]
      exact hlt)

/-- Disagreement between two admissible external process laws on a finite-prefix
gamble is realized by compact path-space endpoint completions: one attains the
lower endpoint, one attains the upper endpoint, and the gap is strict. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_exists_endpointPair_prefix_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n Y < B.prefixPrevision n Y) :
    ∃ Plo : BoundedMeasurablePrecisePrevision (ℕ → Bool),
      Plo ∈ externalPathLawBoundedMeasurableCompactCredalSet C ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision (ℕ → Bool),
        Phi ∈ externalPathLawBoundedMeasurableCompactCredalSet C ∧
        Plo (externalPathLawPrefixBoundedMeasurableGamble n Y) =
          externalPathLawPrefixLowerEnvelope C n Y ∧
        Phi (externalPathLawPrefixBoundedMeasurableGamble n Y) =
          externalPathLawPrefixUpperEnvelope C n Y ∧
        Plo (externalPathLawPrefixBoundedMeasurableGamble n Y) <
          Phi (externalPathLawPrefixBoundedMeasurableGamble n Y) := by
  have hRawLt :
      A.pathBoundedMeasurablePrevision
          (externalPathLawPrefixBoundedMeasurableGamble n Y) <
        B.pathBoundedMeasurablePrevision
          (externalPathLawPrefixBoundedMeasurableGamble n Y) := by
    rw [
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision,
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision]
    exact hlt
  rcases boundedMeasurableEnvelope_exists_endpointPairReadout_evaluationClosure_of_disagreement
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawPrefixBoundedMeasurableGamble n Y)
      (mem_externalPathLawBoundedMeasurableCredalSet C hA)
      (mem_externalPathLawBoundedMeasurableCredalSet C hB) hRawLt with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hltEndpoints, _hWidth, _hComplement,
      _hMidpoint⟩
  refine ⟨Plo, hPlo, Phi, hPhi, ?_, ?_, hltEndpoints⟩
  · rw [hlo]
    exact
      boundedMeasurableLowerEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixLower
        C n Y
  · rw [hhi]
    exact
      boundedMeasurableUpperEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixUpper
        C n Y

/-- Compact path-space determination on a finite-prefix cylinder is exactly
agreement of all admissible external process laws on the corresponding prefix
prevision. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_determines_prefix_iff_processAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableCredalSetDetermines
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) ↔
      ∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
        ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
          A.prefixPrevision n Y = B.prefixPrevision n Y := by
  constructor
  · intro hDet A hA B hB
    have hEq := hDet A.pathBoundedMeasurablePrevision
      (mem_externalPathLawBoundedMeasurableCompactCredalSet C hA)
      B.pathBoundedMeasurablePrevision
      (mem_externalPathLawBoundedMeasurableCompactCredalSet C hB)
    rw [
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision,
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision] at hEq
    exact hEq
  · exact externalPathLawBoundedMeasurableCompactCredalSet_determines_prefix_of_processAgreement
      C hC n Y

/-- Compact path-space strict width on a finite-prefix cylinder is exactly
strict disagreement between two admissible external process laws on the
corresponding prefix prevision.  Thus compactifying the path-law carrier does not
manufacture new PLN imprecision. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_hasStrictWidth_prefix_iff_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableCredalSetHasStrictWidth
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) ↔
      ∃ A : ExternalBoolProcessLaw Ω, A ∈ C ∧
        ∃ B : ExternalBoolProcessLaw Ω, B ∈ C ∧
          A.prefixPrevision n Y < B.prefixPrevision n Y := by
  constructor
  · intro hWidth
    have hRaw :
        boundedMeasurableCredalSetHasStrictWidth
          (externalPathLawBoundedMeasurableCredalSet C)
          (externalPathLawPrefixBoundedMeasurableGamble n Y) := by
      unfold externalPathLawBoundedMeasurableCompactCredalSet at hWidth
      exact
        (boundedMeasurableCredalSetHasStrictWidth_evaluationClosure_iff
          (externalPathLawBoundedMeasurableCredalSet C)
          (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
          (externalPathLawPrefixBoundedMeasurableGamble n Y)).1 hWidth
    rcases hRaw with ⟨P, hP, Q, hQ, hlt⟩
    rcases hP with ⟨A, hA, rfl⟩
    rcases hQ with ⟨B, hB, rfl⟩
    rw [
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision,
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision] at hlt
    exact ⟨A, hA, B, hB, hlt⟩
  · rintro ⟨A, hA, B, hB, hlt⟩
    exact externalPathLawBoundedMeasurableCompactCredalSet_hasStrictWidth_prefix_of_processDisagreement
      C n Y hA hB hlt

/-- Disagreement between two admissible external process laws is realized by
Walley dominating completions of the compact path-law natural extension.

This is the de Finetti/path-law specialization of the generic
bounded-measurable Walley endpoint theorem: the endpoint completions dominate
the compact path-law natural extension, are strictly separated on the prefix
cylinder query, and compute the finite-prefix PLN-facing width,
width-complement, and midpoint coordinates. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_exists_dominatingStrictEndpointPairReadout_prefix_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n Y < B.prefixPrevision n Y) :
    ∃ Plo : BoundedMeasurablePrecisePrevision (ℕ → Bool),
      Plo ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision
            (externalPathLawBoundedMeasurableCompactCredalSet C)
            (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
              C ⟨A, hA⟩)) ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision (ℕ → Bool),
        Phi ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision
            (externalPathLawBoundedMeasurableCompactCredalSet C)
            (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
              C ⟨A, hA⟩)) ∧
        Plo (externalPathLawPrefixBoundedMeasurableGamble n Y) =
          externalPathLawPrefixLowerEnvelope C n Y ∧
        Phi (externalPathLawPrefixBoundedMeasurableGamble n Y) =
          externalPathLawPrefixUpperEnvelope C n Y ∧
        Plo (externalPathLawPrefixBoundedMeasurableGamble n Y) <
          Phi (externalPathLawPrefixBoundedMeasurableGamble n Y) ∧
        externalPathLawPrefixEnvelopeWidth C n Y =
          Phi (externalPathLawPrefixBoundedMeasurableGamble n Y) -
            Plo (externalPathLawPrefixBoundedMeasurableGamble n Y) ∧
        externalPathLawPrefixEnvelopeWidthComplement C n Y =
          1 -
            (Phi (externalPathLawPrefixBoundedMeasurableGamble n Y) -
              Plo (externalPathLawPrefixBoundedMeasurableGamble n Y)) ∧
        externalPathLawPrefixEnvelopeMidpoint C n Y =
          (Plo (externalPathLawPrefixBoundedMeasurableGamble n Y) +
            Phi (externalPathLawPrefixBoundedMeasurableGamble n Y)) / 2 := by
  let Cc : BoundedMeasurableCredalSet (ℕ → Bool) :=
    externalPathLawBoundedMeasurableCompactCredalSet C
  let Z : BoundedMeasurableGamble (ℕ → Bool) :=
    externalPathLawPrefixBoundedMeasurableGamble n Y
  have hCc : Cc.Nonempty := by
    dsimp [Cc]
    exact externalPathLawBoundedMeasurableCompactCredalSet_nonempty
      C ⟨A, hA⟩
  have hStrict :
      boundedMeasurableCredalSetHasStrictWidth Cc Z := by
    dsimp [Cc, Z]
    exact
      externalPathLawBoundedMeasurableCompactCredalSet_hasStrictWidth_prefix_of_processDisagreement
        C n Y hA hB hlt
  rcases
      boundedMeasurableNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
        Cc hCc Z hStrict with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hltEndpoints, hWidthEq, hCompEq, hMidEq⟩
  have hloPrefix :
      Plo Z = externalPathLawPrefixLowerEnvelope C n Y := by
    calc
      Plo Z = boundedMeasurableNaturalExtensionPrevision Cc hCc Z := hlo
      _ = externalPathLawPrefixLowerEnvelope C n Y := by
        dsimp [Cc, Z, hCc]
        exact
          boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
            C ⟨A, hA⟩ n Y
  have hhiPrefix :
      Phi Z = externalPathLawPrefixUpperEnvelope C n Y := by
    calc
      Phi Z = boundedMeasurableNaturalUpperEnvelopePrevision Cc hCc Z := hhi
      _ = externalPathLawPrefixUpperEnvelope C n Y := by
        dsimp [Cc, Z, hCc]
        exact
          boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
            C ⟨A, hA⟩ n Y
  have hWidthPrefix :
      externalPathLawPrefixEnvelopeWidth C n Y = Phi Z - Plo Z := by
    calc
      externalPathLawPrefixEnvelopeWidth C n Y =
          boundedMeasurableEnvelopeWidth Cc Z := by
        dsimp [Cc, Z]
        exact
          (boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_finitePrefixWidth
            C ⟨A, hA⟩ n Y).symm
      _ = Phi Z - Plo Z := hWidthEq
  have hCompPrefix :
      externalPathLawPrefixEnvelopeWidthComplement C n Y =
        1 - (Phi Z - Plo Z) := by
    calc
      externalPathLawPrefixEnvelopeWidthComplement C n Y =
          boundedMeasurableEnvelopeWidthComplement Cc Z := by
        dsimp [Cc, Z]
        exact
          (boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_finitePrefixComplement
            C ⟨A, hA⟩ n Y).symm
      _ = 1 - (Phi Z - Plo Z) := hCompEq
  have hMidPrefix :
      externalPathLawPrefixEnvelopeMidpoint C n Y = (Plo Z + Phi Z) / 2 := by
    calc
      externalPathLawPrefixEnvelopeMidpoint C n Y =
          boundedMeasurableEnvelopeMidpoint Cc Z := by
        dsimp [Cc, Z]
        exact
          (boundedMeasurableEnvelopeMidpoint_externalPathLawCompactCredalSet_prefix_eq_finitePrefixMidpoint
            C ⟨A, hA⟩ n Y).symm
      _ = (Plo Z + Phi Z) / 2 := hMidEq
  refine ⟨Plo, ?_, Phi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Cc] using hPlo
  · simpa [Cc] using hPhi
  · simpa [Z] using hloPrefix
  · simpa [Z] using hhiPrefix
  · simpa [Z] using hltEndpoints
  · simpa [Z] using hWidthPrefix
  · simpa [Z] using hCompPrefix
  · simpa [Z] using hMidPrefix

/-- Agreement of all admissible external process laws forces zero compact
path-space envelope width on the finite-prefix cylinder observable. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_zero_of_processAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
      ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
        A.prefixPrevision n Y = B.prefixPrevision n Y) :
    boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) = 0 := by
  rcases hC with ⟨A, hA⟩
  rw [
    boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_finitePrefixWidth
      C ⟨A, hA⟩ n Y]
  exact credalEnvelopeWidth_eq_zero_of_credalSetDetermines
    (externalPathLawPrefixCredalSet C n) Y
    (externalPathLawPrefixCredalSet_nonempty C n ⟨A, hA⟩)
    (finite_credalRange_bddBelow (externalPathLawPrefixCredalSet C n) Y)
    (finite_credalRange_bddAbove (externalPathLawPrefixCredalSet C n) Y)
    (P := A.prefixPrevision n)
    (by exact ⟨A, hA, rfl⟩)
    (by
      intro P hP Q hQ
      rcases hP with ⟨B, hB, rfl⟩
      rcases hQ with ⟨D, hD, rfl⟩
      exact hAgree B hB D hD)

/-- Disagreement between two admissible external process laws gives positive
compact path-space envelope width on the finite-prefix cylinder observable. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_pos_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n Y < B.prefixPrevision n Y) :
    0 < boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) := by
  rw [
    boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_finitePrefixWidth
      C hC n Y]
  exact externalPathLawPrefixCredalSet_envelopeWidth_pos_of_processDisagreement
    C n Y hA hB hlt

/-- Agreement of all admissible external process laws makes the compact
path-space width-complement confidence coordinate maximal on the finite-prefix
cylinder observable. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_one_of_processAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
      ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
        A.prefixPrevision n Y = B.prefixPrevision n Y) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) = 1 := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_finitePrefixComplement
      C hC n Y]
  exact externalPathLawPrefixEnvelopeWidthComplement_eq_one_of_processAgreement
    C n hC Y hAgree

/-- Disagreement between two admissible external process laws pushes the compact
path-space width-complement confidence coordinate strictly below one on the
finite-prefix cylinder observable. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_lt_one_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n Y < B.prefixPrevision n Y) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) < 1 := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_finitePrefixComplement
      C hC n Y]
  exact externalPathLawPrefixEnvelopeWidthComplement_lt_one_of_processDisagreement
    C n Y hA hB hlt

/-- The finite-prefix law obligation is exactly the claim that the prefix
probabilities form a finite probability vector.  This isolates the remaining
analytic work for arbitrary Bernoulli mixtures: prove the finite weights exist
from the mixture integral, then the projective-credal adapter is automatic. -/
theorem bernoulliMixturePrefixLaw_iff_finiteWeights
    (M : BernoulliMixture) (n : ℕ) :
    BernoulliMixturePrefixLaw M n ↔
      ∃ w : PrecisePrevision.FiniteWeights (Fin n → Bool),
        ∀ xs : Fin n → Bool, w.weight xs = M.prob xs := by
  constructor
  · intro h
    exact ⟨h.toFiniteWeights, fun xs => rfl⟩
  · rintro ⟨w, hw⟩
    refine ⟨?_, ?_⟩
    · intro xs
      simpa [← hw xs] using w.nonneg xs
    · calc
        ∑ xs : (Fin n → Bool), M.prob xs =
            ∑ xs : (Fin n → Bool), w.weight xs := by
          apply Finset.sum_congr rfl
          intro xs _hxs
          exact (hw xs).symm
        _ = 1 := w.total

/-- A credal set of Bernoulli mixtures induces a finite-prefix credal set of
precise previsions once each mixture has its prefix-law obligations discharged. -/
noncomputable def bernoulliMixturePrefixCredalSet
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    CredalPrevisionSet (Fin n → Bool) :=
  {P | ∃ M : BernoulliMixture, ∃ hM : M ∈ C,
    P = (hLaw M hM).toPrecisePrevision}

theorem bernoulliMixturePrefixCredalSet_nonempty
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    (bernoulliMixturePrefixCredalSet C n hLaw).Nonempty := by
  rcases hC with ⟨M, hM⟩
  exact ⟨(hLaw M hM).toPrecisePrevision, M, hM, rfl⟩

/-- The lower envelope over an imprecise de Finetti credal set at a finite
prefix. -/
noncomputable def impreciseDeFinettiPrefixLowerEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  lowerEnvelope (bernoulliMixturePrefixCredalSet C n hLaw)

/-- The imprecise de Finetti prefix lower envelope is below every admissible
mixture-prefix precise prevision. -/
theorem impreciseDeFinettiPrefixLowerEnvelope_le_mixturePrevision
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    {M : BernoulliMixture} (hM : M ∈ C)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    impreciseDeFinettiPrefixLowerEnvelope C n hLaw X ≤
      (hLaw M hM).toPrecisePrevision X := by
  simpa [impreciseDeFinettiPrefixLowerEnvelope] using
    finiteLowerEnvelopePrevision_le_completion
      (bernoulliMixturePrefixCredalSet C n hLaw)
      (bernoulliMixturePrefixCredalSet_nonempty C n hLaw ⟨M, hM⟩)
      (P := (hLaw M hM).toPrecisePrevision)
      (by exact ⟨M, hM, rfl⟩) X

/-- The imprecise de Finetti prefix lower envelope is the greatest lower
prevision dominated by every admissible mixture-prefix precise prevision. -/
theorem impreciseDeFinettiPrefixLowerEnvelope_greatest_lower_bound
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (L : LowerPrevision (Fin n → Bool))
    (hL : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool), L X ≤ (hLaw M hM).toPrecisePrevision X)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    L X ≤ impreciseDeFinettiPrefixLowerEnvelope C n hLaw X := by
  simpa [impreciseDeFinettiPrefixLowerEnvelope] using
    finiteLowerEnvelopePrevision_greatest_lower_bound
      (bernoulliMixturePrefixCredalSet C n hLaw)
      (bernoulliMixturePrefixCredalSet_nonempty C n hLaw hC) L
      (by
        intro P hP Y
        rcases hP with ⟨M, hM, rfl⟩
        exact hL M hM Y)
      X

/-- The upper envelope over an imprecise de Finetti credal set at a finite
prefix. -/
noncomputable def impreciseDeFinettiPrefixUpperEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  upperEnvelope (bernoulliMixturePrefixCredalSet C n hLaw)

/-- The finite-prefix credal width induced by an imprecise de Finetti set of
Bernoulli mixtures. -/
noncomputable def impreciseDeFinettiPrefixEnvelopeWidth
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  credalEnvelopeWidth (bernoulliMixturePrefixCredalSet C n hLaw)

/-- The finite-prefix width-complement induced by an imprecise de Finetti set
of Bernoulli mixtures, used as the PLN-style confidence coordinate. -/
noncomputable def impreciseDeFinettiPrefixEnvelopeWidthComplement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  credalEnvelopeWidthComplement (bernoulliMixturePrefixCredalSet C n hLaw)

/-- The finite-prefix midpoint induced by an imprecise de Finetti set of
Bernoulli mixtures, used as the PLN-style strength coordinate. -/
noncomputable def impreciseDeFinettiPrefixEnvelopeMidpoint
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  credalEnvelopeMidpoint (bernoulliMixturePrefixCredalSet C n hLaw)

/-- Every admissible Bernoulli-mixture prefix prevision is below the imprecise
de Finetti prefix upper envelope. -/
theorem impreciseDeFinettiPrefixPrevision_le_upperEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    {M : BernoulliMixture} (hM : M ∈ C)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (hLaw M hM).toPrecisePrevision X ≤
      impreciseDeFinettiPrefixUpperEnvelope C n hLaw X := by
  simpa [impreciseDeFinettiPrefixUpperEnvelope] using
    finiteCompletion_le_upperEnvelopePrevision
      (bernoulliMixturePrefixCredalSet C n hLaw)
      (bernoulliMixturePrefixCredalSet_nonempty C n hLaw ⟨M, hM⟩)
      (P := (hLaw M hM).toPrecisePrevision)
      (by exact ⟨M, hM, rfl⟩) X

/-- The imprecise de Finetti prefix upper envelope is the least upper
prevision dominating every admissible mixture-prefix precise prevision. -/
theorem impreciseDeFinettiPrefixUpperEnvelope_least_upper_bound
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (U : UpperPrevision (Fin n → Bool))
    (hU : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool), (hLaw M hM).toPrecisePrevision X ≤ U X)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    impreciseDeFinettiPrefixUpperEnvelope C n hLaw X ≤ U X := by
  simpa [impreciseDeFinettiPrefixUpperEnvelope] using
    finiteUpperEnvelopePrevision_least_upper_bound
      (bernoulliMixturePrefixCredalSet C n hLaw)
      (bernoulliMixturePrefixCredalSet_nonempty C n hLaw hC) U
      (by
        intro P hP Y
        rcases hP with ⟨M, hM, rfl⟩
        exact hU M hM Y)
      X

/-! ## Finite-prefix de Finetti credal sets as projective specs -/

/-- The finite-prefix credal set of Bernoulli mixtures as a one-window
projective local credal specification.  This reuses the generic identity-window
adapter: no new projective machinery is duplicated. -/
noncomputable def bernoulliMixturePrefixProjectiveSpec
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    ProjectiveLocalCredalSpec PUnit.{1} (Fin n → Bool) :=
  identityCredalProjectiveSpec (bernoulliMixturePrefixCredalSet C n hLaw)

@[simp] theorem bernoulliMixturePrefixProjectiveSpec_projectiveLimitCredalSet
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).projectiveLimitCredalSet =
      bernoulliMixturePrefixCredalSet C n hLaw := by
  simp [bernoulliMixturePrefixProjectiveSpec]

theorem bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasCompatibleCompletion := by
  rw [bernoulliMixturePrefixProjectiveSpec,
    identityCredalProjectiveSpec_hasCompatibleCompletion_iff]
  exact bernoulliMixturePrefixCredalSet_nonempty C n hLaw hC

/-- A finite Bernoulli-mixture prefix natural extension is Walley-coherent as a
finite lower envelope of precise mixture-prefix previsions. -/
theorem bernoulliMixturePrefixProjectiveSpec_finiteGlobalNaturalExtensionPrevision_isCoherent
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    ((bernoulliMixturePrefixProjectiveSpec C n hLaw).finiteGlobalNaturalExtensionPrevision
      (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)).isCoherent :=
  ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_isCoherent
    (S := bernoulliMixturePrefixProjectiveSpec C n hLaw)
    (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)

/-- A finite Bernoulli-mixture prefix natural extension is exactly the lower
envelope of the precise previsions dominating it. -/
theorem bernoulliMixturePrefixProjectiveSpec_finiteGlobalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    hasExactDominatingPreciseEnvelope
      ((bernoulliMixturePrefixProjectiveSpec C n hLaw).finiteGlobalNaturalExtensionPrevision
        (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)) :=
  ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (S := bernoulliMixturePrefixProjectiveSpec C n hLaw)
    (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)

/-- The projective natural extension of a finite-prefix de Finetti credal set
is exactly its Walley lower envelope. -/
@[simp] theorem bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalNaturalExtension X =
      impreciseDeFinettiPrefixLowerEnvelope C n hLaw X := by
  simp [bernoulliMixturePrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalNaturalExtension,
    impreciseDeFinettiPrefixLowerEnvelope]

/-- The projective upper envelope of a finite-prefix de Finetti credal set is
exactly its upper envelope. -/
@[simp] theorem bernoulliMixturePrefixProjectiveSpec_upperEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    upperEnvelope
        (bernoulliMixturePrefixProjectiveSpec C n hLaw).projectiveLimitCredalSet X =
      impreciseDeFinettiPrefixUpperEnvelope C n hLaw X := by
  simp [bernoulliMixturePrefixProjectiveSpec,
    impreciseDeFinettiPrefixUpperEnvelope]

/-- The packaged finite projective Walley natural extension of an imprecise
Bernoulli-mixture prefix credal set is exactly its lower envelope. -/
theorem bernoulliMixturePrefixProjectiveSpec_finiteGlobalNaturalExtensionPrevision_eq_lowerEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    ((bernoulliMixturePrefixProjectiveSpec C n hLaw).finiteGlobalNaturalExtensionPrevision
        (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)) X =
      impreciseDeFinettiPrefixLowerEnvelope C n hLaw X := by
  rw [ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_apply]
  rw [bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension]

/-- The packaged finite projective Walley upper envelope of an imprecise
Bernoulli-mixture prefix credal set is exactly its upper envelope. -/
theorem bernoulliMixturePrefixProjectiveSpec_finiteGlobalUpperEnvelopePrevision_eq_upperEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    ((bernoulliMixturePrefixProjectiveSpec C n hLaw).finiteGlobalUpperEnvelopePrevision
        (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)) X =
      impreciseDeFinettiPrefixUpperEnvelope C n hLaw X := by
  rw [ProjectiveLocalCredalSpec.finiteGlobalUpperEnvelopePrevision_apply]
  rw [bernoulliMixturePrefixProjectiveSpec_upperEnvelope]

/-- The projective global width of a finite-prefix de Finetti credal set is
exactly its prefix envelope width. -/
@[simp] theorem bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidth
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalEnvelopeWidth X =
      impreciseDeFinettiPrefixEnvelopeWidth C n hLaw X := by
  simp [bernoulliMixturePrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeWidth,
    impreciseDeFinettiPrefixEnvelopeWidth]

/-- The projective global width-complement of a finite-prefix de Finetti
credal set is exactly its prefix width-complement. -/
@[simp] theorem bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidthComplement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalEnvelopeWidthComplement X =
      impreciseDeFinettiPrefixEnvelopeWidthComplement C n hLaw X := by
  simp [bernoulliMixturePrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement,
    impreciseDeFinettiPrefixEnvelopeWidthComplement]

/-- The projective global midpoint of a finite-prefix de Finetti credal set is
exactly its prefix midpoint. -/
@[simp] theorem bernoulliMixturePrefixProjectiveSpec_globalEnvelopeMidpoint
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalEnvelopeMidpoint X =
      impreciseDeFinettiPrefixEnvelopeMidpoint C n hLaw X := by
  simp [bernoulliMixturePrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeMidpoint,
    impreciseDeFinettiPrefixEnvelopeMidpoint]

/-- If all admissible Bernoulli mixtures agree on a finite-prefix gamble, then
the projective de Finetti prefix credal set determines that gamble. -/
theorem bernoulliMixturePrefixProjectiveSpec_determinesGlobalGamble_of_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
        (hLaw M hM).toPrecisePrevision X =
          (hLaw N hN).toPrecisePrevision X) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).determinesGlobalGamble X := by
  rw [bernoulliMixturePrefixProjectiveSpec,
    identityCredalProjectiveSpec_determinesGlobalGamble_iff]
  intro P hP Q hQ
  rcases hP with ⟨M, hM, rfl⟩
  rcases hQ with ⟨N, hN, rfl⟩
  exact hAgree M hM N hN

/-- If two admissible Bernoulli mixtures disagree on a finite-prefix gamble, the
projective de Finetti prefix credal set has strict global width on that gamble. -/
theorem bernoulliMixturePrefixProjectiveSpec_hasStrictGlobalWidth_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (hLaw M hM).toPrecisePrevision X <
        (hLaw N hN).toPrecisePrevision X) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasStrictGlobalWidth X := by
  rw [bernoulliMixturePrefixProjectiveSpec,
    identityCredalProjectiveSpec_hasStrictGlobalWidth_iff]
  refine ⟨(hLaw M hM).toPrecisePrevision, ?_,
    (hLaw N hN).toPrecisePrevision, ?_, hlt⟩
  · exact ⟨M, hM, rfl⟩
  · exact ⟨N, hN, rfl⟩

/-- Mixture disagreement produces a nontrivial finite-prefix de Finetti
lower/upper envelope.  Boundedness is automatic because the prefix state space
is finite. -/
theorem bernoulliMixturePrefixCredalSet_lowerUpperEnvelope_nontrivial_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (hLaw M hM).toPrecisePrevision X <
        (hLaw N hN).toPrecisePrevision X) :
    lowerEnvelope (bernoulliMixturePrefixCredalSet C n hLaw) X <
      upperEnvelope (bernoulliMixturePrefixCredalSet C n hLaw) X := by
  exact
    lower_upperEnvelope_nontrivial_of_strictWidth
      (bernoulliMixturePrefixCredalSet C n hLaw) X
      (finite_credalRange_bddBelow
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (finite_credalRange_bddAbove
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (by
        refine ⟨(hLaw M hM).toPrecisePrevision, ?_,
          (hLaw N hN).toPrecisePrevision, ?_, hlt⟩
        · exact ⟨M, hM, rfl⟩
        · exact ⟨N, hN, rfl⟩)

/-- The same finite-prefix de Finetti disagreement expressed as positive
prefix credal envelope width. -/
theorem bernoulliMixturePrefixCredalSet_envelopeWidth_pos_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (hLaw M hM).toPrecisePrevision X <
        (hLaw N hN).toPrecisePrevision X) :
    0 < credalEnvelopeWidth (bernoulliMixturePrefixCredalSet C n hLaw) X := by
  exact
    credalEnvelopeWidth_pos_of_strictWidth
      (bernoulliMixturePrefixCredalSet C n hLaw) X
      (finite_credalRange_bddBelow
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (finite_credalRange_bddAbove
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (by
        refine ⟨(hLaw M hM).toPrecisePrevision, ?_,
          (hLaw N hN).toPrecisePrevision, ?_, hlt⟩
        · exact ⟨M, hM, rfl⟩
        · exact ⟨N, hN, rfl⟩)

/-- If all admissible Bernoulli mixtures agree on a finite-prefix gamble, then
the imprecise de Finetti width-complement confidence coordinate is maximal. -/
theorem impreciseDeFinettiPrefixEnvelopeWidthComplement_eq_one_of_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
        (hLaw M hM).toPrecisePrevision X =
          (hLaw N hN).toPrecisePrevision X) :
    impreciseDeFinettiPrefixEnvelopeWidthComplement C n hLaw X = 1 := by
  rcases hC with ⟨M, hM⟩
  unfold impreciseDeFinettiPrefixEnvelopeWidthComplement
  exact
    credalEnvelopeWidthComplement_eq_one_of_credalSetDetermines
      (bernoulliMixturePrefixCredalSet C n hLaw) X
      (bernoulliMixturePrefixCredalSet_nonempty C n hLaw ⟨M, hM⟩)
      (finite_credalRange_bddBelow
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (finite_credalRange_bddAbove
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (P := (hLaw M hM).toPrecisePrevision)
      (by exact ⟨M, hM, rfl⟩)
      (by
        intro P hP Q hQ
        rcases hP with ⟨N, hN, rfl⟩
        rcases hQ with ⟨O, hO, rfl⟩
        exact hAgree N hN O hO)

/-- If two admissible Bernoulli mixtures disagree on a finite-prefix gamble,
then the imprecise de Finetti width-complement confidence coordinate is
strictly below one. -/
theorem impreciseDeFinettiPrefixEnvelopeWidthComplement_lt_one_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (hLaw M hM).toPrecisePrevision X <
        (hLaw N hN).toPrecisePrevision X) :
    impreciseDeFinettiPrefixEnvelopeWidthComplement C n hLaw X < 1 := by
  unfold impreciseDeFinettiPrefixEnvelopeWidthComplement
  exact
    credalEnvelopeWidthComplement_lt_one_of_strictWidth
      (bernoulliMixturePrefixCredalSet C n hLaw) X
      (finite_credalRange_bddBelow
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (finite_credalRange_bddAbove
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (by
        refine ⟨(hLaw M hM).toPrecisePrevision, ?_,
          (hLaw N hN).toPrecisePrevision, ?_, hlt⟩
        · exact ⟨M, hM, rfl⟩
        · exact ⟨N, hN, rfl⟩)

/-- Disagreement between two admissible Bernoulli mixtures is realized by
Walley dominating completions of the finite-prefix natural extension.

The endpoint completions need not be admissible mixtures themselves.  They are
precise previsions dominating the finite-prefix lower envelope, and they touch
the lower and conjugate upper endpoints that compute the imprecise de Finetti
PLN-facing width, width-complement, and midpoint coordinates. -/
theorem impreciseDeFinettiPrefix_exists_dominatingStrictEndpointPairReadout_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (hLaw M hM).toPrecisePrevision X <
        (hLaw N hN).toPrecisePrevision X) :
    ∃ Plo : PrecisePrevision (Fin n → Bool),
      Plo ∈ dominatingPreciseCompletions
          ((bernoulliMixturePrefixProjectiveSpec C n hLaw).finiteGlobalNaturalExtensionPrevision
            (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
              C n hLaw ⟨M, hM⟩)) ∧
      ∃ Phi : PrecisePrevision (Fin n → Bool),
        Phi ∈ dominatingPreciseCompletions
          ((bernoulliMixturePrefixProjectiveSpec C n hLaw).finiteGlobalNaturalExtensionPrevision
            (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
              C n hLaw ⟨M, hM⟩)) ∧
        Plo X = impreciseDeFinettiPrefixLowerEnvelope C n hLaw X ∧
        Phi X = impreciseDeFinettiPrefixUpperEnvelope C n hLaw X ∧
        Plo X < Phi X ∧
        impreciseDeFinettiPrefixEnvelopeWidth C n hLaw X =
          Phi X - Plo X ∧
        impreciseDeFinettiPrefixEnvelopeWidthComplement C n hLaw X =
          1 - (Phi X - Plo X) ∧
        impreciseDeFinettiPrefixEnvelopeMidpoint C n hLaw X =
          (Plo X + Phi X) / 2 := by
  have hProjectiveWidth :
      (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasStrictGlobalWidth X :=
    bernoulliMixturePrefixProjectiveSpec_hasStrictGlobalWidth_of_mixtureDisagreement
      C n hLaw X hM hN hlt
  rcases
      ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
        (S := bernoulliMixturePrefixProjectiveSpec C n hLaw)
        (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
          C n hLaw ⟨M, hM⟩) X hProjectiveWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hltEndpoints, hWidthEq, hCompEq, hMidEq⟩
  have hloPrefix :
      Plo X = impreciseDeFinettiPrefixLowerEnvelope C n hLaw X :=
    hlo.trans (bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension
      C n hLaw X)
  have hhiPrefix :
      Phi X = impreciseDeFinettiPrefixUpperEnvelope C n hLaw X :=
    hhi.trans (bernoulliMixturePrefixProjectiveSpec_upperEnvelope C n hLaw X)
  refine ⟨Plo, ?_, Phi, ?_, hloPrefix, hhiPrefix, hltEndpoints, ?_, ?_, ?_⟩
  · exact hPlo
  · exact hPhi
  · calc
      impreciseDeFinettiPrefixEnvelopeWidth C n hLaw X =
          (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalEnvelopeWidth X :=
        (bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidth C n hLaw X).symm
      _ = Phi X - Plo X := hWidthEq
  · calc
      impreciseDeFinettiPrefixEnvelopeWidthComplement C n hLaw X =
          (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalEnvelopeWidthComplement X :=
        (bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidthComplement C n hLaw X).symm
      _ = 1 - (Phi X - Plo X) := hCompEq
  · calc
      impreciseDeFinettiPrefixEnvelopeMidpoint C n hLaw X =
          (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalEnvelopeMidpoint X :=
        (bernoulliMixturePrefixProjectiveSpec_globalEnvelopeMidpoint C n hLaw X).symm
      _ = (Plo X + Phi X) / 2 := hMidEq

/-- Adapter from a de Finetti Bernoulli-mixture factorization into a projective
credal specification.  The `mixtureCompatible` field is the honest gluing map:
it says which projective credal completion the latent mixture induces. -/
structure DeFinettiProjectiveCredalSpecialization
    (X : ℕ → Ω → Bool) (μ : Measure Ω) where
  projectiveSpec : ProjectiveLocalCredalSpec Window Global
  completionOfMixture : BernoulliMixture → PrecisePrevision Global
  mixtureCompatible :
    ∀ M : BernoulliMixture, Represents M X μ →
      completionOfMixture M ∈ projectiveSpec.projectiveLimitCredalSet

namespace DeFinettiProjectiveCredalSpecialization

variable {X : ℕ → Ω → Bool} {μ : Measure Ω}

/-- A de Finetti factorization, plus an explicit adapter from mixtures to
projective precise previsions, gives a nonempty compatible projective credal
set. -/
theorem hasCompatibleCompletion_of_factorization
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := Window) (Global := Global) X μ)
    (hfac : CategoricalDeFinettiFactorization X μ) :
    D.projectiveSpec.hasCompatibleCompletion := by
  let M := latentBernoulliMixtureOf hfac
  exact D.projectiveSpec.projectiveLimitCredalSet_nonempty_of_completion
    (P := D.completionOfMixture M)
    (by
      intro i
      exact D.mixtureCompatible M
        (latentBernoulliMixtureOf_represents hfac) i)

/-- Exchangeability supplies the de Finetti factorization; the adapter supplies
the projective credal completion. -/
theorem hasCompatibleCompletion_of_exchangeable
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := Window) (Global := Global) X μ)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    D.projectiveSpec.hasCompatibleCompletion :=
  D.hasCompatibleCompletion_of_factorization
    (categoricalDeFinetti_factorization_of_exchangeable X μ hX hexch)

end DeFinettiProjectiveCredalSpecialization

/-! ## Profile surface -/

/-- Proof-carrying profile for the de Finetti face of the shared projective
credal abstraction. -/
structure ProjectiveDeFinettiCredalBridgeProfile where
  analyticPrefixLaw :
    ∀ (M : BernoulliMixture) (n : ℕ),
      BernoulliMixturePrefixLaw M n
  prefixLawIffFiniteWeights :
    ∀ (M : BernoulliMixture) (n : ℕ),
      BernoulliMixturePrefixLaw M n ↔
        ∃ w : PrecisePrevision.FiniteWeights (Fin n → Bool),
          ∀ xs : Fin n → Bool, w.weight xs = M.prob xs
  externalIIDProductPrefixMeasureEqProduct :
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (n : ℕ),
      (Exchangeability.Probability.iidProduct ν).map
          (Exchangeability.prefixProj (α := Bool) n) =
        Measure.pi fun _ : Fin n => ν
  externalIIDProductPrefixPrevisionIsPrecise :
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (n : ℕ),
      (externalIIDProductPrefixPrevision ν n).toLowerPrevision.isPrecise
  externalPathLawPrefixMeasureEqProcessPrefix :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) (X : ℕ → Ω → Bool)
      (_hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ),
      Measure.map (Exchangeability.prefixProj (α := Bool) n)
          (Exchangeability.pathLaw (α := Bool) μ X) =
        Measure.map (fun ω => fun i : Fin n => X i ω) μ
  externalPathLawPrefixCylinderApply :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) (X : ℕ → Ω → Bool)
      (_hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ)
      (S : Set (Fin n → Bool)) (_hS : MeasurableSet S),
      Exchangeability.pathLaw (α := Bool) μ X
          (Exchangeability.prefixCylinder (α := Bool) S) =
        Measure.map (fun ω => fun i : Fin n => X i ω) μ S
  externalPathLawPrefixPrevisionIsPrecise :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Bool) (_hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ),
      (externalPathLawPrefixPrevision μ X _hX n).toLowerPrevision.isPrecise
  externalProcessPrefixPrevisionIsPrecise :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (_A : ExternalBoolProcessLaw Ω) (n : ℕ),
      (_A.prefixPrevision n).toLowerPrevision.isPrecise
  externalProcessPrefixCylinderApply :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (_A : ExternalBoolProcessLaw Ω) (n : ℕ)
      (S : Set (Fin n → Bool)) (_hS : MeasurableSet S),
      Exchangeability.pathLaw (α := Bool) _A.μ _A.X
          (Exchangeability.prefixCylinder (α := Bool) S) =
        Measure.map (fun ω => fun i : Fin n => _A.X i ω) _A.μ S
  externalPathLawPrefixCredalSetNonempty :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ),
      C.Nonempty → (externalPathLawPrefixCredalSet C n).Nonempty
  externalPathLawPrefixProjectiveSpecLimitSet :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ),
      (externalPathLawPrefixProjectiveSpec C n).projectiveLimitCredalSet =
        externalPathLawPrefixCredalSet C n
  externalPathLawPrefixProjectiveSpecHasCompatibleCompletion :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ),
      C.Nonempty →
        (externalPathLawPrefixProjectiveSpec C n).hasCompatibleCompletion
  externalPathLawPrefixProjectiveSpecNaturalExtensionEqLowerEnvelope :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (externalPathLawPrefixProjectiveSpec C n).globalNaturalExtension X =
        externalPathLawPrefixLowerEnvelope C n X
  externalPathLawPrefixLowerEnvelopeLeProcess :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      {A : ExternalBoolProcessLaw Ω},
      A ∈ C →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        externalPathLawPrefixLowerEnvelope C n X ≤ A.prefixPrevision n X
  externalPathLawPrefixLowerEnvelopeGreatestLowerBound :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ),
      C.Nonempty →
      ∀ L : LowerPrevision (Fin n → Bool),
      (∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
        ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
          (Fin n → Bool), L X ≤ A.prefixPrevision n X) →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        L X ≤ externalPathLawPrefixLowerEnvelope C n X
  externalPathLawPrefixProjectiveSpecUpperEnvelopeEqUpperEnvelope :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      upperEnvelope
          (externalPathLawPrefixProjectiveSpec C n).projectiveLimitCredalSet X =
        externalPathLawPrefixUpperEnvelope C n X
  externalPathLawPrefixProjectiveSpecWidthEqEnvelopeWidth :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeWidth X =
        externalPathLawPrefixEnvelopeWidth C n X
  externalPathLawPrefixProjectiveSpecWidthComplementEqEnvelopeWidthComplement :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeWidthComplement X =
        externalPathLawPrefixEnvelopeWidthComplement C n X
  externalPathLawPrefixProjectiveSpecMidpointEqEnvelopeMidpoint :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeMidpoint X =
        externalPathLawPrefixEnvelopeMidpoint C n X
  externalPathLawPrefixPrevisionLeUpperEnvelope :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      {A : ExternalBoolProcessLaw Ω},
      A ∈ C →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        A.prefixPrevision n X ≤ externalPathLawPrefixUpperEnvelope C n X
  externalPathLawPrefixUpperEnvelopeLeastUpperBound :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ),
      C.Nonempty →
      ∀ U : UpperPrevision (Fin n → Bool),
      (∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
        ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
          (Fin n → Bool), A.prefixPrevision n X ≤ U X) →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        externalPathLawPrefixUpperEnvelope C n X ≤ U X
  externalPathLawBoundedNaturalExtensionLeProcess :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)),
      (hC : C.Nonempty) →
      ∀ {A : ExternalBoolProcessLaw Ω}, A ∈ C →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        boundedMeasurableNaturalExtensionPrevision
            (externalPathLawBoundedMeasurableCredalSet C)
            (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X ≤
          A.pathBoundedMeasurablePrevision X
  externalPathLawBoundedNaturalExtensionGreatestLowerBound :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)),
      (hC : C.Nonempty) →
      ∀ L : BoundedMeasurableLowerPrevision (ℕ → Bool),
      (∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
        ∀ X : BoundedMeasurableGamble (ℕ → Bool),
          L X ≤ A.pathBoundedMeasurablePrevision X) →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        L X ≤
          boundedMeasurableNaturalExtensionPrevision
            (externalPathLawBoundedMeasurableCredalSet C)
            (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X
  externalPathLawBoundedNaturalUpperEnvelopeProcessLe :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)),
      (hC : C.Nonempty) →
      ∀ {A : ExternalBoolProcessLaw Ω}, A ∈ C →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        A.pathBoundedMeasurablePrevision X ≤
          boundedMeasurableNaturalUpperEnvelopePrevision
            (externalPathLawBoundedMeasurableCredalSet C)
            (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X
  externalPathLawBoundedNaturalUpperEnvelopeLeastUpperBound :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)),
      (hC : C.Nonempty) →
      ∀ U : BoundedMeasurableUpperPrevision (ℕ → Bool),
      (∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
        ∀ X : BoundedMeasurableGamble (ℕ → Bool),
          A.pathBoundedMeasurablePrevision X ≤ U X) →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        boundedMeasurableNaturalUpperEnvelopePrevision
            (externalPathLawBoundedMeasurableCredalSet C)
            (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X ≤
          U X
  externalPathLawCompactBoundedNaturalExtensionLeProcess :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)),
      (hC : C.Nonempty) →
      ∀ {A : ExternalBoolProcessLaw Ω}, A ∈ C →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        boundedMeasurableNaturalExtensionPrevision
            (externalPathLawBoundedMeasurableCompactCredalSet C)
            (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC) X ≤
          A.pathBoundedMeasurablePrevision X
  externalPathLawCompactBoundedNaturalUpperEnvelopeProcessLe :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)),
      (hC : C.Nonempty) →
      ∀ {A : ExternalBoolProcessLaw Ω}, A ∈ C →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        A.pathBoundedMeasurablePrevision X ≤
          boundedMeasurableNaturalUpperEnvelopePrevision
            (externalPathLawBoundedMeasurableCompactCredalSet C)
            (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC) X
  externalPathLawPrefixProjectiveDeterminesOfProcessAgreement :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
        ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
          A.prefixPrevision n X = B.prefixPrevision n X) →
        (externalPathLawPrefixProjectiveSpec C n).determinesGlobalGamble X
  externalPathLawPrefixProjectiveStrictWidthOfProcessDisagreement :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      {A B : ExternalBoolProcessLaw Ω} (_hA : A ∈ C) (_hB : B ∈ C),
      A.prefixPrevision n X < B.prefixPrevision n X →
        (externalPathLawPrefixProjectiveSpec C n).hasStrictGlobalWidth X
  externalPathLawPrefixCredalSetEnvelopeNontrivialOfProcessDisagreement :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      {A B : ExternalBoolProcessLaw Ω} (_hA : A ∈ C) (_hB : B ∈ C),
      A.prefixPrevision n X < B.prefixPrevision n X →
        lowerEnvelope (externalPathLawPrefixCredalSet C n) X <
          upperEnvelope (externalPathLawPrefixCredalSet C n) X
  externalPathLawPrefixCredalSetWidthPositiveOfProcessDisagreement :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      {A B : ExternalBoolProcessLaw Ω} (_hA : A ∈ C) (_hB : B ∈ C),
      A.prefixPrevision n X < B.prefixPrevision n X →
        0 < credalEnvelopeWidth (externalPathLawPrefixCredalSet C n) X
  prefixMixturePrevisionIsPrecise :
    ∀ (M : BernoulliMixture) (n : ℕ)
      (_h : BernoulliMixturePrefixLaw M n),
      _h.toPrecisePrevision.toLowerPrevision.isPrecise
  imprecisePrefixCredalSetNonempty :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n),
      C.Nonempty →
        (bernoulliMixturePrefixCredalSet C n _hLaw).Nonempty
  prefixProjectiveSpecLimitSet :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n),
      (bernoulliMixturePrefixProjectiveSpec C n _hLaw).projectiveLimitCredalSet =
        bernoulliMixturePrefixCredalSet C n _hLaw
  prefixProjectiveSpecHasCompatibleCompletion :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n),
      C.Nonempty →
        (bernoulliMixturePrefixProjectiveSpec C n _hLaw).hasCompatibleCompletion
  prefixProjectiveSpecNaturalExtensionEqLowerEnvelope :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (bernoulliMixturePrefixProjectiveSpec C n _hLaw).globalNaturalExtension X =
        impreciseDeFinettiPrefixLowerEnvelope C n _hLaw X
  imprecisePrefixLowerEnvelopeLeMixture :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      {M : BernoulliMixture},
      (hM : M ∈ C) →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        impreciseDeFinettiPrefixLowerEnvelope C n _hLaw X ≤
          (_hLaw M hM).toPrecisePrevision X
  imprecisePrefixLowerEnvelopeGreatestLowerBound :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n),
      C.Nonempty →
      ∀ L : LowerPrevision (Fin n → Bool),
      (∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
          (Fin n → Bool), L X ≤ (_hLaw M hM).toPrecisePrevision X) →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        L X ≤ impreciseDeFinettiPrefixLowerEnvelope C n _hLaw X
  prefixProjectiveSpecUpperEnvelopeEqUpperEnvelope :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      upperEnvelope
          (bernoulliMixturePrefixProjectiveSpec C n _hLaw).projectiveLimitCredalSet X =
        impreciseDeFinettiPrefixUpperEnvelope C n _hLaw X
  prefixProjectiveSpecWidthEqEnvelopeWidth :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (bernoulliMixturePrefixProjectiveSpec C n _hLaw).globalEnvelopeWidth X =
        impreciseDeFinettiPrefixEnvelopeWidth C n _hLaw X
  prefixProjectiveSpecWidthComplementEqEnvelopeWidthComplement :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (bernoulliMixturePrefixProjectiveSpec C n _hLaw).globalEnvelopeWidthComplement X =
        impreciseDeFinettiPrefixEnvelopeWidthComplement C n _hLaw X
  prefixProjectiveSpecMidpointEqEnvelopeMidpoint :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (bernoulliMixturePrefixProjectiveSpec C n _hLaw).globalEnvelopeMidpoint X =
        impreciseDeFinettiPrefixEnvelopeMidpoint C n _hLaw X
  imprecisePrefixPrevisionLeUpperEnvelope :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      {M : BernoulliMixture},
      (hM : M ∈ C) →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        (_hLaw M hM).toPrecisePrevision X ≤
          impreciseDeFinettiPrefixUpperEnvelope C n _hLaw X
  imprecisePrefixUpperEnvelopeLeastUpperBound :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n),
      C.Nonempty →
      ∀ U : UpperPrevision (Fin n → Bool),
      (∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
          (Fin n → Bool), (_hLaw M hM).toPrecisePrevision X ≤ U X) →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        impreciseDeFinettiPrefixUpperEnvelope C n _hLaw X ≤ U X
  prefixProjectiveDeterminesOfMixtureAgreement :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
          (_hLaw M hM).toPrecisePrevision X =
            (_hLaw N hN).toPrecisePrevision X) →
        (bernoulliMixturePrefixProjectiveSpec C n _hLaw).determinesGlobalGamble X
  prefixProjectiveStrictWidthOfMixtureDisagreement :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      {M N : BernoulliMixture} (_hM : M ∈ C) (_hN : N ∈ C),
      (_hLaw M _hM).toPrecisePrevision X <
        (_hLaw N _hN).toPrecisePrevision X →
        (bernoulliMixturePrefixProjectiveSpec C n _hLaw).hasStrictGlobalWidth X
  prefixCredalSetEnvelopeNontrivialOfMixtureDisagreement :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      {M N : BernoulliMixture} (_hM : M ∈ C) (_hN : N ∈ C),
      (_hLaw M _hM).toPrecisePrevision X <
        (_hLaw N _hN).toPrecisePrevision X →
        lowerEnvelope (bernoulliMixturePrefixCredalSet C n _hLaw) X <
          upperEnvelope (bernoulliMixturePrefixCredalSet C n _hLaw) X
  prefixCredalSetWidthPositiveOfMixtureDisagreement :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      {M N : BernoulliMixture} (_hM : M ∈ C) (_hN : N ∈ C),
      (_hLaw M _hM).toPrecisePrevision X <
        (_hLaw N _hN).toPrecisePrevision X →
        0 < credalEnvelopeWidth (bernoulliMixturePrefixCredalSet C n _hLaw) X
  hasCompatibleCompletionOfFactorization :
    ∀ {Ω Window Global : Type*} [MeasurableSpace Ω] [LE Window]
      {X : ℕ → Ω → Bool} {μ : Measure Ω}
      (_D : DeFinettiProjectiveCredalSpecialization
        (Window := Window) (Global := Global) X μ),
      CategoricalDeFinettiFactorization X μ →
        _D.projectiveSpec.hasCompatibleCompletion
  hasCompatibleCompletionOfExchangeable :
    ∀ {Ω Window Global : Type*} [MeasurableSpace Ω] [LE Window]
      {X : ℕ → Ω → Bool} {μ : Measure Ω}
      (_D : DeFinettiProjectiveCredalSpecialization
        (Window := Window) (Global := Global) X μ)
      [IsProbabilityMeasure μ],
      (∀ i : ℕ, Measurable (X i)) →
        InfiniteExchangeable X μ →
          _D.projectiveSpec.hasCompatibleCompletion

/-- Current de Finetti projective credal bridge profile. -/
noncomputable def projectiveDeFinettiCredalBridgeProfile :
    ProjectiveDeFinettiCredalBridgeProfile where
  analyticPrefixLaw :=
    bernoulliMixturePrefixLaw_analytic
  prefixLawIffFiniteWeights :=
    bernoulliMixturePrefixLaw_iff_finiteWeights
  externalIIDProductPrefixMeasureEqProduct :=
    externalIIDProductPrefixMeasure_eq_product
  externalIIDProductPrefixPrevisionIsPrecise :=
    externalIIDProductPrefixPrevision_precise
  externalPathLawPrefixMeasureEqProcessPrefix :=
    externalPathLawPrefixMeasure_eq_processPrefix
  externalPathLawPrefixCylinderApply :=
    externalPathLawPrefixCylinder_apply
  externalPathLawPrefixPrevisionIsPrecise :=
    externalPathLawPrefixPrevision_precise
  externalProcessPrefixPrevisionIsPrecise :=
    ExternalBoolProcessLaw.prefixPrevision_precise
  externalProcessPrefixCylinderApply :=
    ExternalBoolProcessLaw.prefixCylinder_apply
  externalPathLawPrefixCredalSetNonempty :=
    externalPathLawPrefixCredalSet_nonempty
  externalPathLawPrefixProjectiveSpecLimitSet :=
    externalPathLawPrefixProjectiveSpec_projectiveLimitCredalSet
  externalPathLawPrefixProjectiveSpecHasCompatibleCompletion :=
    externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion
  externalPathLawPrefixProjectiveSpecNaturalExtensionEqLowerEnvelope :=
    externalPathLawPrefixProjectiveSpec_globalNaturalExtension
  externalPathLawPrefixLowerEnvelopeLeProcess :=
    externalPathLawPrefixLowerEnvelope_le_processPrevision
  externalPathLawPrefixLowerEnvelopeGreatestLowerBound :=
    externalPathLawPrefixLowerEnvelope_greatest_lower_bound
  externalPathLawPrefixProjectiveSpecUpperEnvelopeEqUpperEnvelope :=
    externalPathLawPrefixProjectiveSpec_upperEnvelope
  externalPathLawPrefixProjectiveSpecWidthEqEnvelopeWidth :=
    externalPathLawPrefixProjectiveSpec_globalEnvelopeWidth
  externalPathLawPrefixProjectiveSpecWidthComplementEqEnvelopeWidthComplement :=
    externalPathLawPrefixProjectiveSpec_globalEnvelopeWidthComplement
  externalPathLawPrefixProjectiveSpecMidpointEqEnvelopeMidpoint :=
    externalPathLawPrefixProjectiveSpec_globalEnvelopeMidpoint
  externalPathLawPrefixPrevisionLeUpperEnvelope :=
    externalPathLawPrefixPrevision_le_upperEnvelope
  externalPathLawPrefixUpperEnvelopeLeastUpperBound :=
    externalPathLawPrefixUpperEnvelope_least_upper_bound
  externalPathLawBoundedNaturalExtensionLeProcess :=
    boundedMeasurableNaturalExtensionPrevision_externalPathLawCredalSet_le_processPrevision
  externalPathLawBoundedNaturalExtensionGreatestLowerBound :=
    boundedMeasurableNaturalExtensionPrevision_externalPathLawCredalSet_greatest_lower_bound
  externalPathLawBoundedNaturalUpperEnvelopeProcessLe :=
    boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCredalSet_processPrevision_le
  externalPathLawBoundedNaturalUpperEnvelopeLeastUpperBound :=
    boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCredalSet_least_upper_bound
  externalPathLawCompactBoundedNaturalExtensionLeProcess :=
    boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_le_processPrevision
  externalPathLawCompactBoundedNaturalUpperEnvelopeProcessLe :=
    boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_processPrevision_le
  externalPathLawPrefixProjectiveDeterminesOfProcessAgreement :=
    externalPathLawPrefixProjectiveSpec_determinesGlobalGamble_of_processAgreement
  externalPathLawPrefixProjectiveStrictWidthOfProcessDisagreement :=
    externalPathLawPrefixProjectiveSpec_hasStrictGlobalWidth_of_processDisagreement
  externalPathLawPrefixCredalSetEnvelopeNontrivialOfProcessDisagreement :=
    externalPathLawPrefixCredalSet_lowerUpperEnvelope_nontrivial_of_processDisagreement
  externalPathLawPrefixCredalSetWidthPositiveOfProcessDisagreement :=
    externalPathLawPrefixCredalSet_envelopeWidth_pos_of_processDisagreement
  prefixMixturePrevisionIsPrecise :=
    by
      intro M n h
      exact BernoulliMixturePrefixLaw.toPrecisePrevision_precise h
  imprecisePrefixCredalSetNonempty :=
    bernoulliMixturePrefixCredalSet_nonempty
  prefixProjectiveSpecLimitSet :=
    bernoulliMixturePrefixProjectiveSpec_projectiveLimitCredalSet
  prefixProjectiveSpecHasCompatibleCompletion :=
    bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
  prefixProjectiveSpecNaturalExtensionEqLowerEnvelope :=
    bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension
  imprecisePrefixLowerEnvelopeLeMixture :=
    impreciseDeFinettiPrefixLowerEnvelope_le_mixturePrevision
  imprecisePrefixLowerEnvelopeGreatestLowerBound :=
    impreciseDeFinettiPrefixLowerEnvelope_greatest_lower_bound
  prefixProjectiveSpecUpperEnvelopeEqUpperEnvelope :=
    bernoulliMixturePrefixProjectiveSpec_upperEnvelope
  prefixProjectiveSpecWidthEqEnvelopeWidth :=
    bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidth
  prefixProjectiveSpecWidthComplementEqEnvelopeWidthComplement :=
    bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidthComplement
  prefixProjectiveSpecMidpointEqEnvelopeMidpoint :=
    bernoulliMixturePrefixProjectiveSpec_globalEnvelopeMidpoint
  imprecisePrefixPrevisionLeUpperEnvelope :=
    impreciseDeFinettiPrefixPrevision_le_upperEnvelope
  imprecisePrefixUpperEnvelopeLeastUpperBound :=
    impreciseDeFinettiPrefixUpperEnvelope_least_upper_bound
  prefixProjectiveDeterminesOfMixtureAgreement :=
    bernoulliMixturePrefixProjectiveSpec_determinesGlobalGamble_of_mixtureAgreement
  prefixProjectiveStrictWidthOfMixtureDisagreement :=
    bernoulliMixturePrefixProjectiveSpec_hasStrictGlobalWidth_of_mixtureDisagreement
  prefixCredalSetEnvelopeNontrivialOfMixtureDisagreement :=
    bernoulliMixturePrefixCredalSet_lowerUpperEnvelope_nontrivial_of_mixtureDisagreement
  prefixCredalSetWidthPositiveOfMixtureDisagreement :=
    bernoulliMixturePrefixCredalSet_envelopeWidth_pos_of_mixtureDisagreement
  hasCompatibleCompletionOfFactorization :=
    DeFinettiProjectiveCredalSpecialization.hasCompatibleCompletion_of_factorization
  hasCompatibleCompletionOfExchangeable :=
    DeFinettiProjectiveCredalSpecialization.hasCompatibleCompletion_of_exchangeable

end Mettapedia.Logic.DeFinettiProjectiveCredalBridge
