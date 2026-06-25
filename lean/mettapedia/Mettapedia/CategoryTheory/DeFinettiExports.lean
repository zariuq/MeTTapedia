import Mettapedia.CategoryTheory.DeFinettiStableExports
import Mettapedia.CategoryTheory.DeFinettiMarkovGiryBridge
import Mettapedia.CategoryTheory.DeFinettiHigherOrderGiryBridge
import Mettapedia.CategoryTheory.FiniteHiddenMarkovDeFinettiBridge
import Mettapedia.CategoryTheory.DeFinettiExternalBridge
import Mettapedia.CategoryTheory.DeFinettiMarkovCategoryBridge
import Mettapedia.UniversalAI.SolomonoffExchangeable
import Mettapedia.PLN.Bridges.ProbabilityTheory.CategoricalNuPLNBridge

/-!
# De Finetti Category Exports (Recommended Import Surface)

This is the single recommended import path for the categorical de Finetti route.
It re-exports the stable theorem chain needed by downstream users.

## Canonical Endpoints (Use These)
- `deFinetti_kleisliGiry`: categorical de Finetti in Kleisli(Giry) — **finite-mass** cone universality.
- `deFinettiExport_markovMixture_to_kleisliGiryFactorization`: Markov de Finetti at the
  prefix-law Kleisli(Giry) layer through `MarkovParam k`.
- `deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`:
  the canonical Markov-only endpoint.
- `deFinettiExport_globalIIDConeMediatorUnique_finiteMass_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`:
  the canonical **finite-mass** cone endpoint (maximal correct strengthening).
- `deFinetti_measure`: measure-level de Finetti — unique latent-θ measure from infinite exchangeability.

## Structural Boundaries (Negative Results)
- `deFinettiExport_not_allSourcesKleisli_unrestricted`: unrestricted all-sources Kleisli universality is FALSE.
- `deFinettiExport_not_commutesToMarkovBridge_unrestricted`: commutes-to-Markov bridge is not derivable.
- `deFinettiExport_allSourcesKleisli_finiteMass_iff_markovOnly`: finite-mass = maximal correct strengthening.

## Adapters and Legacy Names
- Adapters are suffixed `_adapter_...` and are **assumption-bearing** (use only when the
  extra bridge hypotheses are explicitly available).
- Legacy names are marked `[deprecated]` and mapped to canonical/adapters below.

## Reference Map
For the full API map and legacy migration list, see the section "Migration Map" and
the stable layer `Mettapedia.CategoryTheory.DeFinettiStableExports`.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open MeasureTheory
open ProbabilityTheory
open Mettapedia.ProbabilityTheory.HigherOrderProbability
open scoped BigOperators ENNReal

variable {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Public API: unique latent-θ measure from infinite exchangeability (measure level). -/
theorem deFinettiExport_existsUnique_latentThetaMeasure_of_exchangeable
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : Mettapedia.ProbabilityTheory.Exchangeability.InfiniteExchangeable X μ) :
    ∃! ν : Measure DeFinettiConnection.Theta, RepresentsLatentTheta X μ ν :=
  deFinettiStable_existsUnique_latentThetaMeasure_of_exchangeable X μ hX hexch

/-- Recommended export: a public `MarkovMixture` determines a Kleisli(Giry)
mediator from the terminal object into the Markov-parameter space, and that
mediator recovers the prefix law. -/
theorem deFinettiExport_markovMixture_to_kleisliGiryFactorization
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)}
    (M : Mettapedia.ProbabilityTheory.Exchangeability.MarkovMixture k μ) :
    KleisliGiryMarkovDeFinettiFactorization k μ :=
  kleisliGiryMarkovDeFinettiFactorization_of_markovMixture (k := k) M

/-- Recommended export: a public `MarkovMixture` also determines the
sequence-cylinder Kleisli(Giry) factorization obtained by integrating the
canonical fixed-parameter sequence law. -/
theorem deFinettiExport_markovMixture_to_kleisliGirySequenceCylinderFactorization
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)}
    (M : Mettapedia.ProbabilityTheory.Exchangeability.MarkovMixture k μ) :
    KleisliGiryMarkovSequenceCylinderFactorization k μ :=
  kleisliGiryMarkovSequenceCylinderFactorization_of_markovMixture (k := k) M

/-- Recommended export: the measure-level and Kleisli(Giry) Markov factorization
interfaces are equivalent. -/
theorem deFinettiExport_categoricalMarkovDeFinettiFactorization_iff_kleisliGiry
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)} :
    CategoricalMarkovDeFinettiFactorization k μ ↔
      KleisliGiryMarkovDeFinettiFactorization k μ :=
  categoricalMarkovDeFinettiFactorization_iff_kleisliGiry (k := k) (μ := μ)

/-- Recommended export: the sequence-cylinder and prefix-word Markov
factorization interfaces are equivalent at the measure level. -/
theorem deFinettiExport_categoricalMarkovSequenceCylinderFactorization_iff_prefixLaw
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)} :
    CategoricalMarkovSequenceCylinderFactorization k μ ↔
      CategoricalMarkovDeFinettiFactorization k μ :=
  categoricalMarkovSequenceCylinderFactorization_iff_categoricalMarkovDeFinettiFactorization
    (k := k) (μ := μ)

/-- Recommended export: the sequence-cylinder and prefix-word Markov
factorization interfaces are equivalent in Kleisli(Giry). -/
theorem deFinettiExport_kleisliGiryMarkovSequenceCylinderFactorization_iff_prefixLaw
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)} :
    KleisliGiryMarkovSequenceCylinderFactorization k μ ↔
      KleisliGiryMarkovDeFinettiFactorization k μ :=
  kleisliGiryMarkovSequenceCylinderFactorization_iff_kleisliGiryMarkovDeFinettiFactorization
    (k := k) (μ := μ)

/-- Recommended export: the new Markov Kleisli(Giry) factorization interface is
equivalent to the existing public `MarkovMixture` witness. -/
theorem deFinettiExport_kleisliGiryMarkovDeFinettiFactorization_iff_nonempty_markovMixture
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)} :
    KleisliGiryMarkovDeFinettiFactorization k μ ↔
      Nonempty (Mettapedia.ProbabilityTheory.Exchangeability.MarkovMixture k μ) :=
  kleisliGiryMarkovDeFinettiFactorization_iff_nonempty_markovMixture
    (k := k) (μ := μ)

/-- Recommended export: the sequence-cylinder Kleisli(Giry) Markov
factorization interface is equivalent to the public `MarkovMixture` witness. -/
theorem deFinettiExport_kleisliGiryMarkovSequenceCylinderFactorization_iff_nonempty_markovMixture
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)} :
    KleisliGiryMarkovSequenceCylinderFactorization k μ ↔
      Nonempty (Mettapedia.ProbabilityTheory.Exchangeability.MarkovMixture k μ) :=
  kleisliGiryMarkovSequenceCylinderFactorization_iff_nonempty_markovMixture
    (k := k) (μ := μ)

/-- Recommended export: the Borel-side measurable sequence kernel on
`MarkovParam k` induces a genuine probability measure on state sequences for any
Borel probability law on parameters. -/
theorem deFinettiExport_borelMarkovSequenceMixture_prob
    {k : ℕ}
    (π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov k) :
    IsProbabilityMeasure (borelMarkovSequenceMixture (k := k) π) :=
  borelMarkovSequenceMixture_isProbability (k := k) π

/-- Recommended export: the Borel-side measurable sequence mixture evaluates
finite cylinders by integrating the corresponding cylinder weights of the
measurable sequence kernel. -/
theorem deFinettiExport_borelMarkovSequenceMixture_cylinder_eq
    {k : ℕ}
    (π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov k)
    (xs : List (Fin k)) :
    borelMarkovSequenceMixture (k := k) π
        (Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder (k := k) xs) =
      borelMarkovCylinderWeightViaProbMarkov (k := k) π xs :=
  borelMarkovSequenceMixture_cylinder_eq (k := k) π xs

/-- Recommended export: the Borel-side measurable sequence-kernel cylinder
weights are exactly the older Borel prefix-law moments. -/
theorem deFinettiExport_borelMarkovCylinderWeightViaProbMarkov_eq_momentMapWord
    {k : ℕ}
    (π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov k)
    (xs : List (Fin k)) :
    borelMarkovCylinderWeightViaProbMarkov (k := k) π xs =
      Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.momentMapWord (k := k) xs π :=
  borelMarkovCylinderWeightViaProbMarkov_eq_momentMapWord (k := k) π xs

/-- Recommended export: the Borel-side sequence-kernel factorization is
equivalent to the honest Borel prefix-law factorization. -/
theorem deFinettiExport_categoricalBorelMarkovSequenceKernelFactorization_iff_prefixLaw
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)} :
    CategoricalBorelMarkovSequenceKernelFactorization k μ ↔
      CategoricalBorelMarkovDeFinettiFactorization k μ :=
  categoricalBorelMarkovSequenceKernelFactorization_iff_categoricalBorelMarkovDeFinettiFactorization
    (k := k) (μ := μ)

/-- Recommended export: the Borel-side sequence-kernel factorization can be
presented either by cylinder weights or by the induced sequence mixture. -/
theorem deFinettiExport_categoricalBorelMarkovSequenceKernelFactorization_iff_exists_borelMarkovSequenceMixture
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)} :
    CategoricalBorelMarkovSequenceKernelFactorization k μ ↔
      ∃ π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov k,
        ∀ xs : List (Fin k),
          μ xs =
            borelMarkovSequenceMixture (k := k) π
              (Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder (k := k) xs) :=
  categoricalBorelMarkovSequenceKernelFactorization_iff_exists_borelMarkovSequenceMixture
    (k := k) (μ := μ)

/-- Recommended export: the honest public boundary for the stronger Borel-side
kernel construction is `BorelMarkovMixture`, not the older active-space
`MarkovMixture`. -/
theorem deFinettiExport_categoricalBorelMarkovSequenceKernelFactorization_iff_nonempty_borelMarkovMixture
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)} :
    CategoricalBorelMarkovSequenceKernelFactorization k μ ↔
      Nonempty (BorelMarkovMixture k μ) :=
  categoricalBorelMarkovSequenceKernelFactorization_iff_nonempty_borelMarkovMixture
    (k := k) (μ := μ)

/-- Recommended export: a Borel-side prefix-law factorization lifts one-way to
the older active prefix-law factorization by trimming the Borel law down to the
wordProb-generated σ-algebra. -/
theorem deFinettiExport_categoricalMarkovDeFinettiFactorization_of_categoricalBorel
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)}
    (hfac : CategoricalBorelMarkovDeFinettiFactorization k μ) :
    CategoricalMarkovDeFinettiFactorization k μ :=
  categoricalMarkovDeFinettiFactorization_of_categoricalBorelMarkovDeFinettiFactorization
    (k := k) (μ := μ) hfac

/-- Recommended export: a public `BorelMarkovMixture` lifts one-way to the older
active `MarkovMixture`. -/
noncomputable def deFinettiExport_markovMixture_of_borelMarkovMixture
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)}
    (M : BorelMarkovMixture k μ) :
    Mettapedia.ProbabilityTheory.Exchangeability.MarkovMixture k μ :=
  markovMixtureOfBorelMarkovMixture (k := k) (μ := μ) M

/-- Recommended export: any Borel-side mixture witness yields an active
`MarkovMixture` witness. -/
theorem deFinettiExport_nonempty_markovMixture_of_nonempty_borelMarkovMixture
    {k : ℕ}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)} :
    Nonempty (BorelMarkovMixture k μ) → Nonempty (Mettapedia.ProbabilityTheory.Exchangeability.MarkovMixture k μ) :=
  nonempty_markovMixture_of_nonempty_borelMarkovMixture (k := k) (μ := μ)

/-- Recommended export: the Borel moment map is not injective in the binary
case, so the reverse Borel lift cannot be expected to be uniquely determined
by active prefix data. -/
theorem deFinettiExport_not_injective_borelMomentMapWord_fin2 :
    ¬ Function.Injective
      (fun π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov 2 =>
        fun xs : List (Fin 2) =>
          Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.momentMapWord (k := 2) xs π) :=
  not_injective_borelMomentMapWord_fin2

/-- Recommended export: the dead-row binary counterexample gives two distinct
Borel-side mixture witnesses for the same finite-word law. -/
theorem deFinettiExport_deadRowPrefixMeasure_has_two_distinct_borelMarkovMixtures :
    deadRowBorelMarkovMixture₀ ≠ deadRowBorelMarkovMixture₁ :=
  deadRowPrefixMeasure_has_two_distinct_borelMarkovMixtures

/-- Recommended export: the higher-order long-word Borel/Giry weight is just
the ordinary encoded-context moment map. -/
theorem deFinettiExport_higherOrderLongWordWeightViaProbMarkov_eq_momentMapWord
    {k m : ℕ} [Fact (0 < m)]
    (π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov (HigherOrderContextCard k m))
    (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    higherOrderLongWordWeightViaProbMarkov (k := k) (m := m) π xs hxs =
      Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.momentMapWord
        (k := HigherOrderContextCard k m)
        (higherOrderEncodedContextWord (k := k) (m := m) xs hxs) π :=
  higherOrderLongWordWeightViaProbMarkov_eq_momentMapWord
    (k := k) (m := m) π xs hxs

/-- Recommended export: the honest Borel higher-order long-word factorization
package is equivalent to having the public higher-order mixture witness. -/
theorem deFinettiExport_categoricalBorelHigherOrderLongWordFactorization_iff_nonempty_borelHigherOrderLongWordMixture
    {k m : ℕ} [Fact (0 < m)]
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)} :
    CategoricalBorelHigherOrderLongWordFactorization k m μ ↔
      Nonempty (BorelHigherOrderLongWordMixture k m μ) :=
  BorelHigherOrderLongWordMixture.categoricalBorelHigherOrderLongWordFactorization_iff_nonempty_borelHigherOrderLongWordMixture
    (k := k) (m := m) (μ := μ)

/-- Recommended export: every fixed higher-order parameter yields a degenerate
Dirac Borel witness on encoded context-state parameters. This is the honest
trivial direction, not a higher-order de Finetti mixture theorem. -/
theorem deFinettiExport_borelHigherOrderLongWordFactorization_diracWitness
    {k m : ℕ} [Fact (0 < m)]
    (θ : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHigherOrder.HigherOrderMarkovParam k m) :
    ∃ π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov (HigherOrderContextCard k m),
      ∀ xs : List (Fin k), ∀ hxs : m ≤ xs.length,
        Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHigherOrder.higherOrderSequenceMeasure (k := k) (m := m) θ
            (Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder (k := k) xs) =
          higherOrderLongWordWeightViaProbMarkov (k := k) (m := m) π xs hxs :=
  borelHigherOrderLongWordFactorization_diracWitness (k := k) (m := m) θ

/-- Recommended export: a finite discrete mixture of genuine higher-order
parameters yields an honest non-Dirac higher-order long-word factorization. -/
theorem deFinettiExport_categoricalBorelHigherOrderLongWordFactorization_of_finiteDiscreteMixture
    {k m n : ℕ} [Fact (0 < m)]
    (w : Fin n → ℝ≥0∞) (hw : Finset.sum (Finset.univ : Finset (Fin n)) (fun i => w i) = 1)
    (Θ : Fin n → Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHigherOrder.HigherOrderMarkovParam k m) :
    CategoricalBorelHigherOrderLongWordFactorization k m
      (Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.xiPrefixMeasure
        (ν := fun i : Fin n =>
          higherOrderCylinderPrefixMeasure (k := k) (m := m) (Θ i))
        (w := w)
        (hw := by simpa [tsum_fintype] using hw)) :=
  categoricalBorelHigherOrderLongWordFactorization_of_finiteDiscreteMixture
    (k := k) (m := m) w (by simpa using hw) Θ

/-- Legacy export alias for the higher-order Dirac witness theorem. -/
@[deprecated deFinettiExport_borelHigherOrderLongWordFactorization_diracWitness (since := "2026-04-16")]
theorem deFinettiExport_exists_borelHigherOrderLongWordFactorization_of_param
    {k m : ℕ} [Fact (0 < m)]
    (θ : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHigherOrder.HigherOrderMarkovParam k m) :
    ∃ π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov (HigherOrderContextCard k m),
      ∀ xs : List (Fin k), ∀ hxs : m ≤ xs.length,
        Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHigherOrder.higherOrderSequenceMeasure (k := k) (m := m) θ
            (Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder (k := k) xs) =
          higherOrderLongWordWeightViaProbMarkov (k := k) (m := m) π xs hxs :=
  deFinettiExport_borelHigherOrderLongWordFactorization_diracWitness (k := k) (m := m) θ

/-- Recommended export: the honest Borel finite-HMM factorization package is
equivalent to having the public finite-HMM mixture witness. -/
theorem deFinettiExport_categoricalBorelFiniteHMMFactorization_iff_nonempty_borelFiniteHMMMixture
    {latent obs : ℕ}
    {emission : Fin latent → ProbabilityMeasure (Fin obs)}
    {μ : Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin obs)} :
    CategoricalBorelFiniteHMMFactorization latent obs emission μ ↔
      Nonempty (BorelFiniteHMMMixture latent obs emission μ) :=
  BorelFiniteHMMMixture.categoricalBorelFiniteHMMFactorization_iff_nonempty_borelFiniteHMMMixture
    (latent := latent) (obs := obs) (emission := emission) (μ := μ)

/-- Recommended export: every fixed finite HMM yields a degenerate Dirac Borel
factorization through the latent Markov parameter space. This is the honest
trivial direction, not a finite-HMM de Finetti mixture theorem. -/
theorem deFinettiExport_borelFiniteHMMFactorization_diracWitness
    {latent obs : ℕ}
    (θ : Mettapedia.ProbabilityTheory.HiddenMarkovModels.FiniteHiddenMarkovModel.FiniteHMMParam latent obs) :
    ∃ π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov latent,
      ∀ ys : List (Fin obs),
        Mettapedia.ProbabilityTheory.HiddenMarkovModels.FiniteHiddenMarkovModel.observedSequenceMeasure (latent := latent) (obs := obs) θ
            (Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder (k := obs) ys) =
          observedWordWeightViaProbMarkov (latent := latent) (obs := obs) θ.emission π ys :=
  borelFiniteHMMFactorization_diracWitness (latent := latent) (obs := obs) θ

/-- Legacy export alias for the finite-HMM Dirac witness theorem. -/
@[deprecated deFinettiExport_borelFiniteHMMFactorization_diracWitness (since := "2026-04-16")]
theorem deFinettiExport_exists_borelFiniteHMMFactorization_of_param
    {latent obs : ℕ}
    (θ : Mettapedia.ProbabilityTheory.HiddenMarkovModels.FiniteHiddenMarkovModel.FiniteHMMParam latent obs) :
    ∃ π : Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.ProbMarkov latent,
      ∀ ys : List (Fin obs),
        Mettapedia.ProbabilityTheory.HiddenMarkovModels.FiniteHiddenMarkovModel.observedSequenceMeasure (latent := latent) (obs := obs) θ
            (Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder (k := obs) ys) =
          observedWordWeightViaProbMarkov (latent := latent) (obs := obs) θ.emission π ys :=
  deFinettiExport_borelFiniteHMMFactorization_diracWitness (latent := latent) (obs := obs) θ

/-- Recommended export: a finite discrete mixture of latent Markov parameters
with fixed emission kernel yields an honest non-Dirac finite-HMM factorization
package. -/
theorem deFinettiExport_categoricalBorelFiniteHMMFactorization_of_finiteDiscreteMixture
    {latent obs n : ℕ}
    (emission : Fin latent → ProbabilityMeasure (Fin obs))
    (w : Fin n → ℝ≥0∞) (hw : Finset.sum (Finset.univ : Finset (Fin n)) (fun i => w i) = 1)
    (Θ : Fin n → Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard.MarkovParam latent) :
    CategoricalBorelFiniteHMMFactorization latent obs emission
      (Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.xiPrefixMeasure
        (ν := fun i : Fin n =>
          observedCylinderPrefixMeasure (latent := latent) (obs := obs) emission (Θ i))
        (w := w)
        (hw := by simpa [tsum_fintype] using hw)) :=
  categoricalBorelFiniteHMMFactorization_of_finiteDiscreteMixture
    (latent := latent) (obs := obs) emission w (by simpa using hw) Θ

/-- Recommended export: the concrete binary copy HMM assigns observed cylinder
mass `1` to `[0]`. -/
theorem deFinettiExport_binaryCopyHMM_observedCylinder_0 :
    Mettapedia.ProbabilityTheory.HiddenMarkovModels.FiniteHiddenMarkovModel.observedSequenceMeasure (latent := 2) (obs := 2) binaryCopyHMM
        (Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder (k := 2) ([0] : List (Fin 2))) = 1 :=
  binaryCopyHMM_observedCylinder_0

/-- Recommended export: the concrete binary copy HMM assigns observed cylinder
mass `0` to `[1]`. -/
theorem deFinettiExport_binaryCopyHMM_observedCylinder_1 :
    Mettapedia.ProbabilityTheory.HiddenMarkovModels.FiniteHiddenMarkovModel.observedSequenceMeasure (latent := 2) (obs := 2) binaryCopyHMM
        (Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiRecurrence.cylinder (k := 2) ([1] : List (Fin 2))) = 0 :=
  binaryCopyHMM_observedCylinder_1

/-- Recommended export: kernel-level universal mediator API is equivalent to
per-`n` limit-mediator uniqueness packaging. -/
theorem deFinettiExport_kernelUniversalMediator_iff_perNUnique
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      ExchangeablePerNLimitMediatorUnique (Ω := Ω) X :=
  deFinettiStable_kernelLatentThetaUniversalMediator_iff_perNLimitMediatorUnique
    (Y := Y) (Ω := Ω) X

/-- Recommended export: kernel-level universal mediator API is equivalent, in one
hop, to the global cross-`n` package family. -/
theorem deFinettiExport_kernelUniversalMediator_iff_crossNPackageFamily
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) :=
  deFinettiStable_kernelLatentThetaUniversalMediator_iff_crossNPackageFamily
    (Y := Y) (Ω := Ω) X

/-- Recommended export: in the kernel Markov-category core, exchangeability
implies unique latent-`Theta` mediation. -/
theorem deFinettiExport_kernelMarkovCore_exchangeable_implies_unique_latentThetaMediator
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : KernelExchangeableInMarkovCore (Y := Y) (Ω := Ω) X κ) :
    KernelLatentThetaMediatorInMarkovCore (Y := Y) (Ω := Ω) X κ :=
  kernelMarkovCore_exchangeable_implies_unique_latentThetaMediator
    (Y := Y) (Ω := Ω) X κ hX hexch

/-- Recommended export: Markov-core universal mediator API is equivalent to the
global cross-`n` package family. -/
theorem deFinettiExport_markovCoreUniversal_iff_crossNPackageFamily
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) := by
  calc
    KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X ↔
        KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X := by
          exact
            kernelLatentThetaUniversalMediatorInMarkovCore_iff_kernelLatentThetaUniversalMediator
              (Y := Y) (Ω := Ω) X
    _ ↔ ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) := by
          exact deFinettiExport_kernelUniversalMediator_iff_crossNPackageFamily
            (Y := Y) (Ω := Ω) X

/-- Recommended end-to-end theorem chain: kernel universal mediator API,
per-`n` uniqueness package, and cross-`n` package family are bundled in one
equivalence statement for downstream imports. -/
theorem deFinettiExport_kernelUniversalMediator_endToEndChain
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      (ExchangeablePerNLimitMediatorUnique (Ω := Ω) X ∧
        (∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
          Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ))) := by
  constructor
  · intro h
    exact ⟨
      (deFinettiExport_kernelUniversalMediator_iff_perNUnique
        (Y := Y) (Ω := Ω) X).1 h,
      (deFinettiExport_kernelUniversalMediator_iff_crossNPackageFamily
        (Y := Y) (Ω := Ω) X).1 h⟩
  · intro h
    exact (deFinettiExport_kernelUniversalMediator_iff_perNUnique
      (Y := Y) (Ω := Ω) X).2 h.1

/-- Recommended end-to-end theorem chain (global-action form):
kernel universal mediator API is equivalent to:
1. per-`n` mediator uniqueness, and
2. global lifted commutation producing cross-`n` packages. -/
theorem deFinettiExport_kernelUniversalMediator_endToEnd_globalChain
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      (ExchangeablePerNLimitMediatorUnique (Ω := Ω) X ∧
        (∀ μ : Measure Ω, GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ →
          Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ))) :=
  deFinettiStable_kernelUniversalMediator_endToEnd_globalChain
    (Y := Y) (Ω := Ω) X

/-- Recommended export: global cross-`n` limit package from prefix-law
exchangeability. -/
def deFinettiExport_crossNPackage_of_prefixCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hcone : IsPrefixLawCone (Ω := Ω) X μ) :
    ExchangeableCrossNLimitPackage (Ω := Ω) X μ :=
  deFinettiStable_exchangeableCrossNLimitPackage_of_isPrefixLawCone
    (Ω := Ω) X μ hcone

/-- Recommended export: true global Kleisli(Giry) `IsLimit` packaging is
equivalent to global mediator uniqueness for an iid-cone skeleton. -/
theorem deFinettiExport_isLimit_iff_globalIIDConeMediatorUnique
    (cone : KleisliGiryIIDConeSkeleton) :
    Nonempty (CategoryTheory.Limits.IsLimit (cone.toCone)) ↔
      GlobalIIDConeMediatorUnique cone :=
  deFinettiStable_isLimit_iff_globalIIDConeMediatorUnique cone

/-- Recommended export: specialized `P Bool` form of the true global
Kleisli(Giry) `IsLimit` equivalence. -/
theorem deFinettiExport_isLimit_iff_globalIIDConeMediatorUniqueProbBool
    (cone : KleisliGiryProbBoolIIDCone) :
    Nonempty (CategoryTheory.Limits.IsLimit (cone.toCone)) ↔
      GlobalIIDConeMediatorUniqueProbBool cone :=
  deFinettiStable_isLimit_iff_globalIIDConeMediatorUniqueProbBool cone

/-- Recommended export: for the cone built from `iidSequenceKernelTheta`, true
`IsLimit` is equivalent to global mediator uniqueness. -/
theorem deFinettiExport_isLimit_iff_globalIIDConeMediatorUnique_iidSequenceKernelTheta
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta) :
    Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
      GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes) :=
  deFinettiStable_isLimit_iff_globalIIDConeMediatorUnique_iidSequenceKernelTheta hcommutes

/-- Recommended export: no-extra-hypothesis (beyond global finitary invariance)
IsLimit-ready bundle for `iidSequenceKernelTheta`.
This provides in one hop:
1. the derived commutation witness,
2. unconditional horizon-`n` prefix evaluation via the canonical latent-kernel,
3. the true `IsLimit`/mediator-uniqueness equivalence for the induced cone. -/
theorem deFinettiExport_iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    ∃ hcommutes : ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
          iidSequenceKleisliHomTheta,
      (∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
            (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal θ)) ∧
      (Nonempty (CategoryTheory.Limits.IsLimit ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
        GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)) :=
  deFinettiStable_iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance hglobal

/-- Recommended export (Path-B): finite-prefix Bernoulli product marginals for
`iidSequenceKernelTheta` imply the full IsLimit-ready Kleisli(Giry) bundle. -/
theorem deFinettiExport_iidSequenceKernelTheta_isLimitReady_of_prefix_pi_marginals
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
        GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)) :=
  deFinettiStable_iidSequenceKernelTheta_isLimitReady_of_prefix_pi_marginals hprefix

/-- Recommended export: concrete `IsLimit` witness for the global Kleisli(Giry)
cone built from `iidSequenceKernelTheta`, assuming:
1. global finitary invariance, and
2. global mediator uniqueness for the induced cone. -/
theorem deFinettiExport_iidSequenceKernelTheta_hasIsLimit_of_globalFinitaryInvariance_and_mediatorUnique
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hmed :
      GlobalIIDConeMediatorUnique
        (iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal))) :
    Nonempty
      (CategoryTheory.Limits.IsLimit
        ((iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) :=
  deFinettiStable_iidSequenceKernelTheta_hasIsLimit_of_globalFinitaryInvariance_and_mediatorUnique
    (hglobal := hglobal) hmed

/-- Recommended alias theorem: Markov-core universal mediation plus global
finitary invariance provides the practical bridge to the true Kleisli(Giry)
`IsLimit`-ready package.

This bundles:
1. recovery of the standard kernel-level universal mediator API, and
2. the concrete Kleisli(Giry) `IsLimit`-ready witness/equivalence package for
   `iidSequenceKernelTheta`. -/
theorem deFinettiExport_markovCore_to_kleisliRoute
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      (∃ hcommutes : ∀ τ : FinSuppPermNat,
          CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
            iidSequenceKleisliHomTheta,
        (∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
          iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
            ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
              (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal θ)) ∧
        (Nonempty (CategoryTheory.Limits.IsLimit ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
          GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes))) := by
  exact deFinettiStable_markovCore_to_kleisliRoute
    (Y := Y) (Ω := Ω) X hcore hglobal

/-- Recommended alias theorem: Markov-core universal mediation plus global
finitary invariance imply canonical Markov-only Kleisli(Giry)
mediator-uniqueness for `iidSequenceKernelTheta`, using the default all-sources
kernel witness internally. This route avoids the unrestricted
commutes-to-Markov bridge assumption. -/
theorem deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      GlobalIIDConeMediatorUnique_markovOnly
        (iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) := by
  exact
    deFinettiStable_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
      (Y := Y) (Ω := Ω) X hcore hglobal

/-- Recommended alias theorem: Markov-core universal mediation plus global
finitary invariance and mediator uniqueness yield a concrete global
Kleisli(Giry) `IsLimit` witness for `iidSequenceKernelTheta`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hmed :
      GlobalIIDConeMediatorUnique
        (iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal))) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact deFinettiStable_markovCore_to_kleisliIsLimit
    (Y := Y) (Ω := Ω) X hcore hglobal hmed

/-! ### Legacy full-target wrappers (adapter behavior)

These names keep older call sites working, but they are **assumption-bearing**.
Prefer the canonical Markov-only endpoint or the explicit `_adapter_...` names. -/

/-- Recommended alias theorem (full-target route): Markov-core universal
mediation plus global finitary invariance and unrestricted all-sources Kleisli
universality yield a concrete global Kleisli(Giry) `IsLimit` witness for
`iidSequenceKernelTheta`, without a separate mediator-uniqueness hypothesis. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) X hcore hglobal huniv

/-- Explicit adapter alias for the unrestricted all-sources Kleisli full-target
route.

Prefer the canonical Markov-only endpoint
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) X hcore hglobal huniv

/-- Recommended alias theorem (full-target route): same as above but taking an
unrestricted all-sources kernel-level factorization witness directly. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv :
      KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted
      (Y := Y) (Ω := Ω) X hcore hglobal huniv

/-- Explicit adapter alias for the unrestricted all-sources
kernel-factorization full-target route.

Prefer the canonical Markov-only endpoint
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv :
      KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted
      (Y := Y) (Ω := Ω) X hcore hglobal huniv

/-- Assumption-bearing adapter (full-target route): compose all-sources
kernel mediation with an explicit commutes-to-Markov bridge, then discharge the
global Kleisli(Giry) `IsLimit` goal in one hop.

Canonical endpoint remains the Markov-only theorem
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`.
The bridge assumption is not derivable in unrestricted `Kleisli(MeasCat.Giry)`;
see `deFinettiExport_not_commutesToMarkovBridge_unrestricted`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernel
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernel
      (Y := Y) (Ω := Ω) X hcore hglobal huniv hmarkov_of_commutes

/-- Explicit adapter alias for the all-sources-kernel full-target route.

Prefer the canonical Markov-only endpoint
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernel
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernel
      (Y := Y) (Ω := Ω) X hcore hglobal huniv hmarkov_of_commutes

/-- Compatibility wrapper retaining an explicit iid-prefix-law input.
Prefer
`deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernel`.
-/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernel_and_prefixLaw
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernel
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal huniv hmarkov_of_commutes

/-! ### Structural boundaries (negative results) -/

/-- Structural boundary: in unrestricted `Kleisli(MeasCat.Giry)`, raw
permutation-commutation does not imply Markovness of source kernels. -/
theorem deFinettiExport_not_commutesToMarkovBridge_unrestricted :
    ¬ CommutesToMarkovBridge :=
  not_commutesToMarkovBridge_unrestricted

/-- Structural boundary: the unrestricted all-sources Kleisli mediator property
is FALSE. The counting measure on `ℕ → Bool` from PUnit commutes with all
permutations but admits no mediator through iid(θ), because every singleton
has iid-measure 0 for all θ while counting measure assigns mass 1. -/
theorem deFinettiExport_not_allSourcesKleisli_unrestricted :
    ¬ KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
  deFinettiStable_not_allSourcesKleisli_unrestricted

/-- Structural boundary: the unrestricted strengthening hypothesis is also false
(it implies the unrestricted universality refuted above). The correct
strengthening is the finite-mass version; see
`deFinettiExport_allSourcesKleisli_finiteMass_iff_markovOnly`. -/
theorem deFinettiExport_not_defaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess) :
    ¬ DefaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening :=
  deFinettiStable_not_defaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening
    hglobal hunivDefault

/-- Structural boundary (assumption-free): the unrestricted strengthening is
false, using the unconditional latent-Dirac witness and default all-sources
mediator internally. No external hypotheses required. -/
theorem deFinettiExport_not_defaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening' :
    ¬ DefaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening :=
  deFinettiStable_not_defaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening'

/-- Canonical export theorem (full-target route, crux-isolated):
compose
1. default all-sources qualitative de Finetti,
2. a measurable embedding of latent moments (`thetaMomentSeq`),
3. kernel-level prefix law for `iidSequenceKernelTheta`, and
4. a commutes⇒Markov bridge for source kernels,
then discharge the global Kleisli(Giry) `IsLimit` goal in one hop. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw_of_thetaMomentEmbedding
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (_hEmb : MeasurableEmbedding latentThetaMomentSeq)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  have hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)) :=
    iidSequenceKernelTheta_represents_latentDirac (hprefix := hprefix)
  have huniv :
      KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
      (hglobal := hglobal)
      (hrepDirac := hrepDirac)
      (hunivDefault := fun (Y' : Type) _ =>
        kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))
      (hmarkov_of_commutes := hmarkov_of_commutes)
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) (X := X) hcore hglobal huniv

/-- Compatibility alias of the embedding-driven prefix-law endpoint.
Prefer the latent-Dirac canonical theorem
`deFinettiExport_markovCore_to_kleisliIsLimit_canonical`, which no longer
threads explicit prefix-law/moment-embedding hypotheses through the API. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_canonical_of_prefixLaw_and_thetaMomentEmbedding
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (_hEmb : MeasurableEmbedding latentThetaMomentSeq)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  have hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)) :=
    iidSequenceKernelTheta_represents_latentDirac (hprefix := hprefix)
  have huniv :
      KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
      (hglobal := hglobal)
      (hrepDirac := hrepDirac)
      (hunivDefault := fun (Y' : Type) _ =>
        kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))
      (hmarkov_of_commutes := hmarkov_of_commutes)
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) (X := X) hcore hglobal huniv

/-- Preferred export theorem from an explicit latent-Dirac witness.

This canonical route avoids an external strict-prefix-law hypothesis and
dispatches through the latent-Dirac all-sources bridge.
-/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_canonical
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  have huniv :
      KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
      (hglobal := hglobal)
      (hrepDirac := hrepDirac)
      (hunivDefault := fun (Y' : Type) _ =>
        kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))
      (hmarkov_of_commutes := hmarkov_of_commutes)
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) (X := X) hcore hglobal huniv

/-- Compatibility wrapper (full-target route, no explicit all-sources mediator
input) from an explicit latent-Dirac witness. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_latentDirac
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_canonical
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal hrepDirac hmarkov_of_commutes

/-- Preferred wrapper from default all-sources qualitative de Finetti with no
external strict-prefix-law hypothesis. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_canonical
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal
      iidSequenceKernelTheta_represents_latentDirac_unconditional
      hmarkov_of_commutes

/-- Compatibility wrapper retaining explicit strict iid-prefix equations. Prefer
`deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`.
-/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal hmarkov_of_commutes

/-- Preferred compatibility wrapper if your local context already carries
`StandardBorelSpace (ProbabilityMeasure LatentTheta)`, without requiring an
explicit strict-prefix-law hypothesis. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_standardBorelProbabilityMeasure
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    [StandardBorelSpace (ProbabilityMeasure LatentTheta)]
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal hmarkov_of_commutes

/-- Preferred compatibility fallback when only `BorelSpace (FiniteMeasure LatentTheta)`
is available, without requiring an explicit strict-prefix-law hypothesis. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_finiteMeasureBorel
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    [BorelSpace (FiniteMeasure LatentTheta)]
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  letI : BorelSpace (FiniteMeasure LatentTheta) := inferInstance
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal hmarkov_of_commutes

/-- Compatibility middle-strength wrapper:
if finite-prefix marginals of `iidSequenceKernelTheta` are Bernoulli product
measures, derive the latent-Dirac witness internally and dispatch to the
canonical no-explicit-prefix-law endpoint.

Prefer
`deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals`
or the canonical markov-only endpoint
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hprefixPi :
      ∀ (θ : LatentTheta) (n : ℕ),
        (iidSequenceKernelTheta θ).map (seqPrefixProj n) =
          Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ))
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals
      (Y := Y) (Ω := Ω) (X := X) hcore hglobal hprefixPi
      (hunivDefault := fun (Y' : Type) _ =>
        kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))
      hmarkov_of_commutes

/-- Explicit adapter alias for the default-all-sources prefix-`π`
middle-strength route.

Prefer the canonical Markov-only endpoint
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hprefixPi :
      ∀ (θ : LatentTheta) (n : ℕ),
        (iidSequenceKernelTheta θ).map (seqPrefixProj n) =
          Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ))
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals
      (Y := Y) (Ω := Ω) (X := X) hcore hglobal hprefixPi
      (hunivDefault := fun (Y' : Type) _ =>
        kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))
      hmarkov_of_commutes

/-- Deprecated compatibility wrapper (full-target route, standard-Borel probability-measure
upgrade): use when you want to thread an explicit
`StandardBorelSpace (ProbabilityMeasure LatentTheta)` assumption. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw_of_standardBorelProbabilityMeasure
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    [StandardBorelSpace (ProbabilityMeasure LatentTheta)]
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_standardBorelProbabilityMeasure
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal iidSequenceKernelTheta_represents_latentDirac_unconditional
      hmarkov_of_commutes

/-- Deprecated convenience fallback wrapper (full-target route, finite-measure bridge path):
use this only when the preferred
`deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw`
(`ProbabilityMeasure`-Borel route) is not
available in the local environment.

This fallback is intentionally explicit and retained for compatibility; the
preferred route no longer requires explicit Borel assumptions at call sites. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw_of_finiteMeasureBorel
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    [BorelSpace (FiniteMeasure LatentTheta)]
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  letI : BorelSpace (FiniteMeasure LatentTheta) := inferInstance
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_finiteMeasureBorel
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal iidSequenceKernelTheta_represents_latentDirac_unconditional
      hmarkov_of_commutes

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernel
    (since := "2026-02-20")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernel_and_prefixLaw

attribute
  [deprecated
    deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (since := "2026-02-20")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted
    (since := "2026-02-20")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals
    (since := "2026-02-20")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals

attribute
  [deprecated
    deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (since := "2026-02-20")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernel

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw_of_thetaMomentEmbedding

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_canonical_of_prefixLaw_and_thetaMomentEmbedding

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_canonical

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_latentDirac

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_standardBorelProbabilityMeasure
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw_of_standardBorelProbabilityMeasure

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_finiteMeasureBorel
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw_of_finiteMeasureBorel

/-- Recommended export: any concrete `IsLimit` witness yields the Markov-only
global mediator-uniqueness property for the same Kleisli cone. -/
theorem deFinettiExport_isLimit_implies_globalIIDConeMediatorUnique_markovOnly
    (cone : KleisliGiryIIDConeSkeleton)
    (hlim : CategoryTheory.Limits.IsLimit (cone.toCone)) :
    GlobalIIDConeMediatorUnique_markovOnly cone :=
  deFinettiStable_isLimit_implies_globalIIDConeMediatorUnique_markovOnly
    cone hlim

/-- Recommended export: canonical all-sources strengthening of the kernel
universal mediator API (quantifier-complete source side). -/
theorem deFinettiExport_kernelUniversalMediator_allSources_default
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator_allSources (Ω := Ω) X :=
  deFinettiStable_kernelUniversalMediator_allSources_default (Ω := Ω) X

/-- Recommended export: on discrete source measurable spaces, the default
qualitative all-sources witness upgrades to a measurable latent kernel
mediator. -/
theorem deFinettiExport_allSourcesKernel_discrete_of_allSourcesDefault
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (Y : Type) [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hκexch : KernelExchangeable (X := coordProcess) κ) :
    ∃! L : ProbabilityTheory.Kernel Y LatentTheta,
      KernelRepresentsLatentTheta (X := coordProcess) (κ := κ) (fun y => L y) :=
  deFinettiStable_allSourcesKernel_discrete_of_allSourcesDefault
    (hunivDefault := hunivDefault) Y κ hκexch

/-- Recommended export: all-sources Markov-only Kleisli mediator property
implies Markov-only global mediator uniqueness for `iidSequenceKernelTheta`. -/
theorem deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_allSourcesKleisli
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly) :
    GlobalIIDConeMediatorUnique_markovOnly (iidSequenceKleisliConeSkeleton hcommutes) :=
  deFinettiStable_globalIIDConeMediatorUnique_markovOnly_of_allSourcesKleisli
    (hcommutes := hcommutes) huniv

/-- Recommended canonical Markov-only one-hop route (no commutes⇒Markov
adapter): global finitary invariance implies Markov-only global mediator
uniqueness for the canonical `iidSequenceKernelTheta` cone, using the default
all-sources qualitative de Finetti witness and the canonical moment-embedding
bridge. The latent-Dirac witness is supplied internally. -/
theorem deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    GlobalIIDConeMediatorUnique_markovOnly
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) :=
  deFinettiStable_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (hglobal := hglobal)
    (hunivDefault := fun (Y' : Type) _ =>
      kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))

/-! ### Legacy wrappers (deprecated) -/

/-- Compatibility wrapper retaining an explicit latent-Dirac witness.
Prefer
`deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`.
-/

@[deprecated
  deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
  (since := "2026-02-20")]
theorem deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_latentDirac
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta))) :
    GlobalIIDConeMediatorUnique_markovOnly
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) :=
  deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (hglobal := hglobal)

/-- Recommended export: strict iid prefix law + all-sources kernel-level latent
mediation imply all-sources Markov-only Kleisli universality directly. -/
theorem deFinettiExport_allSourcesKleisli_markovOnly_of_allSourcesKernel_and_prefixLaw
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly :=
  deFinettiStable_allSourcesKleisli_markovOnly_of_allSourcesKernel_and_prefixLaw
    (hprefix := hprefix) huniv

/-- Recommended export: unrestricted all-sources Kleisli mediator property
implies full global mediator uniqueness for `iidSequenceKernelTheta`. -/
theorem deFinettiExport_globalIIDConeMediatorUnique_of_allSourcesKleisli_unrestricted
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes) :=
  deFinettiStable_globalIIDConeMediatorUnique_of_allSourcesKleisli_unrestricted
    (hcommutes := hcommutes) huniv

/-- Recommended export: unrestricted all-sources kernel-level factorization
implies unrestricted all-sources Kleisli universality. -/
theorem deFinettiExport_allSourcesKleisli_unrestricted_of_allSourcesKernelFactorization_unrestricted
    (huniv :
      KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
  deFinettiStable_allSourcesKleisli_unrestricted_of_allSourcesKernelFactorization_unrestricted
    huniv

/-- Recommended export (converse direction): full global mediator uniqueness
for `iidSequenceKernelTheta` implies unrestricted all-sources Kleisli
universality. -/
theorem deFinettiExport_allSourcesKleisli_unrestricted_of_globalIIDConeMediatorUnique
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (hmed : GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
  deFinettiStable_allSourcesKleisli_unrestricted_of_globalIIDConeMediatorUnique
    (hcommutes := hcommutes) hmed

/-- Recommended export: unrestricted all-sources Kleisli universality is
equivalent to full global mediator uniqueness for `iidSequenceKernelTheta`. -/
theorem deFinettiExport_allSourcesKleisli_unrestricted_iff_globalIIDConeMediatorUnique
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted ↔
      GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes) :=
  deFinettiStable_allSourcesKleisli_unrestricted_iff_globalIIDConeMediatorUnique
    (hcommutes := hcommutes)

/-- Recommended export (full target shape): unrestricted all-sources Kleisli
mediator property yields a concrete `IsLimit` witness for the
`iidSequenceKernelTheta` cone. -/
theorem deFinettiExport_iidSequenceKleisliCone_isLimit_of_allSourcesKleisli_unrestricted
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    Nonempty
      (CategoryTheory.Limits.IsLimit
        ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) :=
  deFinettiStable_iidSequenceKleisliCone_isLimit_of_allSourcesKleisli_unrestricted
    (hcommutes := hcommutes) huniv

/-- Recommended bridge for νPLN/Solomonoff restriction:
if a probability law on infinite binary sequences realizes the finite-prefix
weights of a restricted exchangeable Solomonoff prior, then the coordinate
process admits a unique latent-`Theta` de Finetti mediator. -/
theorem deFinettiExport_restrictedSolomonoff_prefixLaw_implies_unique_latentThetaMediator
    (M : Mettapedia.UniversalAI.SolomonoffExchangeable.RestrictedSolomonoffPrior)
    (μ : Measure Mettapedia.UniversalAI.SolomonoffPrior.InfBinString)
    [IsProbabilityMeasure μ]
    (hprefix :
      ∀ (n : ℕ) (xs : Fin n → Bool),
        μ {ω | ∀ i : Fin n, ω i = xs i} =
          ENNReal.ofReal (M.μ (List.ofFn xs))) :
    ∃! ν : Measure Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
      RepresentsLatentTheta (X := fun i ω => ω i) (μ := μ) ν := by
  have hX :
      ∀ i : ℕ, Measurable
        (fun ω : Mettapedia.UniversalAI.SolomonoffPrior.InfBinString => ω i) := by
    intro i
    simpa using (measurable_pi_apply (a := i))
  have hexch :
      Mettapedia.ProbabilityTheory.Exchangeability.InfiniteExchangeable (fun i ω => ω i) μ :=
    Mettapedia.UniversalAI.SolomonoffExchangeable.restrictedSolomonoff_infiniteExchangeable_of_prefixLaw
      (M := M) (μ := μ) (hμprob := inferInstance) hprefix
  exact deFinettiStable_existsUnique_latentThetaMeasure_of_exchangeable
    (X := fun i ω => ω i) (μ := μ) hX hexch

/-- Deprecated entrypoint: one hop from tight cylinder law.
Prefer the concrete theorem
`deFinettiExport_restrictedSolomonoff_totalOutput_and_programMassComplete_implies_nupln_master_chain_and_unique_latentThetaMediator`
when working from machine/program assumptions. This theorem remains for
compatibility at the measure-law boundary.

Recommended νPLN/categorical corollary (one hop from tight cylinder law):
the restricted Solomonoff cylinder law yields both
1. the full `nupln_master_chain` conclusion, and
2. the unique latent-`Theta` mediator conclusion. -/
theorem deFinettiExport_restrictedSolomonoff_cylinderLaw_implies_nupln_master_chain_and_unique_latentThetaMediator
    (M : Mettapedia.UniversalAI.SolomonoffExchangeable.RestrictedSolomonoffPrior)
    (μ : Measure Mettapedia.UniversalAI.SolomonoffPrior.InfBinString)
    [IsProbabilityMeasure μ]
    (hNoLeak :
      Mettapedia.UniversalAI.SolomonoffMeasure.NoLeakageAtCylindersLaw (U := M.U) (programs := M.programs) μ) :
    (∃ (B : Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture),
      Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.Represents B (fun i ω => ω i) μ ∧
      (∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
        Mettapedia.ProbabilityTheory.Exchangeability.countTrue xs₁ =
          Mettapedia.ProbabilityTheory.Exchangeability.countTrue xs₂ →
          B.prob xs₁ = B.prob xs₂)) ∧
    (∃! ν : Measure Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
      RepresentsLatentTheta (X := fun i ω => ω i) (μ := μ) ν) := by
  have hX :
      ∀ i : ℕ, Measurable
        (fun ω : Mettapedia.UniversalAI.SolomonoffPrior.InfBinString => ω i) := by
    intro i
    simpa using (measurable_pi_apply (a := i))
  have hexch :
      Mettapedia.ProbabilityTheory.Exchangeability.InfiniteExchangeable (fun i ω => ω i) μ :=
    Mettapedia.UniversalAI.SolomonoffExchangeable.restrictedSolomonoff_infiniteExchangeable_of_noLeakageAtCylindersLaw
      (M := M) (μ := μ) (hμprob := inferInstance) hNoLeak
  have hmaster := Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.nupln_master_chain
      (X := fun i ω => ω i) (μ := μ) hX hexch
  rcases hmaster with ⟨B, hrep, hsuff, _hevidence, _hconv⟩
  refine ⟨?_, ?_⟩
  · exact ⟨B, hrep, hsuff⟩
  · exact deFinettiStable_existsUnique_latentThetaMeasure_of_exchangeable
      (X := fun i ω => ω i) (μ := μ) hX hexch

/-- Recommended νPLN/categorical corollary from a concrete machine criterion:
if selected programs are total-output and root mass is normalized, the canonical
machine-induced measure yields both `nupln_master_chain` and unique latent-`Theta`
mediation, with no external cylinder-law witness required. -/
theorem deFinettiExport_restrictedSolomonoff_totalOutput_implies_nupln_master_chain_and_unique_latentThetaMediator
    (M : Mettapedia.UniversalAI.SolomonoffExchangeable.RestrictedSolomonoffPrior)
    (htot : Mettapedia.UniversalAI.SolomonoffMeasure.TotalOutputOnPrograms (U := M.U) M.programs)
    (hroot : M.μ [] = 1) :
    let μ := Mettapedia.UniversalAI.SolomonoffMeasure.totalOutputProgramMeasure
      (U := M.U) (programs := M.programs) htot
    (∃ (B : Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture),
      Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.Represents B (fun i ω => ω i) μ ∧
      (∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
        Mettapedia.ProbabilityTheory.Exchangeability.countTrue xs₁ =
          Mettapedia.ProbabilityTheory.Exchangeability.countTrue xs₂ →
          B.prob xs₁ = B.prob xs₂)) ∧
    (∃! ν : Measure Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
      RepresentsLatentTheta (X := fun i ω => ω i) (μ := μ) ν) := by
  let μ : Measure Mettapedia.UniversalAI.SolomonoffPrior.InfBinString :=
    Mettapedia.UniversalAI.SolomonoffMeasure.totalOutputProgramMeasure (U := M.U) (programs := M.programs) htot
  have hμprob : IsProbabilityMeasure μ := by
    simpa [μ, Mettapedia.UniversalAI.SolomonoffExchangeable.RestrictedSolomonoffPrior.μ] using
      (Mettapedia.UniversalAI.SolomonoffMeasure.isProbabilityMeasure_totalOutputProgramMeasure_of_root_one
        (U := M.U) (programs := M.programs) (htot := htot) hroot)
  letI : IsProbabilityMeasure μ := hμprob
  have hNoLeak :
      Mettapedia.UniversalAI.SolomonoffMeasure.NoLeakageAtCylindersLaw (U := M.U) (programs := M.programs) μ := by
    simpa [μ] using
      (Mettapedia.UniversalAI.SolomonoffMeasure.noLeakageAtCylindersLaw_totalOutputProgramMeasure
        (U := M.U) (programs := M.programs) htot)
  simpa [μ] using
    (deFinettiExport_restrictedSolomonoff_cylinderLaw_implies_nupln_master_chain_and_unique_latentThetaMediator
      (M := M) (μ := μ) hNoLeak)

/-- Recommended concrete end-to-end νPLN/categorical corollary:
assume total-output on the selected program family plus concrete program-mass
completeness (`kraftSum = 1`), then derive the same
`nupln_master_chain + unique latent-Theta mediator` conclusion with no explicit
`hroot` argument. -/
theorem deFinettiExport_restrictedSolomonoff_totalOutput_and_programMassComplete_implies_nupln_master_chain_and_unique_latentThetaMediator
    (M : Mettapedia.UniversalAI.SolomonoffExchangeable.RestrictedSolomonoffPrior)
    (htot : Mettapedia.UniversalAI.SolomonoffMeasure.TotalOutputOnPrograms (U := M.U) M.programs)
    (hcomplete : Mettapedia.UniversalAI.SolomonoffExchangeable.RestrictedSolomonoffPrior.ProgramMassComplete M) :
    let μ := Mettapedia.UniversalAI.SolomonoffMeasure.totalOutputProgramMeasure
      (U := M.U) (programs := M.programs) htot
    (∃ (B : Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture),
      Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.Represents B (fun i ω => ω i) μ ∧
      (∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
        Mettapedia.ProbabilityTheory.Exchangeability.countTrue xs₁ =
          Mettapedia.ProbabilityTheory.Exchangeability.countTrue xs₂ →
          B.prob xs₁ = B.prob xs₂)) ∧
    (∃! ν : Measure Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
      RepresentsLatentTheta (X := fun i ω => ω i) (μ := μ) ν) := by
  exact deFinettiExport_restrictedSolomonoff_totalOutput_implies_nupln_master_chain_and_unique_latentThetaMediator
    (M := M) (htot := htot)
    (hroot :=
      Mettapedia.UniversalAI.SolomonoffExchangeable.RestrictedSolomonoffPrior.mu_nil_eq_one_of_programMassComplete
        (M := M) hcomplete)

/-- Public API: finite-mass universality is equivalent to Markov-only
universality (given global finitary invariance).

This is the corrected strengthening: the fully unrestricted version is false
(counting-measure counterexample at `not_commutesToMarkovBridge_unrestricted`),
but finite-mass is proven equivalent to the Markov-only version. -/
theorem deFinettiExport_allSourcesKleisli_finiteMass_iff_markovOnly
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_finiteMass ↔
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly :=
  deFinettiStable_allSourcesKleisli_finiteMass_iff_markovOnly hglobal

/-- Public API: finite-mass universality from global finitary invariance and
default all-sources qualitative witness. Fully proven, no hypotheses needed
beyond the standard de Finetti infrastructure. -/
theorem deFinettiExport_allSourcesKleisli_finiteMass_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_finiteMass :=
  deFinettiStable_allSourcesKleisli_finiteMass_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    hglobal hunivDefault

/-! ### Cone-level finite-mass API (recommended for new downstream code) -/

/-- Public API: finite-mass cone universality for `iidSequenceKernelTheta`
from all-sources finite-mass Kleisli universality. -/
theorem deFinettiExport_globalIIDConeMediatorUnique_finiteMass_of_allSourcesKleisli_finiteMass
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_finiteMass) :
    GlobalIIDConeMediatorUnique_finiteMass (iidSequenceKleisliConeSkeleton hcommutes) :=
  deFinettiStable_globalIIDConeMediatorUnique_finiteMass_of_allSourcesKleisli_finiteMass
    (hcommutes := hcommutes) huniv

/-- Public API: finite-mass cone universality from global finitary invariance
and all-sources Markov-only Kleisli universality. -/
theorem deFinettiExport_globalIIDConeMediatorUnique_finiteMass_of_allSourcesKleisli_markovOnly
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly) :
    GlobalIIDConeMediatorUnique_finiteMass
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) :=
  deFinettiStable_globalIIDConeMediatorUnique_finiteMass_of_allSourcesKleisli_markovOnly
    (hglobal := hglobal) huniv

/-- Public API (canonical finite-mass endpoint): finite-mass cone universality
from global finitary invariance and default all-sources qualitative de Finetti.
This is the maximal correct strengthening of the canonical Markov-only endpoint.

The fully unrestricted version (`GlobalIIDConeMediatorUnique`) is false — see
`deFinettiExport_not_allSourcesKleisli_unrestricted`. The finite-mass version
is the strongest correct universal property provable for the `iidSequenceKernelTheta`
cone. -/
theorem deFinettiExport_globalIIDConeMediatorUnique_finiteMass_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    GlobalIIDConeMediatorUnique_finiteMass
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) :=
  deFinettiStable_globalIIDConeMediatorUnique_finiteMass_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (hglobal := hglobal)
    (hunivDefault := fun (Y' : Type) _ =>
      kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))

/-- Public API: finite-mass cone universality implies Markov-only cone
universality (subsumption). -/
theorem deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_finiteMass
    (cone : KleisliGiryIIDConeSkeleton)
    (hfm : GlobalIIDConeMediatorUnique_finiteMass cone) :
    GlobalIIDConeMediatorUnique_markovOnly cone :=
  deFinettiStable_globalIIDConeMediatorUnique_markovOnly_of_finiteMass cone hfm

/-- **Headline**: Categorical de Finetti in Kleisli(Giry) — finite-mass cone universality.
This is the strongest correct universal property for the iid-sequence cone.
Cite this theorem for the categorical result. -/
abbrev deFinetti_kleisliGiry :=
  @deFinettiExport_globalIIDConeMediatorUnique_finiteMass_of_globalFinitaryInvariance_and_defaultAllSourcesKernel

/-- **Headline**: Measure-level de Finetti — unique latent-θ measure from exchangeability.
Cite this theorem for the classical probabilistic result. -/
abbrev deFinetti_measure :=
  @deFinettiExport_existsUnique_latentThetaMeasure_of_exchangeable

/-! ## Categorical ↔ PLN Bridge Exports -/

/-- Export: Categorical mixture sufficiency factors through MultiEvidence.
    For any k-ary categorical mixture, two words with the same count vector
    (= same `MultiEvidence k`) have the same probability. This connects
    the categorical de Finetti infrastructure to the PLN evidence chain. -/
abbrev deFinettiExport_categorical_pln_sufficiency :=
  @Mettapedia.PLN.Bridges.ProbabilityTheory.CategoricalNuPLNBridge.categorical_pln_sufficiency

/-- Export: For k=2, categorical product PMF equals Bernoulli product PMF.
    This is the compatibility theorem showing the categorical generalization
    subsumes the binary theory. -/
abbrev deFinettiExport_categoricalProductPMF_fin2_eq_bernoulliProductPMF :=
  @Mettapedia.PLN.Bridges.ProbabilityTheory.CategoricalNuPLNBridge.categoricalProductPMF_fin2_eq_bernoulliProductPMF

end Mettapedia.CategoryTheory
