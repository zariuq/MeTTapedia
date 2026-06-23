import Mettapedia.CategoryTheory.DeFinettiKleisliGirySkeleton
import Mettapedia.Logic.MarkovDeFinettiMixtureRepresentation
import Mettapedia.Logic.MarkovDeFinettiSequenceKernel
import Mettapedia.Logic.MarkovDeFinettiSequenceKernelBorel
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Markov de Finetti Bridge to Kleisli(Giry)

This file packages the proved measure-theoretic `MarkovMixture` interface as a
small categorical bridge:

- a measure-level factorization through `MarkovParam k`, and
- a Kleisli(Giry) mediator `1 ⟶ G(MarkovParam k)`.

It now also exposes the induced sequence-level cylinder factorization obtained
by integrating the canonical fixed-parameter sequence law
`markovSequenceMeasure θ`. This still stops short of a full measurable kernel
`MarkovParam k ⟶ G((Fin k)^ℕ)`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

open CategoryTheory
open MeasureTheory
open Mettapedia.Logic
open Mettapedia.Logic.MarkovDeFinettiHard
open Mettapedia.Logic.UniversalPrediction
open scoped NNReal ENNReal

variable {k : ℕ}
variable {μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)}

/-- Terminal-source object used for constant measure mediators in
`Kleisli(MeasCat.Giry)`. -/
abbrev KleisliUnitObj : KleisliGiry :=
  CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of PUnit)

/-- Markov-parameter object in `Kleisli(MeasCat.Giry)`. -/
abbrev KleisliMarkovParamObj (k : ℕ) : KleisliGiry :=
  CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of (MarkovParam k))

/-- A terminal-source Kleisli(Giry) mediator into the Markov-parameter object. -/
structure MarkovKleisliMediator (k : ℕ) where
  hom : (MeasCat.of PUnit : MeasCat) ⟶ MeasCat.Giry.obj (MeasCat.of (MarkovParam k))

/-- Measure-level Markov de Finetti factorization through the parameter space. -/
def CategoricalMarkovDeFinettiFactorization
    (k : ℕ)
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ π : Measure (MarkovParam k), IsProbabilityMeasure π ∧
    ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂π

/-- Consumer API: recover a `MarkovMixture` from the categorical factorization
package. -/
noncomputable def markovMixtureOfCategoricalFactorization
    (hfac : CategoricalMarkovDeFinettiFactorization k μ) :
    MarkovMixture k μ := by
  exact
    ⟨Classical.choose hfac,
      (Classical.choose_spec hfac).1,
      (Classical.choose_spec hfac).2⟩

/-- Any `MarkovMixture` gives the measure-level categorical factorization. -/
theorem categoricalMarkovDeFinettiFactorization_of_markovMixture
    (M : MarkovMixture k μ) :
    CategoricalMarkovDeFinettiFactorization k μ :=
  ⟨M.mixingLaw, M.mixingLaw_prob, M.represents⟩

/-- The categorical factorization package is equivalent to having a public
`MarkovMixture` witness. -/
theorem categoricalMarkovDeFinettiFactorization_iff_nonempty_markovMixture :
    CategoricalMarkovDeFinettiFactorization k μ ↔ Nonempty (MarkovMixture k μ) := by
  constructor
  · intro hfac
    exact ⟨markovMixtureOfCategoricalFactorization (k := k) (μ := μ) hfac⟩
  · rintro ⟨M⟩
    exact categoricalMarkovDeFinettiFactorization_of_markovMixture (k := k) M

/-- Constant Kleisli(Giry) mediator out of the terminal object. -/
noncomputable def constantMarkovKleisliMediator
    (π : Measure (MarkovParam k)) :
    MarkovKleisliMediator k :=
  ⟨⟨fun _ => π, measurable_const⟩⟩

/-- A constant measure mediator is Markov exactly when the chosen measure is a
probability measure. -/
theorem constantMarkovKleisliMediator_prob
    (π : Measure (MarkovParam k))
    [hπ : IsProbabilityMeasure π] :
    IsProbabilityMeasure ((constantMarkovKleisliMediator (k := k) π).hom.1 PUnit.unit) := by
  simpa [constantMarkovKleisliMediator] using hπ

/-- Prefix-word weight induced by a Kleisli mediator into the Markov-parameter
object. -/
def markovWordWeightViaMediator
    (xs : List (Fin k)) :
    MarkovKleisliMediator k → ℝ≥0∞ :=
  fun m => ∫⁻ θ, wordProb (k := k) θ xs ∂(m.hom.1 PUnit.unit)

/-- Sequence-cylinder weight induced by a Kleisli mediator into the
Markov-parameter object. -/
def markovCylinderWeightViaMediator
    (xs : List (Fin k)) :
    MarkovKleisliMediator k → ℝ≥0∞ :=
  fun m => ∫⁻ θ,
    Mettapedia.Logic.MarkovDeFinettiSequenceKernel.markovSequenceMeasure (k := k) θ
      (MarkovDeFinettiRecurrence.cylinder (k := k) xs) ∂(m.hom.1 PUnit.unit)

/-- The sequence-cylinder mediator weight is exactly the prefix-word weight,
because the canonical sequence law of `θ` evaluates cylinders by `wordProb θ`. -/
theorem markovCylinderWeightViaMediator_eq_markovWordWeightViaMediator
    (xs : List (Fin k)) (m : MarkovKleisliMediator k) :
    markovCylinderWeightViaMediator (k := k) xs m =
      markovWordWeightViaMediator (k := k) xs m := by
  simp [markovCylinderWeightViaMediator, markovWordWeightViaMediator,
    Mettapedia.Logic.MarkovDeFinettiSequenceKernel.markovSequenceMeasure_cylinder_eq_wordProb]

/-- Kleisli(Giry) formulation of Markov de Finetti at the finite-prefix level:
there exists a Markov mediator into the parameter object whose fibers recover
the prefix law. -/
def KleisliGiryMarkovDeFinettiFactorization
    (k : ℕ)
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ m : MarkovKleisliMediator k,
    IsProbabilityMeasure (m.hom.1 PUnit.unit) ∧
      ∀ xs : List (Fin k), μ xs = markovWordWeightViaMediator (k := k) xs m

/-- Sequence-level cylinder formulation of the measure-level Markov factorization:
the prefix law is recovered by integrating the canonical sequence law over the
mixing measure on `MarkovParam k`. -/
def CategoricalMarkovSequenceCylinderFactorization
    (k : ℕ)
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ π : Measure (MarkovParam k), IsProbabilityMeasure π ∧
    ∀ xs : List (Fin k),
      μ xs = ∫⁻ θ,
        Mettapedia.Logic.MarkovDeFinettiSequenceKernel.markovSequenceMeasure (k := k) θ
          (MarkovDeFinettiRecurrence.cylinder (k := k) xs) ∂π

/-- Sequence-level cylinder formulation of the Kleisli(Giry) Markov factorization. -/
def KleisliGiryMarkovSequenceCylinderFactorization
    (k : ℕ)
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ m : MarkovKleisliMediator k,
    IsProbabilityMeasure (m.hom.1 PUnit.unit) ∧
      ∀ xs : List (Fin k), μ xs = markovCylinderWeightViaMediator (k := k) xs m

/-- Consumer API: recover a `MarkovMixture` from a Kleisli(Giry) factorization
witness by evaluating the mediator at the unique terminal element. -/
noncomputable def markovMixtureOfKleisliGiryFactorization
    (hfac : KleisliGiryMarkovDeFinettiFactorization k μ) :
    MarkovMixture k μ := by
  let m := Classical.choose hfac
  let hm := (Classical.choose_spec hfac).1
  let hrep := (Classical.choose_spec hfac).2
  exact
    ⟨m.hom.1 PUnit.unit,
      hm,
      hrep⟩

/-- The canonical Kleisli mediator carried by a `MarkovMixture`. -/
noncomputable def markovMixtureKleisliMediator
    (M : MarkovMixture k μ) :
    MarkovKleisliMediator k :=
  constantMarkovKleisliMediator (k := k) M.mixingLaw

/-- The canonical Kleisli mediator of a `MarkovMixture` is Markov. -/
theorem markovMixtureKleisliMediator_prob
    (M : MarkovMixture k μ) :
    IsProbabilityMeasure ((markovMixtureKleisliMediator (k := k) M).hom.1 PUnit.unit) := by
  simpa [markovMixtureKleisliMediator, constantMarkovKleisliMediator] using
    M.mixingLaw_prob

/-- The canonical Kleisli mediator computes the same prefix weights as the
underlying `MarkovMixture`. -/
theorem markovMixtureKleisliMediator_prefix_eq
    (M : MarkovMixture k μ)
    (xs : List (Fin k)) :
    μ xs = markovWordWeightViaMediator (k := k) xs
      (markovMixtureKleisliMediator (k := k) M) := by
  simpa [markovWordWeightViaMediator, markovMixtureKleisliMediator,
    constantMarkovKleisliMediator] using
      M.represents xs

/-- The canonical Kleisli mediator of a `MarkovMixture` also computes the
sequence-cylinder weights induced by the fixed-parameter sequence law. -/
theorem markovMixtureKleisliMediator_cylinder_eq
    (M : MarkovMixture k μ)
    (xs : List (Fin k)) :
    μ xs = markovCylinderWeightViaMediator (k := k) xs
      (markovMixtureKleisliMediator (k := k) M) := by
  rw [markovCylinderWeightViaMediator_eq_markovWordWeightViaMediator (k := k) xs]
  exact markovMixtureKleisliMediator_prefix_eq (k := k) M xs

/-- Any `MarkovMixture` yields a Kleisli(Giry) factorization through the
Markov parameter space. -/
theorem kleisliGiryMarkovDeFinettiFactorization_of_markovMixture
    (M : MarkovMixture k μ) :
    KleisliGiryMarkovDeFinettiFactorization k μ := by
  refine ⟨markovMixtureKleisliMediator (k := k) M, ?_, ?_⟩
  · exact markovMixtureKleisliMediator_prob (k := k) M
  · intro xs
    exact markovMixtureKleisliMediator_prefix_eq (k := k) M xs

/-- Any `MarkovMixture` yields the corresponding sequence-cylinder factorization
through the parameter space. -/
theorem categoricalMarkovSequenceCylinderFactorization_of_markovMixture
    (M : MarkovMixture k μ) :
    CategoricalMarkovSequenceCylinderFactorization k μ := by
  refine ⟨M.mixingLaw, M.mixingLaw_prob, ?_⟩
  intro xs
  simpa [CategoricalMarkovSequenceCylinderFactorization,
    Mettapedia.Logic.MarkovDeFinettiSequenceKernel.markovSequenceMeasure_cylinder_eq_wordProb] using
    M.represents xs

/-- Any `MarkovMixture` yields the sequence-cylinder Kleisli(Giry) factorization. -/
theorem kleisliGiryMarkovSequenceCylinderFactorization_of_markovMixture
    (M : MarkovMixture k μ) :
    KleisliGiryMarkovSequenceCylinderFactorization k μ := by
  refine ⟨markovMixtureKleisliMediator (k := k) M, ?_, ?_⟩
  · exact markovMixtureKleisliMediator_prob (k := k) M
  · intro xs
    exact markovMixtureKleisliMediator_cylinder_eq (k := k) M xs

/-- A Kleisli(Giry) factorization immediately yields the corresponding
measure-level categorical factorization. -/
theorem categoricalMarkovDeFinettiFactorization_of_kleisliGiry
    (hfac : KleisliGiryMarkovDeFinettiFactorization k μ) :
    CategoricalMarkovDeFinettiFactorization k μ := by
  rcases hfac with ⟨m, hm, hrep⟩
  exact ⟨m.hom.1 PUnit.unit, hm, hrep⟩

/-- A measure-level factorization gives a constant Kleisli(Giry) mediator. -/
theorem kleisliGiryMarkovDeFinettiFactorization_of_categorical
    (hfac : CategoricalMarkovDeFinettiFactorization k μ) :
    KleisliGiryMarkovDeFinettiFactorization k μ := by
  rcases hfac with ⟨π, hπ, hrep⟩
  refine ⟨constantMarkovKleisliMediator (k := k) π, ?_, ?_⟩
  · letI : IsProbabilityMeasure π := hπ
    exact constantMarkovKleisliMediator_prob (k := k) π
  · intro xs
    simpa [markovWordWeightViaMediator, constantMarkovKleisliMediator] using hrep xs

/-- The measure-level and Kleisli(Giry) formulations are equivalent. -/
theorem categoricalMarkovDeFinettiFactorization_iff_kleisliGiry :
    CategoricalMarkovDeFinettiFactorization k μ ↔
      KleisliGiryMarkovDeFinettiFactorization k μ := by
  constructor
  · intro hfac
    exact kleisliGiryMarkovDeFinettiFactorization_of_categorical
      (k := k) (μ := μ) hfac
  · intro hfac
    exact categoricalMarkovDeFinettiFactorization_of_kleisliGiry
      (k := k) (μ := μ) hfac

/-- The sequence-cylinder and prefix-word measure-level factorization packages
are equivalent. -/
theorem categoricalMarkovSequenceCylinderFactorization_iff_categoricalMarkovDeFinettiFactorization :
    CategoricalMarkovSequenceCylinderFactorization k μ ↔
      CategoricalMarkovDeFinettiFactorization k μ := by
  constructor
  · rintro ⟨π, hπ, hrep⟩
    refine ⟨π, hπ, ?_⟩
    intro xs
    simpa [Mettapedia.Logic.MarkovDeFinettiSequenceKernel.markovSequenceMeasure_cylinder_eq_wordProb]
      using hrep xs
  · rintro ⟨π, hπ, hrep⟩
    refine ⟨π, hπ, ?_⟩
    intro xs
    simpa [Mettapedia.Logic.MarkovDeFinettiSequenceKernel.markovSequenceMeasure_cylinder_eq_wordProb]
      using hrep xs

/-- The sequence-cylinder and prefix-word Kleisli(Giry) factorization packages
are equivalent. -/
theorem kleisliGiryMarkovSequenceCylinderFactorization_iff_kleisliGiryMarkovDeFinettiFactorization :
    KleisliGiryMarkovSequenceCylinderFactorization k μ ↔
      KleisliGiryMarkovDeFinettiFactorization k μ := by
  constructor
  · rintro ⟨m, hm, hrep⟩
    refine ⟨m, hm, ?_⟩
    intro xs
    rw [← markovCylinderWeightViaMediator_eq_markovWordWeightViaMediator (k := k) xs m]
    exact hrep xs
  · rintro ⟨m, hm, hrep⟩
    refine ⟨m, hm, ?_⟩
    intro xs
    rw [markovCylinderWeightViaMediator_eq_markovWordWeightViaMediator (k := k) xs m]
    exact hrep xs

/-- The Kleisli(Giry) Markov factorization is equivalent to having a public
`MarkovMixture` witness. -/
theorem kleisliGiryMarkovDeFinettiFactorization_iff_nonempty_markovMixture :
    KleisliGiryMarkovDeFinettiFactorization k μ ↔ Nonempty (MarkovMixture k μ) := by
  calc
    KleisliGiryMarkovDeFinettiFactorization k μ ↔
        CategoricalMarkovDeFinettiFactorization k μ := by
          exact (categoricalMarkovDeFinettiFactorization_iff_kleisliGiry
            (k := k) (μ := μ)).symm
    _ ↔ Nonempty (MarkovMixture k μ) :=
      categoricalMarkovDeFinettiFactorization_iff_nonempty_markovMixture
        (k := k) (μ := μ)

/-- The sequence-cylinder Kleisli(Giry) formulation is equivalent to having a
public `MarkovMixture` witness. -/
theorem kleisliGiryMarkovSequenceCylinderFactorization_iff_nonempty_markovMixture :
    KleisliGiryMarkovSequenceCylinderFactorization k μ ↔ Nonempty (MarkovMixture k μ) := by
  calc
    KleisliGiryMarkovSequenceCylinderFactorization k μ ↔
        KleisliGiryMarkovDeFinettiFactorization k μ := by
          exact
            kleisliGiryMarkovSequenceCylinderFactorization_iff_kleisliGiryMarkovDeFinettiFactorization
              (k := k) (μ := μ)
    _ ↔ Nonempty (MarkovMixture k μ) :=
      kleisliGiryMarkovDeFinettiFactorization_iff_nonempty_markovMixture
        (k := k) (μ := μ)

section BorelParameterSpace

local instance : MeasurableSpace (MarkovParam k) := MarkovParam.borelMS (k := k)
local instance : BorelSpace (MarkovParam k) := ⟨rfl⟩

/-- Cylinders in `Fin k`-valued sequence space are measurable. -/
lemma measurableSet_markovCylinder (xs : List (Fin k)) :
    MeasurableSet (Mettapedia.Logic.MarkovDeFinettiRecurrence.cylinder (k := k) xs) := by
  classical
  unfold Mettapedia.Logic.MarkovDeFinettiRecurrence.cylinder
  refine MeasurableSet.iInter ?_
  intro i
  simpa [Set.setOf_eq_eq_singleton] using
    (measurableSet_eq_fun (measurable_pi_apply i.1) measurable_const)

/-- Honest Borel-side prefix-law factorization through the Borel probability
space on `MarkovParam k`. This mirrors the older prefix-law surface, but does
not claim any transport back to the coarser active measurable space. -/
def CategoricalBorelMarkovDeFinettiFactorization
    (k : ℕ)
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov k,
    ∀ xs : List (Fin k), μ xs = momentMapWord (k := k) xs π

/-- Public Borel-side mixture object. This is the honest interface boundary for
the stronger measurable sequence-kernel construction: unlike `MarkovMixture`,
it lives entirely on the Borel parameter space. -/
structure BorelMarkovMixture
    (k : ℕ)
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) where
  mixingLaw : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov k
  represents : ∀ xs : List (Fin k), μ xs = momentMapWord (k := k) xs mixingLaw

namespace BorelMarkovMixture

/-- Any Borel-side mixture witness gives the corresponding Borel prefix-law
factorization. -/
theorem categoricalBorelMarkovDeFinettiFactorization_of_borelMarkovMixture
    (M : BorelMarkovMixture k μ) :
    CategoricalBorelMarkovDeFinettiFactorization k μ :=
  ⟨M.mixingLaw, M.represents⟩

/-- Consumer API: build a `BorelMarkovMixture` from the Borel prefix-law
factorization package. -/
noncomputable def ofCategoricalBorelFactorization
    (hfac : CategoricalBorelMarkovDeFinettiFactorization k μ) :
    BorelMarkovMixture k μ := by
  exact ⟨Classical.choose hfac, Classical.choose_spec hfac⟩

/-- The Borel prefix-law factorization package is equivalent to having a public
`BorelMarkovMixture` witness. -/
theorem categoricalBorelMarkovDeFinettiFactorization_iff_nonempty_borelMarkovMixture :
    CategoricalBorelMarkovDeFinettiFactorization k μ ↔ Nonempty (BorelMarkovMixture k μ) := by
  constructor
  · intro hfac
    exact ⟨ofCategoricalBorelFactorization (k := k) (μ := μ) hfac⟩
  · rintro ⟨M⟩
    exact categoricalBorelMarkovDeFinettiFactorization_of_borelMarkovMixture
      (k := k) (μ := μ) M

end BorelMarkovMixture

/-- Borel-side sequence mixture obtained by binding a Borel probability law on
`MarkovParam k` against the measurable sequence kernel. -/
noncomputable def borelMarkovSequenceMixture
    (π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov k) :
    Measure (ℕ → Fin k) :=
  (π : Measure (MarkovParam k)).bind
    (Mettapedia.Logic.MarkovDeFinettiSequenceKernelBorel.markovSequenceKernel (k := k))

/-- The Borel-side sequence mixture is a probability measure. -/
instance borelMarkovSequenceMixture_isProbability
    (π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov k) :
    IsProbabilityMeasure (borelMarkovSequenceMixture (k := k) π) := by
  letI : IsProbabilityMeasure (π : Measure (MarkovParam k)) := by infer_instance
  exact MeasureTheory.isProbabilityMeasure_bind
    (hf₀ := ProbabilityTheory.Kernel.aemeasurable _)
    (hf₁ := Filter.Eventually.of_forall (fun _ => by infer_instance))

/-- Sequence-cylinder weight induced by a Borel probability law on
`MarkovParam k` through the measurable sequence kernel. -/
def borelMarkovCylinderWeightViaProbMarkov
    (π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov k)
    (xs : List (Fin k)) : ℝ≥0∞ :=
  ∫⁻ θ,
    Mettapedia.Logic.MarkovDeFinettiSequenceKernelBorel.markovSequenceKernel (k := k) θ
      (Mettapedia.Logic.MarkovDeFinettiRecurrence.cylinder (k := k) xs) ∂(π : Measure (MarkovParam k))

/-- The Borel-side kernel cylinder weights coincide with the older Borel
prefix-law moment map. -/
theorem borelMarkovCylinderWeightViaProbMarkov_eq_momentMapWord
    (π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov k)
    (xs : List (Fin k)) :
    borelMarkovCylinderWeightViaProbMarkov (k := k) π xs =
      momentMapWord (k := k) xs π := by
  simp [borelMarkovCylinderWeightViaProbMarkov,
    Mettapedia.Logic.MarkovDeFinettiSequenceKernelBorel.markovSequenceKernel_cylinder_eq_wordProb,
    momentMapWord]

/-- The Borel-side sequence mixture evaluates cylinders by integrating the
corresponding cylinder weights of the measurable sequence kernel. -/
theorem borelMarkovSequenceMixture_cylinder_eq
    (π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov k)
    (xs : List (Fin k)) :
    borelMarkovSequenceMixture (k := k) π
        (Mettapedia.Logic.MarkovDeFinettiRecurrence.cylinder (k := k) xs) =
      borelMarkovCylinderWeightViaProbMarkov (k := k) π xs := by
  letI : IsProbabilityMeasure (π : Measure (MarkovParam k)) := by infer_instance
  rw [borelMarkovSequenceMixture, Measure.bind_apply
    (measurableSet_markovCylinder (k := k) xs)
    (ProbabilityTheory.Kernel.aemeasurable _)]
  rfl

/-- Public Borel-side factorization through the measurable sequence kernel
`MarkovParam k → G((Fin k)^ℕ)`. This is the honest categorical surface for the
stronger kernel construction before transporting back to the coarser active
parameter σ-algebra. -/
def CategoricalBorelMarkovSequenceKernelFactorization
    (k : ℕ)
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov k,
    ∀ xs : List (Fin k),
      μ xs = borelMarkovCylinderWeightViaProbMarkov (k := k) π xs

/-- The Borel-side sequence-kernel and Borel-side prefix-law factorizations are
equivalent. This is the honest analogue of the older prefix/cylinder
equivalence at the stronger Borel measurable-space level. -/
theorem categoricalBorelMarkovSequenceKernelFactorization_iff_categoricalBorelMarkovDeFinettiFactorization :
    CategoricalBorelMarkovSequenceKernelFactorization k μ ↔
      CategoricalBorelMarkovDeFinettiFactorization k μ := by
  constructor
  · rintro ⟨π, hπ⟩
    refine ⟨π, ?_⟩
    intro xs
    rw [hπ xs, borelMarkovCylinderWeightViaProbMarkov_eq_momentMapWord (k := k) π xs]
  · rintro ⟨π, hπ⟩
    refine ⟨π, ?_⟩
    intro xs
    rw [borelMarkovCylinderWeightViaProbMarkov_eq_momentMapWord (k := k) π xs]
    exact hπ xs

/-- Equivalent presentation of the Borel-side factorization using the induced
sequence mixture measure. -/
theorem categoricalBorelMarkovSequenceKernelFactorization_iff_exists_borelMarkovSequenceMixture :
    CategoricalBorelMarkovSequenceKernelFactorization k μ ↔
      ∃ π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov k,
        ∀ xs : List (Fin k),
          μ xs =
            borelMarkovSequenceMixture (k := k) π
              (Mettapedia.Logic.MarkovDeFinettiRecurrence.cylinder (k := k) xs) := by
  constructor
  · rintro ⟨π, hπ⟩
    refine ⟨π, ?_⟩
    intro xs
    rw [borelMarkovSequenceMixture_cylinder_eq (k := k) π xs]
    exact hπ xs
  · rintro ⟨π, hπ⟩
    refine ⟨π, ?_⟩
    intro xs
    rw [← borelMarkovSequenceMixture_cylinder_eq (k := k) π xs]
    exact hπ xs

/-- The Borel-side sequence-kernel factorization is equivalent to having a
public `BorelMarkovMixture` witness. -/
theorem categoricalBorelMarkovSequenceKernelFactorization_iff_nonempty_borelMarkovMixture :
    CategoricalBorelMarkovSequenceKernelFactorization k μ ↔
      Nonempty (BorelMarkovMixture k μ) := by
  calc
    CategoricalBorelMarkovSequenceKernelFactorization k μ ↔
        CategoricalBorelMarkovDeFinettiFactorization k μ := by
          exact
            categoricalBorelMarkovSequenceKernelFactorization_iff_categoricalBorelMarkovDeFinettiFactorization
              (k := k) (μ := μ)
    _ ↔ Nonempty (BorelMarkovMixture k μ) :=
      BorelMarkovMixture.categoricalBorelMarkovDeFinettiFactorization_iff_nonempty_borelMarkovMixture
        (k := k) (μ := μ)

end BorelParameterSpace

section BorelToActiveLift

/-- Trim a Borel probability law on `MarkovParam k` down to the active
wordProb-generated measurable space. This is the honest one-way bridge from the
stronger Borel-side interface back to the older active theorem surface. -/
noncomputable def probMarkovToActiveMeasure
    (π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov k) :
    Measure (MarkovParam k) :=
  (π : @Measure (MarkovParam k) MarkovParam.borelMS).trim
    (Mettapedia.Logic.MarkovDeFinettiHard.wordProbGenerated_le_borel (k := k))

/-- The trimmed active-space law of a Borel probability measure is still a
probability measure. -/
theorem probMarkovToActiveMeasure_isProbability
    (π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov k) :
    IsProbabilityMeasure (probMarkovToActiveMeasure (k := k) π) := by
  refine ⟨?_⟩
  rw [probMarkovToActiveMeasure,
    trim_measurableSet_eq
      (Mettapedia.Logic.MarkovDeFinettiHard.wordProbGenerated_le_borel (k := k))
      MeasurableSet.univ]
  exact measure_univ

/-- Trimming a Borel law down to the active σ-algebra preserves the integrals of
all active `wordProb` coordinates. -/
theorem lintegral_probMarkovToActiveMeasure_wordProb
    (π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov k)
    (xs : List (Fin k)) :
    ∫⁻ θ, wordProb (k := k) θ xs ∂(probMarkovToActiveMeasure (k := k) π) =
      Mettapedia.Logic.MarkovDeFinettiHard.momentMapWord (k := k) xs π := by
  rw [probMarkovToActiveMeasure, Mettapedia.Logic.MarkovDeFinettiHard.momentMapWord]
  exact MeasureTheory.lintegral_trim
    (Mettapedia.Logic.MarkovDeFinettiHard.wordProbGenerated_le_borel (k := k))
    (Mettapedia.Logic.MarkovDeFinettiHard.measurable_wordProb (k := k) xs)

/-- One-way lift: a Borel-side prefix-law factorization yields the older active
prefix-law factorization after trimming the mixing law to the active σ-algebra. -/
theorem categoricalMarkovDeFinettiFactorization_of_categoricalBorelMarkovDeFinettiFactorization
    (hfac : CategoricalBorelMarkovDeFinettiFactorization k μ) :
    CategoricalMarkovDeFinettiFactorization k μ := by
  rcases hfac with ⟨π, hπ⟩
  refine ⟨probMarkovToActiveMeasure (k := k) π,
    probMarkovToActiveMeasure_isProbability (k := k) π, ?_⟩
  intro xs
  calc
    μ xs = Mettapedia.Logic.MarkovDeFinettiHard.momentMapWord (k := k) xs π := hπ xs
    _ = ∫⁻ θ, wordProb (k := k) θ xs ∂(probMarkovToActiveMeasure (k := k) π) := by
          symm
          exact lintegral_probMarkovToActiveMeasure_wordProb (k := k) π xs

/-- One-way lift: a public `BorelMarkovMixture` yields a public active
`MarkovMixture`. -/
noncomputable def markovMixtureOfBorelMarkovMixture
    (M : BorelMarkovMixture k μ) :
    MarkovMixture k μ :=
  markovMixtureOfCategoricalFactorization (k := k) (μ := μ)
    (categoricalMarkovDeFinettiFactorization_of_categoricalBorelMarkovDeFinettiFactorization
      (k := k) (μ := μ)
      (BorelMarkovMixture.categoricalBorelMarkovDeFinettiFactorization_of_borelMarkovMixture
        (k := k) (μ := μ) M))

/-- One-way lift at the existence level: any Borel-side mixture witness gives an
active `MarkovMixture` witness. -/
theorem nonempty_markovMixture_of_nonempty_borelMarkovMixture :
    Nonempty (BorelMarkovMixture k μ) → Nonempty (MarkovMixture k μ) := by
  rintro ⟨M⟩
  exact ⟨markovMixtureOfBorelMarkovMixture (k := k) (μ := μ) M⟩

end BorelToActiveLift

section NonUniquenessCounterexample

local instance : MeasurableSpace (MarkovParam 2) := MarkovParam.borelMS (k := 2)
local instance : BorelSpace (MarkovParam 2) := ⟨rfl⟩

/-- A binary Markov parameter whose initial state is `0`, whose reachable row
`0` is absorbing at `0`, and whose unreachable row `1` also points to `0`. -/
noncomputable def deadRowTheta₀ : MarkovParam 2 where
  init := MeasureTheory.diracProba (0 : Fin 2)
  trans
    | 0 => MeasureTheory.diracProba (0 : Fin 2)
    | 1 => MeasureTheory.diracProba (0 : Fin 2)

/-- Same as `deadRowTheta₀`, except the unreachable row `1` points to `1`. -/
noncomputable def deadRowTheta₁ : MarkovParam 2 where
  init := MeasureTheory.diracProba (0 : Fin 2)
  trans
    | 0 => MeasureTheory.diracProba (0 : Fin 2)
    | 1 => MeasureTheory.diracProba (1 : Fin 2)

private theorem diracProba_singleton_eval (x y : Fin 2) :
    MeasureTheory.diracProba x (Set.singleton y) = if x = y then 1 else 0 := by
  change
    ((((MeasureTheory.diracProba x : ProbabilityMeasure (Fin 2)) : Measure (Fin 2))
      (Set.singleton y)).toNNReal = if x = y then 1 else 0)
  rw [MeasureTheory.diracProba_toMeasure_apply]
  by_cases h : x = y
  · subst h
    rw [Set.indicator_of_mem (by exact Set.mem_singleton _)]
    simp
  · rw [Set.indicator_of_notMem]
    · simp [h]
    · exact h

@[simp] theorem deadRowTheta₀_initProb_zero :
    initProb (k := 2) deadRowTheta₀ 0 = 1 := by
  simpa [deadRowTheta₀, initProb] using diracProba_singleton_eval 0 0

@[simp] theorem deadRowTheta₀_initProb_one :
    initProb (k := 2) deadRowTheta₀ 1 = 0 := by
  simpa [deadRowTheta₀, initProb] using diracProba_singleton_eval 0 1

@[simp] theorem deadRowTheta₁_initProb_zero :
    initProb (k := 2) deadRowTheta₁ 0 = 1 := by
  simpa [deadRowTheta₁, initProb] using diracProba_singleton_eval 0 0

@[simp] theorem deadRowTheta₁_initProb_one :
    initProb (k := 2) deadRowTheta₁ 1 = 0 := by
  simpa [deadRowTheta₁, initProb] using diracProba_singleton_eval 0 1

@[simp] theorem deadRowTheta₀_stepProb_zero_zero :
    stepProb (k := 2) deadRowTheta₀ 0 0 = 1 := by
  simpa [deadRowTheta₀, stepProb] using diracProba_singleton_eval 0 0

@[simp] theorem deadRowTheta₀_stepProb_zero_one :
    stepProb (k := 2) deadRowTheta₀ 0 1 = 0 := by
  simpa [deadRowTheta₀, stepProb] using diracProba_singleton_eval 0 1

@[simp] theorem deadRowTheta₀_stepProb_one_one :
    stepProb (k := 2) deadRowTheta₀ 1 1 = 0 := by
  simpa [deadRowTheta₀, stepProb] using diracProba_singleton_eval 0 1

@[simp] theorem deadRowTheta₁_stepProb_zero_zero :
    stepProb (k := 2) deadRowTheta₁ 0 0 = 1 := by
  simpa [deadRowTheta₁, stepProb] using diracProba_singleton_eval 0 0

@[simp] theorem deadRowTheta₁_stepProb_zero_one :
    stepProb (k := 2) deadRowTheta₁ 0 1 = 0 := by
  simpa [deadRowTheta₁, stepProb] using diracProba_singleton_eval 0 1

@[simp] theorem deadRowTheta₁_stepProb_one_one :
    stepProb (k := 2) deadRowTheta₁ 1 1 = 1 := by
  simpa [deadRowTheta₁, stepProb] using diracProba_singleton_eval 1 1

theorem deadRowTheta₀_ne_deadRowTheta₁ :
    deadRowTheta₀ ≠ deadRowTheta₁ := by
  intro h
  have hstep : (0 : ℝ≥0) = 1 := by
    simpa using congrArg (fun θ => stepProb (k := 2) θ 1 1) h
  exact zero_ne_one hstep

private theorem deadRowTheta_wordProbAux_zero_eq :
    ∀ xs : List (Fin 2),
      wordProbAux (k := 2) deadRowTheta₀ 0 xs =
        wordProbAux (k := 2) deadRowTheta₁ 0 xs
  | [] => by simp [wordProbAux]
  | b :: xs => by
      fin_cases b
      · simpa [wordProbAux] using deadRowTheta_wordProbAux_zero_eq xs
      · simp [wordProbAux]

/-- Two distinct binary Markov parameters can have the same finite-word laws. -/
theorem deadRowTheta_wordProb_eq (xs : List (Fin 2)) :
    wordProb (k := 2) deadRowTheta₀ xs = wordProb (k := 2) deadRowTheta₁ xs := by
  cases xs with
  | nil =>
      simp [wordProb, wordProbNN]
  | cons a xs =>
      fin_cases a
      · simpa [wordProb, wordProbNN] using
          congrArg (fun t : ℝ≥0 => (t : ℝ≥0∞)) (deadRowTheta_wordProbAux_zero_eq xs)
      · simp [wordProb, wordProbNN]

/-- The finite-word profile map `θ ↦ (xs ↦ wordProb θ xs)` is not injective even
in the binary case. -/
theorem not_injective_wordProbProfile_fin2 :
    ¬ Function.Injective (fun θ : MarkovParam 2 => fun xs : List (Fin 2) => wordProb (k := 2) θ xs) := by
  intro hinj
  apply deadRowTheta₀_ne_deadRowTheta₁
  apply hinj
  funext xs
  exact deadRowTheta_wordProb_eq xs

/-- Dirac Borel laws at the two indistinguishable binary parameters. -/
noncomputable def deadRowPi₀ : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov 2 :=
  MeasureTheory.diracProba deadRowTheta₀

/-- Dirac Borel laws at the two indistinguishable binary parameters. -/
noncomputable def deadRowPi₁ : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov 2 :=
  MeasureTheory.diracProba deadRowTheta₁

theorem deadRowPi₀_ne_deadRowPi₁ :
    deadRowPi₀ ≠ deadRowPi₁ := by
  intro h
  have happly := congrArg
    (fun π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov 2 =>
      (π : Measure (MarkovParam 2)) ({deadRowTheta₁} : Set (MarkovParam 2))) h
  have hzero : (0 : ℝ≥0∞) = 1 := by
    simp [deadRowPi₀, deadRowPi₁, deadRowTheta₀_ne_deadRowTheta₁] at happly
  exact zero_ne_one hzero

theorem momentMapWord_diracProba_eq_wordProb
    (θ : MarkovParam 2) (xs : List (Fin 2)) :
    Mettapedia.Logic.MarkovDeFinettiHard.momentMapWord (k := 2) xs
        (MeasureTheory.diracProba θ) =
      wordProb (k := 2) θ xs := by
  simp only [Mettapedia.Logic.MarkovDeFinettiHard.momentMapWord, MeasureTheory.diracProba,
    ProbabilityMeasure.coe_mk,
    MeasureTheory.lintegral_dirac' θ
      (Mettapedia.Logic.MarkovDeFinettiHard.measurable_wordProb_borel (k := 2) xs)]

/-- The Borel moment map also forgets this unreachable-row information. -/
theorem deadRowPi_momentMapWord_eq (xs : List (Fin 2)) :
    Mettapedia.Logic.MarkovDeFinettiHard.momentMapWord (k := 2) xs deadRowPi₀ =
      Mettapedia.Logic.MarkovDeFinettiHard.momentMapWord (k := 2) xs deadRowPi₁ := by
  calc
    Mettapedia.Logic.MarkovDeFinettiHard.momentMapWord (k := 2) xs deadRowPi₀
        = wordProb (k := 2) deadRowTheta₀ xs := by
          simpa [deadRowPi₀] using
            momentMapWord_diracProba_eq_wordProb deadRowTheta₀ xs
    _ = wordProb (k := 2) deadRowTheta₁ xs := deadRowTheta_wordProb_eq xs
    _ = Mettapedia.Logic.MarkovDeFinettiHard.momentMapWord (k := 2) xs deadRowPi₁ := by
          simpa [deadRowPi₁] using
            (momentMapWord_diracProba_eq_wordProb deadRowTheta₁ xs).symm

/-- The Borel prefix-law map `π ↦ (xs ↦ ∫ wordProb θ xs dπ)` is not injective in
the binary case, so Borel lifts of active prefix data are not unique in
general. -/
theorem not_injective_borelMomentMapWord_fin2 :
    ¬ Function.Injective
      (fun π : Mettapedia.Logic.MarkovDeFinettiHard.ProbMarkov 2 =>
        fun xs : List (Fin 2) =>
          Mettapedia.Logic.MarkovDeFinettiHard.momentMapWord (k := 2) xs π) := by
  intro hinj
  apply deadRowPi₀_ne_deadRowPi₁
  apply hinj
  funext xs
  exact deadRowPi_momentMapWord_eq xs

/-- Prefix measure carried by the shared finite-word law of the dead-row
counterexample. -/
noncomputable def deadRowPrefixMeasure :
    Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin 2) where
  toFun := fun xs => wordProb (k := 2) deadRowTheta₀ xs
  root_eq_one' := by simp [wordProb, wordProbNN]
  additive' := by
    intro xs
    exact (Mettapedia.Logic.MarkovDeFinettiHard.wordProb_append_sum
      (k := 2) deadRowTheta₀ xs).symm

/-- First Borel mixture witness for the dead-row prefix law. -/
noncomputable def deadRowBorelMarkovMixture₀ :
    BorelMarkovMixture 2 deadRowPrefixMeasure where
  mixingLaw := deadRowPi₀
  represents := by
    intro xs
    simpa [deadRowPrefixMeasure, deadRowPi₀] using
      (momentMapWord_diracProba_eq_wordProb deadRowTheta₀ xs).symm

/-- Second Borel mixture witness for the same dead-row prefix law. -/
noncomputable def deadRowBorelMarkovMixture₁ :
    BorelMarkovMixture 2 deadRowPrefixMeasure where
  mixingLaw := deadRowPi₁
  represents := by
    intro xs
    calc
      deadRowPrefixMeasure xs = wordProb (k := 2) deadRowTheta₀ xs := by
        rfl
      _ = wordProb (k := 2) deadRowTheta₁ xs := deadRowTheta_wordProb_eq xs
      _ = Mettapedia.Logic.MarkovDeFinettiHard.momentMapWord (k := 2) xs deadRowPi₁ := by
            simpa [deadRowPi₁] using
              (momentMapWord_diracProba_eq_wordProb deadRowTheta₁ xs).symm

/-- Concrete non-uniqueness of Borel lifts for the same finite-word law. -/
theorem deadRowPrefixMeasure_has_two_distinct_borelMarkovMixtures :
    deadRowBorelMarkovMixture₀ ≠ deadRowBorelMarkovMixture₁ := by
  intro h
  apply deadRowPi₀_ne_deadRowPi₁
  exact congrArg BorelMarkovMixture.mixingLaw h

end NonUniquenessCounterexample

end Mettapedia.CategoryTheory
