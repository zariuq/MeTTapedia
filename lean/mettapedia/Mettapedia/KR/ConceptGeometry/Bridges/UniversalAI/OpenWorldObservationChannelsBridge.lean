import Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureConstructionBaseBridge

/-!
# Typed open-world observation channels

This module separates three roles in an open-ended concept-formation system:

* abstract, physical, or mathematical structure;
* phenomenal or qualitative evidence; and
* indexical location or viewpoint.

The three roles have independent types, but they may also be instantiated by
one common mathematical carrier.  Role separation is structural: using the
same carrier does not identify the fields.

An observation system projects typed observations to binary sources for the
existing algorithmic-feature theory.  Its observed set grows monotonically by
stage.  The induced construction base and stagewise feature context reuse the
existing concept, PLN, and indexed operational semantics; no parallel notion
of implication is introduced.

There is deliberately no unconditional totality component.  Full closure over
the declared observation carrier promotes to global strict feature implication
only when the source projection is surjective.  Finite and non-surjective
controls show why that premise is material.
-/

set_option autoImplicit false

namespace Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI
namespace OpenWorldObservationChannels

open scoped Classical
open scoped CategoryTheory

open CategoryTheory
open KolmogorovComplexity
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.IndexedModalFunctor
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence
open Mettapedia.KR.ConceptOntology
open Mettapedia.Logic.WorldModel.Algorithmic
open Mettapedia.Logic.WorldModel.AlgorithmicConceptFormationExamples
open AlgorithmicFeatureEvidence
open OpenEndedAlgorithmicConceptFormation

universe uStage uAbstract uPhenomenal uIndexical uSourceIndex uFeatureIndex

/-! ## Typed observations and growing systems -/

/-- One observation with separately typed abstract/physical, qualitative, and
indexical coordinates. -/
@[ext]
structure ChannelObservation
    (Abstract : Type uAbstract) (Phenomenal : Type uPhenomenal)
    (Indexical : Type uIndexical) where
  abstract : Abstract
  phenomenal : Phenomenal
  indexical : Indexical
  deriving DecidableEq, Repr

/-- A monotone family of typed observations projected into the existing binary
source universe of strict algorithmic features. -/
structure ObservationSystem
    (Stage : Type uStage) [Preorder Stage]
    (Abstract : Type uAbstract) (Phenomenal : Type uPhenomenal)
    (Indexical : Type uIndexical) where
  algorithm : ConditionalAlgorithm
  source : ChannelObservation Abstract Phenomenal Indexical → BinString
  observed : Stage → Set (ChannelObservation Abstract Phenomenal Indexical)
  observed_mono : Monotone observed

namespace ObservationSystem

variable {Stage : Type uStage} [Preorder Stage]
variable {Abstract : Type uAbstract} {Phenomenal : Type uPhenomenal}
variable {Indexical : Type uIndexical}

/-- Binary sources represented by observations visible at one stage. -/
def sourceSet
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (stage : Stage) : Set BinString :=
  C.source '' C.observed stage

/-- Represented source sets grow with their typed observation sets. -/
theorem sourceSet_mono
    (C : ObservationSystem Stage Abstract Phenomenal Indexical) :
    Monotone C.sourceSet := by
  intro earlier later growth
  exact Set.image_mono (C.observed_mono growth)

/-- Reuse the existing open-ended algorithmic feature context after source
projection. -/
def toStagewiseFeatureContext
    (C : ObservationSystem Stage Abstract Phenomenal Indexical) :
    StagewiseFeatureContext Stage where
  algorithm := C.algorithm
  observed := C.sourceSet
  observed_mono := C.sourceSet_mono

/-- Stage-local implication over the typed observations themselves. -/
def ImplicationAt
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (stage : Stage) (premise consequent : BinString) : Prop :=
  ∀ observation, observation ∈ C.observed stage →
    StrictFeatureOf C.algorithm premise (C.source observation) →
    StrictFeatureOf C.algorithm consequent (C.source observation)

/-- Implication over every observation in the declared typed carrier. -/
def Implication
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (premise consequent : BinString) : Prop :=
  ∀ observation,
    StrictFeatureOf C.algorithm premise (C.source observation) →
    StrictFeatureOf C.algorithm consequent (C.source observation)

/-- Typed stage-local implication is exactly the existing source-set
implication after projection.  Injectivity is unnecessary. -/
theorem implicationAt_iff_stagewise
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (stage : Stage) (premise consequent : BinString) :
    C.ImplicationAt stage premise consequent ↔
      C.toStagewiseFeatureContext.ImplicationAt stage premise consequent := by
  constructor
  · intro implication source premiseAtSource
    obtain ⟨observation, observed, rfl⟩ := premiseAtSource.1
    exact ⟨⟨observation, observed, rfl⟩,
      implication observation observed premiseAtSource.2⟩
  · intro implication observation observed premiseAtObservation
    exact (implication ⟨⟨observation, observed, rfl⟩,
      premiseAtObservation⟩).2

/-- Observation growth can retract implications but cannot create a later
implication absent from an earlier stage. -/
theorem implicationAt_anti
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    {earlier later : Stage} (growth : earlier ≤ later)
    {premise consequent : BinString}
    (implication : C.ImplicationAt later premise consequent) :
    C.ImplicationAt earlier premise consequent := by
  intro observation observed premiseAtObservation
  exact implication observation (C.observed_mono growth observed)
    premiseAtObservation

/-! ## Forward Ind(GSLT) semantics -/

/-- Stage order reversed to match the antitone implication relation. -/
abbrev ImplicationStage (Stage : Type uStage) := OrderDual Stage

/-- The operational implication theory at one typed observation stage.
Equality is the term equation and supported implication is the rewrite
relation. -/
abbrev implicationGSLTAt
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (stage : Stage) : GSLT where
  Term := BinString
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := C.ImplicationAt stage
  rewrites_resp_left := by
    intro premise premise' consequent premiseEq implication
    subst premise'
    exact ⟨consequent, implication, rfl⟩
  rewrites_resp_right := by
    intro premise consequent consequent' implication consequentEq
    subst consequent'
    exact implication

@[simp]
theorem implicationGSLTAt_step_iff
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (stage : Stage) (premise consequent : BinString) :
    (C.implicationGSLTAt stage).Step premise consequent ↔
      C.ImplicationAt stage premise consequent :=
  Iff.rfl

/-- Observation growth gives a forward operational translation in the
reverse direction.  Every implication surviving later was already supported
earlier. -/
def implicationGrowthTranslation
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    {earlier later : Stage} (growth : earlier ≤ later) :
    OperationalTranslation
      (C.implicationGSLTAt later) (C.implicationGSLTAt earlier) where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  mapStep := fun implication => C.implicationAt_anti growth implication

@[simp]
theorem implicationGrowthTranslation_mapTerm
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    {earlier later : Stage} (growth : earlier ≤ later)
    (feature : BinString) :
    (C.implicationGrowthTranslation growth).mapTerm feature = feature :=
  rfl

/-- Typed observation stages form a forward operational diagram after
reversing the observation order. -/
def implicationDiagram
    (C : ObservationSystem Stage Abstract Phenomenal Indexical) :
    IndexedOperational.Diagram (ImplicationStage Stage) where
  obj stage := ⟨C.implicationGSLTAt (show Stage from stage)⟩
  map {earlier later} growth :=
    C.implicationGrowthTranslation
      (show (show Stage from later) ≤ (show Stage from earlier) from
        CategoryTheory.leOfHom growth)
  map_id _ := by
    apply OperationalTranslation.ext
    rfl
  map_comp _ _ := by
    apply OperationalTranslation.ext
    rfl

/-- Pointwise lax OSLF semantics for the typed open-world observation
diagram. -/
def implicationIndexedOSLF
    (C : ObservationSystem Stage Abstract Phenomenal Indexical) :
    CategoryTheory.Functor (ImplicationStage Stage)ᵒᵖ
      ForwardModalPredicateTheory :=
  forwardIndexedOSLF C.implicationDiagram

/-- Global strict feature implication restricts to every typed observation
stage. -/
theorem implicationAt_of_strictFeatureImplication
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (stage : Stage) {premise consequent : BinString}
    (implication : StrictFeatureImplication C.algorithm premise consequent) :
    C.ImplicationAt stage premise consequent := by
  intro observation _ premiseAtObservation
  obtain ⟨certificate, realizesPremise⟩ := premiseAtObservation
  exact implication certificate (C.source observation) realizesPremise

/-! ## Existing construction-base semantics -/

/-- The typed observation system viewed through the existing construction-base
API.  Features are the abstract attributes of this FCA presentation; the
three observation channels jointly form its phenomenal carrier. -/
def toConstructionBase
    (C : ObservationSystem Stage Abstract Phenomenal Indexical) :
    ConstructionBase where
  Phenomena := ChannelObservation Abstract Phenomenal Indexical
  Abstract := BinString
  Indexicality := Stage
  incidence := fun observation feature =>
    StrictFeatureOf C.algorithm feature (C.source observation)
  visibleAt := C.observed

@[simp]
theorem toConstructionBase_visibleAt
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (stage : Stage) :
    C.toConstructionBase.visibleAt stage = C.observed stage :=
  rfl

@[simp]
theorem toConstructionBase_refines_iff
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (earlier later : Stage) :
    C.toConstructionBase.Refines earlier later ↔
      C.observed earlier ⊆ C.observed later :=
  Iff.rfl

/-- Singleton closure in the existing construction base is exactly typed
stage-local feature implication. -/
theorem mem_closureAt_singleton_iff_implicationAt
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (stage : Stage) (premise consequent : BinString) :
    consequent ∈ C.toConstructionBase.closureAt stage
        ({premise} : Set BinString) ↔
      C.ImplicationAt stage premise consequent := by
  change consequent ∈ sampledAttributeClosure (C.observed stage)
      (fun observation feature =>
        StrictFeatureOf C.algorithm feature (C.source observation))
      ({premise} : Set BinString) ↔ _
  rw [mem_sampledAttributeClosure_iff]
  constructor
  · intro closure observation observed premiseAtObservation
    exact closure observation observed (by
      intro feature member
      have featureEq : feature = premise := by simpa using member
      subst feature
      exact premiseAtObservation)
  · intro implication observation observed carriesPremise
    exact implication observation observed
      (carriesPremise premise (by simp))

/-- Full singleton closure is implication over the complete declared typed
observation carrier. -/
theorem mem_fullClosure_singleton_iff_implication
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (premise consequent : BinString) :
    consequent ∈ C.toConstructionBase.fullClosure
        ({premise} : Set BinString) ↔
      C.Implication premise consequent := by
  change consequent ∈ fullAttributeClosure
      (fun observation feature =>
        StrictFeatureOf C.algorithm feature (C.source observation))
      ({premise} : Set BinString) ↔ _
  rw [mem_fullAttributeClosure_iff]
  constructor
  · intro closure observation premiseAtObservation
    exact closure observation (by
      intro feature member
      have featureEq : feature = premise := by simpa using member
      subst feature
      exact premiseAtObservation)
  · intro implication observation carriesPremise
    exact implication observation (carriesPremise premise (by simp))

/-- A frontier member is exactly an implication supported at the current stage
and refuted somewhere in the declared observation carrier. -/
theorem mem_frontierAt_singleton_iff
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (stage : Stage) (premise consequent : BinString) :
    consequent ∈ C.toConstructionBase.frontierAt stage
        ({premise} : Set BinString) ↔
      C.ImplicationAt stage premise consequent ∧
        ¬ C.Implication premise consequent := by
  constructor
  · intro frontier
    exact ⟨
      (C.mem_closureAt_singleton_iff_implicationAt
        stage premise consequent).1 frontier.1,
      fun fullImplication => frontier.2
        ((C.mem_fullClosure_singleton_iff_implication
          premise consequent).2 fullImplication)⟩
  · rintro ⟨localImplication, notFullImplication⟩
    exact ⟨
      (C.mem_closureAt_singleton_iff_implicationAt
        stage premise consequent).2 localImplication,
      fun fullMember => notFullImplication
        ((C.mem_fullClosure_singleton_iff_implication
          premise consequent).1 fullMember)⟩

/-- Global strict implication is always valid over the declared observation
carrier. -/
theorem implication_of_strictFeatureImplication
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    {premise consequent : BinString}
    (implication : StrictFeatureImplication C.algorithm premise consequent) :
    C.Implication premise consequent := by
  intro observation premiseAtObservation
  obtain ⟨certificate, realizesPremise⟩ := premiseAtObservation
  exact implication certificate (C.source observation) realizesPremise

/-- Surjectivity of the source projection is the exact extra premise needed to
promote observation-carrier implication to global strict implication. -/
theorem strictFeatureImplication_of_implication_of_surjective
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    {premise consequent : BinString}
    (surjective : Function.Surjective C.source)
    (implication : C.Implication premise consequent) :
    StrictFeatureImplication C.algorithm premise consequent := by
  intro certificate source realizesPremise
  obtain ⟨observation, rfl⟩ := surjective source
  exact implication observation ⟨certificate, realizesPremise⟩

/-- With a surjective source projection, full typed-carrier implication and
global algorithmic implication coincide. -/
theorem implication_iff_strictFeatureImplication_of_surjective
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (surjective : Function.Surjective C.source)
    (premise consequent : BinString) :
    C.Implication premise consequent ↔
      StrictFeatureImplication C.algorithm premise consequent :=
  ⟨C.strictFeatureImplication_of_implication_of_surjective surjective,
    C.implication_of_strictFeatureImplication⟩

/-! ## Finite visible samples and PLN intensional evidence -/

/-- A finite indexed sample whose typed observations are visible at one exact
stage.  Repeated source values may retain distinct observation indices. -/
structure FiniteVisibleSample
    (C : ObservationSystem Stage Abstract Phenomenal Indexical)
    (stage : Stage) (SourceIndex : Type uSourceIndex)
    [Fintype SourceIndex] where
  observation : SourceIndex → ChannelObservation Abstract Phenomenal Indexical
  visible : ∀ index, observation index ∈ C.observed stage

namespace FiniteVisibleSample

variable {C : ObservationSystem Stage Abstract Phenomenal Indexical}
variable {stage : Stage} {SourceIndex : Type uSourceIndex}
variable [Fintype SourceIndex]

/-- Reuse the existing finite feature experiment for one typed visible sample. -/
def toFiniteFeatureExperiment
    (sample : FiniteVisibleSample C stage SourceIndex)
    {FeatureIndex : Type uFeatureIndex} [Fintype FeatureIndex]
    (feature : FeatureIndex → BinString) :
    FiniteFeatureExperiment SourceIndex FeatureIndex where
  algorithm := C.algorithm
  source := fun index => C.source (sample.observation index)
  feature := feature

@[simp]
theorem toFiniteFeatureExperiment_relation_iff
    (sample : FiniteVisibleSample C stage SourceIndex)
    {FeatureIndex : Type uFeatureIndex} [Fintype FeatureIndex]
    (feature : FeatureIndex → BinString)
    (index : SourceIndex) (featureIndex : FeatureIndex) :
    (sample.toFiniteFeatureExperiment feature).Relation index featureIndex ↔
      StrictFeatureOf C.algorithm (feature featureIndex)
        (C.source (sample.observation index)) :=
  Iff.rfl

/-- A typed stage-local implication restricts to every finite visible sample. -/
theorem implication_of_implicationAt
    (sample : FiniteVisibleSample C stage SourceIndex)
    {FeatureIndex : Type uFeatureIndex} [Fintype FeatureIndex]
    (feature : FeatureIndex → BinString)
    {premise consequent : FeatureIndex}
    (implication : C.ImplicationAt stage
      (feature premise) (feature consequent)) :
    (sample.toFiniteFeatureExperiment feature).Implication
      premise consequent := by
  intro index premiseAtIndex
  exact implication (sample.observation index) (sample.visible index)
    premiseAtIndex

/-- The existing dual-concept interpretation turns sampled typed implication
into full extensional and intensional inheritance. -/
theorem inherits_of_implicationAt
    (sample : FiniteVisibleSample C stage SourceIndex)
    {FeatureIndex : Type uFeatureIndex} [Fintype FeatureIndex]
    (feature : FeatureIndex → BinString)
    {premise consequent : FeatureIndex}
    (implication : C.ImplicationAt stage
      (feature premise) (feature consequent)) :
    (sample.toFiniteFeatureExperiment feature).interpretation.Inherits
      premise consequent :=
  ((sample.toFiniteFeatureExperiment feature).inherits_iff_implication
    premise consequent).2
      (sample.implication_of_implicationAt feature implication)

/-- Nonvacuous typed stage-local implication yields perfect finite PLN
inheritance strength while confidence remains below one. -/
theorem inheritanceTV_perfect_but_finite_of_implicationAt
    (sample : FiniteVisibleSample C stage SourceIndex)
    {FeatureIndex : Type uFeatureIndex} [Fintype FeatureIndex]
    (feature : FeatureIndex → BinString)
    {premise consequent : FeatureIndex}
    (witness : ∃ index,
      (sample.toFiniteFeatureExperiment feature).Relation index premise)
    (implication : C.ImplicationAt stage
      (feature premise) (feature consequent)) :
    (inheritanceTV (sample.toFiniteFeatureExperiment feature).interpretation
        premise consequent).strength = 1 ∧
      (inheritanceTV (sample.toFiniteFeatureExperiment feature).interpretation
        premise consequent).confidence < 1 :=
  (sample.toFiniteFeatureExperiment feature)
    |>.inheritanceTV_perfect_but_finite_of_implication witness
      (sample.implication_of_implicationAt feature implication)

end FiniteVisibleSample

end ObservationSystem

/-! ## Same mathematical carrier, distinct roles -/

abbrev MathematicalDatum := Bool

def abstractMarked :
    ChannelObservation MathematicalDatum MathematicalDatum MathematicalDatum :=
  ⟨true, false, false⟩

def phenomenalMarked :
    ChannelObservation MathematicalDatum MathematicalDatum MathematicalDatum :=
  ⟨false, true, false⟩

def indexicalMarked :
    ChannelObservation MathematicalDatum MathematicalDatum MathematicalDatum :=
  ⟨false, false, true⟩

/-- One mathematical carrier can inhabit all three channels without erasing
their proof-relevant roles. -/
theorem same_mathematical_carrier_does_not_identify_roles :
    abstractMarked ≠ phenomenalMarked ∧
      phenomenalMarked ≠ indexicalMarked ∧
      abstractMarked ≠ indexicalMarked := by
  decide

/-! ## Open-world revision canary -/

def indexedObservation (indexical : Bool) :
    ChannelObservation MathematicalDatum MathematicalDatum MathematicalDatum :=
  ⟨false, false, indexical⟩

def mathematicalSource
    (observation :
      ChannelObservation MathematicalDatum MathematicalDatum MathematicalDatum) :
    BinString :=
  if observation.indexical then fourFalse else fourTrue

@[simp]
theorem mathematicalSource_false :
    mathematicalSource (indexedObservation false) = fourTrue :=
  rfl

@[simp]
theorem mathematicalSource_true :
    mathematicalSource (indexedObservation true) = fourFalse :=
  rfl

def canaryObserved (stage : Bool) :
    Set (ChannelObservation MathematicalDatum MathematicalDatum MathematicalDatum) :=
  if stage then {indexedObservation false, indexedObservation true}
  else {indexedObservation false}

/-- A two-stage typed observation system.  The later stage adds one
indexically distinct observation whose projected source is a counterexample. -/
def mathematicalCanary :
    ObservationSystem Bool MathematicalDatum MathematicalDatum MathematicalDatum where
  algorithm := conceptCanaryAlgorithm
  source := mathematicalSource
  observed := canaryObserved
  observed_mono := by
    intro earlier later growth observation observed
    cases earlier <;> cases later
    · simpa [canaryObserved] using observed
    · have observationEq : observation = indexedObservation false := by
        simpa [canaryObserved] using observed
      exact Or.inl observationEq
    · exact Bool.noConfusion (Bool.le_iff_imp.mp growth rfl)
    · simpa [canaryObserved] using observed

theorem mathematicalCanary_strict_growth :
    mathematicalCanary.observed false ⊆ mathematicalCanary.observed true ∧
      indexedObservation true ∉ mathematicalCanary.observed false ∧
      indexedObservation true ∈ mathematicalCanary.observed true := by
  have distinct : indexedObservation true ≠ indexedObservation false := by
    decide
  simp [mathematicalCanary, canaryObserved, distinct]

/-- At the early stage the single observed source exhibits both features. -/
theorem mathematicalCanary_early_true_implies_false :
    mathematicalCanary.ImplicationAt false [true] [false] := by
  intro observation observed _premiseAtObservation
  have observationEq : observation = indexedObservation false := by
    simpa [mathematicalCanary, canaryObserved] using observed
  subst observation
  change StrictFeatureOf conceptCanaryAlgorithm [false] fourTrue
  exact conceptCanary_false_featureOf_fourTrue

/-- The added indexically distinct source refutes that provisional
implication. -/
theorem mathematicalCanary_later_not_true_implies_false :
    ¬ mathematicalCanary.ImplicationAt true [true] [false] := by
  intro implication
  have premiseAtCounterexample :
      StrictFeatureOf mathematicalCanary.algorithm [true]
        (mathematicalCanary.source (indexedObservation true)) := by
    change StrictFeatureOf conceptCanaryAlgorithm [true] fourFalse
    exact conceptCanary_true_featureOf_fourFalse
  have consequentAtCounterexample := implication (indexedObservation true)
    (by simp [mathematicalCanary, canaryObserved]) premiseAtCounterexample
  exact conceptCanary_false_not_featureOf_fourFalse (by
    change StrictFeatureOf conceptCanaryAlgorithm [false] fourFalse at consequentAtCounterexample
    exact consequentAtCounterexample)

/-- The strict-growth canary as a forward Ind(GSLT) arrow. -/
def mathematicalCanaryGrowthTranslation :
    OperationalTranslation
      (mathematicalCanary.implicationGSLTAt true)
      (mathematicalCanary.implicationGSLTAt false) :=
  mathematicalCanary.implicationGrowthTranslation (by decide)

/-- Positive operational control: every later-supported implication is
preserved by the forward diagram arrow. -/
theorem mathematicalCanary_growthTranslation_preserves_steps
    {premise consequent : BinString}
    (step : (mathematicalCanary.implicationGSLTAt true).Step
      premise consequent) :
    (mathematicalCanary.implicationGSLTAt false).Step
      (mathematicalCanaryGrowthTranslation.mapTerm premise)
      (mathematicalCanaryGrowthTranslation.mapTerm consequent) :=
  mathematicalCanaryGrowthTranslation.mapStep step

/-- Negative operational control: the growth arrow is not covered because
the provisional early implication has no later lift. -/
theorem mathematicalCanary_growthTranslation_not_covered :
    ¬ Nonempty (StepCover
      (mathematicalCanary.implicationGSLTAt true)
      (mathematicalCanary.implicationGSLTAt false)
      mathematicalCanaryGrowthTranslation.mapTerm) := by
  rintro ⟨cover⟩
  have earlyStep :
      (mathematicalCanary.implicationGSLTAt false).Step [true] [false] :=
    mathematicalCanary_early_true_implies_false
  obtain ⟨target, laterStep, targetEq⟩ := cover.liftStep earlyStep
  have targetEq' : target = [false] := by
    simpa [mathematicalCanaryGrowthTranslation] using targetEq
  subst target
  exact mathematicalCanary_later_not_true_implies_false laterStep

/-- Forward observation growth therefore obeys only the one-sided diamond
law in general. -/
theorem mathematicalCanary_growthTranslation_diamond_lax
    (predicate : Set BinString) :
    gsltDiamond
        (mathematicalCanary.implicationGSLTAt true)
        (Set.preimage mathematicalCanaryGrowthTranslation.mapTerm predicate) ≤
      Set.preimage mathematicalCanaryGrowthTranslation.mapTerm
        (gsltDiamond
          (mathematicalCanary.implicationGSLTAt false) predicate) :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.OperationalTranslation.preimage_diamond_le
    mathematicalCanaryGrowthTranslation predicate

/-- The provisional implication is a genuine early frontier member and is
discharged by observation growth. -/
theorem mathematicalCanary_frontier_retracted :
    [false] ∈ mathematicalCanary.toConstructionBase.frontierAt false
        ({[true]} : Set BinString) ∧
      [false] ∉ mathematicalCanary.toConstructionBase.frontierAt true
        ({[true]} : Set BinString) := by
  constructor
  · apply (mathematicalCanary.mem_frontierAt_singleton_iff
      false [true] [false]).2
    refine ⟨mathematicalCanary_early_true_implies_false, ?_⟩
    intro fullImplication
    have premiseAtCounterexample :
        StrictFeatureOf mathematicalCanary.algorithm [true]
          (mathematicalCanary.source (indexedObservation true)) := by
      change StrictFeatureOf conceptCanaryAlgorithm [true] fourFalse
      exact conceptCanary_true_featureOf_fourFalse
    exact conceptCanary_false_not_featureOf_fourFalse (by
      have consequentAtCounterexample :=
        fullImplication (indexedObservation true) premiseAtCounterexample
      change StrictFeatureOf conceptCanaryAlgorithm [false] fourFalse at consequentAtCounterexample
      exact consequentAtCounterexample)
  · intro frontier
    exact mathematicalCanary_later_not_true_implies_false
      ((mathematicalCanary.mem_frontierAt_singleton_iff
        true [true] [false]).1 frontier).1

/-- The early typed sample feeds the existing PLN interpretation. -/
def earlyVisibleSample :
    ObservationSystem.FiniteVisibleSample mathematicalCanary false Unit where
  observation := fun _ => indexedObservation false
  visible := by
    intro _
    change indexedObservation false ∈ {indexedObservation false}
    simp

def canaryFeature : Bool → BinString
  | false => [true]
  | true => [false]

/-- Perfect finite intensional evidence can coexist with a later observed
counterexample.  Strength one remains sample-relative and confidence remains
strictly below one. -/
theorem perfect_early_PLN_evidence_does_not_prevent_later_revision :
    (inheritanceTV
        (earlyVisibleSample.toFiniteFeatureExperiment canaryFeature).interpretation
        false true).strength = 1 ∧
      (inheritanceTV
        (earlyVisibleSample.toFiniteFeatureExperiment canaryFeature).interpretation
        false true).confidence < 1 ∧
      ¬ mathematicalCanary.ImplicationAt true [true] [false] := by
  have evidence :=
    earlyVisibleSample.inheritanceTV_perfect_but_finite_of_implicationAt
      (premise := false) (consequent := true) canaryFeature
      ⟨(), by
        change StrictFeatureOf conceptCanaryAlgorithm [true] fourTrue
        exact conceptCanary_true_featureOf_fourTrue⟩
      mathematicalCanary_early_true_implies_false
  exact ⟨evidence.1, evidence.2,
    mathematicalCanary_later_not_true_implies_false⟩

/-! ## Relative carrier completeness is not global totality -/

def uniqueObservation : ChannelObservation Unit Unit Unit := ⟨(), (), ()⟩

def singleSourceSystem : ObservationSystem Unit Unit Unit Unit where
  algorithm := conceptCanaryAlgorithm
  source := fun _ => fourTrue
  observed := fun _ => Set.univ
  observed_mono := monotone_const

/-- Full closure over a non-surjective one-observation carrier can validate a
globally false implication. -/
theorem nonSurjective_fullClosure_does_not_imply_global_totality :
    [false] ∈ singleSourceSystem.toConstructionBase.fullClosure
        ({[true]} : Set BinString) ∧
      ¬ StrictFeatureImplication singleSourceSystem.algorithm
        [true] [false] := by
  constructor
  · apply (singleSourceSystem.mem_fullClosure_singleton_iff_implication
      [true] [false]).2
    intro observation _premiseAtObservation
    have observationEq : observation = uniqueObservation := by
      rcases observation with ⟨abstract, phenomenal, indexical⟩
      cases abstract
      cases phenomenal
      cases indexical
      rfl
    subst observation
    change StrictFeatureOf conceptCanaryAlgorithm [false] fourTrue
    exact conceptCanary_false_featureOf_fourTrue
  · simpa [singleSourceSystem] using conceptCanary_true_not_implies_false

section AxiomAudit

#print axioms ObservationSystem.implicationAt_iff_stagewise
#print axioms ObservationSystem.implicationGrowthTranslation
#print axioms ObservationSystem.implicationDiagram
#print axioms ObservationSystem.implicationIndexedOSLF
#print axioms ObservationSystem.mem_closureAt_singleton_iff_implicationAt
#print axioms ObservationSystem.mem_frontierAt_singleton_iff
#print axioms ObservationSystem.implication_iff_strictFeatureImplication_of_surjective
#print axioms ObservationSystem.FiniteVisibleSample.inherits_of_implicationAt
#print axioms ObservationSystem.FiniteVisibleSample.inheritanceTV_perfect_but_finite_of_implicationAt
#print axioms same_mathematical_carrier_does_not_identify_roles
#print axioms mathematicalCanary_strict_growth
#print axioms mathematicalCanary_growthTranslation_preserves_steps
#print axioms mathematicalCanary_growthTranslation_not_covered
#print axioms mathematicalCanary_growthTranslation_diamond_lax
#print axioms mathematicalCanary_frontier_retracted
#print axioms perfect_early_PLN_evidence_does_not_prevent_later_revision
#print axioms nonSurjective_fullClosure_does_not_imply_global_totality

end AxiomAudit

end OpenWorldObservationChannels
end Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI
