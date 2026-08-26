import Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceBridge
import Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.OpenEndedAlgorithmicConceptFormationBridge

/-!
# Growing finite evidence for algorithmic feature concepts

This module connects finite indexed PLN evidence to the existing open-ended
algorithmic concept semantics.  A set of observed source indices maps to the
corresponding set of binary source values.  Stage-local incidence and
implication then agree with the open-ended source-set context after this
reindexing.

The transport laws are deliberately asymmetric:

* checked incidence persists when the observed index set grows;
* an implication valid at a later stage restricts to every earlier stage;
* a global strict implication remains valid at every finite stage; and
* adding a checked counterexample can retract sampled strength `1`.

The final control makes the last point nonvacuous: the premise occurs at both
stages, the early stage has perfect finite strength, and the later stage adds
one source that refutes the provisional implication.
-/

namespace Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence

open KolmogorovComplexity
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.OpenEndedAlgorithmicConceptFormation
open Mettapedia.Logic.WorldModel.Algorithmic
open Mettapedia.Logic.WorldModel.AlgorithmicConceptFormationExamples

universe u v

namespace FiniteFeatureExperiment

variable {SourceIndex : Type u} {FeatureIndex : Type v}
variable [Fintype SourceIndex] [Fintype FeatureIndex]

/-- Checked incidence restricted to the source indices observed at one stage. -/
def RelationAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex)
    (source : SourceIndex) (feature : FeatureIndex) : Prop :=
  source ∈ observed ∧ E.Relation source feature

/-- Feature implication relative to one finite observation stage. -/
def ImplicationAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex)
    (premise consequent : FeatureIndex) : Prop :=
  ∀ source, E.RelationAt observed source premise →
    E.RelationAt observed source consequent

theorem implicationAt_refl
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (feature : FeatureIndex) :
    E.ImplicationAt observed feature feature :=
  fun _ witness => witness

theorem implicationAt_trans
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) {first second third : FeatureIndex}
    (h₁ : E.ImplicationAt observed first second)
    (h₂ : E.ImplicationAt observed second third) :
    E.ImplicationAt observed first third :=
  fun source witness => h₂ source (h₁ source witness)

/-- The stage-relative sampled concept. -/
def conceptAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (feature : FeatureIndex) :
    DualConcept SourceIndex FeatureIndex where
  extent := {source | E.RelationAt observed source feature}
  intent := {consequent | E.ImplicationAt observed feature consequent}

/-- Interpretation of feature indices at one observation stage. -/
def interpretationAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) :
    Interpretation FeatureIndex SourceIndex FeatureIndex where
  meaning := E.conceptAt observed

/-- Binary source values represented by an observed set of indices. -/
def observedSources
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) : Set BinString :=
  E.source '' observed

/-- Finite indexed incidence maps into the existing open-ended source-set
incidence.  Reflection to the same index is intentionally not claimed because
the source map need not be injective. -/
theorem relationAt_to_sourceSet_relation
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (source : SourceIndex) (feature : FeatureIndex) :
    E.RelationAt observed source feature →
      (sourceSetFeatureContext E.algorithm).relation
        (E.observedSources observed) (E.source source) (E.feature feature) := by
  rintro ⟨observedSource, featureOfSource⟩
  exact ⟨⟨source, observedSource, rfl⟩, featureOfSource⟩

/-- Open-ended incidence at a represented binary source is equivalent to the
existence of an observed index carrying that incidence. -/
theorem sourceSet_relation_iff_exists_relationAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (source : BinString) (feature : FeatureIndex) :
    (sourceSetFeatureContext E.algorithm).relation
        (E.observedSources observed) source (E.feature feature) ↔
      ∃ index, E.source index = source ∧ E.RelationAt observed index feature := by
  constructor
  · rintro ⟨⟨index, indexObserved, sourceEq⟩, featureOfSource⟩
    exact ⟨index, sourceEq, indexObserved, by
      simpa [FiniteFeatureExperiment.Relation, sourceSetFeatureContext, sourceEq]
        using featureOfSource⟩
  · rintro ⟨index, sourceEq, indexedRelation⟩
    subst source
    exact E.relationAt_to_sourceSet_relation observed index feature indexedRelation

/-- Stage-local implication agrees with the open-ended source-set semantics
after reindexing sources and feature programs. -/
theorem implicationAt_iff_sourceSet_implicationAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (premise consequent : FeatureIndex) :
    E.ImplicationAt observed premise consequent ↔
      (sourceSetFeatureContext E.algorithm).ImplicationAt
        (E.observedSources observed) (E.feature premise) (E.feature consequent) := by
  constructor
  · intro implication source sourcePremise
    obtain ⟨representative, representativeObserved, sourceEq⟩ := sourcePremise.1
    have indexedPremise : E.RelationAt observed representative premise := by
      exact ⟨representativeObserved, by
        simpa [Relation, sourceSetFeatureContext, sourceEq] using sourcePremise.2⟩
    have indexedConsequent := implication representative indexedPremise
    exact ⟨⟨representative, representativeObserved, sourceEq⟩, by
      simpa [Relation, sourceSetFeatureContext, sourceEq] using indexedConsequent.2⟩
  · intro implication source indexedPremise
    have sourcePremise :
        (sourceSetFeatureContext E.algorithm).relation
          (E.observedSources observed) (E.source source) (E.feature premise) :=
      E.relationAt_to_sourceSet_relation observed source premise indexedPremise
    have sourceConsequent := implication sourcePremise
    exact ⟨indexedPremise.1, sourceConsequent.2⟩

/-- Incidence persists along observation growth. -/
theorem relationAt_mono
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {earlier later : Set SourceIndex} (growth : earlier ⊆ later)
    {source : SourceIndex} {feature : FeatureIndex}
    (h : E.RelationAt earlier source feature) :
    E.RelationAt later source feature :=
  ⟨growth h.1, h.2⟩

/-- Later implication restricts contravariantly to every earlier observation
stage. -/
theorem implicationAt_anti
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {earlier later : Set SourceIndex} (growth : earlier ⊆ later)
    {premise consequent : FeatureIndex}
    (h : E.ImplicationAt later premise consequent) :
    E.ImplicationAt earlier premise consequent := by
  intro source premiseAtEarlier
  have consequenceAtLater := h source (E.relationAt_mono growth premiseAtEarlier)
  exact ⟨premiseAtEarlier.1, consequenceAtLater.2⟩

theorem conceptAt_extent_mono
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {earlier later : Set SourceIndex} (growth : earlier ⊆ later)
    (feature : FeatureIndex) :
    (E.conceptAt earlier feature).extent ⊆
      (E.conceptAt later feature).extent :=
  fun _ witness => E.relationAt_mono growth witness

theorem conceptAt_intent_anti
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {earlier later : Set SourceIndex} (growth : earlier ⊆ later)
    (feature : FeatureIndex) :
    (E.conceptAt later feature).intent ⊆
      (E.conceptAt earlier feature).intent :=
  fun _ implication => E.implicationAt_anti growth implication

theorem inheritsAt_iff_implicationAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (premise consequent : FeatureIndex) :
    (E.interpretationAt observed).Inherits premise consequent ↔
      E.ImplicationAt observed premise consequent := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    intro later hLater
    exact E.implicationAt_trans observed h hLater

/-- A global strict implication is valid at every finite observation stage. -/
theorem implicationAt_of_global
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) {premise consequent : FeatureIndex}
    (h : StrictFeatureImplication E.algorithm
      (E.feature premise) (E.feature consequent)) :
    E.ImplicationAt observed premise consequent := by
  intro source premiseAtStage
  obtain ⟨certificate, realizesPremise⟩ := premiseAtStage.2
  exact ⟨premiseAtStage.1,
    h certificate (E.source source) realizesPremise⟩

/-- A nonvacuous stage-local implication has full inheritance strength one. -/
theorem fullInheritanceStrengthAt_eq_one_of_implicationAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) {premise consequent : FeatureIndex}
    (witness : ∃ source, E.RelationAt observed source premise)
    (h : E.ImplicationAt observed premise consequent) :
    fullInheritanceStrength (E.interpretationAt observed) premise consequent = 1 := by
  obtain ⟨source, sourceWitness⟩ := witness
  have hExtent :
      ((E.interpretationAt observed).meaning premise).extent.ncard ≠ 0 :=
    Set.ncard_ne_zero_of_mem sourceWitness
  have hIntent :
      ((E.interpretationAt observed).meaning consequent).intent.ncard ≠ 0 :=
    Set.ncard_ne_zero_of_mem (E.implicationAt_refl observed consequent)
  exact (fullInheritanceStrength_eq_one_iff
    (E.interpretationAt observed) premise consequent hExtent hIntent).2
      ((E.inheritsAt_iff_implicationAt observed premise consequent).2 h)

/-- With a witnessed premise, failure of stage-local implication prevents
strength one. -/
theorem fullInheritanceStrengthAt_ne_one_of_not_implicationAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) {premise consequent : FeatureIndex}
    (witness : ∃ source, E.RelationAt observed source premise)
    (h : ¬ E.ImplicationAt observed premise consequent) :
    fullInheritanceStrength (E.interpretationAt observed) premise consequent ≠ 1 := by
  obtain ⟨source, sourceWitness⟩ := witness
  have hExtent :
      ((E.interpretationAt observed).meaning premise).extent.ncard ≠ 0 :=
    Set.ncard_ne_zero_of_mem sourceWitness
  have hIntent :
      ((E.interpretationAt observed).meaning consequent).intent.ncard ≠ 0 :=
    Set.ncard_ne_zero_of_mem (E.implicationAt_refl observed consequent)
  intro strengthOne
  exact h ((E.inheritsAt_iff_implicationAt observed premise consequent).1
    ((fullInheritanceStrength_eq_one_iff
      (E.interpretationAt observed) premise consequent hExtent hIntent).1 strengthOne))

end FiniteFeatureExperiment

end Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence

namespace Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceGrowth

open KolmogorovComplexity
open Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence
open Mettapedia.Logic.WorldModel.AlgorithmicConceptFormationExamples

/-! ## Quantitative strict-growth control -/

/-- A two-source experiment: the early source exhibits both features, while
the later source exhibits only the more general feature. -/
def growthCanaryExperiment : FiniteFeatureExperiment Bool Bool where
  algorithm := conceptCanaryAlgorithm
  source
    | false => fourTrue
    | true => fourFalse
  feature
    | false => [true]
    | true => [false]

def earlyObserved : Set Bool := {false}

def laterObserved : Set Bool := Set.univ

theorem earlyObserved_subset_laterObserved : earlyObserved ⊆ laterObserved := by
  intro source _
  simp [laterObserved]

@[simp]
theorem growthCanary_relation_false_false :
    growthCanaryExperiment.Relation false false :=
  conceptCanary_true_featureOf_fourTrue

@[simp]
theorem growthCanary_relation_false_true :
    growthCanaryExperiment.Relation false true :=
  conceptCanary_false_featureOf_fourTrue

@[simp]
theorem growthCanary_relation_true_false :
    growthCanaryExperiment.Relation true false :=
  conceptCanary_true_featureOf_fourFalse

theorem growthCanary_not_relation_true_true :
    ¬ growthCanaryExperiment.Relation true true :=
  conceptCanary_false_not_featureOf_fourFalse

/-- Before the hidden source is observed, the invalid global direction has a
nonvacuous perfect sampled implication. -/
theorem growthCanary_early_false_implies_true :
    growthCanaryExperiment.ImplicationAt earlyObserved false true := by
  intro source premiseAtStage
  have sourceEq : source = false := by
    simpa [earlyObserved] using premiseAtStage.1
  subst source
  exact ⟨by simp [earlyObserved], growthCanary_relation_false_true⟩

/-- Adding the second checked source refutes that provisional implication. -/
theorem growthCanary_later_not_false_implies_true :
    ¬ growthCanaryExperiment.ImplicationAt laterObserved false true := by
  intro implication
  have premiseAtLater :
      growthCanaryExperiment.RelationAt laterObserved true false :=
    ⟨by simp [laterObserved], growthCanary_relation_true_false⟩
  exact growthCanary_not_relation_true_true (implication true premiseAtLater).2

/-- The premise remains witnessed at both stages. -/
theorem growthCanary_premise_witness_early :
    ∃ source, growthCanaryExperiment.RelationAt earlyObserved source false :=
  ⟨false, by simp [FiniteFeatureExperiment.RelationAt, earlyObserved]⟩

theorem growthCanary_premise_witness_later :
    ∃ source, growthCanaryExperiment.RelationAt laterObserved source false :=
  ⟨false, by simp [FiniteFeatureExperiment.RelationAt, laterObserved]⟩

/-- Quantitative open-world boundary: source growth preserves the premise
witness but retracts full inheritance strength one. -/
theorem growthCanary_retracts_perfect_strength :
    earlyObserved ⊆ laterObserved ∧
      fullInheritanceStrength
        (growthCanaryExperiment.interpretationAt earlyObserved) false true = 1 ∧
      fullInheritanceStrength
        (growthCanaryExperiment.interpretationAt laterObserved) false true ≠ 1 := by
  exact ⟨earlyObserved_subset_laterObserved,
    growthCanaryExperiment.fullInheritanceStrengthAt_eq_one_of_implicationAt
      earlyObserved growthCanary_premise_witness_early
      growthCanary_early_false_implies_true,
    growthCanaryExperiment.fullInheritanceStrengthAt_ne_one_of_not_implicationAt
      laterObserved growthCanary_premise_witness_later
      growthCanary_later_not_false_implies_true⟩

/-- Confidence remains finite at both stages; a larger evidence state still
does not become semantic certainty. -/
theorem growthCanary_confidence_remains_finite :
    (inheritanceTV
      (growthCanaryExperiment.interpretationAt earlyObserved) false true).confidence < 1 ∧
    (inheritanceTV
      (growthCanaryExperiment.interpretationAt laterObserved) false true).confidence < 1 :=
  ⟨inheritanceTV_confidence_lt_one _ _ _,
    inheritanceTV_confidence_lt_one _ _ _⟩

section AxiomAudit

#print axioms FiniteFeatureExperiment.relationAt_to_sourceSet_relation
#print axioms FiniteFeatureExperiment.sourceSet_relation_iff_exists_relationAt
#print axioms FiniteFeatureExperiment.implicationAt_iff_sourceSet_implicationAt
#print axioms FiniteFeatureExperiment.relationAt_mono
#print axioms FiniteFeatureExperiment.implicationAt_anti
#print axioms FiniteFeatureExperiment.implicationAt_of_global
#print axioms FiniteFeatureExperiment.fullInheritanceStrengthAt_eq_one_of_implicationAt
#print axioms FiniteFeatureExperiment.fullInheritanceStrengthAt_ne_one_of_not_implicationAt
#print axioms growthCanary_retracts_perfect_strength
#print axioms growthCanary_confidence_remains_finite

end AxiomAudit

end Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceGrowth
