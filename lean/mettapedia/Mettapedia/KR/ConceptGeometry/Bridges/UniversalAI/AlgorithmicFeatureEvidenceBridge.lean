import Mettapedia.KR.ConceptGeometry.Bridges.PLN.InheritanceIntegration
import Mettapedia.Logic.WorldModel.AlgorithmicConceptFormation

/-!
# Finite evidence for algorithmic feature inheritance

Strict algorithmic feature implication is a global semantic relation over all
binary sources.  A finite experiment can only observe a finite indexed family
of sources and features.  This module keeps those levels distinct:

* a finite experiment induces an ordinary dual-concept interpretation;
* global strict feature implication restricts to inheritance in every finite
  experiment;
* witnessed finite inheritance has PLN strength `1`, while its confidence
  remains strictly below `1`; and
* perfect witnessed sample strength does not imply global strict feature
  implication, as shown by a hidden-counterexample control.

Source indices are separate from source values, so repeated observations may
be represented by distinct indices without changing the algorithmic objects.
No compression score is identified with truth: PLN evidence is computed only
after strict feature witnesses have been checked.
-/

namespace Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence

open KolmogorovComplexity
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence
open Mettapedia.Logic.WorldModel.Algorithmic
open Mettapedia.Logic.WorldModel.AlgorithmicConceptFormationExamples

universe u v

/-- A finite indexed observation table for one conditional algorithm. -/
structure FiniteFeatureExperiment
    (SourceIndex : Type u) (FeatureIndex : Type v)
    [Fintype SourceIndex] [Fintype FeatureIndex] where
  algorithm : ConditionalAlgorithm
  source : SourceIndex → BinString
  feature : FeatureIndex → BinString

namespace FiniteFeatureExperiment

variable {SourceIndex : Type u} {FeatureIndex : Type v}
variable [Fintype SourceIndex] [Fintype FeatureIndex]

/-- Checked incidence in a finite experiment. -/
def Relation
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (source : SourceIndex) (feature : FeatureIndex) : Prop :=
  StrictFeatureOf E.algorithm (E.feature feature) (E.source source)

/-- Sample-restricted feature implication. -/
def Implication
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (premise consequent : FeatureIndex) : Prop :=
  ∀ source, E.Relation source premise → E.Relation source consequent

theorem implication_refl
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex) (feature : FeatureIndex) :
    E.Implication feature feature :=
  fun _ witness => witness

theorem implication_trans
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {first second third : FeatureIndex}
    (h₁ : E.Implication first second) (h₂ : E.Implication second third) :
    E.Implication first third :=
  fun source witness => h₂ source (h₁ source witness)

/-- The sampled concept of a feature: observed extent and sampled consequence
theory. -/
def concept
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (feature : FeatureIndex) : DualConcept SourceIndex FeatureIndex where
  extent := {source | E.Relation source feature}
  intent := {consequent | E.Implication feature consequent}

/-- Interpretation of finite feature indices by their sampled concepts. -/
def interpretation
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex) :
    Interpretation FeatureIndex SourceIndex FeatureIndex where
  meaning := E.concept

theorem extensionalInherits_iff_implication
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (premise consequent : FeatureIndex) :
    (E.interpretation).ExtensionalInherits premise consequent ↔
      E.Implication premise consequent :=
  Iff.rfl

theorem intensionalInherits_of_implication
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {premise consequent : FeatureIndex}
    (h : E.Implication premise consequent) :
    (E.interpretation).IntensionalInherits premise consequent := by
  intro later hLater
  exact E.implication_trans h hLater

/-- Full sampled inheritance is exactly sample-restricted implication. -/
theorem inherits_iff_implication
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (premise consequent : FeatureIndex) :
    (E.interpretation).Inherits premise consequent ↔
      E.Implication premise consequent := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, E.intensionalInherits_of_implication h⟩

/-- A global strict implication remains valid after restriction to any finite
experiment using the same conditional algorithm. -/
theorem implication_of_global
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {premise consequent : FeatureIndex}
    (h : StrictFeatureImplication E.algorithm
      (E.feature premise) (E.feature consequent)) :
    E.Implication premise consequent := by
  intro source featureOfSource
  obtain ⟨certificate, realizesPremise⟩ := featureOfSource
  exact h certificate (E.source source) realizesPremise

/-- Nonempty sampled inheritance yields perfect full inheritance strength.
This is a statement about the finite experiment, not a promotion to global
algorithmic implication. -/
theorem fullInheritanceStrength_eq_one_of_implication
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {premise consequent : FeatureIndex}
    (witness : ∃ source, E.Relation source premise)
    (h : E.Implication premise consequent) :
    fullInheritanceStrength E.interpretation premise consequent = 1 := by
  obtain ⟨source, sourceWitness⟩ := witness
  have hExtent : (E.interpretation.meaning premise).extent.ncard ≠ 0 :=
    Set.ncard_ne_zero_of_mem sourceWitness
  have hIntent : (E.interpretation.meaning consequent).intent.ncard ≠ 0 :=
    Set.ncard_ne_zero_of_mem (E.implication_refl consequent)
  exact (fullInheritanceStrength_eq_one_iff
    E.interpretation premise consequent hExtent hIntent).2
      ((E.inherits_iff_implication premise consequent).2 h)

/-- The corresponding PLN truth value has strength one but finite confidence. -/
theorem inheritanceTV_perfect_but_finite_of_implication
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {premise consequent : FeatureIndex}
    (witness : ∃ source, E.Relation source premise)
    (h : E.Implication premise consequent) :
    (inheritanceTV E.interpretation premise consequent).strength = 1 ∧
      (inheritanceTV E.interpretation premise consequent).confidence < 1 := by
  refine ⟨?_, inheritanceTV_confidence_lt_one E.interpretation premise consequent⟩
  exact E.fullInheritanceStrength_eq_one_of_implication witness h

/-- Global strict implication therefore produces perfect finite strength at
every nonvacuous experiment, without producing certainty. -/
theorem inheritanceTV_of_global
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {premise consequent : FeatureIndex}
    (witness : ∃ source, E.Relation source premise)
    (h : StrictFeatureImplication E.algorithm
      (E.feature premise) (E.feature consequent)) :
    (inheritanceTV E.interpretation premise consequent).strength = 1 ∧
      (inheritanceTV E.interpretation premise consequent).confidence < 1 :=
  E.inheritanceTV_perfect_but_finite_of_implication witness
    (E.implication_of_global h)

end FiniteFeatureExperiment

/-! ## A witnessed hidden-counterexample control -/

/-- One observed source and two indexed features.  Both features occur in the
sample, although only the second-to-first direction is globally valid. -/
def canaryExperiment : FiniteFeatureExperiment Unit Bool where
  algorithm := conceptCanaryAlgorithm
  source := fun _ => fourTrue
  feature
    | false => [true]
    | true => [false]

@[simp]
theorem canary_relation_false : canaryExperiment.Relation () false :=
  conceptCanary_true_featureOf_fourTrue

@[simp]
theorem canary_relation_true : canaryExperiment.Relation () true :=
  conceptCanary_false_featureOf_fourTrue

/-- The finite sample supports the globally invalid direction nonvacuously. -/
theorem canary_sample_false_implies_true :
    canaryExperiment.Implication false true := by
  intro source _
  cases source
  exact canary_relation_true

/-- Positive sampled direction corresponding to the genuine global implication. -/
theorem canary_sample_true_implies_false :
    canaryExperiment.Implication true false := by
  intro source _
  cases source
  exact canary_relation_false

/-- Positive control: the second-to-first sampled direction is backed by a
global strict feature implication. -/
theorem canary_global_true_implies_false :
    StrictFeatureImplication canaryExperiment.algorithm
      (canaryExperiment.feature true) (canaryExperiment.feature false) := by
  simpa [canaryExperiment] using conceptCanary_false_implies_true

/-- Hidden-counterexample control: the converse perfect sampled implication
does not hold globally. -/
theorem canary_not_global_false_implies_true :
    ¬ StrictFeatureImplication canaryExperiment.algorithm
      (canaryExperiment.feature false) (canaryExperiment.feature true) := by
  simpa [canaryExperiment] using conceptCanary_true_not_implies_false

/-- The positive global implication yields perfect sampled strength with
finite confidence. -/
theorem canary_global_direction_evidence :
    (inheritanceTV canaryExperiment.interpretation true false).strength = 1 ∧
      (inheritanceTV canaryExperiment.interpretation true false).confidence < 1 :=
  canaryExperiment.inheritanceTV_of_global
    ⟨(), canary_relation_true⟩ canary_global_true_implies_false

/-- Perfect witnessed finite evidence does not promote to global algorithmic
containment.  The missing source `fourFalse` is the counterexample. -/
theorem canary_perfect_sample_does_not_imply_global :
    ((inheritanceTV canaryExperiment.interpretation false true).strength = 1 ∧
      (inheritanceTV canaryExperiment.interpretation false true).confidence < 1) ∧
    ¬ StrictFeatureImplication canaryExperiment.algorithm
      (canaryExperiment.feature false) (canaryExperiment.feature true) := by
  exact ⟨canaryExperiment.inheritanceTV_perfect_but_finite_of_implication
      ⟨(), canary_relation_false⟩ canary_sample_false_implies_true,
    canary_not_global_false_implies_true⟩

section AxiomAudit

#print axioms FiniteFeatureExperiment.inherits_iff_implication
#print axioms FiniteFeatureExperiment.implication_of_global
#print axioms FiniteFeatureExperiment.fullInheritanceStrength_eq_one_of_implication
#print axioms FiniteFeatureExperiment.inheritanceTV_perfect_but_finite_of_implication
#print axioms FiniteFeatureExperiment.inheritanceTV_of_global
#print axioms canary_global_direction_evidence
#print axioms canary_perfect_sample_does_not_imply_global

end AxiomAudit

end Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence
