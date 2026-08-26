import Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceGrowthBridge

/-!
# Quantitative revision laws for growing algorithmic-feature evidence

This module classifies the finite quantities behind the PLN inheritance truth
value as observed sources grow.

Two count laws are unconditional:

* a feature's observed extent count is monotone; and
* its stage-local intent count is antitone.

Their weakest-link combination is not monotone in either direction.  Concrete
nonvacuous controls show that inheritance strength, evidence weight, and PLN
confidence can each increase or decrease after new checked sources arrive.
Finite confidence remains strictly below one at every stage.
-/

namespace Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence

open KolmogorovComplexity
open Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceGrowth
open Mettapedia.Logic.WorldModel.AlgorithmicConceptFormationExamples
open Mettapedia.PLN.TruthValues.PLNWeightTV

universe u v

namespace FiniteFeatureExperiment

variable {SourceIndex : Type u} {FeatureIndex : Type v}
variable [Fintype SourceIndex] [Fintype FeatureIndex]

/-- Number of observed source indices exhibiting a feature at one stage. -/
noncomputable def extentEvidenceCountAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (feature : FeatureIndex) : Nat :=
  (E.conceptAt observed feature).extent.ncard

/-- Number of feature indices implied by a feature at one stage. -/
noncomputable def intentEvidenceCountAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (feature : FeatureIndex) : Nat :=
  (E.conceptAt observed feature).intent.ncard

/-- Observed extent evidence can only grow when source observations grow. -/
theorem extentEvidenceCountAt_mono
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {earlier later : Set SourceIndex} (growth : earlier ⊆ later)
    (feature : FeatureIndex) :
    E.extentEvidenceCountAt earlier feature ≤
      E.extentEvidenceCountAt later feature := by
  exact Set.ncard_le_ncard (E.conceptAt_extent_mono growth feature)
    (Set.toFinite _)

/-- Stage-local intent evidence can only shrink when source observations grow. -/
theorem intentEvidenceCountAt_anti
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {earlier later : Set SourceIndex} (growth : earlier ⊆ later)
    (feature : FeatureIndex) :
    E.intentEvidenceCountAt later feature ≤
      E.intentEvidenceCountAt earlier feature := by
  exact Set.ncard_le_ncard (E.conceptAt_intent_anti growth feature)
    (Set.toFinite _)

end FiniteFeatureExperiment

end Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence

namespace Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceRevision

open KolmogorovComplexity
open Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceGrowth
open Mettapedia.Logic.WorldModel.AlgorithmicConceptFormationExamples
open Mettapedia.PLN.TruthValues.PLNWeightTV

/-! ## Strength can move in either direction -/

/-- Observe only the source that exhibits the general feature but not the
specific feature. -/
def failureObserved : Set Bool := {true}

theorem failureObserved_subset_laterObserved :
    failureObserved ⊆ laterObserved := by
  intro source _
  simp [laterObserved]

private theorem early_general_extent :
    ((growthCanaryExperiment.interpretationAt earlyObserved).meaning false).extent =
      ({false} : Set Bool) := by
  ext source
  cases source <;>
    simp [FiniteFeatureExperiment.interpretationAt,
      FiniteFeatureExperiment.conceptAt, FiniteFeatureExperiment.RelationAt,
      FiniteFeatureExperiment.Relation, earlyObserved, growthCanaryExperiment,
      conceptCanary_true_featureOf_fourTrue]

private theorem early_specific_intent :
    ((growthCanaryExperiment.interpretationAt earlyObserved).meaning true).intent =
      Set.univ := by
  ext consequent
  cases consequent <;>
    simp [FiniteFeatureExperiment.interpretationAt,
      FiniteFeatureExperiment.conceptAt, FiniteFeatureExperiment.ImplicationAt,
      FiniteFeatureExperiment.RelationAt, FiniteFeatureExperiment.Relation,
      earlyObserved, growthCanaryExperiment,
      conceptCanary_false_featureOf_fourTrue,
      conceptCanary_true_featureOf_fourTrue]

private theorem later_general_extent :
    ((growthCanaryExperiment.interpretationAt laterObserved).meaning false).extent =
      Set.univ := by
  ext source
  cases source <;>
    simp [FiniteFeatureExperiment.interpretationAt,
      FiniteFeatureExperiment.conceptAt, FiniteFeatureExperiment.RelationAt,
      FiniteFeatureExperiment.Relation, laterObserved, growthCanaryExperiment,
      conceptCanary_true_featureOf_fourTrue,
      conceptCanary_true_featureOf_fourFalse]

private theorem later_specific_extent :
    ((growthCanaryExperiment.interpretationAt laterObserved).meaning true).extent =
      ({false} : Set Bool) := by
  ext source
  cases source <;>
    simp [FiniteFeatureExperiment.interpretationAt,
      FiniteFeatureExperiment.conceptAt, FiniteFeatureExperiment.RelationAt,
      FiniteFeatureExperiment.Relation, laterObserved, growthCanaryExperiment,
      conceptCanary_false_featureOf_fourTrue,
      conceptCanary_false_not_featureOf_fourFalse]

private theorem later_general_intent :
    ((growthCanaryExperiment.interpretationAt laterObserved).meaning false).intent =
      ({false} : Set Bool) := by
  ext consequent
  cases consequent
  · simp [FiniteFeatureExperiment.interpretationAt,
      FiniteFeatureExperiment.conceptAt,
      FiniteFeatureExperiment.implicationAt_refl]
  · simp only [FiniteFeatureExperiment.interpretationAt,
      FiniteFeatureExperiment.conceptAt, Set.mem_setOf_eq,
      Set.mem_singleton_iff, Bool.true_eq_false, iff_false]
    exact growthCanary_later_not_false_implies_true

private theorem later_specific_intent :
    ((growthCanaryExperiment.interpretationAt laterObserved).meaning true).intent =
      Set.univ := by
  ext consequent
  cases consequent <;>
    simp [FiniteFeatureExperiment.interpretationAt,
      FiniteFeatureExperiment.conceptAt, FiniteFeatureExperiment.ImplicationAt,
      FiniteFeatureExperiment.RelationAt, FiniteFeatureExperiment.Relation,
      laterObserved, growthCanaryExperiment,
      conceptCanary_false_featureOf_fourTrue,
      conceptCanary_true_featureOf_fourTrue,
      conceptCanary_false_not_featureOf_fourFalse]

private theorem failure_general_extent :
    ((growthCanaryExperiment.interpretationAt failureObserved).meaning false).extent =
      ({true} : Set Bool) := by
  ext source
  cases source <;>
    simp [FiniteFeatureExperiment.interpretationAt,
      FiniteFeatureExperiment.conceptAt, FiniteFeatureExperiment.RelationAt,
      FiniteFeatureExperiment.Relation, failureObserved, growthCanaryExperiment,
      conceptCanary_true_featureOf_fourFalse]

private theorem failure_specific_extent :
    ((growthCanaryExperiment.interpretationAt failureObserved).meaning true).extent =
      (∅ : Set Bool) := by
  ext source
  cases source <;>
    simp [FiniteFeatureExperiment.interpretationAt,
      FiniteFeatureExperiment.conceptAt, FiniteFeatureExperiment.RelationAt,
      FiniteFeatureExperiment.Relation, failureObserved, growthCanaryExperiment,
      conceptCanary_false_not_featureOf_fourFalse]

/-- At the later stage both extensional and intensional factors are exactly
one half. -/
theorem growthCanary_later_fullInheritanceStrength_eq_half :
    fullInheritanceStrength
      (growthCanaryExperiment.interpretationAt laterObserved) false true =
        (1 : ℝ) / 2 := by
  rw [fullInheritanceStrength, pureExtensionalStrength,
    pureIntensionalStrength, later_general_extent, later_specific_extent,
    later_general_intent, later_specific_intent]
  norm_num

/-- Starting from a witnessed failure and then adding a successful source
strictly increases full inheritance strength from zero to one half. -/
theorem growthCanary_fullInheritanceStrength_can_increase :
    fullInheritanceStrength
        (growthCanaryExperiment.interpretationAt failureObserved) false true = 0 ∧
      fullInheritanceStrength
        (growthCanaryExperiment.interpretationAt laterObserved) false true =
          (1 : ℝ) / 2 := by
  constructor
  · have extensionalZero :
        pureExtensionalStrength
          (growthCanaryExperiment.interpretationAt failureObserved) false true = 0 := by
      rw [pureExtensionalStrength, failure_general_extent,
        failure_specific_extent]
      norm_num
    rw [fullInheritanceStrength, extensionalZero]
    exact min_eq_left
      (pureIntensionalStrength_nonneg
        (growthCanaryExperiment.interpretationAt failureObserved) false true)
  · exact growthCanary_later_fullInheritanceStrength_eq_half

/-- Adding a checked counterexample strictly decreases full inheritance
strength from one to one half. -/
theorem growthCanary_fullInheritanceStrength_can_decrease :
    fullInheritanceStrength
        (growthCanaryExperiment.interpretationAt earlyObserved) false true = 1 ∧
      fullInheritanceStrength
        (growthCanaryExperiment.interpretationAt laterObserved) false true =
          (1 : ℝ) / 2 :=
  ⟨growthCanaryExperiment.fullInheritanceStrengthAt_eq_one_of_implicationAt
      earlyObserved growthCanary_premise_witness_early
      growthCanary_early_false_implies_true,
    growthCanary_later_fullInheritanceStrength_eq_half⟩

/-! ## Weight and confidence can move in either direction -/

theorem growthCanary_inheritanceWeight_increases :
    inheritanceWeight
        (growthCanaryExperiment.interpretationAt earlyObserved) false true = 1 ∧
      inheritanceWeight
        (growthCanaryExperiment.interpretationAt laterObserved) false true = 2 := by
  rw [inheritanceWeight, early_general_extent, early_specific_intent,
    inheritanceWeight, later_general_extent, later_specific_intent]
  norm_num

/-- Repeated indices are legitimate independent observations of the same
binary source.  The first two exhibit both features; the final source exhibits
only the general feature. -/
def duplicateCanaryExperiment : FiniteFeatureExperiment (Option Bool) Bool where
  algorithm := conceptCanaryAlgorithm
  source
    | none => fourTrue
    | some false => fourTrue
    | some true => fourFalse
  feature
    | false => [true]
    | true => [false]

def duplicateEarlyObserved : Set (Option Bool) := {none, some false}

def duplicateLaterObserved : Set (Option Bool) := Set.univ

private theorem duplicateEarlyObserved_ncard :
    duplicateEarlyObserved.ncard = 2 := by
  rw [duplicateEarlyObserved]
  exact Set.ncard_pair (by simp)

theorem duplicateEarly_subset_later :
    duplicateEarlyObserved ⊆ duplicateLaterObserved := by
  intro source _
  simp [duplicateLaterObserved]

private theorem duplicate_early_specific_extent :
    ((duplicateCanaryExperiment.interpretationAt duplicateEarlyObserved).meaning
      true).extent = duplicateEarlyObserved := by
  ext source
  cases source with
  | none =>
      simp [FiniteFeatureExperiment.interpretationAt,
        FiniteFeatureExperiment.conceptAt, FiniteFeatureExperiment.RelationAt,
        FiniteFeatureExperiment.Relation, duplicateCanaryExperiment,
        duplicateEarlyObserved, conceptCanary_false_featureOf_fourTrue]
  | some bit =>
      cases bit <;>
        simp [FiniteFeatureExperiment.interpretationAt,
          FiniteFeatureExperiment.conceptAt, FiniteFeatureExperiment.RelationAt,
          FiniteFeatureExperiment.Relation, duplicateCanaryExperiment,
          duplicateEarlyObserved, conceptCanary_false_featureOf_fourTrue,
          conceptCanary_false_not_featureOf_fourFalse]

private theorem duplicate_later_specific_extent :
    ((duplicateCanaryExperiment.interpretationAt duplicateLaterObserved).meaning
      true).extent = duplicateEarlyObserved := by
  ext source
  cases source with
  | none =>
      simp [FiniteFeatureExperiment.interpretationAt,
        FiniteFeatureExperiment.conceptAt, FiniteFeatureExperiment.RelationAt,
        FiniteFeatureExperiment.Relation, duplicateCanaryExperiment,
        duplicateEarlyObserved, duplicateLaterObserved,
        conceptCanary_false_featureOf_fourTrue]
  | some bit =>
      cases bit <;>
        simp [FiniteFeatureExperiment.interpretationAt,
          FiniteFeatureExperiment.conceptAt, FiniteFeatureExperiment.RelationAt,
          FiniteFeatureExperiment.Relation, duplicateCanaryExperiment,
          duplicateEarlyObserved, duplicateLaterObserved,
          conceptCanary_false_featureOf_fourTrue,
          conceptCanary_false_not_featureOf_fourFalse]

private theorem duplicate_early_general_intent :
    ((duplicateCanaryExperiment.interpretationAt duplicateEarlyObserved).meaning
      false).intent = Set.univ := by
  ext consequent
  cases consequent <;>
    simp [FiniteFeatureExperiment.interpretationAt,
      FiniteFeatureExperiment.conceptAt, FiniteFeatureExperiment.ImplicationAt,
      FiniteFeatureExperiment.RelationAt, FiniteFeatureExperiment.Relation,
      duplicateCanaryExperiment, duplicateEarlyObserved,
      conceptCanary_false_featureOf_fourTrue,
      conceptCanary_true_featureOf_fourTrue]

private theorem duplicate_later_not_general_implies_specific :
    ¬ duplicateCanaryExperiment.ImplicationAt
      duplicateLaterObserved false true := by
  intro implication
  have premise : duplicateCanaryExperiment.RelationAt
      duplicateLaterObserved (some true) false :=
    ⟨by simp [duplicateLaterObserved], by
      simpa [FiniteFeatureExperiment.Relation, duplicateCanaryExperiment] using
        conceptCanary_true_featureOf_fourFalse⟩
  exact conceptCanary_false_not_featureOf_fourFalse
    (implication (some true) premise).2

private theorem duplicate_later_general_intent :
    ((duplicateCanaryExperiment.interpretationAt duplicateLaterObserved).meaning
      false).intent = ({false} : Set Bool) := by
  ext consequent
  cases consequent
  · simp [FiniteFeatureExperiment.interpretationAt,
      FiniteFeatureExperiment.conceptAt,
      FiniteFeatureExperiment.implicationAt_refl]
  · simp only [FiniteFeatureExperiment.interpretationAt,
      FiniteFeatureExperiment.conceptAt, Set.mem_setOf_eq,
      Set.mem_singleton_iff, Bool.true_eq_false, iff_false]
    exact duplicate_later_not_general_implies_specific

/-- The competing monotone extent count and antitone intent count make the
weakest evidence weight decrease from two to one in this control. -/
theorem duplicateCanary_inheritanceWeight_decreases :
    inheritanceWeight
        (duplicateCanaryExperiment.interpretationAt duplicateEarlyObserved)
        true false = 2 ∧
      inheritanceWeight
        (duplicateCanaryExperiment.interpretationAt duplicateLaterObserved)
        true false = 1 := by
  rw [inheritanceWeight, duplicate_early_specific_extent,
    duplicate_early_general_intent, inheritanceWeight,
    duplicate_later_specific_extent, duplicate_later_general_intent,
    duplicateEarlyObserved_ncard]
  norm_num

/-- PLN confidence can increase under observation growth. -/
theorem growthCanary_confidence_increases :
    (inheritanceTV
        (growthCanaryExperiment.interpretationAt earlyObserved)
        false true).confidence = (1 : ℝ) / 2 ∧
      (inheritanceTV
        (growthCanaryExperiment.interpretationAt laterObserved)
        false true).confidence = (2 : ℝ) / 3 := by
  change w2c (inheritanceWeight
      (growthCanaryExperiment.interpretationAt earlyObserved) false true) =
        (1 : ℝ) / 2 ∧
    w2c (inheritanceWeight
      (growthCanaryExperiment.interpretationAt laterObserved) false true) =
        (2 : ℝ) / 3
  rw [growthCanary_inheritanceWeight_increases.1,
    growthCanary_inheritanceWeight_increases.2]
  norm_num [w2c]

/-- PLN confidence can also decrease under observation growth. -/
theorem duplicateCanary_confidence_decreases :
    (inheritanceTV
        (duplicateCanaryExperiment.interpretationAt duplicateEarlyObserved)
        true false).confidence = (2 : ℝ) / 3 ∧
      (inheritanceTV
        (duplicateCanaryExperiment.interpretationAt duplicateLaterObserved)
        true false).confidence = (1 : ℝ) / 2 := by
  change w2c (inheritanceWeight
      (duplicateCanaryExperiment.interpretationAt duplicateEarlyObserved)
      true false) = (2 : ℝ) / 3 ∧
    w2c (inheritanceWeight
      (duplicateCanaryExperiment.interpretationAt duplicateLaterObserved)
      true false) = (1 : ℝ) / 2
  rw [duplicateCanary_inheritanceWeight_decreases.1,
    duplicateCanary_inheritanceWeight_decreases.2]
  norm_num [w2c]

section AxiomAudit

#print axioms FiniteFeatureExperiment.extentEvidenceCountAt_mono
#print axioms FiniteFeatureExperiment.intentEvidenceCountAt_anti
#print axioms growthCanary_fullInheritanceStrength_can_increase
#print axioms growthCanary_fullInheritanceStrength_can_decrease
#print axioms growthCanary_inheritanceWeight_increases
#print axioms duplicateCanary_inheritanceWeight_decreases
#print axioms growthCanary_confidence_increases
#print axioms duplicateCanary_confidence_decreases

end AxiomAudit

end Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceRevision
