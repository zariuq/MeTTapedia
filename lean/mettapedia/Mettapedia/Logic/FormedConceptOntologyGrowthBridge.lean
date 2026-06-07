import Mettapedia.Logic.FormedConceptFixpointClosureBridge
import Mettapedia.Logic.MarkovLogicOntologyGrowth

/-!
# Formed Concept ↔ Ontology-Growth Bridge

This module composes two already-proved surfaces:

- exact formed-concept inheritance obligations encoded as WM queries,
- local ontology-growth stability for infinite MLN query probabilities.

The result is a narrow but honest preservation theorem: if every encoded
formed-concept obligation is supported inside a region whose MLN semantics is
stable under distant ontology growth, then threshold-validity of that seed
family is preserved under the growth step. Generic WM consequence closure can
then be re-applied on the grown side without re-proving the semantic slice.
-/

namespace Mettapedia.Logic.FormedConceptOntologyGrowthBridge

open Mettapedia.Logic
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelFixpointClosure
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Hyperseed
open MeasureTheory

universe u v w x

section Generic

variable {Atom ClauseId : Type u} [DecidableEq Atom] [DecidableEq ClauseId]
variable {Obj : Type v} {Attr : Type w} {Q : Type x}
variable [Preorder Q] [Fintype Obj] [Fintype Attr]

/-- For an encoded formed-concept inheritance query whose support lies inside a
region of local MLN agreement, ontology growth preserves the induced WM query
strength exactly. -/
theorem formedConceptQueryStrength_eq_of_specAgreesOnRegion
    {M₁ M₂ : MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : MarkovLogicInfiniteSpecification.Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hclosed₁ : InteractionClosed M₁ Γ)
    (hclosed₂ : InteractionClosed M₂ Γ)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (μ₂ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (hμ₁ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (hμ₂ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (G : ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encode :
      AbstractInheritance.FormedConcept G M →
        AbstractInheritance.FormedConcept G M →
          ConstraintQuery Atom)
    (subConcept superConcept : AbstractInheritance.FormedConcept G M)
    (hSupport :
      ∀ p ∈ encode subConcept superConcept,
        (p : Sigma fun _ : Atom => Bool).1 ∈ Γ) :
    BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics M₁ μ₁ hμ₁} :
          MassState (ConstraintQuery Atom))
        (encode subConcept superConcept) =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics M₂ μ₂ hμ₂} :
          MassState (ConstraintQuery Atom))
        (encode subConcept superConcept) := by
  simp only [MassState.queryStrength_singleton_eq_queryProb]
  exact queryProb_eq_of_specAgreesOnRegion
    hagree hclosed₁ hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂
    (encode subConcept superConcept) hSupport

/-- If a formed-concept seed family is threshold-valid in one MLN world-model
state, and every encoded seed query is supported inside a region of local MLN
agreement, then the same seed family remains threshold-valid after ontology
growth to the agreeing specification. -/
theorem thresholdValid_formedConceptQuerySet_stable_of_specAgreesOnRegion
    {M₁ M₂ : MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : MarkovLogicInfiniteSpecification.Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hclosed₁ : InteractionClosed M₁ Γ)
    (hclosed₂ : InteractionClosed M₂ Γ)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (μ₂ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (hμ₁ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (hμ₂ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (G : ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (tau : ENNReal)
    (encode :
      AbstractInheritance.FormedConcept G M →
        AbstractInheritance.FormedConcept G M →
          ConstraintQuery Atom)
    (seed :
      Set (FormedConceptFixpointClosureBridge.FormedConceptPair G M))
    (hSeed :
      thresholdValid
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        ({infiniteMLNMassSemantics M₁ μ₁ hμ₁}) tau
        (FormedConceptFixpointClosureBridge.formedConceptQuerySet G M encode seed))
    (hSupport :
      ∀ p : FormedConceptFixpointClosureBridge.FormedConceptPair G M, p ∈ seed →
        ∀ c ∈ encode p.1 p.2, (c : Sigma fun _ : Atom => Bool).1 ∈ Γ) :
    thresholdValid
      (State := MassState (ConstraintQuery Atom))
      (Query := ConstraintQuery Atom)
      ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) tau
      (FormedConceptFixpointClosureBridge.formedConceptQuerySet G M encode seed) := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  have hOld :
      tau ≤ BinaryWorldModel.queryStrength
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        ({infiniteMLNMassSemantics M₁ μ₁ hμ₁}) (encode p.1 p.2) :=
    hSeed _ ⟨p, hp, rfl⟩
  have hEq :=
    formedConceptQueryStrength_eq_of_specAgreesOnRegion
      hagree hclosed₁ hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂
      G M encode p.1 p.2 (hSupport p hp)
  simpa [hEq] using hOld

/-- Re-applying generic WM consequence closure on the grown ontology preserves
threshold-validity once the encoded formed-concept seed family is locally
stable under ontology growth. -/
theorem leastRuleClosure_thresholdValid_formedConceptQuerySet_of_specAgreesOnRegion
    (R :
      RuleSet
        (MassState (ConstraintQuery Atom))
        (ConstraintQuery Atom))
    {M₁ M₂ : MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : MarkovLogicInfiniteSpecification.Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hclosed₁ : InteractionClosed M₁ Γ)
    (hclosed₂ : InteractionClosed M₂ Γ)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (μ₂ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (hμ₁ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (hμ₂ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (G : ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (tau : ENNReal)
    (encode :
      AbstractInheritance.FormedConcept G M →
        AbstractInheritance.FormedConcept G M →
          ConstraintQuery Atom)
    (seed :
      Set (FormedConceptFixpointClosureBridge.FormedConceptPair G M))
    (hSeed :
      thresholdValid
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        ({infiniteMLNMassSemantics M₁ μ₁ hμ₁}) tau
        (FormedConceptFixpointClosureBridge.formedConceptQuerySet G M encode seed))
    (hSupport :
      ∀ p : FormedConceptFixpointClosureBridge.FormedConceptPair G M, p ∈ seed →
        ∀ c ∈ encode p.1 p.2, (c : Sigma fun _ : Atom => Bool).1 ∈ Γ) :
    thresholdValid
      (State := MassState (ConstraintQuery Atom))
      (Query := ConstraintQuery Atom)
      ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) tau
      (leastRuleClosure
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        R ({infiniteMLNMassSemantics M₂ μ₂ hμ₂})
        (FormedConceptFixpointClosureBridge.formedConceptQuerySet G M encode seed)) := by
  apply leastRuleClosure_thresholdValid
  exact thresholdValid_formedConceptQuerySet_stable_of_specAgreesOnRegion
    hagree hclosed₁ hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂
    G M tau encode seed hSeed hSupport

end Generic

section Admissibility

variable {Atom ClauseId : Type u} [DecidableEq Atom] [DecidableEq ClauseId]
variable {Obj : Type v} {Attr : Type w} {Q : Type x}
variable {Signal : Type*} {Cost : Type*}
variable [Preorder Q] [Fintype Obj] [Fintype Attr] [Preorder Cost]

/-- If ontology growth preserves the local semantics of an encoded formed-concept
seed family, and the grown state's available region is covered by the grown
closure of that family, then every available query becomes WM-admissible at the
same threshold on the grown ontology. -/
theorem generic_availableRegionAt_subset_wmAdmissibleRegionAt_of_specAgreesOnRegion
    (P : StatefulPerspective (MassState (ConstraintQuery Atom)) (ConstraintQuery Atom) Signal Cost)
    (R :
      RuleSet
        (MassState (ConstraintQuery Atom))
        (ConstraintQuery Atom))
    {M₁ M₂ : MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : MarkovLogicInfiniteSpecification.Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hclosed₁ : InteractionClosed M₁ Γ)
    (hclosed₂ : InteractionClosed M₂ Γ)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (μ₂ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (hμ₁ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (hμ₂ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (G : ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (B : Cost) (guard : Set (ConstraintQuery Atom)) (tau : ENNReal)
    (encode :
      AbstractInheritance.FormedConcept G M →
        AbstractInheritance.FormedConcept G M →
          ConstraintQuery Atom)
    (seed :
      Set (FormedConceptFixpointClosureBridge.FormedConceptPair G M))
    (hSeed :
      thresholdValid
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        ({infiniteMLNMassSemantics M₁ μ₁ hμ₁}) tau
        (FormedConceptFixpointClosureBridge.formedConceptQuerySet G M encode seed))
    (hSupport :
      ∀ p : FormedConceptFixpointClosureBridge.FormedConceptPair G M, p ∈ seed →
        ∀ c ∈ encode p.1 p.2, (c : Sigma fun _ : Atom => Bool).1 ∈ Γ)
    (hAvail :
      availableRegionAt P ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) B guard ⊆
        leastRuleClosure
          (State := MassState (ConstraintQuery Atom))
          (Query := ConstraintQuery Atom)
          R ({infiniteMLNMassSemantics M₂ μ₂ hμ₂})
          (FormedConceptFixpointClosureBridge.formedConceptQuerySet G M encode seed)) :
    availableRegionAt P ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) B guard ⊆
      PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        P ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) B guard tau := by
  apply PLNWorldModelRegimeAdmissibility.availableRegionAt_subset_wmAdmissibleRegionAt_of_thresholdValid
    (S := leastRuleClosure
      (State := MassState (ConstraintQuery Atom))
      (Query := ConstraintQuery Atom)
      R ({infiniteMLNMassSemantics M₂ μ₂ hμ₂})
      (FormedConceptFixpointClosureBridge.formedConceptQuerySet G M encode seed))
  · exact leastRuleClosure_thresholdValid_formedConceptQuerySet_of_specAgreesOnRegion
      R hagree hclosed₁ hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂
      G M tau encode seed hSeed hSupport
  · exact hAvail

/-- If the grown available region is covered by the grown closure of a locally
stable formed-concept seed family, the grown WM-admissible region collapses
back to the available region. -/
theorem generic_wmAdmissibleRegionAt_eq_availableRegionAt_of_specAgreesOnRegion
    (P : StatefulPerspective (MassState (ConstraintQuery Atom)) (ConstraintQuery Atom) Signal Cost)
    (R :
      RuleSet
        (MassState (ConstraintQuery Atom))
        (ConstraintQuery Atom))
    {M₁ M₂ : MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : MarkovLogicInfiniteSpecification.Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hclosed₁ : InteractionClosed M₁ Γ)
    (hclosed₂ : InteractionClosed M₂ Γ)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (μ₂ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (hμ₁ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (hμ₂ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (G : ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (B : Cost) (guard : Set (ConstraintQuery Atom)) (tau : ENNReal)
    (encode :
      AbstractInheritance.FormedConcept G M →
        AbstractInheritance.FormedConcept G M →
          ConstraintQuery Atom)
    (seed :
      Set (FormedConceptFixpointClosureBridge.FormedConceptPair G M))
    (hSeed :
      thresholdValid
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        ({infiniteMLNMassSemantics M₁ μ₁ hμ₁}) tau
        (FormedConceptFixpointClosureBridge.formedConceptQuerySet G M encode seed))
    (hSupport :
      ∀ p : FormedConceptFixpointClosureBridge.FormedConceptPair G M, p ∈ seed →
        ∀ c ∈ encode p.1 p.2, (c : Sigma fun _ : Atom => Bool).1 ∈ Γ)
    (hAvail :
      availableRegionAt P ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) B guard ⊆
        leastRuleClosure
          (State := MassState (ConstraintQuery Atom))
          (Query := ConstraintQuery Atom)
          R ({infiniteMLNMassSemantics M₂ μ₂ hμ₂})
          (FormedConceptFixpointClosureBridge.formedConceptQuerySet G M encode seed)) :
    PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        P ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) B guard tau =
      availableRegionAt P ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) B guard := by
  apply PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt_eq_availableRegionAt_of_thresholdValid
  exact thresholdValid_mono
    (State := MassState (ConstraintQuery Atom))
    (Query := ConstraintQuery Atom)
    (W := {infiniteMLNMassSemantics M₂ μ₂ hμ₂}) (τ := tau)
    hAvail
    (leastRuleClosure_thresholdValid_formedConceptQuerySet_of_specAgreesOnRegion
      R hagree hclosed₁ hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂
      G M tau encode seed hSeed hSupport)

end Admissibility

section Observation

variable {Atom ClauseId : Type u} [DecidableEq Atom] [DecidableEq ClauseId]
variable {Obs : Type v} {Obj : Type w} {Attr : Type x} {Q : Type*}
variable [AddCommMonoid Q] [Preorder Q] [Fintype Obj] [Fintype Attr]

/-- Observation-level specialization of local ontology-growth stability for
formed-concept seed obligations. Positive example: a concept pair formed from a
local observation surface keeps its threshold-valid inheritance query when new
remote ontology clauses are added. Negative example: this theorem does not
apply once the encoded query leaves the agreement region. -/
theorem ConceptOntology.ObservationSurface.thresholdValid_observationFormedConceptQuerySet_stable_of_specAgreesOnRegion
    {M₁ M₂ : MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : MarkovLogicInfiniteSpecification.Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hclosed₁ : InteractionClosed M₁ Γ)
    (hclosed₂ : InteractionClosed M₂ Γ)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (μ₂ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (hμ₁ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (hμ₂ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (S : ConceptOntology.ObservationSurface Obs Obj Attr Q)
    (G : ConceptOntology.EvidenceGate Q) (σ : Multiset Obs)
    (tau : ENNReal)
    (encode :
      ConceptOntology.ObservationSurface.FormedConcept S G σ →
        ConceptOntology.ObservationSurface.FormedConcept S G σ →
          ConstraintQuery Atom)
    (seed :
      Set
        (ConceptOntology.ObservationSurface.FormedConcept S G σ ×
          ConceptOntology.ObservationSurface.FormedConcept S G σ))
    (hSeed :
      thresholdValid
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        ({infiniteMLNMassSemantics M₁ μ₁ hμ₁}) tau
        (FormedConceptFixpointClosureBridge.formedConceptQuerySet G
          (ConceptOntology.ObservationSurface.aggregate S σ) encode seed))
    (hSupport :
      ∀ p : ConceptOntology.ObservationSurface.FormedConcept S G σ ×
          ConceptOntology.ObservationSurface.FormedConcept S G σ, p ∈ seed →
        ∀ c ∈ encode p.1 p.2, (c : Sigma fun _ : Atom => Bool).1 ∈ Γ) :
    thresholdValid
      (State := MassState (ConstraintQuery Atom))
      (Query := ConstraintQuery Atom)
      ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) tau
      (FormedConceptFixpointClosureBridge.formedConceptQuerySet G
        (ConceptOntology.ObservationSurface.aggregate S σ) encode seed) := by
  exact thresholdValid_formedConceptQuerySet_stable_of_specAgreesOnRegion
    hagree hclosed₁ hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂
    G (ConceptOntology.ObservationSurface.aggregate S σ) tau encode seed hSeed hSupport

/-- Observation-level closure corollary: once an observation-formed seed family
is locally stable under ontology growth, generic WM consequence closure on the
grown ontology preserves the same threshold. -/
theorem ConceptOntology.ObservationSurface.leastRuleClosure_thresholdValid_observationFormedConceptQuerySet_of_specAgreesOnRegion
    (R :
      RuleSet
        (MassState (ConstraintQuery Atom))
        (ConstraintQuery Atom))
    {M₁ M₂ : MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : MarkovLogicInfiniteSpecification.Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hclosed₁ : InteractionClosed M₁ Γ)
    (hclosed₂ : InteractionClosed M₂ Γ)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (μ₂ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (hμ₁ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (hμ₂ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (S : ConceptOntology.ObservationSurface Obs Obj Attr Q)
    (G : ConceptOntology.EvidenceGate Q) (σ : Multiset Obs)
    (tau : ENNReal)
    (encode :
      ConceptOntology.ObservationSurface.FormedConcept S G σ →
        ConceptOntology.ObservationSurface.FormedConcept S G σ →
          ConstraintQuery Atom)
    (seed :
      Set
        (ConceptOntology.ObservationSurface.FormedConcept S G σ ×
          ConceptOntology.ObservationSurface.FormedConcept S G σ))
    (hSeed :
      thresholdValid
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        ({infiniteMLNMassSemantics M₁ μ₁ hμ₁}) tau
        (FormedConceptFixpointClosureBridge.formedConceptQuerySet G
          (ConceptOntology.ObservationSurface.aggregate S σ) encode seed))
    (hSupport :
      ∀ p : ConceptOntology.ObservationSurface.FormedConcept S G σ ×
          ConceptOntology.ObservationSurface.FormedConcept S G σ, p ∈ seed →
        ∀ c ∈ encode p.1 p.2, (c : Sigma fun _ : Atom => Bool).1 ∈ Γ) :
    thresholdValid
      (State := MassState (ConstraintQuery Atom))
      (Query := ConstraintQuery Atom)
      ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) tau
      (leastRuleClosure
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        R ({infiniteMLNMassSemantics M₂ μ₂ hμ₂})
        (FormedConceptFixpointClosureBridge.formedConceptQuerySet G
          (ConceptOntology.ObservationSurface.aggregate S σ) encode seed)) := by
  exact leastRuleClosure_thresholdValid_formedConceptQuerySet_of_specAgreesOnRegion
    R hagree hclosed₁ hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂
    G (ConceptOntology.ObservationSurface.aggregate S σ) tau encode seed hSeed hSupport

section ObservationAdmissibility

variable {Atom ClauseId : Type u} [DecidableEq Atom] [DecidableEq ClauseId]
variable {Obs : Type v} {Obj : Type w} {Attr : Type x} {Q : Type*}
variable {Signal : Type*} {Cost : Type*}
variable [AddCommMonoid Q] [Preorder Q] [Fintype Obj] [Fintype Attr] [Preorder Cost]

/-- Observation-level admissibility corollary for locally stable formed-concept
obligations under ontology growth. -/
theorem ConceptOntology.ObservationSurface.availableRegionAt_subset_wmAdmissibleRegionAt_of_specAgreesOnRegion
    (P : StatefulPerspective (MassState (ConstraintQuery Atom)) (ConstraintQuery Atom) Signal Cost)
    (R :
      RuleSet
        (MassState (ConstraintQuery Atom))
        (ConstraintQuery Atom))
    {M₁ M₂ : MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : MarkovLogicInfiniteSpecification.Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hclosed₁ : InteractionClosed M₁ Γ)
    (hclosed₂ : InteractionClosed M₂ Γ)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (μ₂ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (hμ₁ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (hμ₂ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (S : ConceptOntology.ObservationSurface Obs Obj Attr Q)
    (G : ConceptOntology.EvidenceGate Q) (σ : Multiset Obs)
    (B : Cost) (guard : Set (ConstraintQuery Atom)) (tau : ENNReal)
    (encode :
      ConceptOntology.ObservationSurface.FormedConcept S G σ →
        ConceptOntology.ObservationSurface.FormedConcept S G σ →
          ConstraintQuery Atom)
    (seed :
      Set
        (ConceptOntology.ObservationSurface.FormedConcept S G σ ×
          ConceptOntology.ObservationSurface.FormedConcept S G σ))
    (hSeed :
      thresholdValid
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        ({infiniteMLNMassSemantics M₁ μ₁ hμ₁}) tau
        (FormedConceptFixpointClosureBridge.formedConceptQuerySet G
          (ConceptOntology.ObservationSurface.aggregate S σ) encode seed))
    (hSupport :
      ∀ p : ConceptOntology.ObservationSurface.FormedConcept S G σ ×
          ConceptOntology.ObservationSurface.FormedConcept S G σ, p ∈ seed →
        ∀ c ∈ encode p.1 p.2, (c : Sigma fun _ : Atom => Bool).1 ∈ Γ)
    (hAvail :
      availableRegionAt P ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) B guard ⊆
        leastRuleClosure
          (State := MassState (ConstraintQuery Atom))
          (Query := ConstraintQuery Atom)
          R ({infiniteMLNMassSemantics M₂ μ₂ hμ₂})
          (FormedConceptFixpointClosureBridge.formedConceptQuerySet G
            (ConceptOntology.ObservationSurface.aggregate S σ) encode seed)) :
    availableRegionAt P ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) B guard ⊆
      PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        P ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) B guard tau := by
  exact generic_availableRegionAt_subset_wmAdmissibleRegionAt_of_specAgreesOnRegion
    P R hagree hclosed₁ hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂
    G (ConceptOntology.ObservationSurface.aggregate S σ) B guard tau encode seed hSeed hSupport hAvail

/-- Observation-level admissible-region collapse corollary for locally stable
formed-concept obligations under ontology growth. -/
theorem ConceptOntology.ObservationSurface.wmAdmissibleRegionAt_eq_availableRegionAt_of_specAgreesOnRegion
    (P : StatefulPerspective (MassState (ConstraintQuery Atom)) (ConstraintQuery Atom) Signal Cost)
    (R :
      RuleSet
        (MassState (ConstraintQuery Atom))
        (ConstraintQuery Atom))
    {M₁ M₂ : MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : MarkovLogicInfiniteSpecification.Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hclosed₁ : InteractionClosed M₁ Γ)
    (hclosed₂ : InteractionClosed M₂ Γ)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (μ₂ : MeasureTheory.ProbabilityMeasure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom))
    (hμ₁ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (hμ₂ : MarkovLogicInfiniteFixedRegionDLR.FixedRegionCylinderDLR
      M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : MeasureTheory.Measure (MarkovLogicInfiniteSpecification.InfiniteWorld Atom)))
    (S : ConceptOntology.ObservationSurface Obs Obj Attr Q)
    (G : ConceptOntology.EvidenceGate Q) (σ : Multiset Obs)
    (B : Cost) (guard : Set (ConstraintQuery Atom)) (tau : ENNReal)
    (encode :
      ConceptOntology.ObservationSurface.FormedConcept S G σ →
        ConceptOntology.ObservationSurface.FormedConcept S G σ →
          ConstraintQuery Atom)
    (seed :
      Set
        (ConceptOntology.ObservationSurface.FormedConcept S G σ ×
          ConceptOntology.ObservationSurface.FormedConcept S G σ))
    (hSeed :
      thresholdValid
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        ({infiniteMLNMassSemantics M₁ μ₁ hμ₁}) tau
        (FormedConceptFixpointClosureBridge.formedConceptQuerySet G
          (ConceptOntology.ObservationSurface.aggregate S σ) encode seed))
    (hSupport :
      ∀ p : ConceptOntology.ObservationSurface.FormedConcept S G σ ×
          ConceptOntology.ObservationSurface.FormedConcept S G σ, p ∈ seed →
        ∀ c ∈ encode p.1 p.2, (c : Sigma fun _ : Atom => Bool).1 ∈ Γ)
    (hAvail :
      availableRegionAt P ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) B guard ⊆
        leastRuleClosure
          (State := MassState (ConstraintQuery Atom))
          (Query := ConstraintQuery Atom)
          R ({infiniteMLNMassSemantics M₂ μ₂ hμ₂})
          (FormedConceptFixpointClosureBridge.formedConceptQuerySet G
            (ConceptOntology.ObservationSurface.aggregate S σ) encode seed)) :
    PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := MassState (ConstraintQuery Atom))
        (Query := ConstraintQuery Atom)
        P ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) B guard tau =
      availableRegionAt P ({infiniteMLNMassSemantics M₂ μ₂ hμ₂}) B guard := by
  exact generic_wmAdmissibleRegionAt_eq_availableRegionAt_of_specAgreesOnRegion
    P R hagree hclosed₁ hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂
    G (ConceptOntology.ObservationSurface.aggregate S σ) B guard tau encode seed hSeed hSupport hAvail

end ObservationAdmissibility

end Observation

end Mettapedia.Logic.FormedConceptOntologyGrowthBridge
