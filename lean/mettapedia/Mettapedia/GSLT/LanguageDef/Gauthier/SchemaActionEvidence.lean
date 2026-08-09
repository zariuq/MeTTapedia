import Mettapedia.GSLT.LanguageDef.Gauthier.SchemaCredalBank
import Mettapedia.GSLT.LanguageDef.Gauthier.GradeBActionEvidence

/-!
# Compiling promoted schemas to graded action evidence

A schema may contribute action evidence only after credal promotion and an
authenticated source match.  This module compiles that proof-carrying input
to the established Grade-B `ActionObservation`.  It does not define a second
register, innovation identity, posterior, or checker mask.

The source lineage, causal root, and structural source are derived from the
certified match rather than supplied again by the caller.  Consequently the
existing causal deduplication and three-way totality semantics are preserved
definitionally at the compiler boundary.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierSchemaActionEvidence

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema
open Mettapedia.GSLT.LanguageDef.GauthierPatternSupport
open Mettapedia.GSLT.LanguageDef.GauthierSchemaCredalBank
open Mettapedia.GSLT.LanguageDef.GauthierPartialPostfixAlignment
open Mettapedia.GSLT.LanguageDef.GauthierAlignmentEvidence
open Mettapedia.GSLT.LanguageDef.GauthierActionEvidencePCBridge
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.KR.ConceptOntology
open Mettapedia.PLN.Bridges.PredictiveCoding
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

universe u v

variable {Obj : Type u} {Attr : Type v}

/-- A promoted schema action is backed by a robust or provisional canonical
schema and by a concrete source program that actually matches the raw schema.
No rejected schema and no unmatched source can inhabit this structure. -/
structure PromotedSchemaAction
    (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) where
  pattern : Pattern
  promotion :
    canonicalSchema pattern ∈ robustSchemaBank family meaning ∨
      canonicalSchema pattern ∈ provisionalSchemaBank family meaning
  sourceMatch : SourceMatch pattern
  query : ActionQuery
  alignmentCoordinate : AlignmentCoordinate
  action : OperatorAction
  verdict : TotalityVerdict

/-- Compile promoted schema evidence into the existing Grade-B observation
record.  All provenance fields are derived from the authenticated match. -/
def compileActionObservation
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observation : PromotedSchemaAction family meaning) : ActionObservation :=
  { query := observation.query
    alignmentCoordinate := observation.alignmentCoordinate
    structuralSource := rpnTokens observation.sourceMatch.observation.program
    action := observation.action
    verdict := observation.verdict
    sourceLineage := observation.sourceMatch.observation.sourceLineage
    sourceRoot := observation.sourceMatch.observation.sourceRoot }

@[simp] theorem compileActionObservation_query
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observation : PromotedSchemaAction family meaning) :
    (compileActionObservation observation).query = observation.query := rfl

@[simp] theorem compileActionObservation_action
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observation : PromotedSchemaAction family meaning) :
    (compileActionObservation observation).action = observation.action := rfl

@[simp] theorem compileActionObservation_verdict
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observation : PromotedSchemaAction family meaning) :
    (compileActionObservation observation).verdict = observation.verdict := rfl

@[simp] theorem compileActionObservation_sourceRoot
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observation : PromotedSchemaAction family meaning) :
    (compileActionObservation observation).sourceRoot =
      observation.sourceMatch.observation.sourceRoot := rfl

/-- Existing overlap-corrected action evidence after compiling promoted
schemas. -/
def correctedSchemaActionEvidence
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observations : List (PromotedSchemaAction family meaning)) :
    GradedActionEvidence operatorCount :=
  correctedEvidence (observations.map compileActionObservation)

/-- Existing query-indexed representative evidence after compilation. -/
def schemaActionEvidenceForQuery
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observations : List (PromotedSchemaAction family meaning))
    (query : ActionQuery) : GradedActionEvidence operatorCount :=
  alignedRepresentativeEvidence
    (observations.map compileActionObservation) query

/-- A promoted schema cannot be rejected when the credal lower family is a
subset of the upper family. -/
theorem promotedSchema_not_rejected
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (lower_upper : family.lower ⊆ family.upper)
    (observation : PromotedSchemaAction family meaning) :
    canonicalSchema observation.pattern ∉
      rejectedSchemaBank family meaning := by
  intro rejected
  rcases observation.promotion with robust | provisional
  · exact rejected (lower_upper robust)
  · exact rejected provisional.1

/-! ## Causal deduplication -/

/-- Repeating an identical promoted schema observation changes no evidence. -/
theorem correctedSchemaActionEvidence_duplicate
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observation : PromotedSchemaAction family meaning)
    (rest : List (PromotedSchemaAction family meaning)) :
    correctedSchemaActionEvidence (observation :: observation :: rest) =
      correctedSchemaActionEvidence (observation :: rest) := by
  exact correctedEvidence_duplicate (compileActionObservation observation)
    (rest.map compileActionObservation)

/-- Distinct schema witnesses with the same query, action, verdict, and causal
root compile to one innovation identity. -/
theorem compiled_same_root_same_innovation
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (first second : PromotedSchemaAction family meaning)
    (sameQuery : first.query = second.query)
    (sameAction : first.action = second.action)
    (sameVerdict : first.verdict = second.verdict)
    (sameRoot : first.sourceMatch.observation.sourceRoot =
      second.sourceMatch.observation.sourceRoot) :
    (compileActionObservation first).innovationId =
      (compileActionObservation second).innovationId := by
  simp [ActionObservation.innovationId, compileActionObservation,
    sameQuery, sameAction, sameVerdict, sameRoot]

/-- Shared-DAG or descendant manifestations that compile to one causal
identity are assimilated once by the existing accumulator. -/
theorem correctedSchemaActionEvidence_same_root
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (first second : PromotedSchemaAction family meaning)
    (sameQuery : first.query = second.query)
    (sameAction : first.action = second.action)
    (sameVerdict : first.verdict = second.verdict)
    (sameRoot : first.sourceMatch.observation.sourceRoot =
      second.sourceMatch.observation.sourceRoot) :
    correctedSchemaActionEvidence [first, second] =
      correctedSchemaActionEvidence [first] := by
  apply correctedEvidence_common_root
  exact compiled_same_root_same_innovation first second sameQuery sameAction
    sameVerdict sameRoot

/-! ## Three-channel semantics -/

/-- A promoted total observation contributes exactly one positive count to
its action. -/
theorem promoted_total_is_positive
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observation : PromotedSchemaAction family meaning)
    (total : observation.verdict = .provablyTotal) :
    (correctedSchemaActionEvidence [observation]).positive.counts
      observation.action = 1 := by
  simp [correctedSchemaActionEvidence, compileActionObservation,
    correctedEvidence, evidenceOfInnovation, ActionObservation.innovationId,
    GradedActionEvidence.ofVerdict, GradedActionEvidence.oneHot,
    MultiEvidence.zero, total]

/-- A promoted refutation contributes negative evidence and no positive
evidence for the refuted action. -/
theorem promoted_partial_is_negative
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observation : PromotedSchemaAction family meaning)
    (partialVerdict : observation.verdict = .provablyPartial) :
    (correctedSchemaActionEvidence [observation]).positive.counts
          observation.action = 0 ∧
      (correctedSchemaActionEvidence [observation]).negative.counts
          observation.action = 1 := by
  simp [correctedSchemaActionEvidence, compileActionObservation,
    correctedEvidence, evidenceOfInnovation, ActionObservation.innovationId,
    GradedActionEvidence.ofVerdict, GradedActionEvidence.oneHot,
    MultiEvidence.zero, partialVerdict]

/-- A promoted resource-boundary observation remains undetermined rather than
becoming a failure. -/
theorem promoted_undetermined_stays_undetermined
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observation : PromotedSchemaAction family meaning)
    (undetermined : observation.verdict = .undeterminedAtBudget) :
    (correctedSchemaActionEvidence [observation]).positive.counts
          observation.action = 0 ∧
      (correctedSchemaActionEvidence [observation]).negative.counts
          observation.action = 0 ∧
      (correctedSchemaActionEvidence [observation]).undetermined.counts
          observation.action = 1 := by
  simp [correctedSchemaActionEvidence, compileActionObservation,
    correctedEvidence, evidenceOfInnovation, ActionObservation.innovationId,
    GradedActionEvidence.ofVerdict, GradedActionEvidence.oneHot,
    MultiEvidence.zero, undetermined]

/-! ## Existing register, checker, and equilibrium -/

/-- Checker sovereignty survives schema compilation: an illegal action has
zero static support regardless of the promoted evidence. -/
theorem promoted_illegal_action_has_zero_support
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observations : List (PromotedSchemaAction family meaning))
    (query : ActionQuery) (state : MaskState) (action : OperatorAction)
    (illegal : checkerOperatorLegal state action = false) :
    staticActionReadout (schemaActionEvidenceForQuery observations query)
      state action = 0 := by
  exact illegal_operator_has_zero_static_support
    (schemaActionEvidenceForQuery observations query) state action illegal

/-- Schema evidence enters the same established categorical register for the
static readout and the PC equilibrium.  At equilibrium their posterior is
identical, and checker legality alone determines static support. -/
theorem promoted_settled_eq_static_and_same_checker_support
    {family : CredalConceptFamily Obj Attr}
    {meaning : SchemaPattern → DualConcept Obj Attr}
    (observations : List (PromotedSchemaAction family meaning))
    (query : ActionQuery) (settled : OperatorAction → ℝ)
    (equilibrium : ActionPCEnergyEquilibrium
      (schemaActionEvidenceForQuery observations query) settled)
    (state : MaskState)
    (someLegal : ∃ action, checkerOperatorLegal state action = true) :
    settled = categoricalPosterior
        (actionEvidenceRegister
          (schemaActionEvidenceForQuery observations query)) ∧
      (∀ action,
        staticActionReadout (schemaActionEvidenceForQuery observations query)
              state action ≠ 0 ↔
          checkerOperatorLegal state action = true) := by
  exact settledActionReadout_eq_static_and_same_checker_support
    (schemaActionEvidenceForQuery observations query) settled equilibrium
    state someLegal

/-! ## Executable admission controls -/

namespace Control

open Mettapedia.GSLT.LanguageDef.GauthierSchemaCredalBank.Control

def rootKey : HoleKey := { role := .root, left := zero, right := one }
def rootPattern : Pattern := .hole rootKey

def rootZeroMatch : SourceMatch rootPattern where
  observation := ⟨zero, 10, [0], 7⟩
  matching := by
    refine ⟨fun _ => zero, ?_⟩
    simp [rootPattern, rootKey, instantiate]

def coordinate : AlignmentCoordinate := ⟨0, [], .root, true⟩

def positiveAction :
    PromotedSchemaAction controlFamily controlMeaning where
  pattern := rootPattern
  promotion := Or.inl (by
    simpa [rootPattern, rootKey, canonicalSchema, schemaWith,
      holeOccurrences] using root_zero_is_robust)
  sourceMatch := rootZeroMatch
  query := ⟨42, []⟩
  alignmentCoordinate := coordinate
  action := actionZero
  verdict := .provablyTotal

theorem positiveAction_compiles_positive :
    (correctedSchemaActionEvidence [positiveAction]).positive.counts
      actionZero = 1 := by
  exact promoted_total_is_positive positiveAction rfl

/-- The rejected control schema cannot be smuggled through the promotion
boundary. -/
theorem rejected_control_not_promotable :
    ¬ (SchemaPattern.hole .code 0 ∈
          robustSchemaBank controlFamily controlMeaning ∨
        SchemaPattern.hole .code 0 ∈
          provisionalSchemaBank controlFamily controlMeaning) := by
  simp [robustSchemaBank, provisionalSchemaBank, controlFamily,
    controlMeaning, rejectedConcept_ne_robustConcept,
    rejectedConcept_ne_provisionalConcept]

end Control

#print axioms promotedSchema_not_rejected
#print axioms correctedSchemaActionEvidence_duplicate
#print axioms compiled_same_root_same_innovation
#print axioms correctedSchemaActionEvidence_same_root
#print axioms promoted_total_is_positive
#print axioms promoted_partial_is_negative
#print axioms promoted_undetermined_stays_undetermined
#print axioms promoted_illegal_action_has_zero_support
#print axioms promoted_settled_eq_static_and_same_checker_support
#print axioms Control.positiveAction_compiles_positive
#print axioms Control.rejected_control_not_promotable

end Mettapedia.GSLT.LanguageDef.GauthierSchemaActionEvidence
