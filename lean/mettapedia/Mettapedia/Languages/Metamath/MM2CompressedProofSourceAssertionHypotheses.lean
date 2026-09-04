import Mettapedia.Languages.Metamath.MM2CompressedProofSourceMandatoryHypotheses
import Mettapedia.Languages.Metamath.MM2NormalDVAddressed

/-!
# Source assertion boundary with all mandatory hypotheses

This module joins the existing assertion launch, entry, result-body, and
resume boundary with the complete source-derived ordered hypothesis trace.
The same address segment now carries the assertion through every mandatory
hypothesis, the complete disjoint-variable machine, body construction, result
publication, and compressed-proof resume boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionHypotheses

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionResultResume
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceMandatoryHypotheses
open Mettapedia.Languages.Metamath.MM2NormalAddressSegment
open Mettapedia.Languages.Metamath.MM2NormalDVAddressed
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

private theorem sourceAssertion_dvPairNamesDistinct
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    (presentation :
      calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView}
    (member : assertion ∈ projection.assertions) :
    DVPairNamesDistinct assertion.frame.dj.toList := by
  have projectionValid : prefixProjectionValid projection = true :=
    prefixProjectionValid_of_calculusLanguageDefOfProjection?_eq_some
      projection target.1 presentation
  simp only [prefixProjectionValid, Bool.and_eq_true] at projectionValid
  have assertionValid : assertionViewValid projection.declaredConstants
      projection.declaredVariables assertion = true :=
    List.all_eq_true.mp projectionValid.1.2 assertion member
  simp only [assertionViewValid, Bool.and_eq_true] at assertionValid
  have frameValid : frameProjectionValid assertion.frame
      assertion.hypotheses = true := assertionValid.1.1.1
  simp only [frameProjectionValid, Bool.and_eq_true] at frameValid
  have dvValid : frameDVValid assertion.frame
      (floatingVariableNames assertion.hypotheses) = true := frameValid.2
  simp only [frameDVValid] at dvValid
  apply dvPairNamesDistinct_of_strictOrderAll assertion.frame.dj.toList
  apply List.all_eq_true.mpr
  intro pair pairMember
  have pairValid := List.all_eq_true.mp dvValid pair pairMember
  simp only [Bool.and_eq_true] at pairValid
  exact pairValid.1.1

/-- Source-owned assertion composition through mandatory hypotheses and every
addressed disjoint-variable transition. -/
structure SourceAssertionLaunchHypothesesBodyResumeBoundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor proofPosition : Nat)
    (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (request : SourceAssertionRequest context before scannerBefore scannerAfter
      occurrence index assertion)
    (stackExact : before.stack = retained ++ parents)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children) where
  endpoints : SourceAssertionLaunchBodyResumeBoundary context before ledger
    scannerBefore scannerAfter occurrence index cursor proofPosition assertion
    result retained parents children request stackExact node resolved
  hypothesisTrace :
    SourceAddressedMandatoryHypothesesTrace context before ledger
      (sourceAssertionAddressSegment context before scannerAfter index assertion
        retained result)
      assertion.label assertion.hypotheses.length retained.length substitution
      assertion.hypotheses actuals parents substitution 0 retained.length
  finishStep :
    let segment := sourceAssertionAddressSegment context before scannerAfter
      index assertion retained result
    let sourceSpace := normalAssertionFinishPhaseSpaceAt context.scopeOwner
      context.proofOwner segment assertion.label assertion.hypotheses.length
      (retained.length + assertion.hypotheses.length) retained.length
      result.typecode assertion.formula.body
      assertion.frame.toRuntime.dj.toList.length
    let targetSpace := fireReflectiveSourceExecFact sourceSpace
      normalAssertionFinishDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies sourceSpace
        (reflectiveSourceExecExactTargetNativeType targetSpace).pred ∧
      normalDVNextPairRowAt context.scopeOwner context.proofOwner
            segment.currentProof assertion.label 0
            assertion.frame.toRuntime.dj.toList.length assertion.formula.body
            (segment.resultContext context.scopeOwner assertion.label
              result.typecode retained.length) ∈ targetSpace ∧
        normalDVReloadRowAt context.proofOwner segment.currentProof ∈
          targetSpace
  dvTrace :
    let segment := sourceAssertionAddressSegment context before scannerAfter
      index assertion retained result
    AddressedDVListsTrace source.callerFrame.toRuntime.dj.toList
      context.scopeOwner context.proofOwner segment.currentProof assertion.label
      assertion.frame.toRuntime.dj.toList.length assertion.formula.body
      (segment.resultContext context.scopeOwner assertion.label result.typecode
        retained.length)
      substitution assertion.frame.toRuntime.dj.toList 0

def sourceAssertionLaunchHypothesesBodyResumeBoundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor proofPosition : Nat)
    (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (request : SourceAssertionRequest context before scannerBefore scannerAfter
      occurrence index assertion)
    (stackExact : before.stack = retained ++ parents)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children)
    (presentation :
      calculusLanguageDefOfSourcePrefix? source = some target.1) :
    SourceAssertionLaunchHypothesesBodyResumeBoundary context before ledger
      scannerBefore scannerAfter occurrence index cursor proofPosition assertion
      result retained parents children request stackExact node resolved := by
  have projectionPresentation :
      calculusLanguageDefOfProjection? source.toProjection = some target.1 := by
    rw [← calculusLanguageDefOfSourcePrefix?_eq_runtime]
    exact presentation
  have projectionMember :
      assertion.toProjectionView ∈ source.toProjection.assertions :=
    List.mem_map_of_mem request.authored
  rcases (assertionRuleApplication_iff_instances source.toProjection target
      projectionPresentation projectionMember).mp node.application with
    ⟨instances, _resultTypecode⟩
  rcases (assertionSideEvidence_nonempty_iff_semantics source.toProjection
      target projectionPresentation instances).mp ⟨node.sideEvidence⟩ with
    ⟨essentialChecks, dvSemantics, _resultSemantics⟩
  have namesDistinct :
      DVPairNamesDistinct assertion.frame.toRuntime.dj.toList :=
    sourceAssertion_dvPairNamesDistinct source.toProjection target
      projectionPresentation projectionMember
  let segment := sourceAssertionAddressSegment context before scannerAfter
    index assertion retained result
  exact
    { endpoints := sourceAssertionLaunchBodyResumeBoundary context before
        ledger scannerBefore scannerAfter occurrence index cursor proofPosition
        assertion result retained parents children request stackExact node
        resolved presentation
      hypothesisTrace :=
        sourceAddressedMandatoryHypothesesTrace_of_semantics context before
          ledger scannerAfter index assertion retained result substitution
          instances essentialChecks resolved rfl stackExact
      finishStep :=
        normalAssertionFinishPhaseAt_inhabits_target_native_type
          context.scopeOwner context.proofOwner segment assertion.label
          assertion.hypotheses.length
          (retained.length + assertion.hypotheses.length) retained.length
          result.typecode assertion.formula.body
          assertion.frame.toRuntime.dj.toList.length
      dvTrace :=
        addressedDVListsTrace_of_semantics
          source.callerFrame.toRuntime.dj.toList context.scopeOwner
          context.proofOwner segment.currentProof assertion.label
          assertion.frame.toRuntime.dj.toList.length assertion.formula.body
          (segment.resultContext context.scopeOwner assertion.label
            result.typecode retained.length)
          substitution assertion.frame.toRuntime.dj.toList 0
          (Nat.zero_add _) namesDistinct dvSemantics }

/-- The target DV trace reflects the exact source frame-level DV condition. -/
theorem SourceAssertionLaunchHypothesesBodyResumeBoundary.reflects_dvSemantics
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence} {index cursor proofPosition : Nat}
    {assertion : SourceAssertion}
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    {retained parents : List Nat}
    {children : SourceGeneratedProvesForest source target actuals}
    {request : SourceAssertionRequest context before scannerBefore scannerAfter
      occurrence index assertion}
    {stackExact : before.stack = retained ++ parents}
    {node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution}
    {resolved : ResolvesForest before.nodes parents actuals children}
    (boundary : SourceAssertionLaunchHypothesesBodyResumeBoundary context
      before ledger scannerBefore scannerAfter occurrence index cursor
      proofPosition assertion result retained parents children request
      stackExact node resolved) :
    DVOKSemantics substitution source.callerFrame.toRuntime
      assertion.frame.toRuntime := by
  exact boundary.dvTrace.reflects_semantics

/-- The complete target trace reconstructs every source assertion side
condition: hypothesis instantiation, essential-hypothesis matching, and the
frame-level disjoint-variable obligation. -/
theorem SourceAssertionLaunchHypothesesBodyResumeBoundary.reflects_sideConditions
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence} {index cursor proofPosition : Nat}
    {assertion : SourceAssertion}
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    {retained parents : List Nat}
    {children : SourceGeneratedProvesForest source target actuals}
    {request : SourceAssertionRequest context before scannerBefore scannerAfter
      occurrence index assertion}
    {stackExact : before.stack = retained ++ parents}
    {node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution}
    {resolved : ResolvesForest before.nodes parents actuals children}
    (boundary : SourceAssertionLaunchHypothesesBodyResumeBoundary context
      before ledger scannerBefore scannerAfter occurrence index cursor
      proofPosition assertion result retained parents children request
      stackExact node resolved) :
    HypothesisInstances assertion.hypotheses actuals substitution ∧
      EssentialMatches substitution assertion.hypotheses actuals ∧
        DVOKSemantics substitution source.callerFrame.toRuntime
          assertion.frame.toRuntime := by
  exact ⟨boundary.hypothesisTrace.reflects_semantics.1,
    boundary.hypothesisTrace.reflects_semantics.2,
    boundary.dvTrace.reflects_semantics⟩

section AxiomAudit

#print axioms sourceAssertionLaunchHypothesesBodyResumeBoundary
#print axioms SourceAssertionLaunchHypothesesBodyResumeBoundary.reflects_dvSemantics
#print axioms SourceAssertionLaunchHypothesesBodyResumeBoundary.reflects_sideConditions

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionHypotheses
