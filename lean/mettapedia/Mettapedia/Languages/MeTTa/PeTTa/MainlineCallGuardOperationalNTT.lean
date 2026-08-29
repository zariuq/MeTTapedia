import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.StructuralModal.Formula

/-!
# OSLF-derived native type for resumable PeTTa call guarding

This module interprets the authored interaction-bearing call-guard language,
not the older receipt-replay presentation.  Its finite environments are
executable semantic canaries: query answers are relation rows keyed by the
complete typed request, rather than truth values embedded in source actions.

The canaries distinguish witnesses, certified closure, open search, bounded
exhaustion, capture, explicit resumption, missing services, and wrong-request
responses.  Equal witnesses with different occurrence identities remain
different branches.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperationalNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.StructuralModal
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational

set_option autoImplicit false

private def atom (name : String) : Pattern :=
  .apply ("petta-call-guard-operational:demo:" ++ name) []

private def demoRun : Pattern := atom "run"
private def demoOtherRun : Pattern := atom "other-run"
private def demoCall : Pattern := atom "call"
private def demoBranch : Pattern := atom "branch"
private def demoRequest : Pattern := atom "request"
private def demoNextRequest : Pattern := atom "next-request"
private def demoOwner : Pattern := atom "owner"
private def demoRevision : Pattern := atom "revision"
private def demoFamily : Pattern := atom "family"
private def demoPlan : Pattern := atom "plan"
private def demoDeclaration : Pattern := atom "declaration"
private def demoPosition : Pattern := atom "position"
private def demoValue : Pattern := atom "value"
private def demoExpected : Pattern := atom "expected"
private def demoCoverage : Pattern := atom "coverage"
private def demoOccurrenceOne : Pattern := atom "occurrence-one"
private def demoOccurrenceTwo : Pattern := atom "occurrence-two"
private def demoResidual : Pattern := atom "residual"
private def demoBound : Pattern := atom "bound"
private def demoReceipt : Pattern := atom "receipt"
private def demoFault : Pattern := atom "fault"

def demoExactRequest : Pattern :=
  exactRequest [
    demoRun, demoCall, demoBranch, demoRequest, demoOwner, demoRevision,
    demoFamily, demoPlan, demoDeclaration, demoPosition, demoValue,
    demoExpected]

def otherExactRequest : Pattern :=
  exactRequest [
    demoOtherRun, demoCall, demoBranch, demoRequest, demoOwner, demoRevision,
    demoFamily, demoPlan, demoDeclaration, demoPosition, demoValue,
    demoExpected]

def demoMetatypeRequest : Pattern :=
  metatypeRequest [demoExactRequest, demoNextRequest, demoCoverage]

def exactStart : Pattern :=
  awaitExact demoExactRequest demoNextRequest emptyTrace

def metatypeStart : Pattern :=
  awaitMetatype demoMetatypeRequest
    (traceCons (observedEvent (requestOfExact demoExactRequest)
      (closedCompletion demoCoverage)) emptyTrace)

def exactSuccessEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == exactOccurrenceRelation then
      [[demoExactRequest, demoOccurrenceOne]]
    else
      []

def duplicateExactSuccessEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == exactOccurrenceRelation then
      [[demoExactRequest, demoOccurrenceOne],
       [demoExactRequest, demoOccurrenceTwo]]
    else
      []

def closedThenMetatypeSuccessEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == exactClosedEmptyRelation then
      [[demoExactRequest, demoCoverage]]
    else if relation == metatypeOccurrenceRelation then
      [[demoMetatypeRequest, demoOccurrenceOne]]
    else
      []

def exactOpenCapturedEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == exactOpenRelation then
      [[demoExactRequest, demoResidual]]
    else if relation == captureAdmittedRelation then
      [[demoExactRequest, demoResidual]]
    else
      []

def exactOpenCapturedAndResumeEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == exactOpenRelation then
      [[demoExactRequest, demoResidual]]
    else if relation == captureAdmittedRelation then
      [[demoExactRequest, demoResidual]]
    else if relation == resumeRequestedRelation then
      [[demoExactRequest, demoResidual]]
    else
      []

def exactOpenUncapturedEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == exactOpenUncapturedRelation then
      [[demoExactRequest]]
    else
      []

def exactExhaustedUncapturedEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == exactExhaustedUncapturedRelation then
      [[demoExactRequest, demoBound, demoReceipt]]
    else
      []

def exactCancelledEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == exactCancelledRelation then
      [[demoExactRequest]]
    else
      []

def exactFaultEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == exactFaultRelation then
      [[demoExactRequest, demoFault]]
    else
      []

def wrongRequestEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == exactOccurrenceRelation then
      [[otherExactRequest, demoOccurrenceOne]]
    else
      []

def emptyRelationEnv : RelationEnv where
  tuples := fun _ _ => []

def callGuardOperationalOSLFUsing (relationEnv : RelationEnv) :=
  langOSLFUsing relationEnv language "Control"

def callGuardOperationalOSLF :=
  callGuardOperationalOSLFUsing exactSuccessEnv

theorem callGuardOperational_galois (relationEnv : RelationEnv) :
    GaloisConnection
      (langDiamondUsing relationEnv language)
      (langBoxUsing relationEnv language) :=
  langGaloisUsing relationEnv language

theorem exact_request_phase_crossing :
    ("petta-call-guard-operational:request-exact", "ExactRequest", "Request") ∈
      unaryCrossings language := by
  decide

theorem open_completion_crossing :
    ("petta-call-guard-operational:completion-open", "Residual", "Completion") ∈
      unaryCrossings language := by
  decide

theorem no_invented_completion_crossing :
    ("petta-call-guard-operational:completion-refuted", "Residual", "Completion") ∉
      unaryCrossings language := by
  decide

private def exactAcceptedOne : Pattern :=
  halted (accepted (requestOfExact demoExactRequest) demoOccurrenceOne)
    (traceCons (observedEvent (requestOfExact demoExactRequest)
      (occurrenceCompletion demoOccurrenceOne)) emptyTrace)

private def exactAcceptedTwo : Pattern :=
  halted (accepted (requestOfExact demoExactRequest) demoOccurrenceTwo)
    (traceCons (observedEvent (requestOfExact demoExactRequest)
      (occurrenceCompletion demoOccurrenceTwo)) emptyTrace)

private def metatypePending : Pattern :=
  awaitMetatype demoMetatypeRequest
    (traceCons (observedEvent (requestOfExact demoExactRequest)
      (closedCompletion demoCoverage)) emptyTrace)

private def metatypeAccepted : Pattern :=
  halted (accepted (requestOfMetatype demoMetatypeRequest) demoOccurrenceOne)
    (traceCons (observedEvent (requestOfMetatype demoMetatypeRequest)
      (occurrenceCompletion demoOccurrenceOne))
      (traceCons (observedEvent (requestOfExact demoExactRequest)
        (closedCompletion demoCoverage)) emptyTrace))

private def exactOpenCapturedState : Pattern :=
  exactCaptured demoExactRequest demoNextRequest
    (openCompletion demoResidual)
    (traceCons (observedEvent (requestOfExact demoExactRequest)
      (openCompletion demoResidual)) emptyTrace)

private def exactOpenUncapturedState : Pattern :=
  exactUncaptured demoExactRequest demoNextRequest openUncapturedCompletion
    (traceCons (observedEvent (requestOfExact demoExactRequest)
      openUncapturedCompletion) emptyTrace)

private def exactExhaustedUncapturedState : Pattern :=
  exactUncaptured demoExactRequest demoNextRequest
    (exhaustedUncapturedCompletion demoBound demoReceipt)
    (traceCons (observedEvent (requestOfExact demoExactRequest)
      (exhaustedUncapturedCompletion demoBound demoReceipt)) emptyTrace)

private def exactCancelledState : Pattern :=
  halted (cancelled (requestOfExact demoExactRequest))
    (traceCons (observedEvent (requestOfExact demoExactRequest)
      cancelledCompletion) emptyTrace)

private def exactFaultState : Pattern :=
  halted (resourceFault (requestOfExact demoExactRequest) demoFault)
    (traceCons (observedEvent (requestOfExact demoExactRequest)
      (faultCompletion demoFault)) emptyTrace)

private def exactResumed : Pattern :=
  awaitExact demoExactRequest demoNextRequest
    (traceCons (resumedEvent (requestOfExact demoExactRequest) demoResidual)
      (traceCons (observedEvent (requestOfExact demoExactRequest)
        (openCompletion demoResidual)) emptyTrace))

theorem exact_success_step_exact :
    rewriteAt (engineBasePremises exactSuccessEnv) language 1 exactStart =
      [exactAcceptedOne] := by
  decide +kernel

theorem duplicate_occurrences_step_exact :
    rewriteAt (engineBasePremises duplicateExactSuccessEnv) language 1
        exactStart =
      [exactAcceptedOne, exactAcceptedTwo] := by
  decide +kernel

theorem exact_closed_empty_step_exact :
    rewriteAt (engineBasePremises closedThenMetatypeSuccessEnv) language 1
        exactStart =
      [metatypePending] := by
  decide +kernel

theorem metatype_success_step_exact :
    rewriteAt (engineBasePremises closedThenMetatypeSuccessEnv) language 1
        metatypeStart =
      [metatypeAccepted] := by
  decide +kernel

theorem exact_open_capture_step_exact :
    rewriteAt (engineBasePremises exactOpenCapturedEnv) language 1 exactStart =
      [exactOpenCapturedState] := by
  decide +kernel

theorem captured_open_without_resume_is_suspended :
    rewriteAt (engineBasePremises exactOpenCapturedEnv) language 1
        exactOpenCapturedState = [] := by
  decide +kernel

theorem explicit_resume_step_exact :
    rewriteAt (engineBasePremises exactOpenCapturedAndResumeEnv) language 1
        exactOpenCapturedState =
      [exactResumed] := by
  decide +kernel

theorem exact_open_uncaptured_step_exact :
    rewriteAt (engineBasePremises exactOpenUncapturedEnv) language 1 exactStart =
      [exactOpenUncapturedState] := by
  decide +kernel

theorem exact_open_uncaptured_is_normal :
    rewriteAt (engineBasePremises exactOpenUncapturedEnv) language 1
        exactOpenUncapturedState = [] := by
  decide +kernel

theorem exact_exhausted_uncaptured_step_exact :
    rewriteAt (engineBasePremises exactExhaustedUncapturedEnv) language 1
        exactStart =
      [exactExhaustedUncapturedState] := by
  decide +kernel

theorem exact_exhausted_uncaptured_is_normal :
    rewriteAt (engineBasePremises exactExhaustedUncapturedEnv) language 1
        exactExhaustedUncapturedState = [] := by
  decide +kernel

theorem exact_cancelled_step_exact :
    rewriteAt (engineBasePremises exactCancelledEnv) language 1 exactStart =
      [exactCancelledState] := by
  decide +kernel

theorem exact_fault_step_exact :
    rewriteAt (engineBasePremises exactFaultEnv) language 1 exactStart =
      [exactFaultState] := by
  decide +kernel

theorem open_does_not_enable_metatype :
    metatypePending ∉
      rewriteAt (engineBasePremises exactOpenCapturedEnv) language 1 exactStart := by
  decide +kernel

theorem cancelled_does_not_enable_metatype :
    metatypePending ∉
      rewriteAt (engineBasePremises exactCancelledEnv) language 1 exactStart := by
  decide +kernel

theorem fault_does_not_enable_metatype :
    metatypePending ∉
      rewriteAt (engineBasePremises exactFaultEnv) language 1 exactStart := by
  decide +kernel

theorem exhausted_does_not_refute :
    halted (rejected (requestOfExact demoExactRequest)) emptyTrace ∉
      rewriteAt (engineBasePremises exactExhaustedUncapturedEnv) language 1
        exactStart := by
  decide +kernel

theorem wrong_request_response_is_stuck :
    rewriteAt (engineBasePremises wrongRequestEnv) language 1 exactStart = [] := by
  decide +kernel

theorem missing_service_is_stuck :
    rewriteAt (engineBasePremises emptyRelationEnv) language 1 exactStart = [] := by
  decide +kernel

def acceptedCompletionFormula : Formula :=
  .diamond (.headed "petta-call-guard-operational:halted" [
    .headed "petta-call-guard-operational:accepted" [.top, .top],
    .top])

theorem exact_success_inhabits_derived_native_type :
    satisfiesUsing exactSuccessEnv language acceptedCompletionFormula
      exactStart := by
  have executable : exactAcceptedOne ∈
      rewriteAt (engineBasePremises exactSuccessEnv) language 1 exactStart := by
    rw [exact_success_step_exact]
    simp
  have reduction :
      langReducesUsing exactSuccessEnv language exactStart exactAcceptedOne :=
    (langReducesUsing_iff_execUsing exactSuccessEnv language _ _).2
      ⟨1, executable⟩
  refine ⟨⟨(exactStart, exactAcceptedOne), reduction⟩, rfl, ?_⟩
  refine ⟨[accepted (requestOfExact demoExactRequest) demoOccurrenceOne,
      traceCons (observedEvent (requestOfExact demoExactRequest)
        (occurrenceCompletion demoOccurrenceOne)) emptyTrace], rfl, ?_⟩
  refine ⟨⟨[requestOfExact demoExactRequest, demoOccurrenceOne], rfl, ?_⟩,
    ?_⟩
  · simp [satisfiesAllOver, satisfiesOver]
  · simp [satisfiesAllOver, satisfiesOver]

#print axioms callGuardOperational_galois
#print axioms exact_request_phase_crossing
#print axioms no_invented_completion_crossing
#print axioms exact_success_step_exact
#print axioms duplicate_occurrences_step_exact
#print axioms exact_closed_empty_step_exact
#print axioms metatype_success_step_exact
#print axioms exact_open_capture_step_exact
#print axioms captured_open_without_resume_is_suspended
#print axioms explicit_resume_step_exact
#print axioms exact_open_uncaptured_step_exact
#print axioms exact_exhausted_uncaptured_step_exact
#print axioms exact_cancelled_step_exact
#print axioms exact_fault_step_exact
#print axioms open_does_not_enable_metatype
#print axioms cancelled_does_not_enable_metatype
#print axioms fault_does_not_enable_metatype
#print axioms exhausted_does_not_refute
#print axioms wrong_request_response_is_stuck
#print axioms missing_service_is_stuck
#print axioms exact_success_inhabits_derived_native_type

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperationalNTT
