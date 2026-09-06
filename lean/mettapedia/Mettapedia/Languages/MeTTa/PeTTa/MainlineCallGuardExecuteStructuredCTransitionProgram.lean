import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteSourceDerivedStructuredC

/-!
# Exportable generated StructuredC program for the hot call guard

The source-derived module constructs one transition body from the executor's
rule inventory.  This module supplies the C-facing external function types of
the hot ABI (projections, frame queries, decisions, and deltas) needed to
place that body in a complete StructuredC `Program`, and states the
source-derived program and its typing.  It adds no compiler, table, or
semantic operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTransitionProgram

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteSourceDerivedStructuredC

def statePointer : Pattern := namedPointerType "CettaPeTTaCallGuardHotStateV1"

def stateParameter : Pattern := parameter "state" statePointer

private def namedParameter (name typeName : String) : Pattern :=
  parameter name (namedType typeName)

private def external (name returnType : String) (parameters : List Pattern) : Pattern :=
  externalFunction name (namedType returnType) parameters

/-- The typed operand row of every decision, in ABI order. -/
def decisionParameters : Decision → List Pattern
  | .ownerDiffers => [namedParameter "family_owner" ownerType, namedParameter "owner" ownerType]
  | .revisionStale =>
      [namedParameter "family_owner" ownerType, namedParameter "owner" ownerType,
        namedParameter "family_revision" natType, namedParameter "snapshot" snapshotType]
  | .headWrong =>
      [namedParameter "family_owner" ownerType, namedParameter "owner" ownerType,
        namedParameter "family_revision" natType, namedParameter "snapshot" snapshotType,
        namedParameter "family_head" nameType, namedParameter "function" nameType]
  | .arityWrong | .familyCurrent =>
      [namedParameter "family_owner" ownerType, namedParameter "owner" ownerType,
        namedParameter "family_revision" natType, namedParameter "snapshot" snapshotType,
        namedParameter "family_head" nameType, namedParameter "function" nameType,
        namedParameter "family_arity" natType, namedParameter "source_arguments" termsType]
  | .planHeadMatches | .planHeadDiffers =>
      [namedParameter "declaration_function" nameType, namedParameter "function" nameType]
  | .rawEqual | .rawDiffers =>
      [namedParameter "source" termType, namedParameter "value" termType]
  | .exactType | .metatypeAccepts | .metatypeRejects =>
      [namedParameter "snapshot" snapshotType, namedParameter "value" termType,
        namedParameter "expected" termType]
  | .shapeMismatched =>
      [namedParameter "modes" modesType, namedParameter "sources" termsType,
        namedParameter "values" termsType]

private def callParameters : List Pattern :=
  [namedParameter "function" nameType, namedParameter "source_arguments" termsType,
    namedParameter "evaluated_arguments" termsType, namedParameter "result" termType]

private def declarationParameters : List Pattern :=
  [namedParameter "declaration_occurrence" natType,
    namedParameter "declaration_function" nameType, namedParameter "inputs" termsType,
    namedParameter "output" termType]

private def planParameters : List Pattern :=
  [namedParameter "occurrence" natType, namedParameter "plan_modes" modesType,
    namedParameter "result_mode" resultModeType] ++ declarationParameters

private def advanceParameters (expected : List Pattern) : List Pattern :=
  [namedParameter "snapshot" snapshotType, namedParameter "call" callType] ++ planParameters ++
    [namedParameter "remaining" plansType, namedParameter "index" indexType] ++ expected ++
    [namedParameter "modes" modesType, namedParameter "sources" termsType,
      namedParameter "values" termsType, namedParameter "accepted" acceptedType,
      namedParameter "events" eventsType]

private def rejectParameters (expected : List Pattern) : List Pattern :=
  [namedParameter "snapshot" snapshotType, namedParameter "call" callType,
    namedParameter "remaining" plansType, namedParameter "accepted" acceptedType,
    namedParameter "events" eventsType, namedParameter "occurrence" natType,
    namedParameter "index" indexType] ++ expected

private def installParameters (expected : List Pattern) : List Pattern :=
  [namedParameter "snapshot" snapshotType] ++ callParameters ++
    [namedParameter "remaining" plansType, namedParameter "accepted" acceptedType] ++
    declarationParameters ++
    [namedParameter "occurrence" natType, namedParameter "events" eventsType] ++ expected

private def expectedParameter : List Pattern := [namedParameter "expected" termType]

/-- The typed operand row of every delta after the state, in ABI order. -/
def deltaParameters : Delta → List Pattern
  | .recordFallback => [namedParameter "reason" tagType]
  | .beginPlans =>
      [namedParameter "snapshot" snapshotType] ++ callParameters ++
        [namedParameter "plans" plansType]
  | .finishExecuted =>
      [namedParameter "accepted" acceptedType, namedParameter "events" eventsType]
  | .rejectPlanHead =>
      [namedParameter "snapshot" snapshotType] ++ callParameters ++
        [namedParameter "remaining" plansType, namedParameter "accepted" acceptedType,
          namedParameter "events" eventsType, namedParameter "occurrence" natType]
  | .beginArguments =>
      [namedParameter "snapshot" snapshotType] ++ callParameters ++ planParameters ++
        [namedParameter "remaining" plansType, namedParameter "accepted" acceptedType,
          namedParameter "events" eventsType]
  | .evaluateCall =>
      [namedParameter "snapshot" snapshotType, namedParameter "call" callType] ++
        planParameters ++
        [namedParameter "remaining" plansType, namedParameter "accepted" acceptedType,
          namedParameter "events" eventsType]
  | .advanceRaw | .advanceUnchecked => advanceParameters []
  | .advanceExact | .advanceMetatype => advanceParameters expectedParameter
  | .rejectRaw | .rejectShape => rejectParameters []
  | .rejectMetatype => rejectParameters expectedParameter
  | .installUnchecked => installParameters []
  | .installExact | .installMetatype => installParameters expectedParameter
  | .rejectResult =>
      [namedParameter "snapshot" snapshotType] ++ callParameters ++
        [namedParameter "remaining" plansType, namedParameter "accepted" acceptedType,
          namedParameter "events" eventsType, namedParameter "occurrence" natType] ++
        expectedParameter

def frameQueryType : FrameQuery → String
  | .phase | .argumentModeTag | .resultModeTag => tagType
  | .compilationIsOutside | .plansAreEmpty | .argumentsAreFinished | .argumentsAreMismatched =>
      boolType

/-- The primitive catalog: every external the generated body may call. -/
def hotExternals : List Pattern :=
  projections.map (fun projection =>
    external projection.externalName (projectionType projection) [stateParameter]) ++
  frameQueries.map (fun query =>
    external query.externalName (frameQueryType query) [stateParameter]) ++
  decisions.map (fun decision =>
    external decision.externalName boolType (decisionParameters decision)) ++
  deltas.map (fun delta =>
    external delta.externalName unitType (stateParameter :: deltaParameters delta))

def generatedFunctionName : String :=
  "cetta_generated_petta_call_guard_hot_transition_v1"

def hotFunction (body : Pattern) : Pattern :=
  function generatedFunctionName (namedType tagType) [stateParameter] body

def hotProgram (body : Pattern) : Pattern := program hotExternals [hotFunction body]

/-- The generated hot function and program, stated from the inventory. -/
def generatedHotFunction : Pattern := hotFunction generatedHotBody

def generatedHotProgram : Pattern := hotProgram generatedHotBody

/-- The source-derived program: the generic chain's body in the same
wrapper. -/
def sourceDerivedHotProgram? : Option Pattern := sourceDerivedHotBody?.map hotProgram

theorem sourceDerivedHotProgram?_eq : sourceDerivedHotProgram? = some generatedHotProgram := by
  simp [sourceDerivedHotProgram?, sourceDerived_eq, generatedHotProgram]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem generatedHotProgram_typed :
    CarrierWellSorted.HasType StructuredC.language WellSorted.FreeTypeContext.empty []
      generatedHotProgram (.base "Program") := by
  apply CarrierWellSorted.checkHasType_sound
  decide +kernel

/-- The catalog names are the ABI names, in ABI order. -/
theorem hotExternals_count : hotExternals.length = 32 + 7 + 13 + 17 := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTransitionProgram
