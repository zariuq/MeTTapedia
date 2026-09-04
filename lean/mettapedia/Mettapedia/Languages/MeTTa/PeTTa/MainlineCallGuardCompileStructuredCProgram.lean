import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCTotalRealization

/-!
# Exportable generated StructuredC program for the cold call guard

The dispatcher module constructs one function from the exact decoded source
rewrite inventory.  This module supplies only the C-facing external function
types needed to place that generated function in a complete StructuredC
`Program`.  It does not add another compiler, decision table, or semantic
operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCProgram

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCDispatcher

private def statePointer : Pattern :=
  namedPointerType "CettaPeTTaCallGuardCompileStateV1"

private def namedParameter (name typeName : String) : Pattern :=
  parameter name (namedType typeName)

private def stateParameter : Pattern := parameter "state" statePointer

private def external (name returnType : String)
    (parameters : List Pattern) : Pattern :=
  externalFunction name (namedType returnType) parameters

private def stateExternal (name returnType : String) : Pattern :=
  external name returnType [stateParameter]

private def pOwner (name : String := "owner") : Pattern :=
  namedParameter name "CettaPeTTaCallGuardOwnerV1"

private def pNat (name : String) : Pattern :=
  namedParameter name "CettaPeTTaCallGuardNatV1"

private def pName (name : String) : Pattern :=
  namedParameter name "CettaPeTTaCallGuardNameV1"

private def pTerm (name : String) : Pattern :=
  namedParameter name "CettaPeTTaCallGuardTermV1"

private def pTerms (name : String) : Pattern :=
  namedParameter name "CettaPeTTaCallGuardTermsV1"

private def pDeclarations (name : String := "remaining") : Pattern :=
  namedParameter name "CettaPeTTaCallGuardDeclarationsV1"

private def pArgModes (name : String := "modes") : Pattern :=
  namedParameter name "CettaPeTTaCallGuardArgModesV1"

private def pPlans (name : String := "accepted") : Pattern :=
  namedParameter name "CettaPeTTaCallGuardPlansV1"

private def queryExternals : List Pattern := [
  stateExternal compilePhaseQuery "CettaTagV1",
  stateExternal declarationsAreEmptyQuery "CettaBoolV1",
  stateExternal inputCursorIsEmptyQuery "CettaBoolV1",
  stateExternal ownerProjection "CettaPeTTaCallGuardOwnerV1",
  stateExternal revisionProjection "CettaPeTTaCallGuardNatV1",
  stateExternal headProjection "CettaPeTTaCallGuardNameV1",
  stateExternal arityProjection "CettaPeTTaCallGuardNatV1",
  stateExternal acceptedProjection "CettaPeTTaCallGuardPlansV1",
  stateExternal remainingProjection "CettaPeTTaCallGuardDeclarationsV1",
  stateExternal occurrenceProjection "CettaPeTTaCallGuardNatV1",
  stateExternal declarationHeadProjection "CettaPeTTaCallGuardNameV1",
  stateExternal inputsProjection "CettaPeTTaCallGuardTermsV1",
  stateExternal outputProjection "CettaPeTTaCallGuardTermV1",
  stateExternal modesProjection "CettaPeTTaCallGuardArgModesV1",
  stateExternal inputHeadProjection "CettaPeTTaCallGuardTermV1",
  stateExternal inputTailProjection "CettaPeTTaCallGuardTermsV1",
  external termIsAtomQuery "CettaBoolV1" [pTerm "term"],
  external termIsUndefinedQuery "CettaBoolV1" [pTerm "term"],
  external termIsHoleQuery "CettaBoolV1" [pTerm "term"],
  external nameNotEqualQuery "CettaBoolV1"
    [pName "left", pName "right"],
  external arityDiffersQuery "CettaBoolV1"
    [pTerms "inputs", pNat "arity"],
  external arityMatchesQuery "CettaBoolV1"
    [pTerms "inputs", pNat "arity"],
  external inputIsCheckedQuery "CettaBoolV1" [pTerm "expected"],
  external inputIsOpenQuery "CettaBoolV1" [pTerm "expected"],
  external resultIsCheckedQuery "CettaBoolV1" [pTerm "expected"],
  external resultIsOpenQuery "CettaBoolV1" [pTerm "expected"]]

private def deltaExternals : List Pattern := [
  external setCompiledFamilyDelta "CettaUnitV1"
    [stateParameter, pOwner, pNat "revision", pName "head", pNat "arity",
      pPlans],
  external setCompileRunningDelta "CettaUnitV1"
    [stateParameter, pOwner, pNat "revision", pName "head", pNat "arity",
      pDeclarations, pPlans],
  external startCompileArgumentsDelta "CettaUnitV1"
    [stateParameter, pOwner, pNat "revision", pName "head", pNat "arity",
      pNat "occurrence", pName "declaration_head", pTerms "inputs",
      pTerm "output", pDeclarations, pTerms "input_cursor", pPlans],
  external appendArgumentModeDelta "CettaUnitV1"
    [stateParameter, pOwner, pNat "revision", pName "head", pNat "arity",
      pNat "occurrence", pName "declaration_head", pTerms "inputs",
      pTerm "output", pDeclarations, pTerms "input_cursor", pArgModes,
      pPlans,
      namedParameter "mode" "CettaPeTTaCallGuardArgModeTagV1",
      pTerm "payload"],
  external setCompileResultDelta "CettaUnitV1"
    [stateParameter, pOwner, pNat "revision", pName "head", pNat "arity",
      pNat "occurrence", pName "declaration_head", pTerms "inputs",
      pTerm "output", pDeclarations, pArgModes, pPlans],
  external appendCompiledPlanDelta "CettaUnitV1"
    [stateParameter, pOwner, pNat "revision", pName "head", pNat "arity",
      pDeclarations, pPlans, pNat "occurrence", pArgModes,
      pName "declaration_head", pTerms "inputs", pTerm "output",
      namedParameter "mode" "CettaPeTTaCallGuardResultModeTagV1",
      pTerm "payload"],
  external setOutsideFragmentDelta "CettaUnitV1" [stateParameter]]

/-- The exact native boundary of the generated cold function. -/
def primitiveExternals : List Pattern := queryExternals ++ deltaExternals

/-- One complete target program whose sole function is constructed from the
authenticated source rewrite inventory. -/
def generatedColdProgram : Pattern :=
  program primitiveExternals [generatedColdFunction]

theorem generatedColdProgram_shape :
    generatedColdProgram =
      program primitiveExternals [generatedColdFunction] := by
  rfl

/-- The exported wrapper is an actual StructuredC program. -/
theorem generatedColdProgram_target_typed :
    CarrierWellSorted.HasType StructuredC.language
      WellSorted.FreeTypeContext.empty [] generatedColdProgram
      (.base "Program") := by
  apply CarrierWellSorted.checkHasType_sound
  decide +kernel

/-- A source mutation that fails exact row decoding cannot produce the
exported function through the authenticated lowering. -/
theorem rejected_source_cannot_generate_exported_function
    {source : LanguageDef}
    (rejected : lowerDecodedColdFunction? source = none) :
    lowerDecodedColdFunction? source ≠ some generatedColdFunction := by
  simp [rejected]

#print axioms generatedColdProgram_target_typed
#print axioms rejected_source_cannot_generate_exported_function

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCProgram
