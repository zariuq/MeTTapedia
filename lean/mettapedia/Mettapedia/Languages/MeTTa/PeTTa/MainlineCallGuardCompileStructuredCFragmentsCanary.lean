import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments

/-!
# Discriminating controls for source-derived cold StructuredC fragments

The positive controls require the expected query and exact-delta names to be
present in the generated syntax.  The negative controls change authenticated
source structure, request an unsupported family, and supply invented target
syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragmentsCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTransitionFamily
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments

def skipHeadWithoutPremise : RewriteRule :=
  { skipHeadTransition with premises := [] }

def argumentsFinishedChangedRight : RewriteRule :=
  { argumentsFinishedTransition with
    right := argumentsFinishedTransition.left }

def openInputWithoutPremise : RewriteRule :=
  { openInputTransition with premises := [] }

theorem live_rows_lower :
    lowerDecodedTransition? argumentsFinishedTransition =
        some argumentsFinishedBody ∧
      lowerDecodedTransition? skipHeadTransition = some skipHeadBody ∧
      lowerDecodedTransition? openInputTransition = some openInputBody := by
  exact ⟨lower_argumentsFinishedTransition,
    lower_skipHeadTransition, lower_openInputTransition⟩

private theorem skipHeadWithoutPremise_decode_none :
    decodeTransition? skipHeadWithoutPremise = none := by
  simp [decodeTransition?, familyForName?, skipHeadWithoutPremise,
    CompileTransitionFamily.rewrite, finishTransition, skipHeadTransition]

private theorem argumentsFinishedChangedRight_decode_none :
    decodeTransition? argumentsFinishedChangedRight = none := by
  simp [decodeTransition?, familyForName?, argumentsFinishedChangedRight,
    CompileTransitionFamily.rewrite, finishTransition, skipHeadTransition,
    skipArityTransition, beginDeclarationTransition,
    argumentsFinishedTransition, compileArguments, compileResult]

private theorem openInputWithoutPremise_decode_none :
    decodeTransition? openInputWithoutPremise = none := by
  simp [decodeTransition?, familyForName?, openInputWithoutPremise,
    CompileTransitionFamily.rewrite, finishTransition, skipHeadTransition,
    skipArityTransition, beginDeclarationTransition,
    argumentsFinishedTransition, rawInputTransition, undefinedInputTransition,
    holeInputTransition, checkedInputTransition, openInputTransition,
    inputStepTransition]

theorem same_name_changed_rows_are_rejected :
    lowerDecodedTransition? skipHeadWithoutPremise = none ∧
      lowerDecodedTransition? argumentsFinishedChangedRight = none ∧
      lowerDecodedTransition? openInputWithoutPremise = none := by
  unfold lowerDecodedTransition?
  rw [skipHeadWithoutPremise_decode_none,
    argumentsFinishedChangedRight_decode_none,
    openInputWithoutPremise_decode_none]
  decide

theorem every_family_is_covered :
    allMatchedFamilyBodies.length = 15 ∧
      lowerDecodedLanguage? language = some allMatchedFamilyBodies := by
  exact ⟨allMatchedFamilyBodies_length, language_lowers_all_families⟩

theorem required_controls_are_load_bearing :
    (setCompileResultDelta, 0) ∈ argumentsFinishedBody.constructorRefs ∧
      (nameNotEqualQuery, 0) ∈ skipHeadBody.constructorRefs ∧
      (setCompileRunningDelta, 0) ∈ skipHeadBody.constructorRefs ∧
      (inputIsOpenQuery, 0) ∈ openInputBody.constructorRefs ∧
      (setOutsideFragmentDelta, 0) ∈ openInputBody.constructorRefs := by
  decide +kernel

theorem complete_control_surface_is_load_bearing :
    (setCompiledFamilyDelta, 0) ∈ finishBody.constructorRefs ∧
      (arityDiffersQuery, 0) ∈ skipArityBody.constructorRefs ∧
      (arityMatchesQuery, 0) ∈ beginDeclarationBody.constructorRefs ∧
      (startCompileArgumentsDelta, 0) ∈
        beginDeclarationBody.constructorRefs ∧
      (appendArgumentModeDelta, 0) ∈ rawInputBody.constructorRefs ∧
      (inputIsCheckedQuery, 0) ∈ checkedInputBody.constructorRefs ∧
      (appendCompiledPlanDelta, 0) ∈ undefinedResultBody.constructorRefs ∧
      (resultIsCheckedQuery, 0) ∈ checkedResultBody.constructorRefs ∧
      (resultIsOpenQuery, 0) ∈ openResultBody.constructorRefs := by
  decide +kernel

/-- These two source rows deliberately share a matched body because their
different literal patterns are the responsibility of the generated matcher.
This canary prevents the body inventory from being mistaken for the whole
source-to-target lowering. -/
theorem matching_remains_load_bearing :
    undefinedInputBody = holeInputBody ∧
      undefinedInputTransition ≠ holeInputTransition := by
  constructor
  · rfl
  · simp [undefinedInputTransition, holeInputTransition,
      inputStepTransition]

def inventedTarget : Pattern :=
  node "structured-c:invented-call-guard-statements"

theorem invented_target_is_rejected :
    CarrierWellSorted.checkHasType StructuredC.language
      WellSorted.FreeTypeContext.empty [] inventedTarget
      (.base "Statements") = false := by
  decide +kernel

#print axioms live_rows_lower
#print axioms same_name_changed_rows_are_rejected
#print axioms every_family_is_covered
#print axioms required_controls_are_load_bearing
#print axioms complete_control_surface_is_load_bearing
#print axioms matching_remains_load_bearing
#print axioms invented_target_is_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragmentsCanary
