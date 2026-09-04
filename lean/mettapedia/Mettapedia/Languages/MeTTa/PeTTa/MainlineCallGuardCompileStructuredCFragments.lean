import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTransitionFamily
import Mettapedia.GSLT.LanguageDef.StructuredCBuilder
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted

/-!
# Source-derived StructuredC fragments for the cold call-guard compiler

This module begins the cold lowering after exact rewrite-row authentication.
Each fragment is the body of one already matched source row: the source matcher
has bound the row's metavariables, while the generated StructuredC syntax makes
the premise test and exact state delta explicit.

All fifteen cold families are lowered.  The inventory includes three especially
discriminating shapes:

* a premise-free phase change;
* a relation-guarded declaration skip;
* a relation-guarded early exit.

The external calls below are deliberately narrow.  Query calls expose exactly
one authored source predicate.  Delta calls receive every field of the selected
target state, or select one fixed terminal result.  None chooses a declaration,
mode, plan, family, result, or branch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTransitionFamily

def advancedOutcome : String :=
  "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"

def compiledOutcome : String :=
  "CETTA_PETTA_CALL_GUARD_COMPILED_V1"

def outsideFragmentOutcome : String :=
  "CETTA_PETTA_CALL_GUARD_FALLBACK_OUTSIDE_FRAGMENT_V1"

/-- Exact implementation of the authored `PeTTaCallGuardNotEqual` query. -/
def nameNotEqualQuery : String :=
  "cetta_petta_call_guard_name_not_equal_v1"

/-- Exact implementation of the authored `PeTTaCallGuardArityDiffers` query. -/
def arityDiffersQuery : String :=
  "cetta_petta_call_guard_arity_differs_v1"

/-- Exact implementation of the authored `PeTTaCallGuardArityMatches` query. -/
def arityMatchesQuery : String :=
  "cetta_petta_call_guard_arity_matches_v1"

/-- Exact implementation of the authored `PeTTaCallGuardCheckedInput` query. -/
def inputIsCheckedQuery : String :=
  "cetta_petta_call_guard_input_is_checked_v1"

/-- Exact implementation of the authored `PeTTaCallGuardOpenInput` query. -/
def inputIsOpenQuery : String :=
  "cetta_petta_call_guard_input_is_open_v1"

/-- Exact implementation of the authored `PeTTaCallGuardCheckedResult` query. -/
def resultIsCheckedQuery : String :=
  "cetta_petta_call_guard_result_is_checked_v1"

/-- Exact implementation of the authored `PeTTaCallGuardOpenResult` query. -/
def resultIsOpenQuery : String :=
  "cetta_petta_call_guard_result_is_open_v1"

/-- Replace the cold state by the completed family explicitly supplied by the
source row. -/
def setCompiledFamilyDelta : String :=
  "cetta_petta_call_guard_set_compiled_family_v1"

/-- Replace the cold state by the explicitly supplied `compileRunning` row. -/
def setCompileRunningDelta : String :=
  "cetta_petta_call_guard_set_compile_running_v1"

/-- Enter argument compilation for one explicitly supplied declaration.  The
new cursor is the supplied input row and the new mode row is fixed empty. -/
def startCompileArgumentsDelta : String :=
  "cetta_petta_call_guard_start_compile_arguments_v1"

/-- Advance an argument cursor while appending the explicitly supplied mode. -/
def appendArgumentModeDelta : String :=
  "cetta_petta_call_guard_append_argument_mode_v1"

/-- Replace the cold state by the explicitly supplied `compileResult` row. -/
def setCompileResultDelta : String :=
  "cetta_petta_call_guard_set_compile_result_v1"

/-- Return to `compileRunning` while appending the explicitly supplied plan. -/
def appendCompiledPlanDelta : String :=
  "cetta_petta_call_guard_append_compiled_plan_v1"

/-- Replace the cold state by the one fixed outside-fragment result. -/
def setOutsideFragmentDelta : String :=
  "cetta_petta_call_guard_set_outside_fragment_v1"

def noModePayload : String :=
  "CETTA_PETTA_CALL_GUARD_NO_MODE_PAYLOAD_V1"

def rawArgumentMode : String :=
  "CETTA_PETTA_CALL_GUARD_ARGUMENT_RAW_V1"

def uncheckedArgumentMode : String :=
  "CETTA_PETTA_CALL_GUARD_ARGUMENT_UNCHECKED_V1"

def checkedArgumentMode : String :=
  "CETTA_PETTA_CALL_GUARD_ARGUMENT_CHECKED_V1"

def uncheckedResultMode : String :=
  "CETTA_PETTA_CALL_GUARD_RESULT_UNCHECKED_V1"

def checkedResultMode : String :=
  "CETTA_PETTA_CALL_GUARD_RESULT_CHECKED_V1"

def undefinedTerm : String :=
  "CETTA_PETTA_CALL_GUARD_TERM_UNDEFINED_V1"

def holeTerm : String :=
  "CETTA_PETTA_CALL_GUARD_TERM_HOLE_V1"

def atomTerm : String :=
  "CETTA_PETTA_CALL_GUARD_TERM_ATOM_V1"

private def variableExpressions (names : List String) : List Pattern :=
  names.map variableExpression

private def transitionBody (delta : String) (arguments : List Pattern)
    (outcome : String := advancedOutcome) : Pattern :=
  statements [effect (call delta arguments), returnSymbol outcome]

private def guardedTransitionBody (queryName : String)
    (queryArguments : List Pattern) (delta : String)
    (deltaArguments : List Pattern)
    (outcome : String := advancedOutcome) : Pattern :=
  statements [ifThenElse
    (call queryName queryArguments)
    (transitionBody delta deltaArguments outcome)
    (statements [])]

/-- Exhausting the declaration row constructs the complete family from the
explicit owner, revision, call shape, and accumulated plan row. -/
def finishBody : Pattern :=
  transitionBody setCompiledFamilyDelta (variableExpressions
    ["state", "owner", "revision", "head", "arity", "accepted"])
    compiledOutcome

/-- The finish fragment exposes its complete effect/return statement spine. -/
theorem finishBody_shape : finishBody = statements [
    effect (call setCompiledFamilyDelta
      (["state", "owner", "revision", "head", "arity", "accepted"].map
        variableExpression)),
    returnSymbol compiledOutcome] := by
  rfl

/-- The premise-free `compileArguments ... [] ...` to `compileResult` delta.
All fields of the source row's right-hand state are explicit call operands. -/
def argumentsFinishedBody : Pattern :=
  transitionBody setCompileResultDelta (variableExpressions
    [ "state", "owner", "revision", "head", "arity", "occurrence"
    , "declaration_head", "inputs", "output", "remaining", "modes"
    , "accepted" ])

theorem argumentsFinishedBody_shape : argumentsFinishedBody = statements [
    effect (call setCompileResultDelta
      ([ "state", "owner", "revision", "head", "arity", "occurrence"
       , "declaration_head", "inputs", "output", "remaining", "modes"
       , "accepted" ].map variableExpression)),
    returnSymbol advancedOutcome] := by
  rfl

/-- The `notEqual declarationHead head` premise remains visible control.  On
success, the exact `compileRunning` target fields are supplied to the delta;
on failure this row contributes no statement effect and the later fold may try
the next authored row. -/
def skipHeadCondition : Pattern :=
  call nameNotEqualQuery
    (variableExpressions ["declaration_head", "head"])

def skipHeadSuccess : Pattern :=
  transitionBody setCompileRunningDelta (variableExpressions
    ["state", "owner", "revision", "head", "arity", "remaining", "accepted"])

theorem skipHeadSuccess_shape : skipHeadSuccess = statements [
    effect (call setCompileRunningDelta
      (["state", "owner", "revision", "head", "arity", "remaining",
        "accepted"].map variableExpression)),
    returnSymbol advancedOutcome] := by
  rfl

def skipHeadDecision : Pattern :=
  ifThenElse skipHeadCondition skipHeadSuccess (statements [])

def skipHeadBody : Pattern :=
  statements [skipHeadDecision]

/-- The skip-head fragment retains both the authored disequality guard and its
complete effect/return successor spine. -/
theorem skipHeadBody_shape : skipHeadBody = statements [
    ifThenElse
      (call nameNotEqualQuery
        (["declaration_head", "head"].map variableExpression))
      (statements [
        effect (call setCompileRunningDelta
          (["state", "owner", "revision", "head", "arity", "remaining",
            "accepted"].map variableExpression)),
        returnSymbol advancedOutcome])
      (statements [])] := by
  rfl

/-- A declaration with the wrong arity is discarded while retaining its
authored head as the call head carried by this source row. -/
def skipArityCondition : Pattern :=
  call arityDiffersQuery (variableExpressions ["inputs", "arity"])

def skipAritySuccess : Pattern :=
  transitionBody setCompileRunningDelta (variableExpressions
    [ "state", "owner", "revision", "declaration_head", "arity"
    , "remaining", "accepted" ])

def skipArityDecision : Pattern :=
  ifThenElse skipArityCondition skipAritySuccess (statements [])

def skipArityBody : Pattern :=
  statements [skipArityDecision]

theorem skipAritySuccess_shape : skipAritySuccess = statements [
    effect (call setCompileRunningDelta
      (["state", "owner", "revision", "declaration_head", "arity",
        "remaining", "accepted"].map variableExpression)),
    returnSymbol advancedOutcome] := by
  rfl

/-- A matching declaration starts argument compilation with its original input
row as cursor and an empty accumulated mode row. -/
def beginDeclarationCondition : Pattern :=
  call arityMatchesQuery (variableExpressions ["inputs", "arity"])

def beginDeclarationSuccess : Pattern :=
  transitionBody startCompileArgumentsDelta (variableExpressions
    [ "state", "owner", "revision", "declaration_head", "arity"
    , "occurrence", "declaration_head", "inputs", "output", "remaining"
    , "inputs", "accepted" ])

def beginDeclarationDecision : Pattern :=
  ifThenElse beginDeclarationCondition beginDeclarationSuccess (statements [])

def beginDeclarationBody : Pattern :=
  statements [beginDeclarationDecision]

theorem beginDeclarationSuccess_shape : beginDeclarationSuccess = statements [
    effect (call startCompileArgumentsDelta
      (["state", "owner", "revision", "declaration_head", "arity",
        "occurrence", "declaration_head", "inputs", "output", "remaining",
        "inputs", "accepted"].map variableExpression)),
    returnSymbol advancedOutcome] := by
  rfl

private def appendInputModeBody (mode payload : Pattern) : Pattern :=
  transitionBody appendArgumentModeDelta
    (variableExpressions
      [ "state", "owner", "revision", "head", "arity", "occurrence"
      , "declaration_head", "inputs", "output", "remaining", "input_cursor"
      , "modes", "accepted" ] ++ [mode, payload])

def rawInputBody : Pattern :=
  appendInputModeBody (symbol rawArgumentMode) (symbol noModePayload)

/-- The raw-atom family exposes the exact generated effect and return spine.
The mode tag and payload are literal target operands; every source-state field
remains an explicit variable operand. -/
theorem rawInputBody_shape : rawInputBody = statements [
    effect (call appendArgumentModeDelta
      (([ "state", "owner", "revision", "head", "arity", "occurrence"
        , "declaration_head", "inputs", "output", "remaining"
        , "input_cursor", "modes", "accepted" ].map variableExpression) ++
        [symbol rawArgumentMode, symbol noModePayload])),
    returnSymbol advancedOutcome] := by
  rfl

def undefinedInputBody : Pattern :=
  appendInputModeBody (symbol uncheckedArgumentMode) (symbol noModePayload)

theorem undefinedInputBody_shape : undefinedInputBody = statements [
    effect (call appendArgumentModeDelta
      (([ "state", "owner", "revision", "head", "arity", "occurrence"
        , "declaration_head", "inputs", "output", "remaining"
        , "input_cursor", "modes", "accepted" ].map variableExpression) ++
        [symbol uncheckedArgumentMode, symbol noModePayload])),
    returnSymbol advancedOutcome] := by
  rfl

def holeInputBody : Pattern :=
  appendInputModeBody (symbol uncheckedArgumentMode) (symbol noModePayload)

theorem holeInputBody_shape : holeInputBody = statements [
    effect (call appendArgumentModeDelta
      (([ "state", "owner", "revision", "head", "arity", "occurrence"
        , "declaration_head", "inputs", "output", "remaining"
        , "input_cursor", "modes", "accepted" ].map variableExpression) ++
        [symbol uncheckedArgumentMode, symbol noModePayload])),
    returnSymbol advancedOutcome] := by
  rfl

def checkedInputBody : Pattern :=
  guardedTransitionBody inputIsCheckedQuery
    (variableExpressions ["expected"])
    appendArgumentModeDelta
    (variableExpressions
      [ "state", "owner", "revision", "head", "arity", "occurrence"
      , "declaration_head", "inputs", "output", "remaining", "input_cursor"
      , "modes", "accepted" ] ++
      [symbol checkedArgumentMode, variableExpression "expected"])

def checkedInputSuccessBody : Pattern :=
  statements [
    effect (call appendArgumentModeDelta
      (([ "state", "owner", "revision", "head", "arity", "occurrence"
        , "declaration_head", "inputs", "output", "remaining"
        , "input_cursor", "modes", "accepted" ].map variableExpression) ++
        [symbol checkedArgumentMode, variableExpression "expected"])),
    returnSymbol advancedOutcome]

def checkedInputDecision : Pattern :=
  ifThenElse (call inputIsCheckedQuery [variableExpression "expected"])
    checkedInputSuccessBody (statements [])

theorem checkedInputBody_shape : checkedInputBody =
    statements [checkedInputDecision] := by
  rfl

/-- The open-input premise remains visible control.  Its successful branch has
one fixed semantic target, so the delta call cannot choose an outcome. -/
def openInputBody : Pattern :=
  guardedTransitionBody inputIsOpenQuery
    (variableExpressions ["expected"])
    setOutsideFragmentDelta (variableExpressions ["state"])
    outsideFragmentOutcome

def openInputSuccessBody : Pattern :=
  statements [effect (call setOutsideFragmentDelta
      [variableExpression "state"]),
    returnSymbol outsideFragmentOutcome]

def openInputDecision : Pattern :=
  ifThenElse (call inputIsOpenQuery [variableExpression "expected"])
    openInputSuccessBody (statements [])

theorem openInputBody_shape : openInputBody =
    statements [openInputDecision] := by
  rfl

private def appendResultPlanBody (output mode payload : Pattern) : Pattern :=
  transitionBody appendCompiledPlanDelta
    (variableExpressions
      [ "state", "owner", "revision", "head", "arity", "remaining"
      , "accepted", "occurrence", "modes", "declaration_head", "inputs" ] ++
      [output, mode, payload])

def undefinedResultBody : Pattern :=
  appendResultPlanBody (symbol undefinedTerm)
    (symbol uncheckedResultMode) (symbol noModePayload)

def holeResultBody : Pattern :=
  appendResultPlanBody (symbol holeTerm)
    (symbol uncheckedResultMode) (symbol noModePayload)

def atomResultBody : Pattern :=
  appendResultPlanBody (symbol atomTerm)
    (symbol uncheckedResultMode) (symbol noModePayload)

theorem undefinedResultBody_shape : undefinedResultBody = statements [
    effect (call appendCompiledPlanDelta
      (([ "state", "owner", "revision", "head", "arity", "remaining"
        , "accepted", "occurrence", "modes", "declaration_head", "inputs"
        ].map variableExpression) ++
        [symbol undefinedTerm, symbol uncheckedResultMode,
          symbol noModePayload])),
    returnSymbol advancedOutcome] := by
  rfl

theorem holeResultBody_shape : holeResultBody = statements [
    effect (call appendCompiledPlanDelta
      (([ "state", "owner", "revision", "head", "arity", "remaining"
        , "accepted", "occurrence", "modes", "declaration_head", "inputs"
        ].map variableExpression) ++
        [symbol holeTerm, symbol uncheckedResultMode,
          symbol noModePayload])),
    returnSymbol advancedOutcome] := by
  rfl

theorem atomResultBody_shape : atomResultBody = statements [
    effect (call appendCompiledPlanDelta
      (([ "state", "owner", "revision", "head", "arity", "remaining"
        , "accepted", "occurrence", "modes", "declaration_head", "inputs"
        ].map variableExpression) ++
        [symbol atomTerm, symbol uncheckedResultMode,
          symbol noModePayload])),
    returnSymbol advancedOutcome] := by
  rfl

def checkedResultBody : Pattern :=
  guardedTransitionBody resultIsCheckedQuery
    (variableExpressions ["output"])
    appendCompiledPlanDelta
    (variableExpressions
      [ "state", "owner", "revision", "head", "arity", "remaining"
      , "accepted", "occurrence", "modes", "declaration_head", "inputs"
      , "output" ] ++
      [symbol checkedResultMode, variableExpression "output"])

def checkedResultSuccessBody : Pattern :=
  statements [effect (call appendCompiledPlanDelta
    (([ "state", "owner", "revision", "head", "arity", "remaining"
      , "accepted", "occurrence", "modes", "declaration_head", "inputs"
      , "output" ].map variableExpression) ++
      [symbol checkedResultMode, variableExpression "output"])),
    returnSymbol advancedOutcome]

def checkedResultDecision : Pattern :=
  ifThenElse (call resultIsCheckedQuery [variableExpression "output"])
    checkedResultSuccessBody (statements [])

theorem checkedResultBody_shape : checkedResultBody =
    statements [checkedResultDecision] := by
  rfl

def openResultBody : Pattern :=
  guardedTransitionBody resultIsOpenQuery
    (variableExpressions ["output"])
    setOutsideFragmentDelta (variableExpressions ["state"])
    outsideFragmentOutcome

def openResultSuccessBody : Pattern :=
  statements [effect (call setOutsideFragmentDelta
      [variableExpression "state"]),
    returnSymbol outsideFragmentOutcome]

def openResultDecision : Pattern :=
  ifThenElse (call resultIsOpenQuery [variableExpression "output"])
    openResultSuccessBody (statements [])

theorem openResultBody_shape : openResultBody =
    statements [openResultDecision] := by
  rfl

/-- The complete matched-row lowering.  Source matching and variable binding
remain a separate generated stage; every authenticated family has one body. -/
def lowerMatchedFamilyBody : CompileTransitionFamily → Pattern
  | .finish => finishBody
  | .skipHead => skipHeadBody
  | .skipArity => skipArityBody
  | .beginDeclaration => beginDeclarationBody
  | .argumentsFinished => argumentsFinishedBody
  | .rawInput => rawInputBody
  | .undefinedInput => undefinedInputBody
  | .holeInput => holeInputBody
  | .checkedInput => checkedInputBody
  | .openInput => openInputBody
  | .undefinedResult => undefinedResultBody
  | .holeResult => holeResultBody
  | .atomResult => atomResultBody
  | .checkedResult => checkedResultBody
  | .openResult => openResultBody

/-- Lower one row only after its complete source structure has authenticated.
A matching name alone never reaches target generation. -/
def lowerDecodedTransition? (rewrite : RewriteRule) : Option Pattern :=
  (decodeTransition? rewrite).map lowerMatchedFamilyBody

@[simp] theorem lower_family_rewrite (family : CompileTransitionFamily) :
    lowerDecodedTransition? family.rewrite =
      some (lowerMatchedFamilyBody family) := by
  simp [lowerDecodedTransition?]

theorem lower_argumentsFinishedTransition :
    lowerDecodedTransition? argumentsFinishedTransition =
      some argumentsFinishedBody := by
  exact lower_family_rewrite .argumentsFinished

theorem lower_skipHeadTransition :
    lowerDecodedTransition? skipHeadTransition = some skipHeadBody := by
  exact lower_family_rewrite .skipHead

theorem lower_openInputTransition :
    lowerDecodedTransition? openInputTransition = some openInputBody := by
  exact lower_family_rewrite .openInput

/-- Successful lowering identifies one exact authored source row and one
supported family body. -/
theorem lowerDecodedTransition?_eq_some_iff
    (rewrite : RewriteRule) (body : Pattern) :
    lowerDecodedTransition? rewrite = some body ↔
      ∃ family, rewrite = family.rewrite ∧
        body = lowerMatchedFamilyBody family := by
  constructor
  · intro lowered
    unfold lowerDecodedTransition? at lowered
    cases decoded : decodeTransition? rewrite with
    | none => simp [decoded] at lowered
    | some family =>
        refine ⟨family, ?_, ?_⟩
        · exact (decodeTransition?_eq_some_iff rewrite family).mp decoded
        · have mapped : some (lowerMatchedFamilyBody family) = some body := by
            simpa [decoded] using lowered
          exact (Option.some.inj mapped).symm
  · rintro ⟨family, sourceExact, rfl⟩
    subst rewrite
    exact lower_family_rewrite family

theorem lowerMatchedFamilyBody_target_typed
    (family : CompileTransitionFamily) :
    CarrierWellSorted.checkHasType StructuredC.language
      WellSorted.FreeTypeContext.empty [] (lowerMatchedFamilyBody family)
      (.base "Statements") = true := by
  cases family <;> decide +kernel

theorem argumentsFinishedBody_target_typed :
    CarrierWellSorted.checkHasType StructuredC.language
      WellSorted.FreeTypeContext.empty [] argumentsFinishedBody
      (.base "Statements") = true := by
  exact lowerMatchedFamilyBody_target_typed .argumentsFinished

theorem skipHeadBody_target_typed :
    CarrierWellSorted.checkHasType StructuredC.language
      WellSorted.FreeTypeContext.empty [] skipHeadBody
      (.base "Statements") = true := by
  exact lowerMatchedFamilyBody_target_typed .skipHead

theorem openInputBody_target_typed :
    CarrierWellSorted.checkHasType StructuredC.language
      WellSorted.FreeTypeContext.empty [] openInputBody
      (.base "Statements") = true := by
  exact lowerMatchedFamilyBody_target_typed .openInput

/-- Target sorting composes with exact source authentication. -/
theorem lowerDecodedTransition?_target_typed
    {rewrite : RewriteRule} {body : Pattern}
    (lowered : lowerDecodedTransition? rewrite = some body) :
    CarrierWellSorted.checkHasType StructuredC.language
      WellSorted.FreeTypeContext.empty [] body (.base "Statements") = true := by
  obtain ⟨family, _, bodyExact⟩ :=
    (lowerDecodedTransition?_eq_some_iff rewrite body).mp lowered
  subst body
  exact lowerMatchedFamilyBody_target_typed family

/-- The complete target-body inventory, still prior to source matching and
ordered dispatcher assembly. -/
def allMatchedFamilyBodies : List Pattern :=
  orderedFamilies.map lowerMatchedFamilyBody

/-- Decode the complete source inventory before constructing any target body
inventory. -/
def lowerDecodedLanguage? (source : LanguageDef) : Option (List Pattern) :=
  (decodeLanguage? source).map (List.map lowerMatchedFamilyBody)

theorem language_lowers_all_families :
    lowerDecodedLanguage? language = some allMatchedFamilyBodies := by
  unfold lowerDecodedLanguage?
  rw [language_decodes_exactly]
  rfl

/-- Complete lowering succeeds exactly for the authored source row inventory
and returns exactly the fifteen generated bodies. -/
theorem lowerDecodedLanguage?_eq_some_iff
    (source : LanguageDef) (bodies : List Pattern) :
    lowerDecodedLanguage? source = some bodies ↔
      source.rewrites = transitions ∧ bodies = allMatchedFamilyBodies := by
  constructor
  · intro lowered
    unfold lowerDecodedLanguage? at lowered
    cases decoded : decodeLanguage? source with
    | none => simp [decoded] at lowered
    | some families =>
        obtain ⟨sourceExact, rfl⟩ := decodeLanguage?_success_exact decoded
        rw [decoded] at lowered
        simp only [Option.map] at lowered
        exact ⟨sourceExact, (Option.some.inj lowered).symm⟩
  · rintro ⟨sourceExact, rfl⟩
    have decoded : decodeLanguage? source = some orderedFamilies :=
      (decodeLanguage?_eq_some_iff source orderedFamilies).2
        ⟨by simpa using sourceExact, rfl⟩
    simp [lowerDecodedLanguage?, decoded, allMatchedFamilyBodies]

theorem allMatchedFamilyBodies_length :
    allMatchedFamilyBodies.length = 15 := by
  simp [allMatchedFamilyBodies]

theorem allMatchedFamilyBodies_target_typed
    {body : Pattern} (membership : body ∈ allMatchedFamilyBodies) :
    CarrierWellSorted.checkHasType StructuredC.language
      WellSorted.FreeTypeContext.empty [] body (.base "Statements") = true := by
  obtain ⟨family, _, rfl⟩ := List.mem_map.mp membership
  exact lowerMatchedFamilyBody_target_typed family

/-- State-level hooks that would choose or construct semantic content behind
the generated control are not part of this lowering surface. -/
def forbiddenBroadHooks : List String :=
  [ "cetta_petta_call_guard_finish_compiled_family_v1"
  , "cetta_petta_call_guard_declaration_relevant_v1"
  , "cetta_petta_call_guard_begin_mode_compilation_v1"
  , "cetta_petta_call_guard_emit_plan_v1" ]

def usesForbiddenBroadHook (body : Pattern) : Bool :=
  forbiddenBroadHooks.any fun hook =>
    body.constructorRefs.contains (hook, 0)

theorem seed_bodies_avoid_broad_hooks :
    usesForbiddenBroadHook argumentsFinishedBody = false ∧
      usesForbiddenBroadHook skipHeadBody = false ∧
      usesForbiddenBroadHook openInputBody = false := by
  decide +kernel

theorem all_matched_bodies_avoid_broad_hooks :
    allMatchedFamilyBodies.any usesForbiddenBroadHook = false := by
  decide +kernel

theorem seed_bodies_are_discriminating :
    argumentsFinishedBody ≠ skipHeadBody ∧
      skipHeadBody ≠ openInputBody ∧
      argumentsFinishedBody ≠ openInputBody := by
  decide

#print axioms lowerDecodedTransition?_eq_some_iff
#print axioms finishBody_shape
#print axioms lowerDecodedTransition?_target_typed
#print axioms lowerDecodedLanguage?_eq_some_iff
#print axioms allMatchedFamilyBodies_target_typed
#print axioms all_matched_bodies_avoid_broad_hooks
#print axioms seed_bodies_avoid_broad_hooks
#print axioms seed_bodies_are_discriminating

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments
