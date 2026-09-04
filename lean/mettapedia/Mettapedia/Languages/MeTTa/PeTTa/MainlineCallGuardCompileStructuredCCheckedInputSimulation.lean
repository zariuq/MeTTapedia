import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation

/-!
# Generated StructuredC realization of the checked-input family

For every source term classified as `evalSoftcutType expected`, the generated
target program rejects all earlier literal rows, obtains the checked answer
from the same independent classifier, reconstructs the exact typed argument
mode, and reaches precisely the source transition target.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedInputSimulation

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission
open Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
open Mettapedia.GSLT.LanguageDef.NormalizationPath
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCDispatcher
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOneStepSimulation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation

namespace NonLiteral

abbrev inputData :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.inputData
abbrev source :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.source
abbrev environment13 :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.environment13
abbrev holeReceipt :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.holeReceipt
abbrev checkedRest :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.checkedRest
abbrev checkedEndpoint :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.checkedEndpoint
abbrev expected_lookup13 :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.expected_lookup13
abbrev normalize_prefix_exact :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenInputPrefixSimulation.normalize_prefix_exact

end NonLiteral

def inputData
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : InputStateData :=
  { owner, revision, head, arity, declaration, remaining, expected,
    inputCursor, modes, accepted }

def source
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  (inputData expected owner revision head arity declaration remaining
    inputCursor modes accepted).source

def target
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  .arguments owner revision head arity declaration remaining inputCursor
    (modes ++ [.evalSoftcutType expected]) accepted

def environment13
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  (inputData expected owner revision head arity declaration remaining
    inputCursor modes accepted).environment13

def environment14
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  bindName "state"
    (stateValue (target expected owner revision head arity declaration remaining
      inputCursor modes accepted))
    (environment13 expected owner revision head arity declaration remaining
      inputCursor modes accepted)

def checkedReceipt : Pattern :=
  externalReceipt inputIsCheckedQuery NonLiteral.holeReceipt
def deltaReceipt : Pattern :=
  externalReceipt appendArgumentModeDelta checkedReceipt

def operandNames : List String :=
  [ "state", "owner", "revision", "head", "arity", "occurrence"
  , "declaration_head", "inputs", "output", "remaining", "input_cursor"
  , "modes", "accepted" ]

def operandExpressions : List Pattern :=
  operandNames.map variableExpression ++
    [symbol checkedArgumentMode, variableExpression "expected"]

def operandValues
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : List Pattern :=
  [ stateValue (source expected owner revision head arity declaration remaining
      inputCursor modes accepted)
  , abiValue (encodeOwner owner)
  , abiValue (encodeNat revision)
  , abiValue (encodeName head)
  , abiValue (encodeNat arity)
  , abiValue (encodeNat declaration.occurrence)
  , abiValue (encodeName declaration.function)
  , abiValue (encodeTerms declaration.inputTypes)
  , abiValue (encodeTerm declaration.outputType)
  , abiValue (encodeDeclarations remaining)
  , abiValue (encodeTerms inputCursor)
  , abiValue (encodeArgModes modes)
  , abiValue (encodePlans accepted)
  , valueSymbol checkedArgumentMode
  , abiValue (encodeTerm expected) ]

def effectExpression : Pattern :=
  call appendArgumentModeDelta operandExpressions

def effectStatement : Pattern := effect effectExpression

def returnStatements : Pattern := statements [returnSymbol advancedOutcome]

theorem not_atom_of_classified (expected : Term)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected)) :
    expected ≠ atomType := by
  intro equal
  subst expected
  simp [compileArgMode, atomType] at classified

theorem not_undefined_of_classified (expected : Term)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected)) :
    expected ≠ undefinedType := by
  intro equal
  subst expected
  simp [compileArgMode, undefinedType, atomType] at classified

theorem not_hole_of_classified (expected : Term)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected)) :
    expected ≠ holeType := by
  intro equal
  subst expected
  simp [compileArgMode, holeType, undefinedType, atomType] at classified

theorem source_lookup13
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    lookup?
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted)
        (identifier "state") =
      some (stateValue (source expected owner revision head arity declaration
        remaining inputCursor modes accepted)) := by
  simp [environment13, source, inputData, InputStateData.environment13,
    InputStateData.environment12, InputStateData.environment11,
    InputStateData.environment10, InputStateData.environment9,
    InputStateData.environment8, InputStateData.environment7,
    InputStateData.environment6, InputStateData.environment5,
    InputStateData.environment4, InputStateData.environment3,
    InputStateData.environment2, InputStateData.environment1,
    InputStateData.environment0, initialEnvironment, lookup?, bindName,
    environmentBind, identifier, node, token]

theorem expected_lookup13
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    lookup?
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted)
        (identifier "expected") = some (abiValue (encodeTerm expected)) := by
  exact NonLiteral.expected_lookup13 expected owner revision head arity
    declaration remaining inputCursor modes accepted

theorem checked_decision_true_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected)) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (NonLiteral.checkedEndpoint expected owner revision head arity
          declaration remaining inputCursor modes accepted) =
      [run (StructuredC.appendStatements checkedInputSuccessBody
          NonLiteral.checkedRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) checkedReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (consStatement checkedInputDecision NonLiteral.checkedRest)
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) NonLiteral.holeReceipt) = _
  have evaluated :
      evaluate? coldHandler
          (call inputIsCheckedQuery [variableExpression "expected"])
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) NonLiteral.holeReceipt =
        some ⟨.value trueValue,
          environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted, checkedReceipt⟩ := by
    simpa [checkedInputAnswer, classified, checkedReceipt] using
      inputIsChecked_evaluation_exact expected
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) NonLiteral.holeReceipt
        (expected_lookup13 expected owner revision head arity declaration
          remaining inputCursor modes accepted)
  have selected :
      selectBranch? trueValue checkedInputSuccessBody (statements []) =
        some checkedInputSuccessBody := by
    simp [selectBranch?, trueValue, valueSymbol, identifier, node, token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    checkedInputDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call inputIsCheckedQuery [variableExpression "expected"])
      checkedInputSuccessBody (statements []) NonLiteral.checkedRest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) NonLiteral.holeReceipt trueValue
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) checkedReceipt checkedInputSuccessBody
      evaluated selected

theorem checked_body_append_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements checkedInputSuccessBody
          NonLiteral.checkedRest)
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) checkedReceipt) =
      [run (consStatement effectStatement
          (StructuredC.appendStatements returnStatements
            NonLiteral.checkedRest))
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) checkedReceipt] := by
  rw [checkedInputSuccessBody]
  simpa [effectStatement, effectExpression, operandExpressions, operandNames,
    returnStatements, statements, node, StructuredC.consStatement,
    StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations
      effectStatement returnStatements NonLiteral.checkedRest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) checkedReceipt

theorem delta_operands_lookup
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    List.Forall₂
      (fun slot value =>
        lookup?
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted)
          (identifier slot) = some value)
      operandNames
      [ stateValue (source expected owner revision head arity declaration
          remaining inputCursor modes accepted)
      , abiValue (encodeOwner owner)
      , abiValue (encodeNat revision)
      , abiValue (encodeName head)
      , abiValue (encodeNat arity)
      , abiValue (encodeNat declaration.occurrence)
      , abiValue (encodeName declaration.function)
      , abiValue (encodeTerms declaration.inputTypes)
      , abiValue (encodeTerm declaration.outputType)
      , abiValue (encodeDeclarations remaining)
      , abiValue (encodeTerms inputCursor)
      , abiValue (encodeArgModes modes)
      , abiValue (encodePlans accepted) ] := by
  simp [operandNames, environment13, source, inputData,
    InputStateData.environment13,
    InputStateData.environment12, InputStateData.environment11,
    InputStateData.environment10, InputStateData.environment9,
    InputStateData.environment8, InputStateData.environment7,
    InputStateData.environment6, InputStateData.environment5,
    InputStateData.environment4, InputStateData.environment3,
    InputStateData.environment2, InputStateData.environment1,
    InputStateData.environment0, initialEnvironment,
    InputStateData.ownerValue, InputStateData.revisionValue,
    InputStateData.headValue, InputStateData.arityValue,
    InputStateData.acceptedValue, InputStateData.remainingValue,
    InputStateData.occurrenceValue, InputStateData.declarationHeadValue,
    InputStateData.inputsValue, InputStateData.outputValue,
    InputStateData.modesValue, InputStateData.expectedValue,
    InputStateData.inputCursorValue, lookup?, bindName, environmentBind,
    environmentEmpty, identifier, node, token]

theorem delta_leaf_evaluations
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    (List.Forall₂
      (fun expression value =>
        evaluateLeaf? expression
            (environment13 expected owner revision head arity declaration
              remaining inputCursor modes accepted) checkedReceipt =
          some ⟨.value value,
            environment13 expected owner revision head arity declaration
              remaining inputCursor modes accepted, checkedReceipt⟩)
      operandExpressions
      (operandValues expected owner revision head arity declaration remaining
        inputCursor modes accepted)) := by
  have prefixLeaves := evaluateLeaf_variableExpressions_exact
    operandNames
    [ stateValue (source expected owner revision head arity declaration
        remaining inputCursor modes accepted)
    , abiValue (encodeOwner owner)
    , abiValue (encodeNat revision)
    , abiValue (encodeName head)
    , abiValue (encodeNat arity)
    , abiValue (encodeNat declaration.occurrence)
    , abiValue (encodeName declaration.function)
    , abiValue (encodeTerms declaration.inputTypes)
    , abiValue (encodeTerm declaration.outputType)
    , abiValue (encodeDeclarations remaining)
    , abiValue (encodeTerms inputCursor)
    , abiValue (encodeArgModes modes)
    , abiValue (encodePlans accepted) ]
    (environment13 expected owner revision head arity declaration remaining
      inputCursor modes accepted) checkedReceipt
    (delta_operands_lookup expected owner revision head arity declaration
      remaining inputCursor modes accepted)
  have tailLeaves :
      List.Forall₂
        (fun expression value =>
          evaluateLeaf? expression
              (environment13 expected owner revision head arity declaration
                remaining inputCursor modes accepted) checkedReceipt =
            some ⟨.value value,
              environment13 expected owner revision head arity declaration
                remaining inputCursor modes accepted, checkedReceipt⟩)
        [symbol checkedArgumentMode, variableExpression "expected"]
        [valueSymbol checkedArgumentMode, abiValue (encodeTerm expected)] := by
    constructor
    · simp [evaluateLeaf?, symbol, constant, valueSymbol, identifier, node,
        token]
    · constructor
      · have storedExpected := expected_lookup13 expected owner revision head
          arity declaration remaining inputCursor modes accepted
        have storedExpanded :
            lookup?
                (environment13 expected owner revision head arity declaration
                  remaining inputCursor modes accepted)
                (Pattern.apply "structured-c:identifier"
                  [Pattern.apply "expected" []]) =
              some (abiValue (encodeTerm expected)) := by
          simpa [identifier, node, token] using storedExpected
        simp [evaluateLeaf?, variableExpression, identifierName?, identifier,
          node, token, storedExpanded]
      · exact .nil
  have joined := List.rel_append prefixLeaves tailLeaves
  simpa [operandExpressions, operandValues, operandNames] using joined

theorem delta_evaluation_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected)) :
    evaluate? coldHandler effectExpression
        (environment13 expected owner revision head arity declaration remaining
          inputCursor modes accepted) checkedReceipt =
      some ⟨.value valueUnit,
        environment14 expected owner revision head arity declaration remaining
          inputCursor modes accepted, deltaReceipt⟩ := by
  have handled := handler_appendArgumentMode_delta_exact owner revision head
    arity declaration remaining expected inputCursor modes accepted
    (.evalSoftcutType expected)
    (environment13 expected owner revision head arity declaration remaining
      inputCursor modes accepted) checkedReceipt classified
    (source_lookup13 expected owner revision head arity declaration remaining
      inputCursor modes accepted)
  have evaluated := evaluate_pure_call_exact coldHandler
    appendArgumentModeDelta operandExpressions
    (operandValues expected owner revision head arity declaration remaining
      inputCursor modes accepted)
    (environment13 expected owner revision head arity declaration remaining
      inputCursor modes accepted) checkedReceipt _
    (delta_leaf_evaluations expected owner revision head arity declaration
      remaining inputCursor modes accepted) handled
  simpa [effectExpression, environment14, target, deltaReceipt,
    argumentModeTag, argumentModePayload] using evaluated

theorem delta_effect_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected))
    (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement effectStatement rest)
          (environment13 expected owner revision head arity declaration
            remaining inputCursor modes accepted) checkedReceipt) =
      [run rest
        (environment14 expected owner revision head arity declaration remaining
          inputCursor modes accepted) deltaReceipt] := by
  have evaluated := delta_evaluation_exact expected owner revision head arity
    declaration remaining inputCursor modes accepted classified
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    effectStatement, effect, node, StructuredC.a] using
    effect_rewriteAt_exact_of_evaluate coldHandler effectExpression
      rest
      (environment13 expected owner revision head arity declaration remaining
        inputCursor modes accepted) checkedReceipt valueUnit
      (environment14 expected owner revision head arity declaration remaining
        inputCursor modes accepted) deltaReceipt evaluated

theorem return_statements_append_rewrite_exact
    (continuation environment receipt : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements returnStatements continuation)
          environment receipt) =
      [run (consStatement (returnSymbol advancedOutcome)
          (StructuredC.appendStatements (statements []) continuation))
        environment receipt] := by
  simpa [returnStatements, statements, node, StructuredC.consStatement,
    StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations
      (returnSymbol advancedOutcome) (statements []) continuation environment
      receipt

theorem return_rewrite_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (returnSymbol advancedOutcome) rest)
          (environment14 expected owner revision head arity declaration
            remaining inputCursor modes accepted) deltaReceipt) =
      [halted (StructuredC.a "structured-c:outcome-return"
          [valueSymbol advancedOutcome])
        (environment14 expected owner revision head arity declaration remaining
          inputCursor modes accepted) deltaReceipt] := by
  have evaluated := evaluate_symbol_exact coldHandler advancedOutcome
    (environment14 expected owner revision head arity declaration remaining
      inputCursor modes accepted) deltaReceipt
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    returnSymbol, returnExpression, node, StructuredC.a] using
    return_rewriteAt_exact_of_evaluate coldHandler (symbol advancedOutcome)
      rest
      (environment14 expected owner revision head arity declaration remaining
        inputCursor modes accepted) deltaReceipt (valueSymbol advancedOutcome)
      (environment14 expected owner revision head arity declaration remaining
        inputCursor modes accepted) deltaReceipt evaluated

def haltedTarget
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  halted (StructuredC.a "structured-c:outcome-return"
      [valueSymbol advancedOutcome])
    (environment14 expected owner revision head arity declaration remaining
      inputCursor modes accepted) deltaReceipt

theorem terminal_observation_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    terminalControl?
        (haltedTarget expected owner revision head arity declaration remaining
          inputCursor modes accepted) =
      some (target expected owner revision head arity declaration remaining
        inputCursor modes accepted) := by
  simp [haltedTarget, terminalControl?, environment14, target, halted,
    StructuredC.a, lookup?, bindName, environmentBind, identifier,
    decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?, abiValue, node,
    token]

theorem source_step
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected)) :
    compileLanguageGSLT.Step
      (source expected owner revision head arity declaration remaining
        inputCursor modes accepted)
      (target expected owner revision head arity declaration remaining
        inputCursor modes accepted) := by
  change compileLanguageStep?
      (.arguments owner revision head arity declaration remaining
        (expected :: inputCursor) modes accepted) =
    some (target expected owner revision head arity declaration remaining
      inputCursor modes accepted)
  simp [target, compileLanguageStep?, classified]

theorem normalizes_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected)) :
    normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source expected owner revision head arity declaration remaining
            inputCursor modes accepted)) =
      haltedTarget expected owner revision head arity declaration remaining
        inputCursor modes accepted := by
  change normalizeFirstUsing coldRelations StructuredC.language 1 (35 + 29)
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (inputData expected owner revision head arity declaration remaining
          inputCursor modes accepted).source) = _
  rw [Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.normalize_prefix_exact
    (inputData expected owner revision head arity declaration remaining
      inputCursor modes accepted) 35]
  change normalizeFirstAt (engineBasePremises coldRelations)
      StructuredC.language 1 (28 + 7)
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.prefixEndpoint
          (NonLiteral.inputData expected owner revision head arity declaration
            remaining inputCursor modes accepted)) = _
  rw [NonLiteral.normalize_prefix_exact expected owner revision head arity
    declaration remaining inputCursor modes accepted
    (not_atom_of_classified expected classified)
    (not_undefined_of_classified expected classified)
    (not_hole_of_classified expected classified) 28]
  simp only [normalizeFirstAt,
    checked_decision_true_rewrite_exact expected owner revision head arity
      declaration remaining inputCursor modes accepted classified]
  simp only [checked_body_append_rewrite_exact expected owner revision head
    arity declaration remaining inputCursor modes accepted]
  simp only [delta_effect_rewrite_exact expected owner revision head arity
    declaration remaining inputCursor modes accepted classified]
  simp only [return_statements_append_rewrite_exact]
  simp only [return_rewrite_exact expected owner revision head arity declaration
    remaining inputCursor modes accepted]
  simp only [halted_rewriteAt_empty]
  rfl

abbrev run
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (source expected owner revision head arity declaration remaining
          inputCursor modes accepted)) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
      (source expected owner revision head arity declaration remaining
        inputCursor modes accepted))

theorem run_endpoint_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected)) :
    (run expected owner revision head arity declaration remaining inputCursor
      modes accepted).endpoint =
      haltedTarget expected owner revision head arity declaration remaining
        inputCursor modes accepted := by
  calc
    _ = normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source expected owner revision head arity declaration remaining
            inputCursor modes accepted)) :=
      (run expected owner revision head arity declaration remaining inputCursor
        modes accepted).endpoint_eq
    _ = _ := normalizes_exact expected owner revision head arity declaration
      remaining inputCursor modes accepted classified

theorem run_observation_exact
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected)) :
    terminalControl?
        (run expected owner revision head arity declaration remaining
          inputCursor modes accepted).endpoint =
      some (target expected owner revision head arity declaration remaining
        inputCursor modes accepted) := by
  rw [run_endpoint_exact expected owner revision head arity declaration
    remaining inputCursor modes accepted classified]
  exact terminal_observation_exact expected owner revision head arity
    declaration remaining inputCursor modes accepted

theorem run_path_bounded
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    (run expected owner revision head arity declaration remaining inputCursor
      modes accepted).path.length ≤ 64 :=
  (run expected owner revision head arity declaration remaining inputCursor
    modes accepted).length_le

theorem run_path_nonempty
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    0 < (run expected owner revision head arity declaration remaining
      inputCursor modes accepted).path.length := by
  apply (run expected owner revision head arity declaration remaining
    inputCursor modes accepted).nonempty_of_reduct
  · decide
  · change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (inputData expected owner revision head arity declaration remaining
            inputCursor modes accepted).source) ≠ []
    rw [Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.phase_rewrite_exact
      (inputData expected owner revision head arity declaration remaining
        inputCursor modes accepted)]
    simp

theorem step_realization
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected)) :
    ∃ endpoint : Pattern,
      ∃ path : ExecutionPath coldGSLT
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source expected owner revision head arity declaration remaining
              inputCursor modes accepted)) endpoint,
      terminalControl? endpoint =
          some (target expected owner revision head arity declaration remaining
            inputCursor modes accepted) ∧
        0 < path.length ∧ path.length ≤ 64 := by
  let execution := run expected owner revision head arity declaration remaining
    inputCursor modes accepted
  refine ⟨execution.endpoint, execution.path, ?_, ?_, ?_⟩
  · exact run_observation_exact expected owner revision head arity declaration
      remaining inputCursor modes accepted classified
  · exact run_path_nonempty expected owner revision head arity declaration
      remaining inputCursor modes accepted
  · exact run_path_bounded expected owner revision head arity declaration
      remaining inputCursor modes accepted

theorem normalized_observation_iff
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected))
    (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source expected owner revision head arity declaration remaining
              inputCursor modes accepted))) = some observed ↔
      observed = target expected owner revision head arity declaration remaining
        inputCursor modes accepted := by
  rw [normalizes_exact expected owner revision head arity declaration remaining
    inputCursor modes accepted classified]
  have observedExact := terminal_observation_exact expected owner revision head
    arity declaration remaining inputCursor modes accepted
  rw [observedExact]
  simp [eq_comm]

theorem wrong_target_rejected
    (expected : Term)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (classified :
      compileArgMode expected = some (.evalSoftcutType expected))
    (observed : CompileLanguageControl)
    (wrong : observed ≠ target expected owner revision head arity declaration
      remaining inputCursor modes accepted) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source expected owner revision head arity declaration remaining
              inputCursor modes accepted))) ≠ some observed := by
  intro invented
  exact wrong ((normalized_observation_iff expected owner revision head arity
    declaration remaining inputCursor modes accepted classified observed).mp
      invented)

#print axioms source_step
#print axioms normalizes_exact
#print axioms run_endpoint_exact
#print axioms run_observation_exact
#print axioms run_path_bounded
#print axioms run_path_nonempty
#print axioms step_realization
#print axioms normalized_observation_iff
#print axioms wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedInputSimulation
