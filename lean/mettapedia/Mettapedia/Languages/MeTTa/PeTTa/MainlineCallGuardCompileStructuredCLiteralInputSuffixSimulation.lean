import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation

/-!
# Shared literal-input effect suffix

The three literal families have different ordered dispatcher paths, but their
successful branches share one semantic operation: independently classify the
cursor head, append its canonical argument mode, consume exactly that head,
and return.  This module proves that common StructuredC suffix without
collapsing the three dispatcher occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCLiteralInputSuffixSimulation

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission
open Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
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

def literalMode : LiteralPredicate → ArgMode
  | .atom => .rawAtom
  | .undefined
  | .hole => .evalUnchecked

def literalBody : LiteralPredicate → Pattern
  | .atom => rawInputBody
  | .undefined => undefinedInputBody
  | .hole => holeInputBody

theorem literalBody_shape (predicate : LiteralPredicate) :
    literalBody predicate = statements [
      effect (call appendArgumentModeDelta
        (([ "state", "owner", "revision", "head", "arity", "occurrence"
          , "declaration_head", "inputs", "output", "remaining"
          , "input_cursor", "modes", "accepted" ].map variableExpression) ++
          [constant (argumentModeTag (literalMode predicate)),
            constant (argumentModePayload (literalMode predicate))])),
      returnSymbol advancedOutcome] := by
  cases predicate <;>
    simp [literalBody, literalMode, rawInputBody_shape,
      undefinedInputBody_shape, holeInputBody_shape, argumentModeTag,
      argumentModePayload, symbol]

def inputData
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : InputStateData :=
  { owner, revision, head, arity, declaration, remaining
    expected := predicate.term
    inputCursor, modes, accepted }

def source
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  (inputData predicate owner revision head arity declaration remaining
    inputCursor modes accepted).source

def target
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  .arguments owner revision head arity declaration remaining inputCursor
    (modes ++ [literalMode predicate]) accepted

def environment13
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  (inputData predicate owner revision head arity declaration remaining
    inputCursor modes accepted).environment13

def environment14
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  bindName "state"
    (stateValue (target predicate owner revision head arity declaration
      remaining inputCursor modes accepted))
    (environment13 predicate owner revision head arity declaration remaining
      inputCursor modes accepted)

def deltaReceipt (receipt : Pattern) : Pattern :=
  externalReceipt appendArgumentModeDelta receipt

def effectExpression (predicate : LiteralPredicate) : Pattern :=
  call appendArgumentModeDelta
    (([ "state", "owner", "revision", "head", "arity", "occurrence"
      , "declaration_head", "inputs", "output", "remaining"
      , "input_cursor", "modes", "accepted" ].map variableExpression) ++
      [constant (argumentModeTag (literalMode predicate)),
        constant (argumentModePayload (literalMode predicate))])

def effectStatement (predicate : LiteralPredicate) : Pattern :=
  effect (effectExpression predicate)

def returnStatements : Pattern := statements [returnSymbol advancedOutcome]

theorem source_lookup13
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    lookup?
        (environment13 predicate owner revision head arity declaration
          remaining inputCursor modes accepted)
        (identifier "state") =
      some (stateValue (source predicate owner revision head arity declaration
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

theorem literal_expected_lookup13
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    lookup?
        (environment13 predicate owner revision head arity declaration
          remaining inputCursor modes accepted)
        (identifier "expected") =
      some (abiValue (encodeTerm predicate.term)) := by
  simp [environment13, inputData, InputStateData.environment13,
    InputStateData.environment12, lookup?, bindName, environmentBind,
    identifier, node, token, InputStateData.expectedValue]

theorem delta_operands_lookup
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    List.Forall₂
      (fun slot value =>
        lookup?
          (environment13 predicate owner revision head arity declaration
            remaining inputCursor modes accepted)
          (identifier slot) = some value)
      [ "state", "owner", "revision", "head", "arity", "occurrence"
      , "declaration_head", "inputs", "output", "remaining", "input_cursor"
      , "modes", "accepted" ]
      [ stateValue (source predicate owner revision head arity declaration
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
  simp [environment13, source, inputData, InputStateData.environment13,
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

theorem literal_classification_exact (predicate : LiteralPredicate) :
    compileArgMode predicate.term = some (literalMode predicate) := by
  cases predicate <;>
    simp [LiteralPredicate.term, literalMode, compileArgMode, atomType,
      undefinedType, holeType]

theorem delta_evaluation_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt : Pattern) :
    evaluate? coldHandler (effectExpression predicate)
        (environment13 predicate owner revision head arity declaration
          remaining inputCursor modes accepted) receipt =
      some ⟨.value valueUnit,
        environment14 predicate owner revision head arity declaration
          remaining inputCursor modes accepted,
        deltaReceipt receipt⟩ := by
  have handled := handler_appendArgumentMode_delta_exact owner revision head
    arity declaration remaining predicate.term inputCursor modes accepted
    (literalMode predicate)
    (environment13 predicate owner revision head arity declaration remaining
      inputCursor modes accepted) receipt (literal_classification_exact predicate)
    (source_lookup13 predicate owner revision head arity declaration remaining
      inputCursor modes accepted)
  have evaluated := evaluate_variable_constant_call_exact coldHandler
    appendArgumentModeDelta
    [ "state", "owner", "revision", "head", "arity", "occurrence"
    , "declaration_head", "inputs", "output", "remaining", "input_cursor"
    , "modes", "accepted" ]
    [ stateValue (source predicate owner revision head arity declaration
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
    [argumentModeTag (literalMode predicate),
      argumentModePayload (literalMode predicate)]
    (environment13 predicate owner revision head arity declaration remaining
      inputCursor modes accepted) receipt _
    (delta_operands_lookup predicate owner revision head arity declaration
      remaining inputCursor modes accepted) handled
  simpa [effectExpression, environment14, target, deltaReceipt] using evaluated

theorem body_append_rewrite_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements (literalBody predicate) continuation)
          (environment13 predicate owner revision head arity declaration
            remaining inputCursor modes accepted) receipt) =
      [run (consStatement (effectStatement predicate)
          (StructuredC.appendStatements returnStatements continuation))
        (environment13 predicate owner revision head arity declaration
          remaining inputCursor modes accepted) receipt] := by
  rw [literalBody_shape]
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement (effectStatement predicate) returnStatements)
        continuation)
        (environment13 predicate owner revision head arity declaration
          remaining inputCursor modes accepted) receipt) = _
  exact appendConsTransition_rewriteAt_exact coldRelations
    (effectStatement predicate) returnStatements continuation
    (environment13 predicate owner revision head arity declaration remaining
      inputCursor modes accepted) receipt

theorem delta_effect_rewrite_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (effectStatement predicate) rest)
          (environment13 predicate owner revision head arity declaration
            remaining inputCursor modes accepted) receipt) =
      [run rest
        (environment14 predicate owner revision head arity declaration
          remaining inputCursor modes accepted) (deltaReceipt receipt)] := by
  have evaluated := delta_evaluation_exact predicate owner revision head arity
    declaration remaining inputCursor modes accepted receipt
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    effectStatement, effect, node, StructuredC.a] using
    effect_rewriteAt_exact_of_evaluate coldHandler (effectExpression predicate)
      rest
      (environment13 predicate owner revision head arity declaration remaining
        inputCursor modes accepted) receipt valueUnit
      (environment14 predicate owner revision head arity declaration remaining
        inputCursor modes accepted) (deltaReceipt receipt) evaluated

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
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (returnSymbol advancedOutcome) rest)
          (environment14 predicate owner revision head arity declaration
            remaining inputCursor modes accepted) (deltaReceipt receipt)) =
      [halted (StructuredC.a "structured-c:outcome-return"
          [valueSymbol advancedOutcome])
        (environment14 predicate owner revision head arity declaration
          remaining inputCursor modes accepted) (deltaReceipt receipt)] := by
  have evaluated := evaluate_symbol_exact coldHandler advancedOutcome
    (environment14 predicate owner revision head arity declaration remaining
      inputCursor modes accepted) (deltaReceipt receipt)
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    returnSymbol, returnExpression, node, StructuredC.a] using
    return_rewriteAt_exact_of_evaluate coldHandler (symbol advancedOutcome)
      rest
      (environment14 predicate owner revision head arity declaration remaining
        inputCursor modes accepted) (deltaReceipt receipt)
      (valueSymbol advancedOutcome)
      (environment14 predicate owner revision head arity declaration remaining
        inputCursor modes accepted) (deltaReceipt receipt) evaluated

def haltedTarget
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt : Pattern) : Pattern :=
  halted (StructuredC.a "structured-c:outcome-return"
      [valueSymbol advancedOutcome])
    (environment14 predicate owner revision head arity declaration remaining
      inputCursor modes accepted) (deltaReceipt receipt)

theorem terminal_observation_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt : Pattern) :
    terminalControl?
        (haltedTarget predicate owner revision head arity declaration remaining
          inputCursor modes accepted receipt) =
      some (target predicate owner revision head arity declaration remaining
        inputCursor modes accepted) := by
  simp [haltedTarget, terminalControl?, environment14, target, halted,
    StructuredC.a, lookup?, bindName, environmentBind, identifier,
    decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?, abiValue, node,
    token]

theorem source_step
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    compileLanguageGSLT.Step
      (source predicate owner revision head arity declaration remaining
        inputCursor modes accepted)
      (target predicate owner revision head arity declaration remaining
        inputCursor modes accepted) := by
  change compileLanguageStep?
      (source predicate owner revision head arity declaration remaining
        inputCursor modes accepted) =
    some (target predicate owner revision head arity declaration remaining
      inputCursor modes accepted)
  simp [source, inputData, InputStateData.source, target, compileLanguageStep?,
    literal_classification_exact]

/-- Four target steps implement the successful literal-family suffix: expose
the body head, apply the exact delta, expose the return, and halt. -/
theorem normalize_suffix_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt continuation : Pattern)
    (fuel : Nat) :
    normalizeFirstAt (engineBasePremises coldRelations) StructuredC.language 1
        (fuel + 4)
        (run (StructuredC.appendStatements (literalBody predicate) continuation)
          (environment13 predicate owner revision head arity declaration
            remaining inputCursor modes accepted) receipt) =
      haltedTarget predicate owner revision head arity declaration remaining
        inputCursor modes accepted receipt := by
  simp only [normalizeFirstAt,
    body_append_rewrite_exact predicate owner revision head arity declaration
      remaining inputCursor modes accepted receipt continuation]
  simp only [delta_effect_rewrite_exact predicate owner revision head arity
    declaration remaining inputCursor modes accepted receipt]
  simp only [return_statements_append_rewrite_exact]
  simp only [return_rewrite_exact predicate owner revision head arity
    declaration remaining inputCursor modes accepted receipt]
  induction fuel with
  | zero => rfl
  | succ fuel _ =>
      simp [normalizeFirstAt, haltedTarget, halted_rewriteAt_empty]

#print axioms literal_classification_exact
#print axioms source_step
#print axioms normalize_suffix_exact
#print axioms terminal_observation_exact

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCLiteralInputSuffixSimulation
