import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation

/-!
# Generated StructuredC realization of the three literal-result families

Undefined, hole, and atom results occupy distinct authored dispatcher
occurrences.  Their successful branches share one semantic suffix: construct
the exact unchecked result plan, append it, and return to the running phase.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCLiteralResultSimulation

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
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation

def literalBody : LiteralPredicate → Pattern
  | .undefined => undefinedResultBody
  | .hole => holeResultBody
  | .atom => atomResultBody

def literalOutputExpression : LiteralPredicate → Pattern
  | .undefined => symbol undefinedTerm
  | .hole => symbol holeTerm
  | .atom => symbol atomTerm

theorem literalOutputValue_exact (predicate : LiteralPredicate) :
    resultOutputValue predicate.term =
      match predicate with
      | .undefined => valueSymbol undefinedTerm
      | .hole => valueSymbol holeTerm
      | .atom => valueSymbol atomTerm := by
  cases predicate <;>
    simp [resultOutputValue, LiteralPredicate.term, undefinedType, holeType,
      atomType]

theorem literalBody_shape (predicate : LiteralPredicate) :
    literalBody predicate = statements [
      effect (call appendCompiledPlanDelta
        (([ "state", "owner", "revision", "head", "arity", "remaining"
          , "accepted", "occurrence", "modes", "declaration_head", "inputs"
          ].map variableExpression) ++
          [constant (resultOutputValue predicate.term),
            constant (resultModeTag .resultUnchecked),
            constant (resultModePayload .resultUnchecked)])),
      returnSymbol advancedOutcome] := by
  cases predicate <;>
    simp [literalBody, undefinedResultBody_shape, holeResultBody_shape,
      atomResultBody_shape, resultOutputValue, LiteralPredicate.term,
      resultModeTag, resultModePayload, undefinedType, holeType, atomType,
      symbol]

def declaration
    (predicate : LiteralPredicate) (occurrence : Nat)
    (declarationHead : String) (inputs : List Term) : ArrowDeclaration :=
  ⟨occurrence, declarationHead, inputs, predicate.term⟩

def data
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) : ResultStateData :=
  { owner, revision, head, arity
    declaration := declaration predicate occurrence declarationHead inputs
    remaining, modes, accepted }

def source
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  (data predicate owner revision head arity occurrence declarationHead inputs
    remaining modes accepted).source

def plan
    (predicate : LiteralPredicate) (occurrence : Nat)
    (declarationHead : String) (inputs : List Term)
    (modes : List ArgMode) : GuardPlan := {
  declarationOccurrence := occurrence
  argumentModes := modes
  resultMode := .resultUnchecked
  declaration := declaration predicate occurrence declarationHead inputs }

def target
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  .running owner revision head arity remaining
    (accepted ++ [plan predicate occurrence declarationHead inputs modes])

def environment11
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  (data predicate owner revision head arity occurrence declarationHead inputs
    remaining modes accepted).environment11

def environment12
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  bindName "state"
    (stateValue (target predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted))
    (environment11 predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted)

def undefinedReceipt : Pattern :=
  externalReceipt termIsUndefinedQuery receipt12
def holeReceipt : Pattern := externalReceipt termIsHoleQuery undefinedReceipt
def atomReceipt : Pattern := externalReceipt termIsAtomQuery holeReceipt
def deltaReceipt (receipt : Pattern) : Pattern :=
  externalReceipt appendCompiledPlanDelta receipt

def baseContinuation : Pattern :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation.baseContinuation
def holeContinuation : Pattern :=
  StructuredC.appendStatements (statements []) baseContinuation
def atomContinuation : Pattern :=
  StructuredC.appendStatements (statements []) holeContinuation

def effectExpression (predicate : LiteralPredicate) : Pattern :=
  call appendCompiledPlanDelta
    (([ "state", "owner", "revision", "head", "arity", "remaining"
      , "accepted", "occurrence", "modes", "declaration_head", "inputs"
      ].map variableExpression) ++
      [constant (resultOutputValue predicate.term),
        constant (resultModeTag .resultUnchecked),
        constant (resultModePayload .resultUnchecked)])

def effectStatement (predicate : LiteralPredicate) : Pattern :=
  effect (effectExpression predicate)

def returnStatements : Pattern := statements [returnSymbol advancedOutcome]

theorem source_lookup11
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    lookup?
        (environment11 predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted)
        (identifier "state") =
      some (stateValue (source predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted)) := by
  simp [environment11, source, data, ResultStateData.environment11,
    ResultStateData.environment10, ResultStateData.environment9,
    ResultStateData.environment8, ResultStateData.environment7,
    ResultStateData.environment6, ResultStateData.environment5,
    ResultStateData.environment4, ResultStateData.environment3,
    ResultStateData.environment2, ResultStateData.environment1,
    ResultStateData.environment0, initialEnvironment, lookup?, bindName,
    environmentBind, identifier, node, token]

theorem output_lookup11
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    lookup?
        (environment11 predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted)
        (identifier "output") =
      some (abiValue (encodeTerm predicate.term)) := by
  simp [environment11, data, declaration, ResultStateData.environment11,
    ResultStateData.environment10, lookup?, bindName, environmentBind,
    identifier, node, token, ResultStateData.outputValue]

theorem delta_operands_lookup
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    List.Forall₂
      (fun slot value =>
        lookup?
          (environment11 predicate owner revision head arity occurrence
            declarationHead inputs remaining modes accepted)
          (identifier slot) = some value)
      [ "state", "owner", "revision", "head", "arity", "remaining"
      , "accepted", "occurrence", "modes", "declaration_head", "inputs" ]
      [ stateValue (source predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted)
      , abiValue (encodeOwner owner)
      , abiValue (encodeNat revision)
      , abiValue (encodeName head)
      , abiValue (encodeNat arity)
      , abiValue (encodeDeclarations remaining)
      , abiValue (encodePlans accepted)
      , abiValue (encodeNat occurrence)
      , abiValue (encodeArgModes modes)
      , abiValue (encodeName declarationHead)
      , abiValue (encodeTerms inputs) ] := by
  simp [environment11, source, data, declaration,
    ResultStateData.environment11, ResultStateData.environment10,
    ResultStateData.environment9, ResultStateData.environment8,
    ResultStateData.environment7, ResultStateData.environment6,
    ResultStateData.environment5, ResultStateData.environment4,
    ResultStateData.environment3, ResultStateData.environment2,
    ResultStateData.environment1, ResultStateData.environment0,
    initialEnvironment, ResultStateData.ownerValue,
    ResultStateData.revisionValue, ResultStateData.headValue,
    ResultStateData.arityValue, ResultStateData.acceptedValue,
    ResultStateData.remainingValue, ResultStateData.occurrenceValue,
    ResultStateData.declarationHeadValue, ResultStateData.inputsValue,
    ResultStateData.outputValue, ResultStateData.modesValue, lookup?, bindName,
    environmentBind, environmentEmpty, identifier, node, token]

theorem literal_classification_exact (predicate : LiteralPredicate) :
    compileResultMode predicate.term = some .resultUnchecked := by
  cases predicate <;>
    simp [LiteralPredicate.term, compileResultMode, atomType, undefinedType,
      holeType]

theorem delta_evaluation_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt : Pattern) :
    evaluate? coldHandler (effectExpression predicate)
        (environment11 predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) receipt =
      some ⟨.value valueUnit,
        environment12 predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted,
        deltaReceipt receipt⟩ := by
  have handled := handler_appendCompiledPlan_delta_exact owner revision head
    arity (declaration predicate occurrence declarationHead inputs) remaining
    modes accepted .resultUnchecked
    (environment11 predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted) receipt
    (literal_classification_exact predicate)
    (source_lookup11 predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted)
  have evaluated := evaluate_variable_constant_call_exact coldHandler
    appendCompiledPlanDelta
    [ "state", "owner", "revision", "head", "arity", "remaining"
    , "accepted", "occurrence", "modes", "declaration_head", "inputs" ]
    [ stateValue (source predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted)
    , abiValue (encodeOwner owner)
    , abiValue (encodeNat revision)
    , abiValue (encodeName head)
    , abiValue (encodeNat arity)
    , abiValue (encodeDeclarations remaining)
    , abiValue (encodePlans accepted)
    , abiValue (encodeNat occurrence)
    , abiValue (encodeArgModes modes)
    , abiValue (encodeName declarationHead)
    , abiValue (encodeTerms inputs) ]
    [resultOutputValue predicate.term, resultModeTag .resultUnchecked,
      resultModePayload .resultUnchecked]
    (environment11 predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted) receipt _
    (delta_operands_lookup predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted) handled
  simpa [effectExpression, environment12, target, plan, declaration,
    deltaReceipt] using evaluated

theorem body_append_rewrite_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements (literalBody predicate) continuation)
          (environment11 predicate owner revision head arity occurrence
            declarationHead inputs remaining modes accepted) receipt) =
      [run (consStatement (effectStatement predicate)
          (StructuredC.appendStatements returnStatements continuation))
        (environment11 predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) receipt] := by
  rw [literalBody_shape]
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement (effectStatement predicate) returnStatements)
        continuation)
        (environment11 predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) receipt) = _
  exact appendConsTransition_rewriteAt_exact coldRelations
    (effectStatement predicate) returnStatements continuation
    (environment11 predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted) receipt

theorem delta_effect_rewrite_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (effectStatement predicate) rest)
          (environment11 predicate owner revision head arity occurrence
            declarationHead inputs remaining modes accepted) receipt) =
      [run rest
        (environment12 predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted)
        (deltaReceipt receipt)] := by
  have evaluated := delta_evaluation_exact predicate owner revision head arity
    occurrence declarationHead inputs remaining modes accepted receipt
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    effectStatement, effect, node, StructuredC.a] using
    effect_rewriteAt_exact_of_evaluate coldHandler (effectExpression predicate)
      rest
      (environment11 predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted) receipt valueUnit
      (environment12 predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted) (deltaReceipt receipt)
      evaluated

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
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (returnSymbol advancedOutcome) rest)
          (environment12 predicate owner revision head arity occurrence
            declarationHead inputs remaining modes accepted)
          (deltaReceipt receipt)) =
      [halted (StructuredC.a "structured-c:outcome-return"
          [valueSymbol advancedOutcome])
        (environment12 predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted)
        (deltaReceipt receipt)] := by
  have evaluated := evaluate_symbol_exact coldHandler advancedOutcome
    (environment12 predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted) (deltaReceipt receipt)
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    returnSymbol, returnExpression, node, StructuredC.a] using
    return_rewriteAt_exact_of_evaluate coldHandler (symbol advancedOutcome)
      rest
      (environment12 predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted) (deltaReceipt receipt)
      (valueSymbol advancedOutcome)
      (environment12 predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted) (deltaReceipt receipt)
      evaluated

def haltedTarget
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt : Pattern) : Pattern :=
  halted (StructuredC.a "structured-c:outcome-return"
      [valueSymbol advancedOutcome])
    (environment12 predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted) (deltaReceipt receipt)

theorem terminal_observation_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt : Pattern) :
    terminalControl?
        (haltedTarget predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted receipt) =
      some (target predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted) := by
  simp [haltedTarget, terminalControl?, environment12, target, plan,
    declaration, halted, StructuredC.a, lookup?, bindName, environmentBind,
    identifier, decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?,
    abiValue, node, token]

theorem source_step
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    compileLanguageGSLT.Step
      (source predicate owner revision head arity occurrence declarationHead
        inputs remaining modes accepted)
      (target predicate owner revision head arity occurrence declarationHead
        inputs remaining modes accepted) := by
  change compileLanguageStep?
      (.result owner revision head arity
        (declaration predicate occurrence declarationHead inputs) remaining
        modes accepted) =
    some (target predicate owner revision head arity occurrence declarationHead
      inputs remaining modes accepted)
  simp [target, plan, declaration, compileLanguageStep?,
    literal_classification_exact]

/-- Four target steps implement the shared successful literal-result suffix. -/
theorem normalize_suffix_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) (receipt continuation : Pattern)
    (fuel : Nat) :
    normalizeFirstAt (engineBasePremises coldRelations) StructuredC.language 1
        (fuel + 4)
        (run (StructuredC.appendStatements (literalBody predicate) continuation)
          (environment11 predicate owner revision head arity occurrence
            declarationHead inputs remaining modes accepted) receipt) =
      haltedTarget predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted receipt := by
  simp only [normalizeFirstAt,
    body_append_rewrite_exact predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted receipt continuation]
  simp only [delta_effect_rewrite_exact predicate owner revision head arity
    occurrence declarationHead inputs remaining modes accepted receipt]
  simp only [return_statements_append_rewrite_exact]
  simp only [return_rewrite_exact predicate owner revision head arity
    occurrence declarationHead inputs remaining modes accepted receipt]
  induction fuel with
  | zero => rfl
  | succ fuel _ =>
      simp [normalizeFirstAt, haltedTarget, halted_rewriteAt_empty]

theorem undefined_decision_true_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (prefixEndpoint (data .undefined owner revision head arity occurrence
          declarationHead inputs remaining modes accepted)) =
      [run (StructuredC.appendStatements undefinedResultBody baseContinuation)
        (environment11 .undefined owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) undefinedReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (consStatement generatedUndefinedResultDecision baseContinuation)
        (environment11 .undefined owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) receipt12) = _
  have evaluated := literalResultPredicate_evaluation_exact .undefined
    LiteralPredicate.undefined.term
    (environment11 .undefined owner revision head arity occurrence
      declarationHead inputs remaining modes accepted) receipt12
    (output_lookup11 .undefined owner revision head arity occurrence
      declarationHead inputs remaining modes accepted)
  have selected :
      selectBranch? trueValue undefinedResultBody
          generatedUndefinedResultFallback = some undefinedResultBody := by
    simp [selectBranch?, trueValue, valueSymbol, identifier, node, token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedUndefinedResultDecision, ifThenElse, LiteralPredicate.term,
    undefinedReceipt, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsUndefinedQuery [variableExpression "output"])
      undefinedResultBody generatedUndefinedResultFallback baseContinuation
      (environment11 .undefined owner revision head arity occurrence
        declarationHead inputs remaining modes accepted) receipt12 trueValue
      (environment11 .undefined owner revision head arity occurrence
        declarationHead inputs remaining modes accepted) undefinedReceipt
      undefinedResultBody evaluated selected

theorem undefined_decision_false_rewrite_exact
    (predicate : LiteralPredicate) (different : predicate.term ≠ undefinedType)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (prefixEndpoint (data predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted)) =
      [run (StructuredC.appendStatements generatedUndefinedResultFallback
          baseContinuation)
        (environment11 predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) undefinedReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (consStatement generatedUndefinedResultDecision baseContinuation)
        (environment11 predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) receipt12) = _
  have comparison :
      (predicate.term == LiteralPredicate.undefined.term) = false := by
    exact beq_eq_false_iff_ne.mpr different
  have evaluatedRaw := literalResultPredicate_evaluation_exact .undefined
    predicate.term
    (environment11 predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted) receipt12
    (output_lookup11 predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted)
  rw [comparison] at evaluatedRaw
  have evaluated :
      evaluate? coldHandler
          (call termIsUndefinedQuery [variableExpression "output"])
          (environment11 predicate owner revision head arity occurrence
            declarationHead inputs remaining modes accepted) receipt12 =
        some ⟨.value falseValue,
          environment11 predicate owner revision head arity occurrence
            declarationHead inputs remaining modes accepted,
          undefinedReceipt⟩ := by
    simpa [LiteralPredicate.externalName, undefinedReceipt] using evaluatedRaw
  have selected :
      selectBranch? falseValue undefinedResultBody
          generatedUndefinedResultFallback =
        some generatedUndefinedResultFallback := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedUndefinedResultDecision, ifThenElse, LiteralPredicate.term,
    undefinedReceipt, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsUndefinedQuery [variableExpression "output"])
      undefinedResultBody generatedUndefinedResultFallback baseContinuation
      (environment11 predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted) receipt12 falseValue
      (environment11 predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted) undefinedReceipt
      generatedUndefinedResultFallback evaluated selected

theorem undefined_fallback_append_rewrite_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedUndefinedResultFallback
          baseContinuation)
          (environment11 predicate owner revision head arity occurrence
            declarationHead inputs remaining modes accepted) undefinedReceipt) =
      [run (consStatement generatedHoleResultDecision holeContinuation)
        (environment11 predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) undefinedReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement generatedHoleResultDecision (statements []))
        baseContinuation)
        (environment11 predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) undefinedReceipt) = _
  simpa [holeContinuation] using
    appendConsTransition_rewriteAt_exact coldRelations
      generatedHoleResultDecision (statements []) baseContinuation
      (environment11 predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted) undefinedReceipt

theorem hole_decision_true_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedHoleResultDecision holeContinuation)
          (environment11 .hole owner revision head arity occurrence
            declarationHead inputs remaining modes accepted) undefinedReceipt) =
      [run (StructuredC.appendStatements holeResultBody holeContinuation)
        (environment11 .hole owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) holeReceipt] := by
  have evaluated := literalResultPredicate_evaluation_exact .hole
    LiteralPredicate.hole.term
    (environment11 .hole owner revision head arity occurrence declarationHead
      inputs remaining modes accepted) undefinedReceipt
    (output_lookup11 .hole owner revision head arity occurrence
      declarationHead inputs remaining modes accepted)
  have selected :
      selectBranch? trueValue holeResultBody generatedHoleResultFallback =
        some holeResultBody := by
    simp [selectBranch?, trueValue, valueSymbol, identifier, node, token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedHoleResultDecision, ifThenElse, LiteralPredicate.term,
    holeReceipt, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsHoleQuery [variableExpression "output"])
      holeResultBody generatedHoleResultFallback holeContinuation
      (environment11 .hole owner revision head arity occurrence declarationHead
        inputs remaining modes accepted) undefinedReceipt trueValue
      (environment11 .hole owner revision head arity occurrence declarationHead
        inputs remaining modes accepted) holeReceipt holeResultBody evaluated
      selected

theorem hole_decision_false_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedHoleResultDecision holeContinuation)
          (environment11 .atom owner revision head arity occurrence
            declarationHead inputs remaining modes accepted) undefinedReceipt) =
      [run (StructuredC.appendStatements generatedHoleResultFallback
          holeContinuation)
        (environment11 .atom owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) holeReceipt] := by
  have comparison :
      (LiteralPredicate.atom.term == LiteralPredicate.hole.term) = false := by
    exact beq_eq_false_iff_ne.mpr (by decide)
  have evaluatedRaw := literalResultPredicate_evaluation_exact .hole
    LiteralPredicate.atom.term
    (environment11 .atom owner revision head arity occurrence declarationHead
      inputs remaining modes accepted) undefinedReceipt
    (output_lookup11 .atom owner revision head arity occurrence
      declarationHead inputs remaining modes accepted)
  rw [comparison] at evaluatedRaw
  have evaluated :
      evaluate? coldHandler
          (call termIsHoleQuery [variableExpression "output"])
          (environment11 .atom owner revision head arity occurrence
            declarationHead inputs remaining modes accepted) undefinedReceipt =
        some ⟨.value falseValue,
          environment11 .atom owner revision head arity occurrence
            declarationHead inputs remaining modes accepted,
          holeReceipt⟩ := by
    simpa [LiteralPredicate.externalName, holeReceipt] using evaluatedRaw
  have selected :
      selectBranch? falseValue holeResultBody generatedHoleResultFallback =
        some generatedHoleResultFallback := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedHoleResultDecision, ifThenElse, LiteralPredicate.term,
    holeReceipt, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsHoleQuery [variableExpression "output"])
      holeResultBody generatedHoleResultFallback holeContinuation
      (environment11 .atom owner revision head arity occurrence declarationHead
        inputs remaining modes accepted) undefinedReceipt falseValue
      (environment11 .atom owner revision head arity occurrence declarationHead
        inputs remaining modes accepted) holeReceipt
      generatedHoleResultFallback evaluated selected

theorem hole_fallback_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedHoleResultFallback
          holeContinuation)
          (environment11 .atom owner revision head arity occurrence
            declarationHead inputs remaining modes accepted) holeReceipt) =
      [run (consStatement generatedAtomResultDecision atomContinuation)
        (environment11 .atom owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) holeReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement generatedAtomResultDecision (statements []))
        holeContinuation)
        (environment11 .atom owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) holeReceipt) = _
  simpa [atomContinuation] using
    appendConsTransition_rewriteAt_exact coldRelations
      generatedAtomResultDecision (statements []) holeContinuation
      (environment11 .atom owner revision head arity occurrence
        declarationHead inputs remaining modes accepted) holeReceipt

theorem atom_decision_true_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedAtomResultDecision atomContinuation)
          (environment11 .atom owner revision head arity occurrence
            declarationHead inputs remaining modes accepted) holeReceipt) =
      [run (StructuredC.appendStatements atomResultBody atomContinuation)
        (environment11 .atom owner revision head arity occurrence
          declarationHead inputs remaining modes accepted) atomReceipt] := by
  have evaluated := literalResultPredicate_evaluation_exact .atom
    LiteralPredicate.atom.term
    (environment11 .atom owner revision head arity occurrence declarationHead
      inputs remaining modes accepted) holeReceipt
    (output_lookup11 .atom owner revision head arity occurrence
      declarationHead inputs remaining modes accepted)
  have selected :
      selectBranch? trueValue atomResultBody
          generatedCheckedOpenResultFallback = some atomResultBody := by
    simp [selectBranch?, trueValue, valueSymbol, identifier, node, token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedAtomResultDecision, ifThenElse, LiteralPredicate.term,
    atomReceipt, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsAtomQuery [variableExpression "output"])
      atomResultBody generatedCheckedOpenResultFallback atomContinuation
      (environment11 .atom owner revision head arity occurrence declarationHead
        inputs remaining modes accepted) holeReceipt trueValue
      (environment11 .atom owner revision head arity occurrence declarationHead
        inputs remaining modes accepted) atomReceipt atomResultBody evaluated
      selected

theorem normalizes_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source predicate owner revision head arity occurrence declarationHead
            inputs remaining modes accepted)) =
      match predicate with
      | .undefined =>
          haltedTarget .undefined owner revision head arity occurrence
            declarationHead inputs remaining modes accepted undefinedReceipt
      | .hole =>
          haltedTarget .hole owner revision head arity occurrence
            declarationHead inputs remaining modes accepted holeReceipt
      | .atom =>
          haltedTarget .atom owner revision head arity occurrence
            declarationHead inputs remaining modes accepted atomReceipt := by
  change normalizeFirstUsing coldRelations StructuredC.language 1 (40 + 24)
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (data predicate owner revision head arity occurrence declarationHead
          inputs remaining modes accepted).source) = _
  rw [normalize_prefix_exact
    (data predicate owner revision head arity occurrence declarationHead inputs
      remaining modes accepted) 40]
  cases predicate with
  | undefined =>
      simp only [normalizeFirstAt,
        undefined_decision_true_rewrite_exact owner revision head arity
          occurrence declarationHead inputs remaining modes accepted]
      exact normalize_suffix_exact .undefined owner revision head arity
        occurrence declarationHead inputs remaining modes accepted
        undefinedReceipt baseContinuation 35
  | hole =>
      simp only [normalizeFirstAt,
        undefined_decision_false_rewrite_exact .hole (by decide) owner revision
          head arity occurrence declarationHead inputs remaining modes accepted]
      simp only [undefined_fallback_append_rewrite_exact .hole owner revision
        head arity occurrence declarationHead inputs remaining modes accepted]
      simp only [hole_decision_true_rewrite_exact owner revision head arity
        occurrence declarationHead inputs remaining modes accepted]
      exact normalize_suffix_exact .hole owner revision head arity occurrence
        declarationHead inputs remaining modes accepted holeReceipt
        holeContinuation 33
  | atom =>
      simp only [normalizeFirstAt,
        undefined_decision_false_rewrite_exact .atom (by decide) owner revision
          head arity occurrence declarationHead inputs remaining modes accepted]
      simp only [undefined_fallback_append_rewrite_exact .atom owner revision
        head arity occurrence declarationHead inputs remaining modes accepted]
      simp only [hole_decision_false_rewrite_exact owner revision
        head arity occurrence declarationHead inputs remaining modes accepted]
      simp only [hole_fallback_append_rewrite_exact owner revision head arity
        occurrence declarationHead inputs remaining modes accepted]
      simp only [atom_decision_true_rewrite_exact owner revision head arity
        occurrence declarationHead inputs remaining modes accepted]
      exact normalize_suffix_exact .atom owner revision head arity occurrence
        declarationHead inputs remaining modes accepted atomReceipt
        atomContinuation 31

abbrev execution
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (source predicate owner revision head arity occurrence declarationHead
          inputs remaining modes accepted)) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
      (source predicate owner revision head arity occurrence declarationHead
        inputs remaining modes accepted))

theorem execution_observation_exact
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    terminalControl?
        (execution predicate owner revision head arity occurrence
          declarationHead inputs remaining modes accepted).endpoint =
      some (target predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted) := by
  have endpoint := (execution predicate owner revision head arity occurrence
    declarationHead inputs remaining modes accepted).endpoint_eq
  rw [endpoint, normalizes_exact predicate owner revision head arity occurrence
    declarationHead inputs remaining modes accepted]
  cases predicate <;>
    exact terminal_observation_exact _ owner revision head arity occurrence
      declarationHead inputs remaining modes accepted _

theorem execution_path_bounded
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    (execution predicate owner revision head arity occurrence declarationHead
      inputs remaining modes accepted).path.length ≤ 64 :=
  (execution predicate owner revision head arity occurrence declarationHead
    inputs remaining modes accepted).length_le

theorem execution_path_nonempty
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    0 < (execution predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted).path.length := by
  apply (execution predicate owner revision head arity occurrence
    declarationHead inputs remaining modes accepted).nonempty_of_reduct
  · decide
  · change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (data predicate owner revision head arity occurrence declarationHead
            inputs remaining modes accepted).source) ≠ []
    rw [phase_rewrite_exact
      (data predicate owner revision head arity occurrence declarationHead
        inputs remaining modes accepted)]
    simp

theorem normalized_observation_iff
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source predicate owner revision head arity occurrence
              declarationHead inputs remaining modes accepted))) =
        some observed ↔
      observed = target predicate owner revision head arity occurrence
        declarationHead inputs remaining modes accepted := by
  rw [normalizes_exact predicate owner revision head arity occurrence
    declarationHead inputs remaining modes accepted]
  cases predicate <;>
    simp only [terminal_observation_exact]
  all_goals simp [eq_comm]

theorem wrong_target_rejected
    (predicate : LiteralPredicate)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (occurrence : Nat) (declarationHead : String) (inputs : List Term)
    (remaining : List ArrowDeclaration) (modes : List ArgMode)
    (accepted : List GuardPlan) (observed : CompileLanguageControl)
    (wrong : observed ≠ target predicate owner revision head arity occurrence
      declarationHead inputs remaining modes accepted) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source predicate owner revision head arity occurrence
              declarationHead inputs remaining modes accepted))) ≠
        some observed := by
  intro invented
  exact wrong ((normalized_observation_iff predicate owner revision head arity
    occurrence declarationHead inputs remaining modes accepted observed).mp
      invented)

#print axioms literal_classification_exact
#print axioms source_step
#print axioms normalizes_exact
#print axioms execution_observation_exact
#print axioms execution_path_bounded
#print axioms execution_path_nonempty
#print axioms normalized_observation_iff
#print axioms wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCLiteralResultSimulation
