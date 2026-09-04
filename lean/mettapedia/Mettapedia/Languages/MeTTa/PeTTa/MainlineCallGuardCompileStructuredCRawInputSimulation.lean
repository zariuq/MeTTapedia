import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation

/-!
# Generated StructuredC realization of the raw-atom input family

This is the first nonempty argument family.  The source rule classifies the
exact PeTTa `Atom` type as a raw argument and consumes one cursor entry.  The
generated target program reaches that same state only by executing its ordered
literal decision, reconstructing every delta operand, invoking the independent
PeTTa classifier, and returning through the StructuredC semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCRawInputSimulation

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

def inputData
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : InputStateData :=
  { owner, revision, head, arity, declaration, remaining
    expected := atomType
    inputCursor, modes, accepted }

def source
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  (inputData owner revision head arity declaration remaining inputCursor modes
    accepted).source

def target
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  .arguments owner revision head arity declaration remaining inputCursor
    (modes ++ [.rawAtom]) accepted

def environment13
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  (inputData owner revision head arity declaration remaining inputCursor modes
    accepted).environment13

def environment14
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  bindName "state"
    (stateValue (target owner revision head arity declaration remaining
      inputCursor modes accepted))
    (environment13 owner revision head arity declaration remaining inputCursor
      modes accepted)

def receipt16 : Pattern := externalReceipt termIsAtomQuery receipt15
def receipt17 : Pattern := externalReceipt appendArgumentModeDelta receipt16

def baseContinuation : Pattern :=
  StructuredC.appendStatements (statements []) (statements [])

def decisionRest : Pattern :=
  StructuredC.appendStatements (statements []) baseContinuation

def effectStatement : Pattern :=
  effect (call appendArgumentModeDelta
    (([ "state", "owner", "revision", "head", "arity", "occurrence"
      , "declaration_head", "inputs", "output", "remaining"
      , "input_cursor", "modes", "accepted" ].map variableExpression) ++
      [symbol rawArgumentMode, symbol noModePayload]))

def returnStatements : Pattern := statements [returnSymbol advancedOutcome]

theorem source_lookup13
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    lookup?
        (environment13 owner revision head arity declaration remaining
          inputCursor modes accepted)
        (identifier "state") =
      some (stateValue (source owner revision head arity declaration remaining
        inputCursor modes accepted)) := by
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
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    lookup?
        (environment13 owner revision head arity declaration remaining
          inputCursor modes accepted)
        (identifier "expected") = some (abiValue (encodeTerm atomType)) := by
  simp [environment13, inputData, InputStateData.environment13,
    InputStateData.environment12, lookup?, bindName, environmentBind,
    identifier, node, token, InputStateData.expectedValue]

theorem literal_dispatcher_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (prefixEndpoint
          (inputData owner revision head arity declaration remaining
            inputCursor modes accepted)) =
      [run (consStatement generatedAtomInputDecision decisionRest)
        (environment13 owner revision head arity declaration remaining
          inputCursor modes accepted) receipt15] := by
  rw [prefixEndpoint, generatedLiteralInputDispatcher_shape]
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement generatedAtomInputDecision (statements []))
        baseContinuation)
        (environment13 owner revision head arity declaration remaining
          inputCursor modes accepted) receipt15) = _
  simpa [decisionRest] using appendConsTransition_rewriteAt_exact
    coldRelations generatedAtomInputDecision (statements []) baseContinuation
    (environment13 owner revision head arity declaration remaining inputCursor
      modes accepted) receipt15

theorem atom_decision_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement generatedAtomInputDecision decisionRest)
          (environment13 owner revision head arity declaration remaining
            inputCursor modes accepted) receipt15) =
      [run (StructuredC.appendStatements rawInputBody decisionRest)
        (environment13 owner revision head arity declaration remaining
          inputCursor modes accepted) receipt16] := by
  have evaluated :
      evaluate? coldHandler
          (call termIsAtomQuery [variableExpression "expected"])
          (environment13 owner revision head arity declaration remaining
            inputCursor modes accepted) receipt15 =
        some ⟨.value trueValue,
          environment13 owner revision head arity declaration remaining
            inputCursor modes accepted,
          receipt16⟩ := by
    simpa [LiteralPredicate.externalName, LiteralPredicate.term, receipt16]
      using literalPredicate_evaluation_exact .atom atomType
        (environment13 owner revision head arity declaration remaining
          inputCursor modes accepted) receipt15
        (expected_lookup13 owner revision head arity declaration remaining
          inputCursor modes accepted)
  have selected :
      selectBranch? trueValue rawInputBody generatedAtomInputFallback =
        some rawInputBody := by
    simp [selectBranch?, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    generatedAtomInputDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call termIsAtomQuery [variableExpression "expected"])
      rawInputBody generatedAtomInputFallback decisionRest
      (environment13 owner revision head arity declaration remaining
        inputCursor modes accepted) receipt15 trueValue
      (environment13 owner revision head arity declaration remaining
        inputCursor modes accepted) receipt16 rawInputBody evaluated selected

theorem raw_body_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements rawInputBody decisionRest)
          (environment13 owner revision head arity declaration remaining
            inputCursor modes accepted) receipt16) =
      [run (consStatement effectStatement
          (StructuredC.appendStatements returnStatements decisionRest))
        (environment13 owner revision head arity declaration remaining
          inputCursor modes accepted) receipt16] := by
  rw [rawInputBody_shape]
  simpa [effectStatement, returnStatements, statements, node,
    StructuredC.consStatement, StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations effectStatement
      returnStatements decisionRest
      (environment13 owner revision head arity declaration remaining
        inputCursor modes accepted) receipt16

theorem delta_operands_lookup
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    List.Forall₂
      (fun slot value =>
        lookup?
          (environment13 owner revision head arity declaration remaining
            inputCursor modes accepted) (identifier slot) = some value)
      [ "state", "owner", "revision", "head", "arity", "occurrence"
      , "declaration_head", "inputs", "output", "remaining", "input_cursor"
      , "modes", "accepted" ]
      [ stateValue (source owner revision head arity declaration remaining
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

theorem delta_evaluation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    evaluate? coldHandler
        (call appendArgumentModeDelta
          (([ "state", "owner", "revision", "head", "arity", "occurrence"
            , "declaration_head", "inputs", "output", "remaining"
            , "input_cursor", "modes", "accepted" ].map
              variableExpression) ++
            [symbol rawArgumentMode, symbol noModePayload]))
        (environment13 owner revision head arity declaration remaining
          inputCursor modes accepted) receipt16 =
      some ⟨.value valueUnit,
        environment14 owner revision head arity declaration remaining
          inputCursor modes accepted,
        receipt17⟩ := by
  have handled := handler_appendArgumentMode_delta_exact owner revision head
    arity declaration remaining atomType inputCursor modes accepted .rawAtom
    (environment13 owner revision head arity declaration remaining inputCursor
      modes accepted) receipt16
    (by simp [compileArgMode])
    (source_lookup13 owner revision head arity declaration remaining
      inputCursor modes accepted)
  have evaluated := evaluate_variable_constant_call_exact coldHandler
    appendArgumentModeDelta
    [ "state", "owner", "revision", "head", "arity", "occurrence"
    , "declaration_head", "inputs", "output", "remaining", "input_cursor"
    , "modes", "accepted" ]
    [ stateValue (source owner revision head arity declaration remaining
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
    , abiValue (encodePlans accepted) ]
    [valueSymbol rawArgumentMode, valueSymbol noModePayload]
    (environment13 owner revision head arity declaration remaining inputCursor
      modes accepted) receipt16 _
    (delta_operands_lookup owner revision head arity declaration remaining
      inputCursor modes accepted) handled
  simpa [symbol, environment14, target, receipt17] using evaluated

theorem delta_effect_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement effectStatement rest)
          (environment13 owner revision head arity declaration remaining
            inputCursor modes accepted) receipt16) =
      [run rest
        (environment14 owner revision head arity declaration remaining
          inputCursor modes accepted) receipt17] := by
  have evaluated := delta_evaluation_exact owner revision head arity
    declaration remaining inputCursor modes accepted
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    effectStatement, effect, node, StructuredC.a] using
    effect_rewriteAt_exact_of_evaluate coldHandler
      (call appendArgumentModeDelta
        (([ "state", "owner", "revision", "head", "arity", "occurrence"
          , "declaration_head", "inputs", "output", "remaining"
          , "input_cursor", "modes", "accepted" ].map
            variableExpression) ++
          [symbol rawArgumentMode, symbol noModePayload])) rest
      (environment13 owner revision head arity declaration remaining
        inputCursor modes accepted) receipt16 valueUnit
      (environment14 owner revision head arity declaration remaining
        inputCursor modes accepted) receipt17 evaluated

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
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (returnSymbol advancedOutcome) rest)
          (environment14 owner revision head arity declaration remaining
            inputCursor modes accepted) receipt17) =
      [halted (StructuredC.a "structured-c:outcome-return"
          [valueSymbol advancedOutcome])
        (environment14 owner revision head arity declaration remaining
          inputCursor modes accepted) receipt17] := by
  have evaluated := evaluate_symbol_exact coldHandler advancedOutcome
    (environment14 owner revision head arity declaration remaining inputCursor
      modes accepted) receipt17
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    returnSymbol, returnExpression, node, StructuredC.a] using
    return_rewriteAt_exact_of_evaluate coldHandler (symbol advancedOutcome)
      rest
      (environment14 owner revision head arity declaration remaining
        inputCursor modes accepted) receipt17 (valueSymbol advancedOutcome)
      (environment14 owner revision head arity declaration remaining
        inputCursor modes accepted) receipt17 evaluated

def haltedTarget
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) : Pattern :=
  halted (StructuredC.a "structured-c:outcome-return"
      [valueSymbol advancedOutcome])
    (environment14 owner revision head arity declaration remaining inputCursor
      modes accepted) receipt17

theorem terminal_observation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    terminalControl?
        (haltedTarget owner revision head arity declaration remaining
          inputCursor modes accepted) =
      some (target owner revision head arity declaration remaining inputCursor
        modes accepted) := by
  simp [haltedTarget, terminalControl?, environment14, target, halted,
    StructuredC.a, lookup?, bindName, environmentBind, identifier,
    decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?, abiValue, node,
    token]

theorem source_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    compileLanguageGSLT.Step
      (source owner revision head arity declaration remaining inputCursor modes
        accepted)
      (target owner revision head arity declaration remaining inputCursor modes
        accepted) := by
  change compileLanguageStep?
      (source owner revision head arity declaration remaining inputCursor modes
        accepted) =
    some (target owner revision head arity declaration remaining inputCursor
      modes accepted)
  simp [source, inputData, InputStateData.source, target,
    compileLanguageStep?, compileArgMode]

theorem normalizes_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source owner revision head arity declaration remaining inputCursor
            modes accepted)) =
      haltedTarget owner revision head arity declaration remaining inputCursor
        modes accepted := by
  change normalizeFirstUsing coldRelations StructuredC.language 1 (35 + 29)
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (inputData owner revision head arity declaration remaining inputCursor
          modes accepted).source) = _
  rw [normalize_prefix_exact
    (inputData owner revision head arity declaration remaining inputCursor
      modes accepted) 35]
  simp only [normalizeFirstAt,
    literal_dispatcher_append_rewrite_exact owner revision head arity
      declaration remaining inputCursor modes accepted]
  simp only [atom_decision_rewrite_exact owner revision head arity declaration
    remaining inputCursor modes accepted]
  simp only [raw_body_append_rewrite_exact owner revision head arity declaration
    remaining inputCursor modes accepted]
  simp only [delta_effect_rewrite_exact owner revision head arity declaration
    remaining inputCursor modes accepted]
  simp only [return_statements_append_rewrite_exact]
  simp only [return_rewrite_exact owner revision head arity declaration
    remaining inputCursor modes accepted]
  simp only [halted_rewriteAt_empty]
  rfl

abbrev run
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (source owner revision head arity declaration remaining inputCursor
          modes accepted)) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
      (source owner revision head arity declaration remaining inputCursor modes
        accepted))

theorem run_endpoint_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    (run owner revision head arity declaration remaining inputCursor modes
      accepted).endpoint =
      haltedTarget owner revision head arity declaration remaining inputCursor
        modes accepted := by
  calc
    _ = normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source owner revision head arity declaration remaining inputCursor
            modes accepted)) :=
      (run owner revision head arity declaration remaining inputCursor modes
        accepted).endpoint_eq
    _ = _ := normalizes_exact owner revision head arity declaration remaining
      inputCursor modes accepted

theorem run_observation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    terminalControl?
        (run owner revision head arity declaration remaining inputCursor modes
          accepted).endpoint =
      some (target owner revision head arity declaration remaining inputCursor
        modes accepted) := by
  rw [run_endpoint_exact owner revision head arity declaration remaining
    inputCursor modes accepted]
  exact terminal_observation_exact owner revision head arity declaration
    remaining inputCursor modes accepted

theorem run_path_bounded
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    (run owner revision head arity declaration remaining inputCursor modes
      accepted).path.length ≤ 64 :=
  (run owner revision head arity declaration remaining inputCursor modes
    accepted).length_le

theorem run_path_nonempty
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    0 < (run owner revision head arity declaration remaining inputCursor modes
      accepted).path.length := by
  apply (run owner revision head arity declaration remaining inputCursor modes
    accepted).nonempty_of_reduct
  · decide
  · change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (inputData owner revision head arity declaration remaining
            inputCursor modes accepted).source) ≠ []
    rw [Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation.phase_rewrite_exact
      (inputData owner revision head arity declaration remaining inputCursor
        modes accepted)]
    simp

theorem step_realization
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    ∃ endpoint : Pattern,
      ∃ path : ExecutionPath coldGSLT
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source owner revision head arity declaration remaining inputCursor
              modes accepted)) endpoint,
      terminalControl? endpoint =
          some (target owner revision head arity declaration remaining
            inputCursor modes accepted) ∧
        0 < path.length ∧ path.length ≤ 64 := by
  let execution := run owner revision head arity declaration remaining
    inputCursor modes accepted
  refine ⟨execution.endpoint, execution.path, ?_, ?_, ?_⟩
  · exact run_observation_exact owner revision head arity declaration remaining
      inputCursor modes accepted
  · exact run_path_nonempty owner revision head arity declaration remaining
      inputCursor modes accepted
  · exact run_path_bounded owner revision head arity declaration remaining
      inputCursor modes accepted

theorem normalized_observation_iff
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source owner revision head arity declaration remaining inputCursor
              modes accepted))) = some observed ↔
      observed = target owner revision head arity declaration remaining
        inputCursor modes accepted := by
  rw [normalizes_exact owner revision head arity declaration remaining
    inputCursor modes accepted]
  have observedExact := terminal_observation_exact owner revision head arity
    declaration remaining inputCursor modes accepted
  rw [observedExact]
  simp [eq_comm]

theorem wrong_target_rejected
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (observed : CompileLanguageControl)
    (wrong : observed ≠ target owner revision head arity declaration remaining
      inputCursor modes accepted) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source owner revision head arity declaration remaining inputCursor
              modes accepted))) ≠ some observed := by
  intro invented
  exact wrong ((normalized_observation_iff owner revision head arity declaration
    remaining inputCursor modes accepted observed).mp invented)

#print axioms source_step
#print axioms normalizes_exact
#print axioms run_endpoint_exact
#print axioms run_observation_exact
#print axioms run_path_bounded
#print axioms run_path_nonempty
#print axioms step_realization
#print axioms normalized_observation_iff
#print axioms wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCRawInputSimulation
