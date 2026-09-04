import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSkipAritySimulation

/-!
# Generated StructuredC realization of begin-declaration

This is the final running-state family.  The generated dispatcher proves that
the declaration head agrees with the requested head, bypasses skip-arity when
the input lengths agree, then constructs the exact argument-compilation state
from twelve ordered operands, including the intentionally repeated authored
head and input-row occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCBeginDeclarationSimulation

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
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSkipHeadSimulation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSkipAritySimulation

def beginSource
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    CompileLanguageControl :=
  skipAritySource owner revision declaration.inputTypes.length declaration
    remaining accepted

def beginTarget
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    CompileLanguageControl :=
  .arguments owner revision declaration.function declaration.inputTypes.length
    declaration remaining declaration.inputTypes [] accepted

def beginGuardReceipt : Pattern :=
  externalReceipt arityMatchesQuery arityGuardReceipt

def beginDeltaReceipt : Pattern :=
  externalReceipt startCompileArgumentsDelta beginGuardReceipt

def beginEffectStatement : Pattern :=
  effect (call startCompileArgumentsDelta
    (["state", "owner", "revision", "declaration_head", "arity",
      "occurrence", "declaration_head", "inputs", "output", "remaining",
      "inputs", "accepted"].map variableExpression))

def beginReturnStatements : Pattern :=
  statements [returnSymbol advancedOutcome]

theorem after_skipArity_spine :
    generatedRunningAfterSkipArity =
      consStatement beginDeclarationDecision
        generatedRunningAfterBeginDeclaration := by
  rfl

theorem skipArity_guard_false_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement skipArityDecision rest)
          (environment10 owner revision declaration.function
            declaration.inputTypes.length declaration remaining accepted)
          receipt13) =
      [run (StructuredC.appendStatements (statements []) rest)
        (environment10 owner revision declaration.function
          declaration.inputTypes.length declaration remaining accepted)
        arityGuardReceipt] := by
  have evaluated := arityDiffers_false_evaluation_exact
    declaration.inputTypes
    (environment10 owner revision declaration.function
      declaration.inputTypes.length declaration remaining accepted)
    receipt13
    (by
      simpa [inputsValue, arityValue] using
        arity_guard_operands_lookup owner revision declaration.inputTypes.length
          declaration remaining accepted)
  have selected :
      selectBranch? falseValue skipAritySuccess (statements []) =
        some (statements []) := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    skipArityDecision, skipArityCondition, ifThenElse, node, StructuredC.a,
    arityGuardReceipt] using
    if_rewriteAt_exact_of_evaluate coldHandler skipArityCondition
      skipAritySuccess (statements []) rest
      (environment10 owner revision declaration.function
        declaration.inputTypes.length declaration remaining accepted)
      receipt13 falseValue
      (environment10 owner revision declaration.function
        declaration.inputTypes.length declaration remaining accepted)
      arityGuardReceipt (statements []) evaluated selected

theorem empty_skipArity_branch_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements (statements []) continuation)
          (environment10 owner revision declaration.function
            declaration.inputTypes.length declaration remaining accepted)
          arityGuardReceipt) =
      [run continuation
        (environment10 owner revision declaration.function
          declaration.inputTypes.length declaration remaining accepted)
        arityGuardReceipt] := by
  simpa [statements, StructuredC.nilStatements, node, StructuredC.a] using
    appendEmptyTransition_rewriteAt_exact coldRelations continuation
      (environment10 owner revision declaration.function
        declaration.inputTypes.length declaration remaining accepted)
      arityGuardReceipt

theorem after_skipArity_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedRunningAfterSkipArity
          continuation)
          (environment10 owner revision declaration.function
            declaration.inputTypes.length declaration remaining accepted)
          arityGuardReceipt) =
      [run (consStatement beginDeclarationDecision
          (StructuredC.appendStatements generatedRunningAfterBeginDeclaration
            continuation))
        (environment10 owner revision declaration.function
          declaration.inputTypes.length declaration remaining accepted)
        arityGuardReceipt] := by
  rw [after_skipArity_spine]
  exact appendConsTransition_rewriteAt_exact coldRelations
    beginDeclarationDecision generatedRunningAfterBeginDeclaration continuation
    (environment10 owner revision declaration.function
      declaration.inputTypes.length declaration remaining accepted)
    arityGuardReceipt

theorem begin_guard_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement beginDeclarationDecision rest)
          (environment10 owner revision declaration.function
            declaration.inputTypes.length declaration remaining accepted)
          arityGuardReceipt) =
      [run (StructuredC.appendStatements beginDeclarationSuccess rest)
        (environment10 owner revision declaration.function
          declaration.inputTypes.length declaration remaining accepted)
        beginGuardReceipt] := by
  have evaluated := arityMatches_evaluation_exact declaration.inputTypes
    (environment10 owner revision declaration.function
      declaration.inputTypes.length declaration remaining accepted)
    arityGuardReceipt
    (by
      simpa [inputsValue, arityValue] using
        arity_guard_operands_lookup owner revision declaration.inputTypes.length
          declaration remaining accepted)
  have selected :
      selectBranch? trueValue beginDeclarationSuccess (statements []) =
        some beginDeclarationSuccess := by simp [selectBranch?]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    beginDeclarationDecision, beginDeclarationCondition, ifThenElse, node,
    StructuredC.a, beginGuardReceipt] using
    if_rewriteAt_exact_of_evaluate coldHandler beginDeclarationCondition
      beginDeclarationSuccess (statements []) rest
      (environment10 owner revision declaration.function
        declaration.inputTypes.length declaration remaining accepted)
      arityGuardReceipt trueValue
      (environment10 owner revision declaration.function
        declaration.inputTypes.length declaration remaining accepted)
      beginGuardReceipt beginDeclarationSuccess evaluated selected

theorem begin_success_append_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements beginDeclarationSuccess continuation)
          (environment10 owner revision declaration.function
            declaration.inputTypes.length declaration remaining accepted)
          beginGuardReceipt) =
      [run (consStatement beginEffectStatement
          (StructuredC.appendStatements beginReturnStatements continuation))
        (environment10 owner revision declaration.function
          declaration.inputTypes.length declaration remaining accepted)
        beginGuardReceipt] := by
  rw [beginDeclarationSuccess_shape]
  simpa [beginEffectStatement, beginReturnStatements, statements, node,
    StructuredC.consStatement, StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations beginEffectStatement
      beginReturnStatements continuation
      (environment10 owner revision declaration.function
        declaration.inputTypes.length declaration remaining accepted)
      beginGuardReceipt

def environment11
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) : Pattern :=
  bindName "state" (stateValue
      (beginTarget owner revision declaration remaining accepted))
    (environment10 owner revision declaration.function
      declaration.inputTypes.length declaration remaining accepted)

theorem begin_delta_operands_lookup
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    List.Forall₂
      (fun slot value =>
        lookup? (environment10 owner revision declaration.function
          declaration.inputTypes.length declaration remaining accepted)
          (identifier slot) = some value)
      ["state", "owner", "revision", "declaration_head", "arity",
        "occurrence", "declaration_head", "inputs", "output", "remaining",
        "inputs", "accepted"]
      [ stateValue (beginSource owner revision declaration remaining accepted)
      , ownerValue owner
      , revisionValue revision
      , declarationHeadValue declaration
      , arityValue declaration.inputTypes.length
      , occurrenceValue declaration
      , declarationHeadValue declaration
      , inputsValue declaration
      , outputValue declaration
      , remainingValue remaining
      , inputsValue declaration
      , acceptedValue accepted ] := by
  simp [beginSource, skipAritySource, skipHeadSource, environment10,
    environment9, environment8, environment7, environment6, environment5,
    environment4, environment3, environment2, environment1, environment0,
    initialEnvironment, ownerValue, revisionValue, declarationHeadValue,
    arityValue, occurrenceValue, inputsValue, outputValue, remainingValue,
    acceptedValue, lookup?, bindName, environmentBind, environmentEmpty,
    identifier, node, token]

theorem begin_delta_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement beginEffectStatement rest)
          (environment10 owner revision declaration.function
            declaration.inputTypes.length declaration remaining accepted)
          beginGuardReceipt) =
      [run rest
        (environment11 owner revision declaration remaining accepted)
        beginDeltaReceipt] := by
  have evaluated := beginDeclaration_delta_evaluation_exact owner revision
    declaration remaining accepted
    (environment10 owner revision declaration.function
      declaration.inputTypes.length declaration remaining accepted)
    beginGuardReceipt
    (by
      simpa [beginSource, skipAritySource, skipHeadSource] using
        source_lookup10 owner revision declaration.function
          declaration.inputTypes.length declaration remaining accepted)
    (by
      simpa [beginSource, skipAritySource, skipHeadSource, ownerValue,
        revisionValue, declarationHeadValue, arityValue, occurrenceValue,
        inputsValue, outputValue, remainingValue, acceptedValue] using
        begin_delta_operands_lookup owner revision declaration remaining
          accepted)
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    beginEffectStatement, environment11, beginDeltaReceipt, effect, node,
    StructuredC.a] using
    effect_rewriteAt_exact_of_evaluate coldHandler
      (call startCompileArgumentsDelta
        (["state", "owner", "revision", "declaration_head", "arity",
          "occurrence", "declaration_head", "inputs", "output", "remaining",
          "inputs", "accepted"].map variableExpression)) rest
      (environment10 owner revision declaration.function
        declaration.inputTypes.length declaration remaining accepted)
      beginGuardReceipt valueUnit
      (environment11 owner revision declaration remaining accepted)
      beginDeltaReceipt evaluated

theorem begin_delta_effect_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement
          (effect (call startCompileArgumentsDelta
            (["state", "owner", "revision", "declaration_head", "arity",
              "occurrence", "declaration_head", "inputs", "output",
              "remaining", "inputs", "accepted"].map variableExpression)))
          rest)
          (environment10 owner revision declaration.function
            declaration.inputTypes.length declaration remaining accepted)
          beginGuardReceipt) =
      [run rest
        (environment11 owner revision declaration remaining accepted)
        beginDeltaReceipt] := by
  simpa [beginEffectStatement] using
    begin_delta_rewrite_exact owner revision declaration remaining accepted rest

theorem begin_return_statements_append_rewrite_exact
    (continuation environment receipt : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements beginReturnStatements continuation)
          environment receipt) =
      [run (consStatement (returnSymbol advancedOutcome)
          (StructuredC.appendStatements (statements []) continuation))
        environment receipt] := by
  simpa [beginReturnStatements, statements, node, StructuredC.consStatement,
    StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations
      (returnSymbol advancedOutcome) (statements []) continuation environment
      receipt

theorem begin_return_rewrite_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (returnSymbol advancedOutcome) rest)
          (environment11 owner revision declaration remaining accepted)
          beginDeltaReceipt) =
      [halted (StructuredC.a "structured-c:outcome-return"
          [valueSymbol advancedOutcome])
        (environment11 owner revision declaration remaining accepted)
        beginDeltaReceipt] := by
  have evaluated := evaluate_symbol_exact coldHandler advancedOutcome
    (environment11 owner revision declaration remaining accepted)
    beginDeltaReceipt
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    returnSymbol, returnExpression, node, StructuredC.a] using
    return_rewriteAt_exact_of_evaluate coldHandler (symbol advancedOutcome)
      rest (environment11 owner revision declaration remaining accepted)
      beginDeltaReceipt (valueSymbol advancedOutcome)
      (environment11 owner revision declaration remaining accepted)
      beginDeltaReceipt evaluated

def haltedTarget
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) : Pattern :=
  halted (StructuredC.a "structured-c:outcome-return"
      [valueSymbol advancedOutcome])
    (environment11 owner revision declaration remaining accepted)
    beginDeltaReceipt

theorem terminal_observation_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    terminalControl?
        (haltedTarget owner revision declaration remaining accepted) =
      some (beginTarget owner revision declaration remaining accepted) := by
  simp [haltedTarget, terminalControl?, environment11, beginTarget, halted,
    StructuredC.a, lookup?, bindName, environmentBind, identifier,
    decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?, abiValue,
    node, token]

theorem source_step
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    compileLanguageGSLT.Step
      (beginSource owner revision declaration remaining accepted)
      (beginTarget owner revision declaration remaining accepted) := by
  change compileLanguageStep?
      (beginSource owner revision declaration remaining accepted) =
    some (beginTarget owner revision declaration remaining accepted)
  simp [beginSource, beginTarget, skipAritySource, skipHeadSource,
    compileLanguageStep?, Relevant]

/-- The generated running-state dispatcher normalizes through both rejecting
guards and takes the exact declaration-start branch when head and arity agree. -/
theorem normalizes_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (beginSource owner revision declaration remaining accepted)) =
      haltedTarget owner revision declaration remaining accepted := by
  unfold beginSource
  unfold skipAritySource
  unfold normalizeFirstUsing
  simp only [normalizeFirstAt,
    phase_rewrite_exact owner revision declaration.function
      declaration.inputTypes.length declaration remaining accepted]
  simp only [dispatcher_append_rewrite_exact owner revision
    declaration.function declaration.inputTypes.length declaration remaining
    accepted]
  simp only [owner_declare_rewrite_exact owner revision declaration.function
    declaration.inputTypes.length declaration remaining accepted]
  simp only [commonTail1_shape, appendConsTransition_rewriteAt_exact]
  simp only [revision_declare_rewrite_exact owner revision
    declaration.function declaration.inputTypes.length declaration remaining
    accepted]
  simp only [commonTail2_shape, appendConsTransition_rewriteAt_exact]
  simp only [head_declare_rewrite_exact owner revision declaration.function
    declaration.inputTypes.length declaration remaining accepted]
  simp only [commonTail3_shape, appendConsTransition_rewriteAt_exact]
  simp only [arity_declare_rewrite_exact owner revision declaration.function
    declaration.inputTypes.length declaration remaining accepted]
  simp only [commonTail4_shape, appendConsTransition_rewriteAt_exact]
  simp only [accepted_declare_rewrite_exact owner revision
    declaration.function declaration.inputTypes.length declaration remaining
    accepted]
  simp only [commonTail5_shape, appendConsTransition_rewriteAt_exact]
  simp only [running_decision_rewrite_exact owner revision
    declaration.function declaration.inputTypes.length declaration remaining
    accepted]
  simp only [fallback_append_rewrite_exact owner revision declaration.function
    declaration.inputTypes.length declaration remaining accepted]
  simp only [remaining_declare_rewrite_exact owner revision declaration.function
    declaration.inputTypes.length declaration remaining accepted]
  simp only [declarationTail1_shape, appendConsTransition_rewriteAt_exact]
  simp only [occurrence_declare_rewrite_exact owner revision
    declaration.function declaration.inputTypes.length declaration remaining
    accepted]
  simp only [declarationTail2_shape, appendConsTransition_rewriteAt_exact]
  simp only [declarationHead_declare_rewrite_exact owner revision
    declaration.function declaration.inputTypes.length declaration remaining
    accepted]
  simp only [declarationTail3_shape, appendConsTransition_rewriteAt_exact]
  simp only [inputs_declare_rewrite_exact owner revision declaration.function
    declaration.inputTypes.length declaration remaining accepted]
  simp only [declarationTail4_shape, appendConsTransition_rewriteAt_exact]
  simp only [output_declare_rewrite_exact owner revision declaration.function
    declaration.inputTypes.length declaration remaining accepted]
  simp only [declarationTail5_shape, appendConsTransition_rewriteAt_exact]
  simp only [skipHead_guard_false_rewrite_exact owner revision
    declaration.inputTypes.length declaration remaining accepted]
  simp only [empty_skipHead_branch_rewrite_exact owner revision
    declaration.inputTypes.length declaration remaining accepted]
  simp only [after_skipHead_append_rewrite_exact owner revision
    declaration.inputTypes.length declaration remaining accepted]
  simp only [skipArity_guard_false_rewrite_exact owner revision declaration
    remaining accepted]
  simp only [empty_skipArity_branch_rewrite_exact owner revision declaration
    remaining accepted]
  simp only [after_skipArity_append_rewrite_exact owner revision declaration
    remaining accepted]
  simp only [begin_guard_rewrite_exact owner revision declaration remaining
    accepted]
  simp only [begin_success_append_rewrite_exact owner revision declaration
    remaining accepted]
  simp only [beginEffectStatement]
  simp only [begin_delta_effect_rewrite_exact owner revision declaration
    remaining accepted]
  simp only [begin_return_statements_append_rewrite_exact]
  simp only [begin_return_rewrite_exact owner revision declaration remaining
    accepted]
  simp only [halted_rewriteAt_empty]
  rfl

abbrev run
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (beginSource owner revision declaration remaining accepted)) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
      (beginSource owner revision declaration remaining accepted))

theorem run_endpoint_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    (run owner revision declaration remaining accepted).endpoint =
      haltedTarget owner revision declaration remaining accepted := by
  calc
    _ = normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (beginSource owner revision declaration remaining accepted)) :=
      (run owner revision declaration remaining accepted).endpoint_eq
    _ = _ := normalizes_exact owner revision declaration remaining accepted

theorem run_observation_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    terminalControl?
        (run owner revision declaration remaining accepted).endpoint =
      some (beginTarget owner revision declaration remaining accepted) := by
  rw [run_endpoint_exact owner revision declaration remaining accepted]
  exact terminal_observation_exact owner revision declaration remaining accepted

theorem run_path_bounded
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    (run owner revision declaration remaining accepted).path.length ≤ 64 :=
  (run owner revision declaration remaining accepted).length_le

theorem run_path_nonempty
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    0 < (run owner revision declaration remaining accepted).path.length := by
  apply (run owner revision declaration remaining accepted).nonempty_of_reduct
  · decide
  · unfold beginSource
    unfold skipAritySource
    rw [phase_rewrite_exact owner revision declaration.function
      declaration.inputTypes.length declaration remaining accepted]
    simp

theorem step_realization
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan) :
    ∃ endpoint : Pattern,
      ∃ path : ExecutionPath coldGSLT
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (beginSource owner revision declaration remaining accepted))
          endpoint,
      terminalControl? endpoint =
          some (beginTarget owner revision declaration remaining accepted) ∧
        0 < path.length ∧ path.length ≤ 64 := by
  let execution := run owner revision declaration remaining accepted
  refine ⟨execution.endpoint, execution.path, ?_, ?_, ?_⟩
  · exact run_observation_exact owner revision declaration remaining accepted
  · exact run_path_nonempty owner revision declaration remaining accepted
  · exact run_path_bounded owner revision declaration remaining accepted

theorem normalized_observation_iff
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (beginSource owner revision declaration remaining accepted))) =
        some observed ↔
      observed = beginTarget owner revision declaration remaining accepted := by
  rw [normalizes_exact owner revision declaration remaining accepted]
  have observedExact := terminal_observation_exact owner revision declaration
    remaining accepted
  rw [observedExact]
  simp [eq_comm]

theorem wrong_target_rejected
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (observed : CompileLanguageControl)
    (wrong : observed ≠ beginTarget owner revision declaration remaining
      accepted) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (beginSource owner revision declaration remaining accepted))) ≠
      some observed := by
  intro invented
  exact wrong ((normalized_observation_iff owner revision declaration remaining
    accepted observed).mp invented)

#print axioms source_step
#print axioms normalizes_exact
#print axioms run_endpoint_exact
#print axioms run_observation_exact
#print axioms run_path_bounded
#print axioms run_path_nonempty
#print axioms step_realization
#print axioms normalized_observation_iff
#print axioms wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCBeginDeclarationSimulation
