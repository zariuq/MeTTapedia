import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSkipHeadSimulation

/-!
# Generated StructuredC realization of the cold skip-arity transition

The skip-arity route shares the generated running-state and declaration
projections with skip-head.  It then proves that name equality bypasses the
earlier row, input-length disequality selects this row, and the exact
seven-field successor is constructed by the shared structural delta.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSkipAritySimulation

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

def skipAritySource
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  skipHeadSource owner revision declaration.function arity declaration remaining
    accepted

def skipArityTarget
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : CompileLanguageControl :=
  skipHeadTarget owner revision declaration.function arity remaining accepted

def arityGuardReceipt : Pattern :=
  externalReceipt arityDiffersQuery receipt13

def arityDeltaReceipt : Pattern :=
  externalReceipt setCompileRunningDelta arityGuardReceipt

def arityEffectStatement : Pattern :=
  effect (call setCompileRunningDelta
    (["state", "owner", "revision", "declaration_head", "arity",
      "remaining", "accepted"].map variableExpression))

def arityReturnStatements : Pattern :=
  statements [returnSymbol advancedOutcome]

theorem after_skipHead_spine :
    generatedRunningAfterSkipHead =
      consStatement skipArityDecision generatedRunningAfterSkipArity := by
  rfl

theorem skipHead_guard_false_rewrite_exact
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement skipHeadDecision rest)
          (environment10 owner revision declaration.function arity declaration
            remaining accepted) receipt12) =
      [run (StructuredC.appendStatements (statements []) rest)
        (environment10 owner revision declaration.function arity declaration
          remaining accepted) receipt13] := by
  have evaluated := nameNotEqual_false_evaluation_exact declaration.function
    (environment10 owner revision declaration.function arity declaration
      remaining accepted) receipt12
    (by
      simpa [declarationHeadValue, headValue] using
        guard_operands_lookup10 owner revision declaration.function arity
          declaration remaining accepted)
  have selected :
      selectBranch? falseValue skipHeadSuccess (statements []) =
        some (statements []) := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    skipHeadDecision, skipHeadCondition, ifThenElse, node, StructuredC.a,
    receipt13] using
    if_rewriteAt_exact_of_evaluate coldHandler skipHeadCondition
      skipHeadSuccess (statements []) rest
      (environment10 owner revision declaration.function arity declaration
        remaining accepted) receipt12 falseValue
      (environment10 owner revision declaration.function arity declaration
        remaining accepted) receipt13 (statements []) evaluated selected

theorem empty_skipHead_branch_rewrite_exact
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements (statements []) continuation)
          (environment10 owner revision declaration.function arity declaration
            remaining accepted) receipt13) =
      [run continuation
        (environment10 owner revision declaration.function arity declaration
          remaining accepted) receipt13] := by
  simpa [statements, StructuredC.nilStatements, node, StructuredC.a] using
    appendEmptyTransition_rewriteAt_exact coldRelations continuation
      (environment10 owner revision declaration.function arity declaration
        remaining accepted) receipt13

theorem after_skipHead_append_rewrite_exact
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements generatedRunningAfterSkipHead
          continuation)
          (environment10 owner revision declaration.function arity declaration
            remaining accepted) receipt13) =
      [run (consStatement skipArityDecision
          (StructuredC.appendStatements generatedRunningAfterSkipArity
            continuation))
        (environment10 owner revision declaration.function arity declaration
          remaining accepted) receipt13] := by
  rw [after_skipHead_spine]
  exact appendConsTransition_rewriteAt_exact coldRelations skipArityDecision
    generatedRunningAfterSkipArity continuation
    (environment10 owner revision declaration.function arity declaration
      remaining accepted) receipt13

theorem arity_guard_operands_lookup
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    List.Forall₂
      (fun slot value =>
        lookup? (environment10 owner revision declaration.function arity
          declaration remaining accepted) (identifier slot) = some value)
      ["inputs", "arity"]
      [inputsValue declaration, arityValue arity] := by
  simp [environment10, environment9, environment8, environment7, environment6,
    environment5, environment4, environment3, environment2, environment1,
    environment0, initialEnvironment, inputsValue, arityValue, lookup?,
    bindName, environmentBind, environmentEmpty, identifier, node, token]

theorem arity_guard_rewrite_exact
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan)
    (different : declaration.inputTypes.length ≠ arity) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement skipArityDecision rest)
          (environment10 owner revision declaration.function arity declaration
            remaining accepted) receipt13) =
      [run (StructuredC.appendStatements skipAritySuccess rest)
        (environment10 owner revision declaration.function arity declaration
          remaining accepted) arityGuardReceipt] := by
  have evaluated := arityDiffers_evaluation_exact declaration.inputTypes arity
    (environment10 owner revision declaration.function arity declaration
      remaining accepted) receipt13 different
    (by
      simpa [inputsValue, arityValue] using
        arity_guard_operands_lookup owner revision arity declaration remaining
          accepted)
  have selected :
      selectBranch? trueValue skipAritySuccess (statements []) =
        some skipAritySuccess := by simp [selectBranch?]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    skipArityDecision, skipArityCondition, ifThenElse, node, StructuredC.a,
    arityGuardReceipt] using
    if_rewriteAt_exact_of_evaluate coldHandler skipArityCondition
      skipAritySuccess (statements []) rest
      (environment10 owner revision declaration.function arity declaration
        remaining accepted) receipt13 trueValue
      (environment10 owner revision declaration.function arity declaration
        remaining accepted) arityGuardReceipt skipAritySuccess evaluated
      selected

theorem arity_success_append_rewrite_exact
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (continuation : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements skipAritySuccess continuation)
          (environment10 owner revision declaration.function arity declaration
            remaining accepted) arityGuardReceipt) =
      [run (consStatement arityEffectStatement
          (StructuredC.appendStatements arityReturnStatements continuation))
        (environment10 owner revision declaration.function arity declaration
          remaining accepted) arityGuardReceipt] := by
  rw [skipAritySuccess_shape]
  simpa [arityEffectStatement, arityReturnStatements, statements, node,
    StructuredC.consStatement, StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations arityEffectStatement
      arityReturnStatements continuation
      (environment10 owner revision declaration.function arity declaration
        remaining accepted) arityGuardReceipt

theorem arity_delta_operands_lookup
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    List.Forall₂
      (fun slot value =>
        lookup? (environment10 owner revision declaration.function arity
          declaration remaining accepted) (identifier slot) = some value)
      ["state", "owner", "revision", "declaration_head", "arity",
        "remaining", "accepted"]
      [ stateValue (skipAritySource owner revision arity declaration remaining
          accepted)
      , ownerValue owner, revisionValue revision,
        declarationHeadValue declaration, arityValue arity,
        remainingValue remaining, acceptedValue accepted ] := by
  simp [skipAritySource, environment10, environment9, environment8,
    environment7, environment6, environment5, environment4, environment3,
    environment2, environment1, environment0, initialEnvironment, ownerValue,
    revisionValue, declarationHeadValue, arityValue, remainingValue,
    acceptedValue, lookup?, bindName, environmentBind, environmentEmpty,
    identifier, node, token]

theorem arity_delta_rewrite_exact
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan)
    (different : declaration.inputTypes.length ≠ arity) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement arityEffectStatement rest)
          (environment10 owner revision declaration.function arity declaration
            remaining accepted) arityGuardReceipt) =
      [run rest
        (environment11 owner revision declaration.function arity declaration
          remaining accepted) arityDeltaReceipt] := by
  have evaluated := skipArity_delta_evaluation_exact owner revision arity
    declaration remaining accepted
    (environment10 owner revision declaration.function arity declaration
      remaining accepted) arityGuardReceipt different
    (by
      simpa [skipAritySource, skipHeadSource] using
        source_lookup10 owner revision declaration.function arity declaration
          remaining accepted)
    (by
      simpa [skipAritySource, skipHeadSource, ownerValue, revisionValue,
        declarationHeadValue, arityValue, remainingValue, acceptedValue] using
        arity_delta_operands_lookup owner revision arity declaration remaining
          accepted)
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    arityEffectStatement, environment11, arityDeltaReceipt, effect, node,
    StructuredC.a] using
    effect_rewriteAt_exact_of_evaluate coldHandler
      (call setCompileRunningDelta
        (["state", "owner", "revision", "declaration_head", "arity",
          "remaining", "accepted"].map variableExpression)) rest
      (environment10 owner revision declaration.function arity declaration
        remaining accepted) arityGuardReceipt valueUnit
      (environment11 owner revision declaration.function arity declaration
        remaining accepted) arityDeltaReceipt evaluated

theorem arity_delta_effect_rewrite_exact
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan)
    (different : declaration.inputTypes.length ≠ arity) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement
          (effect (call setCompileRunningDelta
            (["state", "owner", "revision", "declaration_head", "arity",
              "remaining", "accepted"].map variableExpression))) rest)
          (environment10 owner revision declaration.function arity declaration
            remaining accepted) arityGuardReceipt) =
      [run rest
        (environment11 owner revision declaration.function arity declaration
          remaining accepted) arityDeltaReceipt] := by
  simpa [arityEffectStatement] using
    arity_delta_rewrite_exact owner revision arity declaration remaining
      accepted different rest

theorem arity_return_statements_append_rewrite_exact
    (continuation environment receipt : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements arityReturnStatements continuation)
          environment receipt) =
      [run (consStatement (returnSymbol advancedOutcome)
          (StructuredC.appendStatements (statements []) continuation))
        environment receipt] := by
  simpa [arityReturnStatements, statements, node, StructuredC.consStatement,
    StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations
      (returnSymbol advancedOutcome) (statements []) continuation environment
      receipt

theorem arity_return_rewrite_exact
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (returnSymbol advancedOutcome) rest)
          (environment11 owner revision declaration.function arity declaration
            remaining accepted) arityDeltaReceipt) =
      [halted (StructuredC.a "structured-c:outcome-return"
          [valueSymbol advancedOutcome])
        (environment11 owner revision declaration.function arity declaration
          remaining accepted) arityDeltaReceipt] := by
  have evaluated := evaluate_symbol_exact coldHandler advancedOutcome
    (environment11 owner revision declaration.function arity declaration
      remaining accepted) arityDeltaReceipt
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    returnSymbol, returnExpression, node, StructuredC.a] using
    return_rewriteAt_exact_of_evaluate coldHandler (symbol advancedOutcome)
      rest
      (environment11 owner revision declaration.function arity declaration
        remaining accepted) arityDeltaReceipt (valueSymbol advancedOutcome)
      (environment11 owner revision declaration.function arity declaration
        remaining accepted) arityDeltaReceipt evaluated

def haltedTarget
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : Pattern :=
  halted (StructuredC.a "structured-c:outcome-return"
      [valueSymbol advancedOutcome])
    (environment11 owner revision declaration.function arity declaration
      remaining accepted) arityDeltaReceipt

theorem terminal_observation_exact
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    terminalControl? (haltedTarget owner revision arity declaration remaining
      accepted) =
      some (skipArityTarget owner revision arity declaration remaining
        accepted) := by
  simp [haltedTarget, terminalControl?, environment11, skipArityTarget,
    skipHeadTarget, halted, StructuredC.a, lookup?, bindName, environmentBind,
    identifier, decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?,
    abiValue, node, token]

theorem source_step
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan)
    (different : declaration.inputTypes.length ≠ arity) :
    compileLanguageGSLT.Step
      (skipAritySource owner revision arity declaration remaining accepted)
      (skipArityTarget owner revision arity declaration remaining accepted) := by
  change compileLanguageStep?
      (skipAritySource owner revision arity declaration remaining accepted) =
    some (skipArityTarget owner revision arity declaration remaining accepted)
  simp [skipAritySource, skipArityTarget, skipHeadSource, skipHeadTarget,
    compileLanguageStep?, Relevant, different]

theorem normalizes_exact
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan)
    (different : declaration.inputTypes.length ≠ arity) :
    normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (skipAritySource owner revision arity declaration remaining
            accepted)) =
      haltedTarget owner revision arity declaration remaining accepted := by
  unfold skipAritySource
  unfold normalizeFirstUsing
  simp only [normalizeFirstAt,
    phase_rewrite_exact owner revision declaration.function arity declaration
      remaining accepted]
  simp only [
    dispatcher_append_rewrite_exact owner revision declaration.function arity
      declaration remaining accepted]
  simp only [
    owner_declare_rewrite_exact owner revision declaration.function arity
      declaration remaining accepted]
  simp only [commonTail1_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    revision_declare_rewrite_exact owner revision declaration.function arity
      declaration remaining accepted]
  simp only [commonTail2_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    head_declare_rewrite_exact owner revision declaration.function arity
      declaration remaining accepted]
  simp only [commonTail3_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    arity_declare_rewrite_exact owner revision declaration.function arity
      declaration remaining accepted]
  simp only [commonTail4_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    accepted_declare_rewrite_exact owner revision declaration.function arity
      declaration remaining accepted]
  simp only [commonTail5_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    running_decision_rewrite_exact owner revision declaration.function arity
      declaration remaining accepted]
  simp only [
    fallback_append_rewrite_exact owner revision declaration.function arity
      declaration remaining accepted]
  simp only [
    remaining_declare_rewrite_exact owner revision declaration.function arity
      declaration remaining accepted]
  simp only [declarationTail1_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    occurrence_declare_rewrite_exact owner revision declaration.function arity
      declaration remaining accepted]
  simp only [declarationTail2_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    declarationHead_declare_rewrite_exact owner revision declaration.function
      arity declaration remaining accepted]
  simp only [declarationTail3_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    inputs_declare_rewrite_exact owner revision declaration.function arity
      declaration remaining accepted]
  simp only [declarationTail4_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    output_declare_rewrite_exact owner revision declaration.function arity
      declaration remaining accepted]
  simp only [declarationTail5_shape, appendConsTransition_rewriteAt_exact]
  simp only [
    skipHead_guard_false_rewrite_exact owner revision arity declaration
      remaining accepted]
  simp only [
    empty_skipHead_branch_rewrite_exact owner revision arity declaration
      remaining accepted]
  simp only [
    after_skipHead_append_rewrite_exact owner revision arity declaration
      remaining accepted]
  simp only [
    arity_guard_rewrite_exact owner revision arity declaration remaining
      accepted different]
  simp only [
    arity_success_append_rewrite_exact owner revision arity declaration
      remaining accepted]
  simp only [arityEffectStatement]
  simp only [
    arity_delta_effect_rewrite_exact owner revision arity declaration remaining
      accepted different]
  simp only [arity_return_statements_append_rewrite_exact]
  simp only [
    arity_return_rewrite_exact owner revision arity declaration remaining
      accepted]
  simp only [halted_rewriteAt_empty]
  rfl

abbrev run
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (skipAritySource owner revision arity declaration remaining accepted)) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
      (skipAritySource owner revision arity declaration remaining accepted))

theorem run_endpoint_exact
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan)
    (different : declaration.inputTypes.length ≠ arity) :
    (run owner revision arity declaration remaining accepted).endpoint =
      haltedTarget owner revision arity declaration remaining accepted := by
  calc
    _ = normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (skipAritySource owner revision arity declaration remaining
            accepted)) :=
      (run owner revision arity declaration remaining accepted).endpoint_eq
    _ = _ := normalizes_exact owner revision arity declaration remaining
      accepted different

theorem run_observation_exact
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan)
    (different : declaration.inputTypes.length ≠ arity) :
    terminalControl?
        (run owner revision arity declaration remaining accepted).endpoint =
      some (skipArityTarget owner revision arity declaration remaining
        accepted) := by
  rw [run_endpoint_exact owner revision arity declaration remaining accepted
    different]
  exact terminal_observation_exact owner revision arity declaration remaining
    accepted

theorem run_path_bounded
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    (run owner revision arity declaration remaining accepted).path.length ≤ 64 :=
  (run owner revision arity declaration remaining accepted).length_le

theorem run_path_nonempty
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    0 < (run owner revision arity declaration remaining accepted).path.length := by
  apply (run owner revision arity declaration remaining accepted).nonempty_of_reduct
  · decide
  · unfold skipAritySource
    rw [phase_rewrite_exact owner revision declaration.function arity declaration
      remaining accepted]
    simp

theorem step_realization
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan)
    (different : declaration.inputTypes.length ≠ arity) :
    ∃ endpoint : Pattern,
      ∃ path : ExecutionPath coldGSLT
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (skipAritySource owner revision arity declaration remaining
              accepted)) endpoint,
      terminalControl? endpoint =
          some (skipArityTarget owner revision arity declaration remaining
            accepted) ∧
        0 < path.length ∧ path.length ≤ 64 := by
  let execution := run owner revision arity declaration remaining accepted
  refine ⟨execution.endpoint, execution.path, ?_, ?_, ?_⟩
  · exact run_observation_exact owner revision arity declaration remaining
      accepted different
  · exact run_path_nonempty owner revision arity declaration remaining
      accepted
  · exact run_path_bounded owner revision arity declaration remaining
      accepted

theorem normalized_observation_iff
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan)
    (different : declaration.inputTypes.length ≠ arity)
    (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (skipAritySource owner revision arity declaration remaining
              accepted))) = some observed ↔
      observed = skipArityTarget owner revision arity declaration remaining
        accepted := by
  rw [normalizes_exact owner revision arity declaration remaining accepted
    different]
  have observedExact := terminal_observation_exact owner revision arity
    declaration remaining accepted
  rw [observedExact]
  simp [eq_comm]

theorem wrong_target_rejected
    (owner : SpaceOwner) (revision arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan)
    (different : declaration.inputTypes.length ≠ arity)
    (observed : CompileLanguageControl)
    (wrong : observed ≠
      skipArityTarget owner revision arity declaration remaining accepted) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (skipAritySource owner revision arity declaration remaining
              accepted))) ≠ some observed := by
  intro invented
  exact wrong ((normalized_observation_iff owner revision arity declaration
    remaining accepted different observed).mp invented)

#print axioms source_step
#print axioms normalizes_exact
#print axioms run_endpoint_exact
#print axioms run_observation_exact
#print axioms run_path_bounded
#print axioms run_path_nonempty
#print axioms step_realization
#print axioms normalized_observation_iff
#print axioms wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSkipAritySimulation
