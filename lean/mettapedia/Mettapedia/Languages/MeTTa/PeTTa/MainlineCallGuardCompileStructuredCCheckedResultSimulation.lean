import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenResultPrefixSimulation

/-!
# Generated StructuredC realization of the checked-result family

For every source result classified as `resultSoftcutType output`, the generated
target rejects all earlier literal rows, obtains the checked answer from the
independent classifier, reconstructs the exact dependent result mode, and
appends precisely the source guard plan.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedResultSimulation

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

namespace NonLiteral

abbrev undefinedReceipt :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenResultPrefixSimulation.undefinedReceipt
abbrev holeReceipt :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenResultPrefixSimulation.holeReceipt
abbrev atomReceipt :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenResultPrefixSimulation.atomReceipt
abbrev checkedRest :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenResultPrefixSimulation.checkedRest
abbrev checkedEndpoint :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenResultPrefixSimulation.checkedEndpoint
abbrev output_lookup11 :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenResultPrefixSimulation.output_lookup11
abbrev normalize_prefix_exact :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenResultPrefixSimulation.normalize_prefix_exact

end NonLiteral

def source (data : ResultStateData) : CompileLanguageControl := data.source

def plan (data : ResultStateData) : GuardPlan := {
  declarationOccurrence := data.declaration.occurrence
  argumentModes := data.modes
  resultMode := .resultSoftcutType data.declaration.outputType
  declaration := data.declaration }

def target (data : ResultStateData) : CompileLanguageControl :=
  .running data.owner data.revision data.head data.arity data.remaining
    (data.accepted ++ [plan data])

def environment12 (data : ResultStateData) : Pattern :=
  bindName "state" (stateValue (target data)) data.environment11

def checkedReceipt : Pattern :=
  externalReceipt resultIsCheckedQuery NonLiteral.atomReceipt

def deltaReceipt : Pattern :=
  externalReceipt appendCompiledPlanDelta checkedReceipt

def operandNames : List String :=
  [ "state", "owner", "revision", "head", "arity", "remaining"
  , "accepted", "occurrence", "modes", "declaration_head", "inputs"
  , "output" ]

def operandExpressions : List Pattern :=
  operandNames.map variableExpression ++
    [symbol checkedResultMode, variableExpression "output"]

def operandValues (data : ResultStateData) : List Pattern :=
  [ stateValue (source data)
  , abiValue (encodeOwner data.owner)
  , abiValue (encodeNat data.revision)
  , abiValue (encodeName data.head)
  , abiValue (encodeNat data.arity)
  , abiValue (encodeDeclarations data.remaining)
  , abiValue (encodePlans data.accepted)
  , abiValue (encodeNat data.declaration.occurrence)
  , abiValue (encodeArgModes data.modes)
  , abiValue (encodeName data.declaration.function)
  , abiValue (encodeTerms data.declaration.inputTypes)
  , abiValue (encodeTerm data.declaration.outputType)
  , valueSymbol checkedResultMode
  , abiValue (encodeTerm data.declaration.outputType) ]

def effectExpression : Pattern :=
  call appendCompiledPlanDelta operandExpressions

def effectStatement : Pattern := effect effectExpression

def returnStatements : Pattern := statements [returnSymbol advancedOutcome]

theorem not_undefined_of_classified (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    data.declaration.outputType ≠ undefinedType := by
  intro equal
  rw [equal] at classified
  simp [compileResultMode, undefinedType] at classified

theorem not_hole_of_classified (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    data.declaration.outputType ≠ holeType := by
  intro equal
  rw [equal] at classified
  simp [compileResultMode, holeType, undefinedType] at classified

theorem not_atom_of_classified (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    data.declaration.outputType ≠ atomType := by
  intro equal
  rw [equal] at classified
  simp [compileResultMode, atomType, holeType, undefinedType] at classified

theorem resultOutputValue_of_classified (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    resultOutputValue data.declaration.outputType =
      abiValue (encodeTerm data.declaration.outputType) := by
  simp [resultOutputValue, not_undefined_of_classified data classified,
    not_hole_of_classified data classified,
    not_atom_of_classified data classified]

theorem source_lookup11 (data : ResultStateData) :
    lookup? data.environment11 (identifier "state") =
      some (stateValue (source data)) := by
  simp [source, ResultStateData.source, ResultStateData.environment11,
    ResultStateData.environment10, ResultStateData.environment9,
    ResultStateData.environment8, ResultStateData.environment7,
    ResultStateData.environment6, ResultStateData.environment5,
    ResultStateData.environment4, ResultStateData.environment3,
    ResultStateData.environment2, ResultStateData.environment1,
    ResultStateData.environment0, initialEnvironment, lookup?, bindName,
    environmentBind, identifier, node, token]

theorem checked_decision_true_rewrite_exact
    (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (NonLiteral.checkedEndpoint data) =
      [run (StructuredC.appendStatements checkedResultSuccessBody
          NonLiteral.checkedRest) data.environment11 checkedReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (consStatement checkedResultDecision NonLiteral.checkedRest)
        data.environment11 NonLiteral.atomReceipt) = _
  have evaluated :
      evaluate? coldHandler
          (call resultIsCheckedQuery [variableExpression "output"])
          data.environment11 NonLiteral.atomReceipt =
        some ⟨.value trueValue, data.environment11, checkedReceipt⟩ := by
    simpa [checkedResultAnswer, classified, checkedReceipt] using
      resultIsChecked_evaluation_exact data.declaration.outputType
        data.environment11 NonLiteral.atomReceipt
        (NonLiteral.output_lookup11 data)
  have selected :
      selectBranch? trueValue checkedResultSuccessBody (statements []) =
        some checkedResultSuccessBody := by
    simp [selectBranch?, trueValue, valueSymbol, identifier, node, token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    checkedResultDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call resultIsCheckedQuery [variableExpression "output"])
      checkedResultSuccessBody (statements []) NonLiteral.checkedRest
      data.environment11 NonLiteral.atomReceipt trueValue data.environment11
      checkedReceipt checkedResultSuccessBody evaluated selected

theorem checked_body_append_rewrite_exact (data : ResultStateData) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements checkedResultSuccessBody
          NonLiteral.checkedRest) data.environment11 checkedReceipt) =
      [run (consStatement effectStatement
          (StructuredC.appendStatements returnStatements
            NonLiteral.checkedRest)) data.environment11 checkedReceipt] := by
  rw [checkedResultSuccessBody]
  simpa [effectStatement, effectExpression, operandExpressions, operandNames,
    returnStatements, statements, node, StructuredC.consStatement,
    StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations effectStatement
      returnStatements NonLiteral.checkedRest data.environment11 checkedReceipt

theorem delta_operands_lookup (data : ResultStateData) :
    List.Forall₂
      (fun slot value =>
        lookup? data.environment11 (identifier slot) = some value)
      operandNames
      [ stateValue (source data)
      , abiValue (encodeOwner data.owner)
      , abiValue (encodeNat data.revision)
      , abiValue (encodeName data.head)
      , abiValue (encodeNat data.arity)
      , abiValue (encodeDeclarations data.remaining)
      , abiValue (encodePlans data.accepted)
      , abiValue (encodeNat data.declaration.occurrence)
      , abiValue (encodeArgModes data.modes)
      , abiValue (encodeName data.declaration.function)
      , abiValue (encodeTerms data.declaration.inputTypes)
      , abiValue (encodeTerm data.declaration.outputType) ] := by
  simp [operandNames, source, ResultStateData.source,
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

theorem delta_leaf_evaluations (data : ResultStateData) :
    List.Forall₂
      (fun expression value =>
        evaluateLeaf? expression data.environment11 checkedReceipt =
          some ⟨.value value, data.environment11, checkedReceipt⟩)
      operandExpressions (operandValues data) := by
  have prefixLeaves := evaluateLeaf_variableExpressions_exact operandNames
    [ stateValue (source data)
    , abiValue (encodeOwner data.owner)
    , abiValue (encodeNat data.revision)
    , abiValue (encodeName data.head)
    , abiValue (encodeNat data.arity)
    , abiValue (encodeDeclarations data.remaining)
    , abiValue (encodePlans data.accepted)
    , abiValue (encodeNat data.declaration.occurrence)
    , abiValue (encodeArgModes data.modes)
    , abiValue (encodeName data.declaration.function)
    , abiValue (encodeTerms data.declaration.inputTypes)
    , abiValue (encodeTerm data.declaration.outputType) ]
    data.environment11 checkedReceipt (delta_operands_lookup data)
  have tailLeaves :
      List.Forall₂
        (fun expression value =>
          evaluateLeaf? expression data.environment11 checkedReceipt =
            some ⟨.value value, data.environment11, checkedReceipt⟩)
        [symbol checkedResultMode, variableExpression "output"]
        [valueSymbol checkedResultMode,
          abiValue (encodeTerm data.declaration.outputType)] := by
    constructor
    · simp [evaluateLeaf?, symbol, constant, valueSymbol, identifier, node,
        token]
    · constructor
      · have stored := NonLiteral.output_lookup11 data
        have expanded :
            lookup? data.environment11
                (Pattern.apply "structured-c:identifier"
                  [Pattern.apply "output" []]) =
              some (abiValue (encodeTerm data.declaration.outputType)) := by
          simpa [identifier, node, token] using stored
        simp [evaluateLeaf?, variableExpression, identifierName?, identifier,
          node, token, expanded]
      · exact .nil
  have joined := List.rel_append prefixLeaves tailLeaves
  simpa [operandExpressions, operandValues, operandNames] using joined

theorem delta_evaluation_exact
    (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    evaluate? coldHandler effectExpression data.environment11 checkedReceipt =
      some ⟨.value valueUnit, environment12 data, deltaReceipt⟩ := by
  have handledRaw := handler_appendCompiledPlan_delta_exact data.owner
    data.revision data.head data.arity data.declaration data.remaining
    data.modes data.accepted
    (.resultSoftcutType data.declaration.outputType) data.environment11
    checkedReceipt classified (source_lookup11 data)
  have handled :
      coldHandler appendCompiledPlanDelta (operandValues data)
          data.environment11 checkedReceipt =
        some ⟨.value valueUnit, environment12 data, deltaReceipt⟩ := by
    simpa [coldHandler, operandValues, source, ResultStateData.source, target,
      plan, environment12, deltaReceipt,
      resultOutputValue_of_classified data classified, resultModeTag,
      resultModePayload] using handledRaw
  have evaluated := evaluate_pure_call_exact coldHandler
    appendCompiledPlanDelta operandExpressions (operandValues data)
    data.environment11 checkedReceipt _ (delta_leaf_evaluations data) handled
  simpa [effectExpression] using evaluated

theorem delta_effect_rewrite_exact
    (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType))
    (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement effectStatement rest)
          data.environment11 checkedReceipt) =
      [run rest (environment12 data) deltaReceipt] := by
  have evaluated := delta_evaluation_exact data classified
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    effectStatement, effect, node, StructuredC.a] using
    effect_rewriteAt_exact_of_evaluate coldHandler effectExpression rest
      data.environment11 checkedReceipt valueUnit (environment12 data)
      deltaReceipt evaluated

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

theorem return_rewrite_exact (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (returnSymbol advancedOutcome) rest)
          (environment12 data) deltaReceipt) =
      [halted (StructuredC.a "structured-c:outcome-return"
          [valueSymbol advancedOutcome]) (environment12 data) deltaReceipt] := by
  have evaluated := evaluate_symbol_exact coldHandler advancedOutcome
    (environment12 data) deltaReceipt
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    returnSymbol, returnExpression, node, StructuredC.a] using
    return_rewriteAt_exact_of_evaluate coldHandler (symbol advancedOutcome)
      rest (environment12 data) deltaReceipt (valueSymbol advancedOutcome)
      (environment12 data) deltaReceipt evaluated

def haltedTarget (data : ResultStateData) : Pattern :=
  halted (StructuredC.a "structured-c:outcome-return"
      [valueSymbol advancedOutcome]) (environment12 data) deltaReceipt

theorem terminal_observation_exact (data : ResultStateData) :
    terminalControl? (haltedTarget data) = some (target data) := by
  simp [haltedTarget, terminalControl?, environment12, target, plan, halted,
    StructuredC.a, lookup?, bindName, environmentBind, identifier,
    decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?, abiValue, node,
    token]

theorem source_step
    (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    compileLanguageGSLT.Step (source data) (target data) := by
  change compileLanguageStep? data.source = some (target data)
  simp [ResultStateData.source, target, plan, compileLanguageStep?, classified]

theorem normalizes_exact
    (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    normalizeFirstUsing coldRelations StructuredC.language 1 64
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          (source data)) = haltedTarget data := by
  change normalizeFirstUsing coldRelations StructuredC.language 1 (40 + 24)
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        data.source) = _
  rw [Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation.normalize_prefix_exact
    data 40]
  change normalizeFirstAt (engineBasePremises coldRelations)
      StructuredC.language 1 (34 + 6)
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation.prefixEndpoint
          data) = _
  rw [NonLiteral.normalize_prefix_exact data
    (not_undefined_of_classified data classified)
    (not_hole_of_classified data classified)
    (not_atom_of_classified data classified) 34]
  simp only [normalizeFirstAt, checked_decision_true_rewrite_exact data
    classified]
  simp only [checked_body_append_rewrite_exact data]
  simp only [delta_effect_rewrite_exact data classified]
  simp only [return_statements_append_rewrite_exact]
  simp only [return_rewrite_exact data]
  simp only [halted_rewriteAt_empty]
  rfl

abbrev execution
    (data : ResultStateData)
    (_classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (source data)) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
      (source data))

theorem execution_endpoint_exact
    (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    (execution data classified).endpoint = haltedTarget data := by
  exact (execution data classified).endpoint_eq.trans
    (normalizes_exact data classified)

theorem execution_observation_exact
    (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    terminalControl? (execution data classified).endpoint =
      some (target data) := by
  rw [execution_endpoint_exact data classified]
  exact terminal_observation_exact data

theorem execution_path_bounded
    (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    (execution data classified).path.length ≤ 64 :=
  (execution data classified).length_le

theorem execution_path_nonempty
    (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    0 < (execution data classified).path.length := by
  apply (execution data classified).nonempty_of_reduct
  · decide
  · change rewriteAt (engineBasePremises coldRelations)
        StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          data.source) ≠ []
    rw [phase_rewrite_exact data]
    simp

theorem step_realization
    (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType)) :
    compileLanguageGSLT.Step (source data) (target data) ∧
      terminalControl? (execution data classified).endpoint =
        some (target data) ∧
      0 < (execution data classified).path.length ∧
      (execution data classified).path.length ≤ 64 := by
  exact ⟨source_step data classified,
    execution_observation_exact data classified,
    execution_path_nonempty data classified,
    execution_path_bounded data classified⟩

theorem normalized_observation_iff
    (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType))
    (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source data))) = some observed ↔
      observed = target data := by
  rw [normalizes_exact data classified, terminal_observation_exact]
  simp [eq_comm]

theorem wrong_target_rejected
    (data : ResultStateData)
    (classified : compileResultMode data.declaration.outputType =
      some (.resultSoftcutType data.declaration.outputType))
    (observed : CompileLanguageControl) (wrong : observed ≠ target data) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source data))) ≠ some observed := by
  intro invented
  exact wrong ((normalized_observation_iff data classified observed).mp invented)

#print axioms source_step
#print axioms normalizes_exact
#print axioms execution_observation_exact
#print axioms execution_path_bounded
#print axioms execution_path_nonempty
#print axioms step_realization
#print axioms normalized_observation_iff
#print axioms wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedResultSimulation
