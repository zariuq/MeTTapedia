import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedResultSimulation

/-!
# Generated StructuredC realization of the open-result family

For every source result outside the supported call-guard fragment, the
generated target rejects the literal and checked result rows, confirms the
open-result premise, and changes the stored compiler state to
`outsideFragment`.  The state-changing primitive independently checks the
same source classification; the generated branch cannot manufacture the
terminal state merely by returning its outcome tag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOpenResultSimulation

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

abbrev atomReceipt :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenResultPrefixSimulation.atomReceipt
abbrev atomRest :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedOpenResultPrefixSimulation.atomRest
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

def target : CompileLanguageControl := .halted .outsideFragment

def environment12 (data : ResultStateData) : Pattern :=
  bindName "state" (stateValue target) data.environment11

def checkedReceipt : Pattern :=
  externalReceipt resultIsCheckedQuery NonLiteral.atomReceipt

def openReceipt : Pattern :=
  externalReceipt resultIsOpenQuery checkedReceipt

def deltaReceipt : Pattern :=
  externalReceipt setOutsideFragmentDelta openReceipt

def openRest : Pattern :=
  StructuredC.appendStatements
    (statements [returnSymbol noTransitionOutcome]) NonLiteral.atomRest

def effectExpression : Pattern :=
  call setOutsideFragmentDelta [variableExpression "state"]

def effectStatement : Pattern := effect effectExpression

def returnStatements : Pattern :=
  statements [returnSymbol outsideFragmentOutcome]

theorem not_undefined_of_unsupported (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none) :
    data.declaration.outputType ≠ undefinedType := by
  intro equal
  rw [equal] at unsupported
  simp [compileResultMode, undefinedType] at unsupported

theorem not_hole_of_unsupported (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none) :
    data.declaration.outputType ≠ holeType := by
  intro equal
  rw [equal] at unsupported
  simp [compileResultMode, holeType, undefinedType] at unsupported

theorem not_atom_of_unsupported (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none) :
    data.declaration.outputType ≠ atomType := by
  intro equal
  rw [equal] at unsupported
  simp [compileResultMode, atomType, holeType, undefinedType] at unsupported

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

theorem checked_decision_false_rewrite_exact
    (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (NonLiteral.checkedEndpoint data) =
      [run (StructuredC.appendStatements (statements [])
          NonLiteral.checkedRest) data.environment11 checkedReceipt] := by
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (consStatement checkedResultDecision NonLiteral.checkedRest)
        data.environment11 NonLiteral.atomReceipt) = _
  have evaluated :
      evaluate? coldHandler
          (call resultIsCheckedQuery [variableExpression "output"])
          data.environment11 NonLiteral.atomReceipt =
        some ⟨.value falseValue, data.environment11, checkedReceipt⟩ := by
    simpa [checkedResultAnswer, unsupported, checkedReceipt] using
      resultIsChecked_evaluation_exact data.declaration.outputType
        data.environment11 NonLiteral.atomReceipt
        (NonLiteral.output_lookup11 data)
  have selected :
      selectBranch? falseValue checkedResultSuccessBody (statements []) =
        some (statements []) := by
    simp [selectBranch?, falseValue, trueValue, valueSymbol, identifier, node,
      token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    checkedResultDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call resultIsCheckedQuery [variableExpression "output"])
      checkedResultSuccessBody (statements []) NonLiteral.checkedRest
      data.environment11 NonLiteral.atomReceipt falseValue data.environment11
      checkedReceipt (statements []) evaluated selected

theorem checked_empty_append_rewrite_exact (data : ResultStateData) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements (statements [])
          NonLiteral.checkedRest) data.environment11 checkedReceipt) =
      [run NonLiteral.checkedRest data.environment11 checkedReceipt] := by
  simpa [statements, StructuredC.nilStatements, node, StructuredC.a] using
    appendEmptyTransition_rewriteAt_exact coldRelations NonLiteral.checkedRest
      data.environment11 checkedReceipt

theorem checked_rest_append_rewrite_exact (data : ResultStateData) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run NonLiteral.checkedRest data.environment11 checkedReceipt) =
      [run (consStatement openResultDecision openRest)
        data.environment11 checkedReceipt] := by
  rw [show NonLiteral.checkedRest =
      StructuredC.appendStatements
        (statements [openResultDecision, returnSymbol noTransitionOutcome])
        NonLiteral.atomRest by rfl]
  change rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
      (run (StructuredC.appendStatements
        (consStatement openResultDecision
          (statements [returnSymbol noTransitionOutcome])) NonLiteral.atomRest)
        data.environment11 checkedReceipt) = _
  simpa [openRest] using
    appendConsTransition_rewriteAt_exact coldRelations openResultDecision
      (statements [returnSymbol noTransitionOutcome]) NonLiteral.atomRest
      data.environment11 checkedReceipt

theorem open_decision_true_rewrite_exact
    (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement openResultDecision openRest)
          data.environment11 checkedReceipt) =
      [run (StructuredC.appendStatements openResultSuccessBody openRest)
        data.environment11 openReceipt] := by
  have evaluated :
      evaluate? coldHandler
          (call resultIsOpenQuery [variableExpression "output"])
          data.environment11 checkedReceipt =
        some ⟨.value trueValue, data.environment11, openReceipt⟩ := by
    simpa [openResultAnswer, unsupported, openReceipt] using
      resultIsOpen_evaluation_exact data.declaration.outputType
        data.environment11 checkedReceipt (NonLiteral.output_lookup11 data)
  have selected :
      selectBranch? trueValue openResultSuccessBody (statements []) =
        some openResultSuccessBody := by
    simp [selectBranch?, trueValue, valueSymbol, identifier, node, token]
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    openResultDecision, ifThenElse, node, StructuredC.a] using
    if_rewriteAt_exact_of_evaluate coldHandler
      (call resultIsOpenQuery [variableExpression "output"])
      openResultSuccessBody (statements []) openRest data.environment11
      checkedReceipt trueValue data.environment11 openReceipt
      openResultSuccessBody evaluated selected

theorem open_body_append_rewrite_exact (data : ResultStateData) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements openResultSuccessBody openRest)
          data.environment11 openReceipt) =
      [run (consStatement effectStatement
          (StructuredC.appendStatements returnStatements openRest))
        data.environment11 openReceipt] := by
  rw [openResultSuccessBody]
  simpa [effectStatement, effectExpression, returnStatements, statements,
    node, StructuredC.consStatement, StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations effectStatement
      returnStatements openRest data.environment11 openReceipt

theorem delta_evaluation_exact
    (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none) :
    evaluate? coldHandler effectExpression data.environment11 openReceipt =
      some ⟨.value valueUnit, environment12 data, deltaReceipt⟩ := by
  have handled := handler_setOutsideFragment_result_exact data.owner
    data.revision data.head data.arity data.declaration data.remaining
    data.modes data.accepted data.environment11 openReceipt unsupported
    (source_lookup11 data)
  simpa [effectExpression, environment12, target, deltaReceipt] using
    evaluate_single_variable_call_exact coldHandler setOutsideFragmentDelta
      "state" (stateValue (source data)) data.environment11 openReceipt _
      (source_lookup11 data) handled

theorem delta_effect_rewrite_exact
    (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none)
    (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement effectStatement rest)
          data.environment11 openReceipt) =
      [run rest (environment12 data) deltaReceipt] := by
  have evaluated := delta_evaluation_exact data unsupported
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    effectStatement, effect, node, StructuredC.a] using
    effect_rewriteAt_exact_of_evaluate coldHandler effectExpression rest
      data.environment11 openReceipt valueUnit (environment12 data)
      deltaReceipt evaluated

theorem return_statements_append_rewrite_exact
    (continuation environment receipt : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (StructuredC.appendStatements returnStatements continuation)
          environment receipt) =
      [run (consStatement (returnSymbol outsideFragmentOutcome)
          (StructuredC.appendStatements (statements []) continuation))
        environment receipt] := by
  simpa [returnStatements, statements, node, StructuredC.consStatement,
    StructuredC.a] using
    appendConsTransition_rewriteAt_exact coldRelations
      (returnSymbol outsideFragmentOutcome) (statements []) continuation
      environment receipt

theorem return_rewrite_exact (data : ResultStateData) (rest : Pattern) :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1
        (run (consStatement (returnSymbol outsideFragmentOutcome) rest)
          (environment12 data) deltaReceipt) =
      [halted (StructuredC.a "structured-c:outcome-return"
          [valueSymbol outsideFragmentOutcome])
        (environment12 data) deltaReceipt] := by
  have evaluated := evaluate_symbol_exact coldHandler outsideFragmentOutcome
    (environment12 data) deltaReceipt
  simpa [coldRelations, coldHandler,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.relations,
    returnSymbol, returnExpression, node, StructuredC.a] using
    return_rewriteAt_exact_of_evaluate coldHandler
      (symbol outsideFragmentOutcome) rest (environment12 data) deltaReceipt
      (valueSymbol outsideFragmentOutcome) (environment12 data) deltaReceipt
      evaluated

def haltedTarget (data : ResultStateData) : Pattern :=
  halted (StructuredC.a "structured-c:outcome-return"
      [valueSymbol outsideFragmentOutcome])
    (environment12 data) deltaReceipt

theorem terminal_observation_exact (data : ResultStateData) :
    terminalControl? (haltedTarget data) = some target := by
  simp [haltedTarget, terminalControl?, environment12, target, halted,
    StructuredC.a, lookup?, bindName, environmentBind, identifier,
    decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?, abiValue, node,
    token]

theorem source_step
    (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none) :
    compileLanguageGSLT.Step (source data) target := by
  change compileLanguageStep? data.source = some target
  simp [ResultStateData.source, target, compileLanguageStep?, unsupported]

theorem normalizes_exact
    (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none) :
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
    (not_undefined_of_unsupported data unsupported)
    (not_hole_of_unsupported data unsupported)
    (not_atom_of_unsupported data unsupported) 34]
  simp only [normalizeFirstAt,
    checked_decision_false_rewrite_exact data unsupported]
  simp only [checked_empty_append_rewrite_exact data]
  simp only [checked_rest_append_rewrite_exact data]
  simp only [open_decision_true_rewrite_exact data unsupported]
  simp only [open_body_append_rewrite_exact data]
  simp only [delta_effect_rewrite_exact data unsupported]
  simp only [return_statements_append_rewrite_exact]
  simp only [return_rewrite_exact data]
  simp only [halted_rewriteAt_empty]
  rfl

abbrev execution (data : ResultStateData) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
        (source data)) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
      (source data))

theorem execution_endpoint_exact
    (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none) :
    (execution data).endpoint = haltedTarget data := by
  exact (execution data).endpoint_eq.trans (normalizes_exact data unsupported)

theorem execution_observation_exact
    (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none) :
    terminalControl? (execution data).endpoint = some target := by
  rw [execution_endpoint_exact data unsupported]
  exact terminal_observation_exact data

theorem execution_path_bounded (data : ResultStateData) :
    (execution data).path.length ≤ 64 :=
  (execution data).length_le

theorem execution_path_nonempty (data : ResultStateData) :
    0 < (execution data).path.length := by
  apply (execution data).nonempty_of_reduct
  · decide
  · change rewriteAt (engineBasePremises coldRelations)
        StructuredC.language 1
        (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
          data.source) ≠ []
    rw [phase_rewrite_exact data]
    simp

theorem step_realization
    (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none) :
    compileLanguageGSLT.Step (source data) target ∧
      terminalControl? (execution data).endpoint = some target ∧
      0 < (execution data).path.length ∧
      (execution data).path.length ≤ 64 := by
  exact ⟨source_step data unsupported,
    execution_observation_exact data unsupported,
    execution_path_nonempty data,
    execution_path_bounded data⟩

theorem normalized_observation_iff
    (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none)
    (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source data))) = some observed ↔ observed = target := by
  rw [normalizes_exact data unsupported, terminal_observation_exact]
  simp [eq_comm]

theorem wrong_target_rejected
    (data : ResultStateData)
    (unsupported : compileResultMode data.declaration.outputType = none)
    (observed : CompileLanguageControl) (wrong : observed ≠ target) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics.runControl
            (source data))) ≠ some observed := by
  intro invented
  exact wrong ((normalized_observation_iff data unsupported observed).mp invented)

#print axioms source_step
#print axioms normalizes_exact
#print axioms execution_observation_exact
#print axioms execution_path_bounded
#print axioms execution_path_nonempty
#print axioms step_realization
#print axioms normalized_observation_iff
#print axioms wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOpenResultSimulation
