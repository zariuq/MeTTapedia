import Mettapedia.GSLT.LanguageDef.DerivationWordMachineControlSimulation

/-!
# Exact finish-instruction simulation for the derivation-word machine

This module proves the authored one-record operational square for every
semantic outcome of `finish`.  The proof is structural: the decoded finish
record excludes every non-finish row, and the five finish rows are separated
by the remaining stream, root state, relevance closure, and declared calculus
decision.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationWordMachineFinishSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineSimulation
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineInputSimulation
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineControlSimulation

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}
variable [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation]
  [DecidableEq ServiceState]

def nonFinishSourceRules : List RewriteRule := [
  DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
  DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
  DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
  DerivationCheckMachineLanguageDef.inputAcceptTransition,
  DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
  DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
  DerivationCheckMachineLanguageDef.inferParentFaultTransition,
  DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
  DerivationCheckMachineLanguageDef.inferAcceptTransition,
  DerivationCheckMachineLanguageDef.dropFaultTransition,
  DerivationCheckMachineLanguageDef.dropAcceptTransition
]

/-- Input rows are excluded at the common decoder premise. -/
theorem input_lifted_rule_empty_on_finish_record
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState : Pattern)
    (membership : sourceRule ∈ nonDropInputSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish")) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  simp only [nonDropInputSourceRules, List.mem_cons, List.mem_nil_iff,
    or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl
  all_goals
    apply generic_lifted_record_rule_empty_of_decode_mismatch host _ record
      rest nodes nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [v "id", v "formula", v "provenance", v "relevance"])
      (DerivationCheckMachineLanguageDef.a "dcm:finish")
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
        DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
        DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
        DerivationCheckMachineLanguageDef.inputAcceptTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
        DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
        DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
        DerivationCheckMachineLanguageDef.inputAcceptTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v, run, recordsCons, v,
        DerivationWordMachineLanguageDef.a]
    · exact recordDecoded
    · simp [inputStartBindings, decoded,
        DerivationWordMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.a, v, applyBindings, matchPattern,
        matchArgs]

#print axioms input_lifted_rule_empty_on_finish_record

/-- Inference rows are excluded at the common decoder premise. -/
theorem infer_lifted_rule_empty_on_finish_record
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState : Pattern)
    (membership : sourceRule ∈ nonDropInferSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish")) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  simp only [nonDropInferSourceRules, List.mem_cons, List.mem_nil_iff,
    or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl
  all_goals
    apply generic_lifted_record_rule_empty_of_decode_mismatch host _ record
      rest nodes nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [v "id", v "rule", v "parents", v "evidence", v "conclusion",
          v "relevance"])
      (DerivationCheckMachineLanguageDef.a "dcm:finish")
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
        DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
        DerivationCheckMachineLanguageDef.inferParentFaultTransition,
        DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
        DerivationCheckMachineLanguageDef.inferAcceptTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
        DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
        DerivationCheckMachineLanguageDef.inferParentFaultTransition,
        DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
        DerivationCheckMachineLanguageDef.inferAcceptTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v, run, recordsCons, v,
        DerivationWordMachineLanguageDef.a]
    · exact recordDecoded
    · simp [inputStartBindings, decoded,
        DerivationWordMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.a, v, applyBindings, matchPattern,
        matchArgs]

#print axioms infer_lifted_rule_empty_on_finish_record

/-- Drop rows are excluded at the common decoder premise. -/
theorem drop_lifted_rule_empty_on_finish_record
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.dropFaultTransition,
      DerivationCheckMachineLanguageDef.dropAcceptTransition])
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish")) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  all_goals
    apply generic_lifted_record_rule_empty_of_decode_mismatch host _ record
      rest nodes nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:drop" [v "id"])
      (DerivationCheckMachineLanguageDef.a "dcm:finish")
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.dropFaultTransition,
        DerivationCheckMachineLanguageDef.dropAcceptTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.dropFaultTransition,
        DerivationCheckMachineLanguageDef.dropAcceptTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v, run, recordsCons, v,
        DerivationWordMachineLanguageDef.a]
    · exact recordDecoded
    · simp [inputStartBindings, decoded,
        DerivationWordMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.a, v, applyBindings, matchPattern,
        matchArgs]

#print axioms drop_lifted_rule_empty_on_finish_record

/-- A decoded finish record excludes every input, inference, and drop row at
the common decoder premise.  Root rows are handled at their more specific
root-state patterns below. -/
theorem non_finish_lifted_rule_empty_on_finish_record
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState : Pattern)
    (membership : sourceRule ∈ nonFinishSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish")) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  simp only [nonFinishSourceRules, List.mem_cons, List.mem_nil_iff, or_false]
    at membership
  rcases membership with h | h | h | h | h | h | h | h | h | h | h
  · exact input_lifted_rule_empty_on_finish_record host sourceRule record rest
      nodes nextId root serviceState (by simp [nonDropInputSourceRules, h])
      recordDecoded
  · exact input_lifted_rule_empty_on_finish_record host sourceRule record rest
      nodes nextId root serviceState (by simp [nonDropInputSourceRules, h])
      recordDecoded
  · exact input_lifted_rule_empty_on_finish_record host sourceRule record rest
      nodes nextId root serviceState (by simp [nonDropInputSourceRules, h])
      recordDecoded
  · exact input_lifted_rule_empty_on_finish_record host sourceRule record rest
      nodes nextId root serviceState (by simp [nonDropInputSourceRules, h])
      recordDecoded
  · exact infer_lifted_rule_empty_on_finish_record host sourceRule record rest
      nodes nextId root serviceState (by simp [nonDropInferSourceRules, h])
      recordDecoded
  · exact infer_lifted_rule_empty_on_finish_record host sourceRule record rest
      nodes nextId root serviceState (by simp [nonDropInferSourceRules, h])
      recordDecoded
  · exact infer_lifted_rule_empty_on_finish_record host sourceRule record rest
      nodes nextId root serviceState (by simp [nonDropInferSourceRules, h])
      recordDecoded
  · exact infer_lifted_rule_empty_on_finish_record host sourceRule record rest
      nodes nextId root serviceState (by simp [nonDropInferSourceRules, h])
      recordDecoded
  · exact infer_lifted_rule_empty_on_finish_record host sourceRule record rest
      nodes nextId root serviceState (by simp [nonDropInferSourceRules, h])
      recordDecoded
  · exact drop_lifted_rule_empty_on_finish_record host sourceRule record rest
      nodes nextId root serviceState (by simp [h]) recordDecoded
  · exact drop_lifted_rule_empty_on_finish_record host sourceRule record rest
      nodes nextId root serviceState (by simp [h]) recordDecoded

#print axioms non_finish_lifted_rule_empty_on_finish_record

theorem root_rows_empty_on_finish_record_root_none
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId serviceState : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.duplicateRootTransition,
      DerivationCheckMachineLanguageDef.rootFaultTransition,
      DerivationCheckMachineLanguageDef.rootAcceptTransition])
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish")) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · exact duplicate_root_on_root_none_applyRule_empty host record rest nodes
      nextId serviceState
  · simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.rootFaultTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.rootNone,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.query,
      query, v, run, recordsCons, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, matchRelationArgs, matchRelationArgument,
      matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]
  · simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.rootAcceptTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.rootNone,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.query,
      query, v, run, recordsCons, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, matchRelationArgs, matchRelationArgument,
      matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms root_rows_empty_on_finish_record_root_none

theorem root_rows_empty_on_finish_record_root_some
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId serviceState priorId priorFormula
      priorObligation : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.duplicateRootTransition,
      DerivationCheckMachineLanguageDef.rootFaultTransition,
      DerivationCheckMachineLanguageDef.rootAcceptTransition])
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish")) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern,
      DerivationCheckMachineLanguageDef.duplicateRootTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.rootSome,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      query, v, run, recordsCons, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, matchRelationArgs, matchRelationArgument,
      matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]
  · exact root_rules_on_root_some_empty host
      DerivationCheckMachineLanguageDef.rootFaultTransition record rest nodes
      nextId serviceState priorId priorFormula priorObligation (by simp)
  · exact root_rules_on_root_some_empty host
      DerivationCheckMachineLanguageDef.rootAcceptTransition record rest nodes
      nextId serviceState priorId priorFormula priorObligation (by simp)

#print axioms root_rows_empty_on_finish_record_root_some

theorem finish_trailing_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record nextRecord rest nodes nextId root serviceState : Pattern)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish")) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.finishTrailingTransition)
      (run (recordsCons record (recordsCons nextRecord rest)) nodes nextId root
        serviceState) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault
          (faultPattern .trailingAfterFinish))
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern,
    DerivationCheckMachineLanguageDef.finishTrailingTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    query, v, run, halted, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a,
    DerivationWordMachineRelationEnv.a, faultPattern, relationEnv,
    relationTuples,
    recordDecoded, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms finish_trailing_applyRule_exact

theorem nontrailing_finish_rules_empty_on_trailing
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record nextRecord rest nodes nextId root serviceState : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishMissingRootTransition,
      DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition]) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record (recordsCons nextRecord rest)) nodes nextId root
        serviceState) = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl
  all_goals
    simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition,
      DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.instructionsNil,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      run, recordsCons, recordsNil, DerivationWordMachineLanguageDef.a,
      matchPattern, matchArgs, mergeBindings]

#print axioms nontrailing_finish_rules_empty_on_trailing

theorem finish_trailing_rewriteAt_partition
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record nextRecord : DerivationCheckMachineBinary.WordRecord)
    (trailingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId root serviceState : Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish"))
    (rootRowsEmpty : forall sourceRule, sourceRule ∈ [
        DerivationCheckMachineLanguageDef.duplicateRootTransition,
        DerivationCheckMachineLanguageDef.rootFaultTransition,
        DerivationCheckMachineLanguageDef.rootAcceptTransition] ->
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) (liftRewrite sourceRule)
        (run (recordsCons (wordsPattern record)
          (recordsCons (wordsPattern nextRecord)
            (recordsPattern trailingRecords)))
          nodes nextId root serviceState) = []) :
    let source := run
      (recordsCons (wordsPattern record)
        (recordsCons (wordsPattern nextRecord)
          (recordsPattern trailingRecords)))
      nodes nextId root serviceState
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => [])
        (liftRewrite DerivationCheckMachineLanguageDef.finishTrailingTransition)
        source := by
  dsimp only
  change language.rewrites.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) rule
        (run (recordsCons (wordsPattern record)
          (recordsCons (wordsPattern nextRecord)
            (recordsPattern trailingRecords)))
          nodes nextId root serviceState)) = _
  rw [show language.rewrites = transitions by rfl]
  simp only [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil]
  rw [malformed_record_applyRule_empty host (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState
    (DerivationCheckMachineLanguageDef.a "dcm:finish") recordDecoded]
  rw [missing_finish_applyRule_empty host (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition
    (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState (by simp [nonFinishSourceRules])
    recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition
    (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState (by simp [nonFinishSourceRules])
    recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition
    (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState (by simp [nonFinishSourceRules])
    recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inputAcceptTransition
    (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState (by simp [nonFinishSourceRules])
    recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition
    (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState (by simp [nonFinishSourceRules])
    recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition
    (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState (by simp [nonFinishSourceRules])
    recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferParentFaultTransition
    (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState (by simp [nonFinishSourceRules])
    recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState (by simp [nonFinishSourceRules])
    recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState (by simp [nonFinishSourceRules])
    recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.dropFaultTransition
    (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState (by simp [nonFinishSourceRules])
    recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.dropAcceptTransition
    (wordsPattern record)
    (recordsCons (wordsPattern nextRecord) (recordsPattern trailingRecords))
    nodes nextId root serviceState (by simp [nonFinishSourceRules])
    recordDecoded]
  rw [rootRowsEmpty DerivationCheckMachineLanguageDef.duplicateRootTransition
    (by simp)]
  rw [rootRowsEmpty DerivationCheckMachineLanguageDef.rootFaultTransition
    (by simp)]
  rw [rootRowsEmpty DerivationCheckMachineLanguageDef.rootAcceptTransition
    (by simp)]
  rw [nontrailing_finish_rules_empty_on_trailing host
    DerivationCheckMachineLanguageDef.finishMissingRootTransition
    (wordsPattern record) (wordsPattern nextRecord)
    (recordsPattern trailingRecords) nodes nextId root serviceState (by simp)]
  rw [nontrailing_finish_rules_empty_on_trailing host
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition
    (wordsPattern record) (wordsPattern nextRecord)
    (recordsPattern trailingRecords) nodes nextId root serviceState (by simp)]
  rw [nontrailing_finish_rules_empty_on_trailing host
    DerivationCheckMachineLanguageDef.finishRootFaultTransition
    (wordsPattern record) (wordsPattern nextRecord)
    (recordsPattern trailingRecords) nodes nextId root serviceState (by simp)]
  rw [nontrailing_finish_rules_empty_on_trailing host
    DerivationCheckMachineLanguageDef.finishVerifiedTransition
    (wordsPattern record) (wordsPattern nextRecord)
    (recordsPattern trailingRecords) nodes nextId root serviceState (by simp)]
  simp

#print axioms finish_trailing_rewriteAt_partition

theorem finish_trailing_rewriteAt_exact_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record nextRecord : DerivationCheckMachineBinary.WordRecord)
    (trailingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState : Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish"))
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsCons (wordsPattern nextRecord)
          (recordsPattern trailingRecords)))
        nodes nextId rootPatternValue serviceState) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault
          (faultPattern .trailingAfterFinish))
        nodes] := by
  cases rootState with
  | none =>
      simp [rootPattern?] at rootEncoded
      subst rootPatternValue
      rw [finish_trailing_rewriteAt_partition host record nextRecord
        trailingRecords nodes nextId DerivationCheckMachineLanguageDef.rootNone
        serviceState recordDecoded]
      · exact finish_trailing_applyRule_exact host (wordsPattern record)
          (wordsPattern nextRecord) (recordsPattern trailingRecords) nodes
          nextId DerivationCheckMachineLanguageDef.rootNone serviceState
          recordDecoded
      · intro sourceRule membership
        exact root_rows_empty_on_finish_record_root_none host sourceRule
          (wordsPattern record)
          (recordsCons (wordsPattern nextRecord)
            (recordsPattern trailingRecords))
          nodes nextId serviceState membership recordDecoded
  | some priorRoot =>
      rcases priorRoot with ⟨priorId, priorFormula, priorObligation⟩
      unfold rootPattern? at rootEncoded
      cases formulaEncoded : encodeFormula? host priorFormula with
      | none => simp [formulaEncoded] at rootEncoded
      | some priorFormulaPattern =>
          cases obligationEncoded : encodeObligation? host priorObligation with
          | none => simp [formulaEncoded, obligationEncoded] at rootEncoded
          | some priorObligationPattern =>
              simp [formulaEncoded, obligationEncoded] at rootEncoded
              subst rootPatternValue
              rw [finish_trailing_rewriteAt_partition host record nextRecord
                trailingRecords nodes nextId
                (DerivationCheckMachineLanguageDef.rootSome
                  (indexPattern priorId) priorFormulaPattern
                  priorObligationPattern)
                serviceState recordDecoded]
              · exact finish_trailing_applyRule_exact host
                  (wordsPattern record) (wordsPattern nextRecord)
                  (recordsPattern trailingRecords) nodes nextId
                  (DerivationCheckMachineLanguageDef.rootSome
                    (indexPattern priorId) priorFormulaPattern
                    priorObligationPattern)
                  serviceState recordDecoded
              · intro sourceRule membership
                exact root_rows_empty_on_finish_record_root_some host
                  sourceRule (wordsPattern record)
                  (recordsCons (wordsPattern nextRecord)
                    (recordsPattern trailingRecords))
                  nodes nextId serviceState (indexPattern priorId)
                  priorFormulaPattern priorObligationPattern membership
                  recordDecoded

#print axioms finish_trailing_rewriteAt_exact_encoded_root

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance] in
theorem finish_source_encodes_running
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (nextId : Nat)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some .finish)
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .finish :: remainingInstructions
      nodes := oldNodes
      nextId := nextId
      root? := rootState
      serviceState := serviceState
    }
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern nextId) rootPatternValue
      serviceStatePattern
    EncodesConfig host (record :: remainingRecords) (.running before)
      source := by
  dsimp only
  constructor
  · simp [DerivationCheckMachineBinary.decodeProgramUsing?,
      recordInstructionDecoded, remainingDecoded]
  · simp [runningPattern?, nodesEncoded, serviceStateEncoded, rootEncoded,
      recordsPattern, recordsCons, DerivationWordMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]

#print axioms finish_source_encodes_running

theorem finish_trailing_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record nextRecord : DerivationCheckMachineBinary.WordRecord)
    (trailingRecords : DerivationCheckMachineBinary.WordProgram)
    (nextInstruction : Instruction Formula Rule Evidence Provenance Obligation)
    (trailingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (nextId : Nat)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some .finish)
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing? host.codecs.decoders
          (nextRecord :: trailingRecords) =
        some (nextInstruction :: trailingInstructions))
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .finish :: nextInstruction :: trailingInstructions
      nodes := oldNodes
      nextId := nextId
      root? := rootState
      serviceState := serviceState
    }
    let failure := Fault.trailingAfterFinish
    let source := run
      (recordsCons (wordsPattern record)
        (recordsCons (wordsPattern nextRecord)
          (recordsPattern trailingRecords)))
      nodesPatternValue (indexPattern nextId) rootPatternValue
      serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault (faultPattern failure))
      nodesPatternValue
    EncodesConfig host (record :: nextRecord :: trailingRecords)
        (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault failure)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host (nextRecord :: trailingRecords)
        (.halted (.fault failure)) target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host
          (Instruction.finish :
            Instruction Formula Rule Evidence Provenance Obligation) =
        some (DerivationCheckMachineLanguageDef.a "dcm:finish") := by
    simp [instructionPattern?, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish") := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:finish"]
    exact decodeDecision_wordsPattern_exact host record .finish
      (DerivationCheckMachineLanguageDef.a "dcm:finish")
      recordInstructionDecoded instructionPatternEncoded
  constructor
  · exact finish_source_encodes_running host rootState rootPatternValue record
      (nextRecord :: trailingRecords)
      (nextInstruction :: trailingInstructions) oldNodes nextId serviceState
      serviceStatePattern nodesPatternValue recordInstructionDecoded
      remainingDecoded rootEncoded serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault]
  constructor
  · exact finish_trailing_rewriteAt_exact_encoded_root host rootState
      rootPatternValue record nextRecord trailingRecords nodesPatternValue
      (indexPattern nextId) serviceStatePattern recordDecoded rootEncoded
  · exact fault_target_encodes_halted host (nextRecord :: trailingRecords)
      oldNodes .trailingAfterFinish nodesPatternValue nodesEncoded

#print axioms finish_trailing_semantic_square_encoded_root

theorem finish_trailing_applyRule_empty_on_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record nodes nextId root serviceState : Pattern) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.finishTrailingTransition)
      (run (recordsCons record recordsNil) nodes nextId root serviceState) =
        [] := by
  simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
    liftPattern,
    DerivationCheckMachineLanguageDef.finishTrailingTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    run, recordsCons, recordsNil, DerivationWordMachineLanguageDef.a,
    matchPattern, matchArgs, mergeBindings]

#print axioms finish_trailing_applyRule_empty_on_empty

theorem finish_missing_root_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record nodes nextId serviceState : Pattern)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish")) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite
        DerivationCheckMachineLanguageDef.finishMissingRootTransition)
      (run (recordsCons record recordsNil) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault
          (faultPattern .missingRoot))
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern,
    DerivationCheckMachineLanguageDef.finishMissingRootTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.rootNone,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    query, v, run, halted, recordsCons, recordsNil, decoded,
    DerivationWordMachineLanguageDef.a,
    DerivationWordMachineRelationEnv.a, faultPattern, relationEnv,
    relationTuples, recordDecoded, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms finish_missing_root_applyRule_exact

theorem finish_missing_root_applyRule_empty_root_some
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record nodes nextId serviceState id formula obligation : Pattern) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite
        DerivationCheckMachineLanguageDef.finishMissingRootTransition)
      (run (recordsCons record recordsNil) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
        serviceState) = [] := by
  simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
    liftPattern,
    DerivationCheckMachineLanguageDef.finishMissingRootTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.rootNone,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    run, recordsCons, recordsNil, DerivationWordMachineLanguageDef.a,
    matchPattern, matchArgs, mergeBindings]

#print axioms finish_missing_root_applyRule_empty_root_some

theorem finish_relevance_fault_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record nodes nextId serviceState idPattern formulaPattern
      obligationPattern faultPatternValue : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish"))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (relevanceFaulted : relevanceClosureDecision oldNodes id =
      DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite
        DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition)
      (run (recordsCons record recordsNil) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome idPattern formulaPattern
          obligationPattern)
        serviceState) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, halted, recordsCons, recordsNil, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, relevanceFaulted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms finish_relevance_fault_applyRule_exact

theorem later_finish_rules_empty_of_relevance_fault
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record nodes nextId serviceState idPattern formulaPattern
      obligationPattern faultPatternValue : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition])
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish"))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (relevanceFaulted : relevanceClosureDecision oldNodes id =
      DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record recordsNil) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome idPattern formulaPattern
          obligationPattern)
        serviceState) = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  all_goals
    simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.instructionsNil,
      DerivationCheckMachineLanguageDef.rootSome,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.query,
      query, v, run, recordsCons, recordsNil, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, nodesDecoded, idDecoded, relevanceFaulted,
      premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
      mergeBindings, applyBindings, Bindings.lookup]

#print axioms later_finish_rules_empty_of_relevance_fault

theorem finish_root_fault_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record nodes nextId serviceStatePattern idPattern formulaPattern
      obligationPattern faultPatternValue : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (serviceState : ServiceState) (formula : Formula)
    (obligation : Obligation)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish"))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (obligationDecoded :
      decodeObligation? host obligationPattern = some obligation)
    (relevanceAccepted : relevanceClosureDecision oldNodes id =
      DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (finalFaulted : finalDecision host id serviceState formula obligation =
      DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite
        DerivationCheckMachineLanguageDef.finishRootFaultTransition)
      (run (recordsCons record recordsNil) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome idPattern formulaPattern
          obligationPattern)
        serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.finishRootFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, halted, recordsCons, recordsNil, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, serviceStateDecoded,
    formulaDecoded, obligationDecoded, relevanceAccepted, finalFaulted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms finish_root_fault_applyRule_exact

theorem finish_verified_applyRule_empty_of_root_fault
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record nodes nextId serviceStatePattern idPattern formulaPattern
      obligationPattern faultPatternValue : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (serviceState : ServiceState) (formula : Formula)
    (obligation : Obligation)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish"))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (obligationDecoded :
      decodeObligation? host obligationPattern = some obligation)
    (relevanceAccepted : relevanceClosureDecision oldNodes id =
      DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (finalFaulted : finalDecision host id serviceState formula obligation =
      DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.finishVerifiedTransition)
      (run (recordsCons record recordsNil) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome idPattern formulaPattern
          obligationPattern)
        serviceStatePattern) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.finishVerifiedTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, recordsNil, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, serviceStateDecoded,
    formulaDecoded, obligationDecoded, relevanceAccepted, finalFaulted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms finish_verified_applyRule_empty_of_root_fault

theorem finish_verified_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record nodes nextId serviceStatePattern idPattern formulaPattern
      obligationPattern : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (serviceState : ServiceState) (formula : Formula)
    (obligation : Obligation)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish"))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (obligationDecoded :
      decodeObligation? host obligationPattern = some obligation)
    (relevanceAccepted : relevanceClosureDecision oldNodes id =
      DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (finalAccepted : finalDecision host id serviceState formula obligation =
      DerivationCheckMachineLanguageDef.a "dcm:decision-accept") :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.finishVerifiedTransition)
      (run (recordsCons record recordsNil) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome idPattern formulaPattern
          obligationPattern)
        serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.a "dcm:outcome-verified"
          [idPattern, formulaPattern, obligationPattern])
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.finishVerifiedTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, halted, recordsCons, recordsNil, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, serviceStateDecoded,
    formulaDecoded, obligationDecoded, relevanceAccepted, finalAccepted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms finish_verified_applyRule_exact

theorem finish_root_fault_applyRule_empty_of_accept
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record nodes nextId serviceStatePattern idPattern formulaPattern
      obligationPattern : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (serviceState : ServiceState) (formula : Formula)
    (obligation : Obligation)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish"))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (obligationDecoded :
      decodeObligation? host obligationPattern = some obligation)
    (relevanceAccepted : relevanceClosureDecision oldNodes id =
      DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (finalAccepted : finalDecision host id serviceState formula obligation =
      DerivationCheckMachineLanguageDef.a "dcm:decision-accept") :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite
        DerivationCheckMachineLanguageDef.finishRootFaultTransition)
      (run (recordsCons record recordsNil) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome idPattern formulaPattern
          obligationPattern)
        serviceStatePattern) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.finishRootFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, recordsNil, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, serviceStateDecoded,
    formulaDecoded, obligationDecoded, relevanceAccepted, finalAccepted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms finish_root_fault_applyRule_empty_of_accept

theorem finish_empty_rewriteAt_partition_root_none
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (nodes nextId serviceState : Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish")) :
    let source := run (recordsCons (wordsPattern record) recordsNil) nodes
      nextId DerivationCheckMachineLanguageDef.rootNone serviceState
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => [])
        (liftRewrite
          DerivationCheckMachineLanguageDef.finishMissingRootTransition)
        source := by
  dsimp only
  change language.rewrites.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) rule
        (run (recordsCons (wordsPattern record) recordsNil) nodes nextId
          DerivationCheckMachineLanguageDef.rootNone serviceState)) = _
  rw [show language.rewrites = transitions by rfl]
  simp only [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil]
  rw [malformed_record_applyRule_empty host (wordsPattern record) recordsNil
    nodes nextId DerivationCheckMachineLanguageDef.rootNone serviceState
    (DerivationCheckMachineLanguageDef.a "dcm:finish") recordDecoded]
  rw [missing_finish_applyRule_empty host (wordsPattern record) recordsNil nodes
    nextId DerivationCheckMachineLanguageDef.rootNone serviceState]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inputAcceptTransition
    (wordsPattern record) recordsNil nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferParentFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record) recordsNil nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.dropFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.dropAcceptTransition
    (wordsPattern record) recordsNil nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (by simp [nonFinishSourceRules]) recordDecoded]
  rw [root_rows_empty_on_finish_record_root_none host
    DerivationCheckMachineLanguageDef.duplicateRootTransition
    (wordsPattern record) recordsNil nodes nextId serviceState (by simp)
    recordDecoded]
  rw [root_rows_empty_on_finish_record_root_none host
    DerivationCheckMachineLanguageDef.rootFaultTransition
    (wordsPattern record) recordsNil nodes nextId serviceState (by simp)
    recordDecoded]
  rw [root_rows_empty_on_finish_record_root_none host
    DerivationCheckMachineLanguageDef.rootAcceptTransition
    (wordsPattern record) recordsNil nodes nextId serviceState (by simp)
    recordDecoded]
  rw [finish_trailing_applyRule_empty_on_empty host (wordsPattern record)
    nodes nextId DerivationCheckMachineLanguageDef.rootNone serviceState]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition
    (wordsPattern record) recordsNil nodes nextId serviceState (by simp)]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishRootFaultTransition
    (wordsPattern record) recordsNil nodes nextId serviceState (by simp)]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishVerifiedTransition
    (wordsPattern record) recordsNil nodes nextId serviceState (by simp)]
  simp

#print axioms finish_empty_rewriteAt_partition_root_none

theorem finish_empty_rewriteAt_partition_root_some
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (nodes nextId serviceState id formula obligation : Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish")) :
    let root :=
      DerivationCheckMachineLanguageDef.rootSome id formula obligation
    let source := run (recordsCons (wordsPattern record) recordsNil) nodes
      nextId root serviceState
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite
            DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite
            DerivationCheckMachineLanguageDef.finishRootFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite
            DerivationCheckMachineLanguageDef.finishVerifiedTransition)
          source := by
  dsimp only
  change language.rewrites.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) rule
        (run (recordsCons (wordsPattern record) recordsNil) nodes nextId
          (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
          serviceState)) = _
  rw [show language.rewrites = transitions by rfl]
  simp only [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil]
  rw [malformed_record_applyRule_empty host (wordsPattern record) recordsNil
    nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState (DerivationCheckMachineLanguageDef.a "dcm:finish")
    recordDecoded]
  rw [missing_finish_applyRule_empty host (wordsPattern record) recordsNil nodes
    nextId (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inputAcceptTransition
    (wordsPattern record) recordsNil nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferParentFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record) recordsNil nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.dropFaultTransition
    (wordsPattern record) recordsNil nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState (by simp [nonFinishSourceRules]) recordDecoded]
  rw [non_finish_lifted_rule_empty_on_finish_record host
    DerivationCheckMachineLanguageDef.dropAcceptTransition
    (wordsPattern record) recordsNil nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState (by simp [nonFinishSourceRules]) recordDecoded]
  rw [root_rows_empty_on_finish_record_root_some host
    DerivationCheckMachineLanguageDef.duplicateRootTransition
    (wordsPattern record) recordsNil nodes nextId serviceState id formula
    obligation (by simp) recordDecoded]
  rw [root_rows_empty_on_finish_record_root_some host
    DerivationCheckMachineLanguageDef.rootFaultTransition
    (wordsPattern record) recordsNil nodes nextId serviceState id formula
    obligation (by simp) recordDecoded]
  rw [root_rows_empty_on_finish_record_root_some host
    DerivationCheckMachineLanguageDef.rootAcceptTransition
    (wordsPattern record) recordsNil nodes nextId serviceState id formula
    obligation (by simp) recordDecoded]
  rw [finish_trailing_applyRule_empty_on_empty host (wordsPattern record)
    nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome id formula obligation)
    serviceState]
  rw [finish_missing_root_applyRule_empty_root_some host (wordsPattern record)
    nodes nextId serviceState id formula obligation]
  simp

#print axioms finish_empty_rewriteAt_partition_root_some

theorem finish_relevance_fault_applyRule_empty_of_accept
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record nodes nextId serviceState idPattern formulaPattern
      obligationPattern : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish"))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (relevanceAccepted : relevanceClosureDecision oldNodes id =
      DerivationCheckMachineLanguageDef.a "dcm:decision-accept") :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite
        DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition)
      (run (recordsCons record recordsNil) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome idPattern formulaPattern
          obligationPattern)
        serviceState) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, recordsNil, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, relevanceAccepted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms finish_relevance_fault_applyRule_empty_of_accept

theorem finish_missing_root_rewriteAt_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (nodes nextId serviceState : Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish")) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record) recordsNil) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault
          (faultPattern .missingRoot))
        nodes] := by
  rw [finish_empty_rewriteAt_partition_root_none host record nodes nextId
    serviceState recordDecoded]
  exact finish_missing_root_applyRule_exact host (wordsPattern record) nodes
    nextId serviceState recordDecoded

#print axioms finish_missing_root_rewriteAt_exact

theorem finish_relevance_fault_rewriteAt_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (nodes nextId serviceState idPattern formulaPattern obligationPattern
      faultPatternValue : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish"))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (relevanceFaulted : relevanceClosureDecision oldNodes id =
      DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record) recordsNil) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome idPattern formulaPattern
          obligationPattern)
        serviceState) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  rw [finish_empty_rewriteAt_partition_root_some host record nodes nextId
    serviceState idPattern formulaPattern obligationPattern recordDecoded]
  rw [finish_relevance_fault_applyRule_exact host (wordsPattern record) nodes
    nextId serviceState idPattern formulaPattern obligationPattern
    faultPatternValue oldNodes id recordDecoded nodesDecoded idDecoded
    relevanceFaulted]
  rw [later_finish_rules_empty_of_relevance_fault host
    DerivationCheckMachineLanguageDef.finishRootFaultTransition
    (wordsPattern record) nodes nextId serviceState idPattern formulaPattern
    obligationPattern faultPatternValue oldNodes id (by simp) recordDecoded
    nodesDecoded idDecoded relevanceFaulted]
  rw [later_finish_rules_empty_of_relevance_fault host
    DerivationCheckMachineLanguageDef.finishVerifiedTransition
    (wordsPattern record) nodes nextId serviceState idPattern formulaPattern
    obligationPattern faultPatternValue oldNodes id (by simp) recordDecoded
    nodesDecoded idDecoded relevanceFaulted]
  simp

#print axioms finish_relevance_fault_rewriteAt_exact

theorem finish_root_fault_rewriteAt_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (nodes nextId serviceStatePattern idPattern formulaPattern
      obligationPattern faultPatternValue : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (serviceState : ServiceState) (formula : Formula)
    (obligation : Obligation)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish"))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (obligationDecoded :
      decodeObligation? host obligationPattern = some obligation)
    (relevanceAccepted : relevanceClosureDecision oldNodes id =
      DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (finalFaulted : finalDecision host id serviceState formula obligation =
      DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record) recordsNil) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome idPattern formulaPattern
          obligationPattern)
        serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  rw [finish_empty_rewriteAt_partition_root_some host record nodes nextId
    serviceStatePattern idPattern formulaPattern obligationPattern
    recordDecoded]
  rw [finish_relevance_fault_applyRule_empty_of_accept host
    (wordsPattern record) nodes nextId serviceStatePattern idPattern
    formulaPattern obligationPattern oldNodes id recordDecoded nodesDecoded
    idDecoded relevanceAccepted]
  rw [finish_root_fault_applyRule_exact host (wordsPattern record) nodes nextId
    serviceStatePattern idPattern formulaPattern obligationPattern
    faultPatternValue oldNodes id serviceState formula obligation recordDecoded
    nodesDecoded idDecoded serviceStateDecoded formulaDecoded
    obligationDecoded relevanceAccepted finalFaulted]
  rw [finish_verified_applyRule_empty_of_root_fault host
    (wordsPattern record) nodes nextId serviceStatePattern idPattern
    formulaPattern obligationPattern faultPatternValue oldNodes id serviceState
    formula obligation recordDecoded nodesDecoded idDecoded
    serviceStateDecoded formulaDecoded obligationDecoded relevanceAccepted
    finalFaulted]
  simp

#print axioms finish_root_fault_rewriteAt_exact

theorem finish_verified_rewriteAt_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (nodes nextId serviceStatePattern idPattern formulaPattern
      obligationPattern : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (serviceState : ServiceState) (formula : Formula)
    (obligation : Obligation)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish"))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (obligationDecoded :
      decodeObligation? host obligationPattern = some obligation)
    (relevanceAccepted : relevanceClosureDecision oldNodes id =
      DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (finalAccepted : finalDecision host id serviceState formula obligation =
      DerivationCheckMachineLanguageDef.a "dcm:decision-accept") :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record) recordsNil) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome idPattern formulaPattern
          obligationPattern)
        serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.a "dcm:outcome-verified"
          [idPattern, formulaPattern, obligationPattern])
        nodes] := by
  rw [finish_empty_rewriteAt_partition_root_some host record nodes nextId
    serviceStatePattern idPattern formulaPattern obligationPattern
    recordDecoded]
  rw [finish_relevance_fault_applyRule_empty_of_accept host
    (wordsPattern record) nodes nextId serviceStatePattern idPattern
    formulaPattern obligationPattern oldNodes id recordDecoded nodesDecoded
    idDecoded relevanceAccepted]
  rw [finish_root_fault_applyRule_empty_of_accept host
    (wordsPattern record) nodes nextId serviceStatePattern idPattern
    formulaPattern obligationPattern oldNodes id serviceState formula
    obligation recordDecoded nodesDecoded idDecoded serviceStateDecoded
    formulaDecoded obligationDecoded relevanceAccepted finalAccepted]
  rw [finish_verified_applyRule_exact host (wordsPattern record) nodes nextId
    serviceStatePattern idPattern formulaPattern obligationPattern oldNodes id
    serviceState formula obligation recordDecoded nodesDecoded idDecoded
    serviceStateDecoded formulaDecoded obligationDecoded relevanceAccepted
    finalAccepted]
  simp

#print axioms finish_verified_rewriteAt_exact

theorem finish_missing_root_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (oldNodes : List (Node Formula)) (nextId : Nat)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some .finish)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := [.finish]
      nodes := oldNodes
      nextId := nextId
      root? := none
      serviceState := serviceState
    }
    let failure := Fault.missingRoot
    let source := run (recordsCons (wordsPattern record) recordsNil)
      nodesPatternValue (indexPattern nextId)
      DerivationCheckMachineLanguageDef.rootNone serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault (faultPattern failure))
      nodesPatternValue
    EncodesConfig host [record] (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault failure)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host [] (.halted (.fault failure)) target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host
          (Instruction.finish :
            Instruction Formula Rule Evidence Provenance Obligation) =
        some (DerivationCheckMachineLanguageDef.a "dcm:finish") := by
    simp [instructionPattern?, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish") := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:finish"]
    exact decodeDecision_wordsPattern_exact host record .finish
      (DerivationCheckMachineLanguageDef.a "dcm:finish")
      recordInstructionDecoded instructionPatternEncoded
  constructor
  · exact finish_source_encodes_running host none
      DerivationCheckMachineLanguageDef.rootNone record [] [] oldNodes nextId
      serviceState serviceStatePattern nodesPatternValue
      recordInstructionDecoded rfl rfl serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault]
  constructor
  · exact finish_missing_root_rewriteAt_exact host record nodesPatternValue
      (indexPattern nextId) serviceStatePattern recordDecoded
  · exact fault_target_encodes_halted host [] oldNodes .missingRoot
      nodesPatternValue nodesEncoded

#print axioms finish_missing_root_semantic_square

theorem finish_irrelevant_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (root : RootClaim Formula Obligation)
    (formulaPattern obligationPattern : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (oldNodes : List (Node Formula)) (irrelevantId nextId : Nat)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (irrelevant : firstIrrelevant? root.id oldNodes = some irrelevantId)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some .finish)
    (formulaEncoded :
      encodeFormula? host root.formula = some formulaPattern)
    (obligationEncoded :
      encodeObligation? host root.obligation = some obligationPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := [.finish]
      nodes := oldNodes
      nextId := nextId
      root? := some root
      serviceState := serviceState
    }
    let failure := Fault.irrelevantNode irrelevantId
    let rootPatternValue := DerivationCheckMachineLanguageDef.rootSome
      (indexPattern root.id) formulaPattern obligationPattern
    let source := run (recordsCons (wordsPattern record) recordsNil)
      nodesPatternValue (indexPattern nextId) rootPatternValue
      serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault (faultPattern failure))
      nodesPatternValue
    EncodesConfig host [record] (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault failure)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host [] (.halted (.fault failure)) target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host
          (Instruction.finish :
            Instruction Formula Rule Evidence Provenance Obligation) =
        some (DerivationCheckMachineLanguageDef.a "dcm:finish") := by
    simp [instructionPattern?, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish") := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:finish"]
    exact decodeDecision_wordsPattern_exact host record .finish
      (DerivationCheckMachineLanguageDef.a "dcm:finish")
      recordInstructionDecoded instructionPatternEncoded
  have rootEncoded : rootPattern? host (some root) =
      some (DerivationCheckMachineLanguageDef.rootSome
        (indexPattern root.id) formulaPattern obligationPattern) := by
    rcases root with ⟨id, formula, obligation⟩
    simp [rootPattern?, formulaEncoded, obligationEncoded]
  have nodesDecoded :=
    decodeNodes_nodesPattern host oldNodes nodesPatternValue nodesEncoded
  have relevanceFaulted : relevanceClosureDecision oldNodes root.id =
      DerivationCheckMachineLanguageDef.decisionFault
        (faultPattern (.irrelevantNode irrelevantId)) := by
    simp [relevanceClosureDecision, irrelevant, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact finish_source_encodes_running host (some root)
      (DerivationCheckMachineLanguageDef.rootSome (indexPattern root.id)
        formulaPattern obligationPattern)
      record [] [] oldNodes nextId serviceState serviceStatePattern
      nodesPatternValue recordInstructionDecoded rfl rootEncoded
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault, irrelevant]
  constructor
  · exact finish_relevance_fault_rewriteAt_exact host record
      nodesPatternValue (indexPattern nextId) serviceStatePattern
      (indexPattern root.id) formulaPattern obligationPattern
      (faultPattern (.irrelevantNode irrelevantId)) oldNodes root.id
      recordDecoded nodesDecoded (decodeIndex_indexPattern root.id)
      relevanceFaulted
  · exact fault_target_encodes_halted host [] oldNodes
      (.irrelevantNode irrelevantId) nodesPatternValue nodesEncoded

#print axioms finish_irrelevant_semantic_square

theorem finish_root_rejected_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (root : RootClaim Formula Obligation)
    (formulaPattern obligationPattern : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (oldNodes : List (Node Formula)) (nextId : Nat)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (relevant : firstIrrelevant? root.id oldNodes = none)
    (rejected :
      host.services.root serviceState root.formula root.obligation = false)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some .finish)
    (formulaEncoded :
      encodeFormula? host root.formula = some formulaPattern)
    (obligationEncoded :
      encodeObligation? host root.obligation = some obligationPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := [.finish]
      nodes := oldNodes
      nextId := nextId
      root? := some root
      serviceState := serviceState
    }
    let failure := Fault.rootRejected root.id
    let rootPatternValue := DerivationCheckMachineLanguageDef.rootSome
      (indexPattern root.id) formulaPattern obligationPattern
    let source := run (recordsCons (wordsPattern record) recordsNil)
      nodesPatternValue (indexPattern nextId) rootPatternValue
      serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault (faultPattern failure))
      nodesPatternValue
    EncodesConfig host [record] (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault failure)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host [] (.halted (.fault failure)) target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host
          (Instruction.finish :
            Instruction Formula Rule Evidence Provenance Obligation) =
        some (DerivationCheckMachineLanguageDef.a "dcm:finish") := by
    simp [instructionPattern?, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish") := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:finish"]
    exact decodeDecision_wordsPattern_exact host record .finish
      (DerivationCheckMachineLanguageDef.a "dcm:finish")
      recordInstructionDecoded instructionPatternEncoded
  have rootEncoded : rootPattern? host (some root) =
      some (DerivationCheckMachineLanguageDef.rootSome
        (indexPattern root.id) formulaPattern obligationPattern) := by
    rcases root with ⟨id, formula, obligation⟩
    simp [rootPattern?, formulaEncoded, obligationEncoded]
  have nodesDecoded :=
    decodeNodes_nodesPattern host oldNodes nodesPatternValue nodesEncoded
  have serviceStateDecoded :=
    decodeServiceState_encodeServiceState host serviceState
      serviceStatePattern serviceStateEncoded
  have formulaDecoded :=
    decodeFormula_encodeFormula host root.formula formulaPattern formulaEncoded
  have obligationDecoded :=
    decodeObligation_encodeObligation host root.obligation obligationPattern
      obligationEncoded
  have relevanceAccepted : relevanceClosureDecision oldNodes root.id =
      DerivationCheckMachineLanguageDef.a "dcm:decision-accept" := by
    simp [relevanceClosureDecision, relevant,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have finalFaulted :
      finalDecision host root.id serviceState root.formula root.obligation =
        DerivationCheckMachineLanguageDef.decisionFault
          (faultPattern (.rootRejected root.id)) := by
    simp [finalDecision, rejected, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact finish_source_encodes_running host (some root)
      (DerivationCheckMachineLanguageDef.rootSome (indexPattern root.id)
        formulaPattern obligationPattern)
      record [] [] oldNodes nextId serviceState serviceStatePattern
      nodesPatternValue recordInstructionDecoded rfl rootEncoded
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault, relevant, rejected]
  constructor
  · exact finish_root_fault_rewriteAt_exact host record nodesPatternValue
      (indexPattern nextId) serviceStatePattern (indexPattern root.id)
      formulaPattern obligationPattern (faultPattern (.rootRejected root.id))
      oldNodes root.id serviceState root.formula root.obligation recordDecoded
      nodesDecoded (decodeIndex_indexPattern root.id) serviceStateDecoded
      formulaDecoded obligationDecoded relevanceAccepted finalFaulted
  · exact fault_target_encodes_halted host [] oldNodes
      (.rootRejected root.id) nodesPatternValue nodesEncoded

#print axioms finish_root_rejected_semantic_square

theorem finish_verified_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (root : RootClaim Formula Obligation)
    (formulaPattern obligationPattern : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (oldNodes : List (Node Formula)) (nextId : Nat)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (relevant : firstIrrelevant? root.id oldNodes = none)
    (accepted :
      host.services.root serviceState root.formula root.obligation = true)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some .finish)
    (formulaEncoded :
      encodeFormula? host root.formula = some formulaPattern)
    (obligationEncoded :
      encodeObligation? host root.obligation = some obligationPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := [.finish]
      nodes := oldNodes
      nextId := nextId
      root? := some root
      serviceState := serviceState
    }
    let rootPatternValue := DerivationCheckMachineLanguageDef.rootSome
      (indexPattern root.id) formulaPattern obligationPattern
    let source := run (recordsCons (wordsPattern record) recordsNil)
      nodesPatternValue (indexPattern nextId) rootPatternValue
      serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.a "dcm:outcome-verified"
        [indexPattern root.id, formulaPattern, obligationPattern])
      nodesPatternValue
    EncodesConfig host [record] (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.verified root)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host [] (.halted (.verified root)) target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host
          (Instruction.finish :
            Instruction Formula Rule Evidence Provenance Obligation) =
        some (DerivationCheckMachineLanguageDef.a "dcm:finish") := by
    simp [instructionPattern?, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:finish") := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:finish"]
    exact decodeDecision_wordsPattern_exact host record .finish
      (DerivationCheckMachineLanguageDef.a "dcm:finish")
      recordInstructionDecoded instructionPatternEncoded
  have rootEncoded : rootPattern? host (some root) =
      some (DerivationCheckMachineLanguageDef.rootSome
        (indexPattern root.id) formulaPattern obligationPattern) := by
    rcases root with ⟨id, formula, obligation⟩
    simp [rootPattern?, formulaEncoded, obligationEncoded]
  have nodesDecoded :=
    decodeNodes_nodesPattern host oldNodes nodesPatternValue nodesEncoded
  have serviceStateDecoded :=
    decodeServiceState_encodeServiceState host serviceState
      serviceStatePattern serviceStateEncoded
  have formulaDecoded :=
    decodeFormula_encodeFormula host root.formula formulaPattern formulaEncoded
  have obligationDecoded :=
    decodeObligation_encodeObligation host root.obligation obligationPattern
      obligationEncoded
  have relevanceAccepted : relevanceClosureDecision oldNodes root.id =
      DerivationCheckMachineLanguageDef.a "dcm:decision-accept" := by
    simp [relevanceClosureDecision, relevant,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have finalAccepted :
      finalDecision host root.id serviceState root.formula root.obligation =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept" := by
    simp [finalDecision, accepted, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact finish_source_encodes_running host (some root)
      (DerivationCheckMachineLanguageDef.rootSome (indexPattern root.id)
        formulaPattern obligationPattern)
      record [] [] oldNodes nextId serviceState serviceStatePattern
      nodesPatternValue recordInstructionDecoded rfl rootEncoded
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, relevant, accepted]
  constructor
  · exact finish_verified_rewriteAt_exact host record nodesPatternValue
      (indexPattern nextId) serviceStatePattern (indexPattern root.id)
      formulaPattern obligationPattern oldNodes root.id serviceState
      root.formula root.obligation recordDecoded nodesDecoded
      (decodeIndex_indexPattern root.id) serviceStateDecoded formulaDecoded
      obligationDecoded relevanceAccepted finalAccepted
  · refine ⟨oldNodes, ⟨?_⟩⟩
    simp [haltedPattern?, outcomePattern?, formulaEncoded, obligationEncoded,
      nodesEncoded, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]

#print axioms finish_verified_semantic_square

/- Every representable finish instruction takes exactly one authored step.
The theorem covers trailing-input rejection, a missing root, an irrelevant
node, calculus rejection, and successful verification. -/
theorem finish_one_record_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (nextId : Nat)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some .finish)
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .finish :: remainingInstructions
      nodes := oldNodes
      nextId := nextId
      root? := rootState
      serviceState := serviceState
    }
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern nextId) rootPatternValue
      serviceStatePattern
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      exists next target,
        step? host.services (.running before) = some next ∧
          rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
            [target] ∧
          EncodesConfig host remainingRecords next target := by
  dsimp only
  cases remainingRecords with
  | cons nextRecord trailingRecords =>
      cases nextDecoded :
          DerivationCheckMachineBinary.decodeInstructionUsing?
            host.codecs.decoders nextRecord with
      | none =>
          simp [DerivationCheckMachineBinary.decodeProgramUsing?, nextDecoded]
            at remainingDecoded
      | some nextInstruction =>
          cases trailingDecoded :
              DerivationCheckMachineBinary.decodeProgramUsing?
                host.codecs.decoders trailingRecords with
          | none =>
              simp [DerivationCheckMachineBinary.decodeProgramUsing?,
                nextDecoded, trailingDecoded] at remainingDecoded
          | some trailingInstructions =>
              simp [DerivationCheckMachineBinary.decodeProgramUsing?,
                nextDecoded, trailingDecoded] at remainingDecoded
              subst remainingInstructions
              rcases finish_trailing_semantic_square_encoded_root host
                  rootState rootPatternValue record nextRecord trailingRecords
                  nextInstruction trailingInstructions oldNodes nextId
                  serviceState serviceStatePattern nodesPatternValue
                  recordInstructionDecoded
                  (by simp [DerivationCheckMachineBinary.decodeProgramUsing?,
                    nextDecoded, trailingDecoded])
                  rootEncoded serviceStateEncoded nodesEncoded with
                ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
              exact ⟨sourceEncodes, _, _, semanticStep, authoredStep,
                targetEncodes⟩
  | nil =>
      simp [DerivationCheckMachineBinary.decodeProgramUsing?]
        at remainingDecoded
      subst remainingInstructions
      cases rootState with
      | none =>
          simp [rootPattern?] at rootEncoded
          subst rootPatternValue
          rcases finish_missing_root_semantic_square host record oldNodes
              nextId serviceState serviceStatePattern nodesPatternValue
              recordInstructionDecoded serviceStateEncoded nodesEncoded with
            ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
          exact ⟨sourceEncodes, _, _, semanticStep, authoredStep,
            targetEncodes⟩
      | some root =>
          rcases root with ⟨rootId, rootFormula, rootObligation⟩
          unfold rootPattern? at rootEncoded
          cases formulaEncoded : encodeFormula? host rootFormula with
          | none => simp [formulaEncoded] at rootEncoded
          | some formulaPattern =>
              cases obligationEncoded :
                  encodeObligation? host rootObligation with
              | none =>
                  simp [formulaEncoded, obligationEncoded] at rootEncoded
              | some obligationPattern =>
                  simp [formulaEncoded, obligationEncoded] at rootEncoded
                  subst rootPatternValue
                  let root : RootClaim Formula Obligation := {
                    id := rootId
                    formula := rootFormula
                    obligation := rootObligation
                  }
                  cases irrelevant : firstIrrelevant? rootId oldNodes with
                  | some irrelevantId =>
                      rcases finish_irrelevant_semantic_square host root
                          formulaPattern obligationPattern record oldNodes
                          irrelevantId nextId serviceState serviceStatePattern
                          nodesPatternValue irrelevant recordInstructionDecoded
                          formulaEncoded obligationEncoded serviceStateEncoded
                          nodesEncoded with
                        ⟨sourceEncodes, semanticStep, authoredStep,
                          targetEncodes⟩
                      exact ⟨sourceEncodes, _, _, semanticStep, authoredStep,
                        targetEncodes⟩
                  | none =>
                      cases accepted : host.services.root serviceState
                          rootFormula rootObligation with
                      | false =>
                          rcases finish_root_rejected_semantic_square host root
                              formulaPattern obligationPattern record oldNodes
                              nextId serviceState serviceStatePattern
                              nodesPatternValue irrelevant accepted
                              recordInstructionDecoded formulaEncoded
                              obligationEncoded serviceStateEncoded nodesEncoded
                              with
                            ⟨sourceEncodes, semanticStep, authoredStep,
                              targetEncodes⟩
                          exact ⟨sourceEncodes, _, _, semanticStep,
                            authoredStep, targetEncodes⟩
                      | true =>
                          rcases finish_verified_semantic_square host root
                              formulaPattern obligationPattern record oldNodes
                              nextId serviceState serviceStatePattern
                              nodesPatternValue irrelevant accepted
                              recordInstructionDecoded formulaEncoded
                              obligationEncoded serviceStateEncoded nodesEncoded
                              with
                            ⟨sourceEncodes, semanticStep, authoredStep,
                              targetEncodes⟩
                          exact ⟨sourceEncodes, _, _, semanticStep,
                            authoredStep, targetEncodes⟩

#print axioms finish_one_record_semantic_square_encoded_root

end Mettapedia.GSLT.LanguageDef.DerivationWordMachineFinishSimulation
