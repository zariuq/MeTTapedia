import Mettapedia.GSLT.LanguageDef.DerivationWordMachineInferSimulation

/-!
# Exact control-instruction simulation for the derivation-word machine

This module proves the authored one-record operational squares for instructions
whose meaning is structural rather than supplied by a calculus service.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationWordMachineControlSimulation

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
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineInferSimulation

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}
variable [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation]
  [DecidableEq ServiceState]

def nonDropInputSourceRules : List RewriteRule := [
  DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
  DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
  DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
  DerivationCheckMachineLanguageDef.inputAcceptTransition
]

def nonDropInferSourceRules : List RewriteRule := [
  DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
  DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
  DerivationCheckMachineLanguageDef.inferParentFaultTransition,
  DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
  DerivationCheckMachineLanguageDef.inferAcceptTransition
]

def genericNonDropSourceRules : List RewriteRule :=
  nonDropInputSourceRules ++ nonDropInferSourceRules

theorem input_lifted_rule_empty_on_drop_record
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState id : Pattern)
    (membership : sourceRule ∈ nonDropInputSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])) :
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
      (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])
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

#print axioms input_lifted_rule_empty_on_drop_record

theorem infer_lifted_rule_empty_on_drop_record
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState id : Pattern)
    (membership : sourceRule ∈ nonDropInferSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])) :
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
      (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])
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

#print axioms infer_lifted_rule_empty_on_drop_record

/-- Every input or infer row is excluded by the first decoder premise when the
current record decodes as drop. -/
theorem generic_non_drop_lifted_rule_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState id : Pattern)
    (membership : sourceRule ∈ genericNonDropSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  rcases List.mem_append.mp membership with inputMembership | inferMembership
  · exact input_lifted_rule_empty_on_drop_record host sourceRule record rest
      nodes nextId root serviceState id inputMembership recordDecoded
  · exact infer_lifted_rule_empty_on_drop_record host sourceRule record rest
      nodes nextId root serviceState id inferMembership recordDecoded

#print axioms generic_non_drop_lifted_rule_empty

theorem input_lifted_rule_empty_on_root_record
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState id obligation : Pattern)
    (membership : sourceRule ∈ nonDropInputSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [id, obligation])) :
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
      (DerivationCheckMachineLanguageDef.a "dcm:root" [id, obligation])
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

#print axioms input_lifted_rule_empty_on_root_record

theorem infer_lifted_rule_empty_on_root_record
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState id obligation : Pattern)
    (membership : sourceRule ∈ nonDropInferSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [id, obligation])) :
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
      (DerivationCheckMachineLanguageDef.a "dcm:root" [id, obligation])
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

#print axioms infer_lifted_rule_empty_on_root_record

theorem drop_lifted_rule_empty_on_root_record
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState id obligation : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.dropFaultTransition,
      DerivationCheckMachineLanguageDef.dropAcceptTransition])
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [id, obligation])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  all_goals
    apply generic_lifted_record_rule_empty_of_decode_mismatch host _ record
      rest nodes nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:drop" [v "id"])
      (DerivationCheckMachineLanguageDef.a "dcm:root" [id, obligation])
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

#print axioms drop_lifted_rule_empty_on_root_record

theorem root_rules_on_drop_record_root_none_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId serviceState id : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.rootFaultTransition,
      DerivationCheckMachineLanguageDef.rootAcceptTransition])
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  all_goals
    simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.rootFaultTransition,
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

#print axioms root_rules_on_drop_record_root_none_empty

theorem finish_shape_rules_on_nonfinish_record_root_none_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState actualInstruction : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishTrailingTransition,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) = decoded actualInstruction)
    (notFinish :
      matchPattern (DerivationCheckMachineLanguageDef.a "dcm:finish")
        actualInstruction = []) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId DerivationCheckMachineLanguageDef.rootNone serviceState) =
      [] := by
  change matchPattern (.apply "dcm:finish" []) actualInstruction = [] at notFinish
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  · cases remainingRecords with
    | nil =>
        simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern,
          DerivationCheckMachineLanguageDef.finishTrailingTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          run, recordsCons, recordsPattern,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, matchPattern, matchArgs,
          mergeBindings]
    | cons nextRecord trailingRecords =>
        simp [applyRuleUsing, premisesUsing, premiseStepUsing,
          engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern,
          DerivationCheckMachineLanguageDef.finishTrailingTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          query, v, run, recordsCons, recordsPattern, decoded,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, relationEnv, relationTuples,
          recordDecoded, premiseStepWithEnv, relationQueryStep,
          builtinRelationTuples, matchRelationArgs, matchRelationArgument,
          matchPattern, matchArgs, mergeBindings, applyBindings,
          Bindings.lookup, notFinish]
  · cases remainingRecords with
    | nil =>
        simp [applyRuleUsing, premisesUsing, premiseStepUsing,
          engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern,
          DerivationCheckMachineLanguageDef.finishMissingRootTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.instructionsNil,
          DerivationCheckMachineLanguageDef.rootNone,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          query, v, run, recordsCons, recordsNil, recordsPattern, decoded,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, relationEnv, relationTuples,
          recordDecoded, premiseStepWithEnv, relationQueryStep,
          builtinRelationTuples, matchRelationArgs, matchRelationArgument,
          matchPattern, matchArgs, mergeBindings, applyBindings,
          Bindings.lookup, notFinish]
    | cons nextRecord trailingRecords =>
        simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern,
          DerivationCheckMachineLanguageDef.finishMissingRootTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.instructionsNil,
          DerivationCheckMachineLanguageDef.rootNone,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          run, recordsCons, recordsNil, recordsPattern,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, matchPattern, matchArgs,
          mergeBindings]

#print axioms finish_shape_rules_on_nonfinish_record_root_none_empty

theorem finish_shape_rules_on_drop_record_root_none_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState id : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishTrailingTransition,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId DerivationCheckMachineLanguageDef.rootNone serviceState) =
      [] :=
  finish_shape_rules_on_nonfinish_record_root_none_empty host sourceRule record
    remainingRecords nodes nextId serviceState
    (DerivationCheckMachineLanguageDef.a "dcm:drop" [id]) membership
    recordDecoded (by simp [DerivationCheckMachineLanguageDef.a,
      matchPattern])

#print axioms finish_shape_rules_on_drop_record_root_none_empty

theorem finish_shape_rules_on_root_record_root_none_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState id obligation : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishTrailingTransition,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [id, obligation])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId DerivationCheckMachineLanguageDef.rootNone serviceState) =
      [] :=
  finish_shape_rules_on_nonfinish_record_root_none_empty host sourceRule record
    remainingRecords nodes nextId serviceState
    (DerivationCheckMachineLanguageDef.a "dcm:root" [id, obligation])
    membership recordDecoded (by simp [DerivationCheckMachineLanguageDef.a,
      matchPattern])

#print axioms finish_shape_rules_on_root_record_root_none_empty

theorem duplicate_root_on_drop_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId serviceState priorId priorFormula
      priorObligation id : Pattern)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.duplicateRootTransition)
      (run (recordsCons record rest) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern,
    DerivationCheckMachineLanguageDef.duplicateRootTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    query, v, run, recordsCons, decoded, DerivationWordMachineLanguageDef.a,
    relationEnv, relationTuples, recordDecoded, premiseStepWithEnv,
    relationQueryStep, builtinRelationTuples, matchRelationArgs,
    matchRelationArgument, matchPattern, matchArgs, mergeBindings,
    applyBindings, Bindings.lookup]

#print axioms duplicate_root_on_drop_record_root_some_empty

theorem finish_shape_rules_on_nonfinish_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation
      actualInstruction : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishTrailingTransition,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) = decoded actualInstruction)
    (notFinish :
      matchPattern (DerivationCheckMachineLanguageDef.a "dcm:finish")
        actualInstruction = []) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) = [] := by
  change matchPattern (.apply "dcm:finish" []) actualInstruction = [] at notFinish
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  · cases remainingRecords with
    | nil =>
        simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern,
          DerivationCheckMachineLanguageDef.finishTrailingTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.rootSome,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          run, recordsCons, recordsPattern,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, matchPattern, matchArgs,
          mergeBindings]
    | cons nextRecord trailingRecords =>
        simp [applyRuleUsing, premisesUsing, premiseStepUsing,
          engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern,
          DerivationCheckMachineLanguageDef.finishTrailingTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.rootSome,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          query, v, run, recordsCons, recordsPattern, decoded,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, relationEnv, relationTuples,
          recordDecoded, premiseStepWithEnv, relationQueryStep,
          builtinRelationTuples, matchRelationArgs, matchRelationArgument,
          matchPattern, matchArgs, mergeBindings, applyBindings,
          Bindings.lookup, notFinish]
  · cases remainingRecords with
    | nil =>
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
          run, recordsCons, recordsNil, recordsPattern,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, matchPattern, matchArgs,
          mergeBindings]
    | cons nextRecord trailingRecords =>
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
          run, recordsCons, recordsNil, recordsPattern,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, matchPattern, matchArgs,
          mergeBindings]

#print axioms finish_shape_rules_on_nonfinish_record_root_some_empty

theorem finish_shape_rules_on_drop_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation id :
      Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishTrailingTransition,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) = [] :=
  finish_shape_rules_on_nonfinish_record_root_some_empty host sourceRule record
    remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])
    membership recordDecoded (by simp [DerivationCheckMachineLanguageDef.a,
      matchPattern])

#print axioms finish_shape_rules_on_drop_record_root_some_empty

theorem finish_shape_rules_on_root_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation id
      obligation : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishTrailingTransition,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [id, obligation])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) = [] :=
  finish_shape_rules_on_nonfinish_record_root_some_empty host sourceRule record
    remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation
    (DerivationCheckMachineLanguageDef.a "dcm:root" [id, obligation])
    membership recordDecoded (by simp [DerivationCheckMachineLanguageDef.a,
      matchPattern])

#print axioms finish_shape_rules_on_root_record_root_some_empty

theorem finish_root_some_rules_on_nonfinish_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation
      actualInstruction : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) = decoded actualInstruction)
    (notFinish :
      matchPattern (DerivationCheckMachineLanguageDef.a "dcm:finish")
        actualInstruction = []) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) = [] := by
  change matchPattern (.apply "dcm:finish" []) actualInstruction = [] at notFinish
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  all_goals
    cases remainingRecords with
    | nil =>
        simp [applyRuleUsing, premisesUsing, premiseStepUsing,
          engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern, liftPremise,
          DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
          DerivationCheckMachineLanguageDef.finishRootFaultTransition,
          DerivationCheckMachineLanguageDef.finishVerifiedTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.instructionsNil,
          DerivationCheckMachineLanguageDef.rootSome,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          DerivationCheckMachineLanguageDef.query,
          query, v, run, recordsCons, recordsNil, recordsPattern, decoded,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, relationEnv, relationTuples,
          recordDecoded, premiseStepWithEnv, relationQueryStep,
          builtinRelationTuples, matchRelationArgs, matchRelationArgument,
          matchPattern, matchArgs, mergeBindings, applyBindings,
          Bindings.lookup, notFinish]
    | cons nextRecord trailingRecords =>
        apply applyRuleUsing_empty_of_no_left_match
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
        simp [liftRewrite, sourceInstruction?, liftLeft, liftPattern,
          DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
          DerivationCheckMachineLanguageDef.finishRootFaultTransition,
          DerivationCheckMachineLanguageDef.finishVerifiedTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.instructionsNil,
          DerivationCheckMachineLanguageDef.rootSome,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          run, recordsCons, recordsNil, recordsPattern,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, v, matchPattern, matchArgs,
          mergeBindings]

#print axioms finish_root_some_rules_on_nonfinish_record_root_some_empty

theorem finish_root_some_rules_on_drop_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation id :
      Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) = [] :=
  finish_root_some_rules_on_nonfinish_record_root_some_empty host sourceRule
    record remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])
    membership recordDecoded (by simp [DerivationCheckMachineLanguageDef.a,
      matchPattern])

#print axioms finish_root_some_rules_on_drop_record_root_some_empty

theorem finish_root_some_rules_on_root_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation id
      obligation : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [id, obligation])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) = [] :=
  finish_root_some_rules_on_nonfinish_record_root_some_empty host sourceRule
    record remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation
    (DerivationCheckMachineLanguageDef.a "dcm:root" [id, obligation])
    membership recordDecoded (by simp [DerivationCheckMachineLanguageDef.a,
      matchPattern])

#print axioms finish_root_some_rules_on_root_record_root_some_empty

theorem duplicate_root_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId serviceState priorId priorFormula
      priorObligation idPattern obligationPattern : Pattern)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [idPattern, obligationPattern])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.duplicateRootTransition)
      (run (recordsCons record rest) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault
          (faultPattern .duplicateRoot))
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern,
    DerivationCheckMachineLanguageDef.duplicateRootTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    query, v, run, halted, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup,
    faultPattern, DerivationWordMachineRelationEnv.a]

#print axioms duplicate_root_applyRule_exact

theorem root_fault_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId serviceState idPattern obligationPattern
      faultPatternValue : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [idPattern, obligationPattern]))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (rootFaulted :
      rootShapeDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.rootFaultTransition)
      (run (recordsCons record rest) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.rootFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.rootNone,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, halted, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, rootFaulted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms root_fault_applyRule_exact

theorem root_accept_applyRule_empty_of_fault
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId serviceState idPattern obligationPattern
      faultPatternValue : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [idPattern, obligationPattern]))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (rootFaulted :
      rootShapeDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.rootAcceptTransition)
      (run (recordsCons record rest) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.rootAcceptTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.rootNone,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, rootFaulted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms root_accept_applyRule_empty_of_fault

theorem root_accept_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId serviceState idPattern obligationPattern
      formulaPattern : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [idPattern, obligationPattern]))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (rootAccepted :
      rootShapeDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-root"
          [formulaPattern]) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.rootAcceptTransition)
      (run (recordsCons record rest) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) =
      [run rest nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome idPattern formulaPattern
          obligationPattern)
        serviceState] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.rootAcceptTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.rootNone,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, rootAccepted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms root_accept_applyRule_exact

theorem root_fault_applyRule_empty_of_accept
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId serviceState idPattern obligationPattern
      formulaPattern : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [idPattern, obligationPattern]))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (rootAccepted :
      rootShapeDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-root"
          [formulaPattern]) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.rootFaultTransition)
      (run (recordsCons record rest) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.rootFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.rootNone,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, rootAccepted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms root_fault_applyRule_empty_of_accept

theorem root_record_rewriteAt_partition_root_none
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState id obligation : Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [id, obligation])) :
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodes nextId DerivationCheckMachineLanguageDef.rootNone serviceState
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite DerivationCheckMachineLanguageDef.rootFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite DerivationCheckMachineLanguageDef.rootAcceptTransition)
          source := by
  dsimp only
  change language.rewrites.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) rule
        (run (recordsCons (wordsPattern record)
          (recordsPattern remainingRecords)) nodes nextId
          DerivationCheckMachineLanguageDef.rootNone serviceState)) = _
  rw [show language.rewrites = transitions by rfl]
  simp only [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil]
  rw [malformed_record_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (DerivationCheckMachineLanguageDef.a "dcm:root" [id, obligation])
    recordDecoded]
  rw [missing_finish_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState]
  rw [input_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id obligation
    (by simp [nonDropInputSourceRules]) recordDecoded]
  rw [input_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id obligation
    (by simp [nonDropInputSourceRules]) recordDecoded]
  rw [input_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id obligation
    (by simp [nonDropInputSourceRules]) recordDecoded]
  rw [input_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inputAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id obligation
    (by simp [nonDropInputSourceRules]) recordDecoded]
  rw [infer_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id obligation
    (by simp [nonDropInferSourceRules]) recordDecoded]
  rw [infer_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id obligation
    (by simp [nonDropInferSourceRules]) recordDecoded]
  rw [infer_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inferParentFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id obligation
    (by simp [nonDropInferSourceRules]) recordDecoded]
  rw [infer_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id obligation
    (by simp [nonDropInferSourceRules]) recordDecoded]
  rw [infer_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id obligation
    (by simp [nonDropInferSourceRules]) recordDecoded]
  rw [drop_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.dropFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id obligation
    (by simp) recordDecoded]
  rw [drop_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.dropAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id obligation
    (by simp) recordDecoded]
  rw [duplicate_root_on_root_none_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId serviceState]
  rw [finish_shape_rules_on_root_record_root_none_empty host
    DerivationCheckMachineLanguageDef.finishTrailingTransition record
    remainingRecords nodes nextId serviceState id obligation (by simp)
    recordDecoded]
  rw [finish_shape_rules_on_root_record_root_none_empty host
    DerivationCheckMachineLanguageDef.finishMissingRootTransition record
    remainingRecords nodes nextId serviceState id obligation (by simp)
    recordDecoded]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    serviceState (by simp)]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishRootFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    serviceState (by simp)]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishVerifiedTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    serviceState (by simp)]
  simp

#print axioms root_record_rewriteAt_partition_root_none

theorem root_record_rewriteAt_partition_root_some
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation id
      obligation : Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [id, obligation])) :
    let priorRoot := DerivationCheckMachineLanguageDef.rootSome priorId
      priorFormula priorObligation
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodes nextId priorRoot serviceState
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => [])
        (liftRewrite DerivationCheckMachineLanguageDef.duplicateRootTransition)
        source := by
  dsimp only
  change language.rewrites.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) rule
        (run (recordsCons (wordsPattern record)
          (recordsPattern remainingRecords)) nodes nextId
          (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
            priorObligation)
          serviceState)) = _
  rw [show language.rewrites = transitions by rfl]
  simp only [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil]
  rw [malformed_record_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState
    (DerivationCheckMachineLanguageDef.a "dcm:root" [id, obligation])
    recordDecoded]
  rw [missing_finish_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState]
  rw [input_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id obligation (by simp [nonDropInputSourceRules])
    recordDecoded]
  rw [input_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id obligation (by simp [nonDropInputSourceRules])
    recordDecoded]
  rw [input_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id obligation (by simp [nonDropInputSourceRules])
    recordDecoded]
  rw [input_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inputAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id obligation (by simp [nonDropInputSourceRules])
    recordDecoded]
  rw [infer_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id obligation (by simp [nonDropInferSourceRules])
    recordDecoded]
  rw [infer_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id obligation (by simp [nonDropInferSourceRules])
    recordDecoded]
  rw [infer_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inferParentFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id obligation (by simp [nonDropInferSourceRules])
    recordDecoded]
  rw [infer_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id obligation (by simp [nonDropInferSourceRules])
    recordDecoded]
  rw [infer_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id obligation (by simp [nonDropInferSourceRules])
    recordDecoded]
  rw [drop_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.dropFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id obligation (by simp) recordDecoded]
  rw [drop_lifted_rule_empty_on_root_record host
    DerivationCheckMachineLanguageDef.dropAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id obligation (by simp) recordDecoded]
  rw [root_rules_on_root_some_empty host
    DerivationCheckMachineLanguageDef.rootFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    serviceState priorId priorFormula priorObligation (by simp)]
  rw [root_rules_on_root_some_empty host
    DerivationCheckMachineLanguageDef.rootAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    serviceState priorId priorFormula priorObligation (by simp)]
  rw [finish_shape_rules_on_root_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishTrailingTransition record
    remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation id obligation (by simp) recordDecoded]
  rw [finish_shape_rules_on_root_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishMissingRootTransition record
    remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation id obligation (by simp) recordDecoded]
  rw [finish_root_some_rules_on_root_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition record
    remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation id obligation (by simp) recordDecoded]
  rw [finish_root_some_rules_on_root_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishRootFaultTransition record
    remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation id obligation (by simp) recordDecoded]
  rw [finish_root_some_rules_on_root_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishVerifiedTransition record
    remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation id obligation (by simp) recordDecoded]
  simp

#print axioms root_record_rewriteAt_partition_root_some

theorem duplicate_root_rewriteAt_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation idPattern
      obligationPattern : Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [idPattern, obligationPattern])) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault
          (faultPattern .duplicateRoot))
        nodes] := by
  rw [root_record_rewriteAt_partition_root_some host record remainingRecords
    nodes nextId serviceState priorId priorFormula priorObligation idPattern
    obligationPattern recordDecoded]
  rw [duplicate_root_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId serviceState priorId
    priorFormula priorObligation idPattern obligationPattern recordDecoded]

#print axioms duplicate_root_rewriteAt_exact

theorem root_fault_rewriteAt_exact_root_none
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState idPattern obligationPattern faultPatternValue :
      Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [idPattern, obligationPattern]))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (rootFaulted :
      rootShapeDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  rw [root_record_rewriteAt_partition_root_none host record remainingRecords
    nodes nextId serviceState idPattern obligationPattern recordDecoded]
  rw [root_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId serviceState idPattern
    obligationPattern faultPatternValue oldNodes id recordDecoded nodesDecoded
    idDecoded rootFaulted]
  rw [root_accept_applyRule_empty_of_fault host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId serviceState idPattern
    obligationPattern faultPatternValue oldNodes id recordDecoded nodesDecoded
    idDecoded rootFaulted]
  simp

#print axioms root_fault_rewriteAt_exact_root_none

theorem root_accept_rewriteAt_exact_root_none
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState idPattern obligationPattern formulaPattern :
      Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [idPattern, obligationPattern]))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (rootAccepted :
      rootShapeDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-root"
          [formulaPattern]) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) =
      [run (recordsPattern remainingRecords) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome idPattern formulaPattern
          obligationPattern)
        serviceState] := by
  rw [root_record_rewriteAt_partition_root_none host record remainingRecords
    nodes nextId serviceState idPattern obligationPattern recordDecoded]
  rw [root_fault_applyRule_empty_of_accept host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId serviceState idPattern
    obligationPattern formulaPattern oldNodes id recordDecoded nodesDecoded
    idDecoded rootAccepted]
  rw [root_accept_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId serviceState idPattern
    obligationPattern formulaPattern oldNodes id recordDecoded nodesDecoded
    idDecoded rootAccepted]
  simp

#print axioms root_accept_rewriteAt_exact_root_none

theorem drop_fault_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId root serviceState idPattern faultPatternValue :
      Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [idPattern]))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (dropFaulted :
      dropDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.dropFaultTransition)
      (run (recordsCons record rest) nodes nextId root serviceState) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.dropFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, halted, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, dropFaulted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms drop_fault_applyRule_exact

theorem drop_accept_applyRule_empty_of_fault
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId root serviceState idPattern faultPatternValue :
      Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [idPattern]))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (dropFaulted :
      dropDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.dropAcceptTransition)
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.dropAcceptTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, dropFaulted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms drop_accept_applyRule_empty_of_fault

theorem drop_accept_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId root serviceState idPattern nextNodesPattern :
      Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [idPattern]))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (dropAccepted :
      dropDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-nodes"
          [nextNodesPattern]) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.dropAcceptTransition)
      (run (recordsCons record rest) nodes nextId root serviceState) =
      [run rest nextNodesPattern nextId root serviceState] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.dropAcceptTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, dropAccepted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms drop_accept_applyRule_exact

theorem drop_fault_applyRule_empty_of_accept
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId root serviceState idPattern nextNodesPattern :
      Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [idPattern]))
    (nodesDecoded : decodeNodes? host nodes = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (dropAccepted :
      dropDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-nodes"
          [nextNodesPattern]) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.dropFaultTransition)
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.dropFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, idDecoded, dropAccepted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms drop_fault_applyRule_empty_of_accept

/-- A decoded drop record restricts the full authored table to exactly the two
drop rows when no root has yet been selected. -/
theorem drop_record_rewriteAt_partition_root_none
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState id : Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])) :
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodes nextId DerivationCheckMachineLanguageDef.rootNone serviceState
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite DerivationCheckMachineLanguageDef.dropFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite DerivationCheckMachineLanguageDef.dropAcceptTransition)
          source := by
  dsimp only
  change language.rewrites.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) rule
        (run (recordsCons (wordsPattern record)
          (recordsPattern remainingRecords)) nodes nextId
          DerivationCheckMachineLanguageDef.rootNone serviceState)) = _
  rw [show language.rewrites = transitions by rfl]
  simp only [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil]
  rw [malformed_record_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState
    (DerivationCheckMachineLanguageDef.a "dcm:drop" [id]) recordDecoded]
  rw [missing_finish_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id
    (by simp [genericNonDropSourceRules, nonDropInputSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id
    (by simp [genericNonDropSourceRules, nonDropInputSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id
    (by simp [genericNonDropSourceRules, nonDropInputSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inputAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id
    (by simp [genericNonDropSourceRules, nonDropInputSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id
    (by simp [genericNonDropSourceRules, nonDropInferSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id
    (by simp [genericNonDropSourceRules, nonDropInferSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferParentFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id
    (by simp [genericNonDropSourceRules, nonDropInferSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id
    (by simp [genericNonDropSourceRules, nonDropInferSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    DerivationCheckMachineLanguageDef.rootNone serviceState id
    (by simp [genericNonDropSourceRules, nonDropInferSourceRules])
    recordDecoded]
  rw [duplicate_root_on_root_none_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId serviceState]
  rw [root_rules_on_drop_record_root_none_empty host
    DerivationCheckMachineLanguageDef.rootFaultTransition (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId serviceState id (by simp)
    recordDecoded]
  rw [root_rules_on_drop_record_root_none_empty host
    DerivationCheckMachineLanguageDef.rootAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    serviceState id (by simp) recordDecoded]
  rw [finish_shape_rules_on_drop_record_root_none_empty host
    DerivationCheckMachineLanguageDef.finishTrailingTransition record
    remainingRecords nodes nextId serviceState id (by simp) recordDecoded]
  rw [finish_shape_rules_on_drop_record_root_none_empty host
    DerivationCheckMachineLanguageDef.finishMissingRootTransition record
    remainingRecords nodes nextId serviceState id (by simp) recordDecoded]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    serviceState (by simp)]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishRootFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    serviceState (by simp)]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishVerifiedTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    serviceState (by simp)]
  simp

#print axioms drop_record_rewriteAt_partition_root_none

theorem drop_record_rewriteAt_partition_root_some
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation id :
      Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])) :
    let root := DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodes nextId root serviceState
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite DerivationCheckMachineLanguageDef.dropFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite DerivationCheckMachineLanguageDef.dropAcceptTransition)
          source := by
  dsimp only
  change language.rewrites.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) rule
        (run (recordsCons (wordsPattern record)
          (recordsPattern remainingRecords)) nodes nextId
          (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
            priorObligation)
          serviceState)) = _
  rw [show language.rewrites = transitions by rfl]
  simp only [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil]
  rw [malformed_record_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState (DerivationCheckMachineLanguageDef.a "dcm:drop" [id])
    recordDecoded]
  rw [missing_finish_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id
    (by simp [genericNonDropSourceRules, nonDropInputSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id
    (by simp [genericNonDropSourceRules, nonDropInputSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id
    (by simp [genericNonDropSourceRules, nonDropInputSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inputAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id
    (by simp [genericNonDropSourceRules, nonDropInputSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id
    (by simp [genericNonDropSourceRules, nonDropInferSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id
    (by simp [genericNonDropSourceRules, nonDropInferSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferParentFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id
    (by simp [genericNonDropSourceRules, nonDropInferSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id
    (by simp [genericNonDropSourceRules, nonDropInferSourceRules])
    recordDecoded]
  rw [generic_non_drop_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
      priorObligation)
    serviceState id
    (by simp [genericNonDropSourceRules, nonDropInferSourceRules])
    recordDecoded]
  rw [duplicate_root_on_drop_record_root_some_empty host
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    serviceState priorId priorFormula priorObligation id recordDecoded]
  rw [root_rules_on_root_some_empty host
    DerivationCheckMachineLanguageDef.rootFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    serviceState priorId priorFormula priorObligation (by simp)]
  rw [root_rules_on_root_some_empty host
    DerivationCheckMachineLanguageDef.rootAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextId
    serviceState priorId priorFormula priorObligation (by simp)]
  rw [finish_shape_rules_on_drop_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishTrailingTransition record
    remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation id (by simp) recordDecoded]
  rw [finish_shape_rules_on_drop_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishMissingRootTransition record
    remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation id (by simp) recordDecoded]
  rw [finish_root_some_rules_on_drop_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition record
    remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation id (by simp) recordDecoded]
  rw [finish_root_some_rules_on_drop_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishRootFaultTransition record
    remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation id (by simp) recordDecoded]
  rw [finish_root_some_rules_on_drop_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishVerifiedTransition record
    remainingRecords nodes nextId serviceState priorId priorFormula
    priorObligation id (by simp) recordDecoded]
  simp

#print axioms drop_record_rewriteAt_partition_root_some

/-- A rejected drop is the unique authored successor of a decoded drop record,
independently of the encoded root state. -/
theorem drop_fault_rewriteAt_exact_root_none
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodesPatternValue nextIdPattern serviceStatePattern idPattern
      faultPatternValue : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [idPattern]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (dropFaulted :
      dropDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodesPatternValue nextIdPattern
        DerivationCheckMachineLanguageDef.rootNone serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodesPatternValue] := by
  rw [drop_record_rewriteAt_partition_root_none host record remainingRecords
    nodesPatternValue nextIdPattern serviceStatePattern idPattern
    recordDecoded]
  rw [drop_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    faultPatternValue oldNodes id recordDecoded nodesDecoded idDecoded
    dropFaulted]
  rw [drop_accept_applyRule_empty_of_fault host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    faultPatternValue oldNodes id recordDecoded nodesDecoded idDecoded
    dropFaulted]
  simp

#print axioms drop_fault_rewriteAt_exact_root_none

theorem drop_fault_rewriteAt_exact_root_some
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodesPatternValue nextIdPattern serviceStatePattern priorIdPattern
      priorFormulaPattern priorObligationPattern idPattern faultPatternValue :
      Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [idPattern]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (dropFaulted :
      dropDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodesPatternValue nextIdPattern
        (DerivationCheckMachineLanguageDef.rootSome priorIdPattern
          priorFormulaPattern priorObligationPattern)
        serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodesPatternValue] := by
  rw [drop_record_rewriteAt_partition_root_some host record remainingRecords
    nodesPatternValue nextIdPattern serviceStatePattern priorIdPattern
    priorFormulaPattern priorObligationPattern idPattern recordDecoded]
  rw [drop_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    (DerivationCheckMachineLanguageDef.rootSome priorIdPattern
      priorFormulaPattern priorObligationPattern)
    serviceStatePattern idPattern faultPatternValue oldNodes id recordDecoded
    nodesDecoded idDecoded dropFaulted]
  rw [drop_accept_applyRule_empty_of_fault host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    (DerivationCheckMachineLanguageDef.rootSome priorIdPattern
      priorFormulaPattern priorObligationPattern)
    serviceStatePattern idPattern faultPatternValue oldNodes id recordDecoded
    nodesDecoded idDecoded dropFaulted]
  simp

#print axioms drop_fault_rewriteAt_exact_root_some

/-- A rejected drop is the unique authored successor for every canonically
encoded semantic root state. -/
theorem drop_fault_rewriteAt_exact_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodesPatternValue nextIdPattern serviceStatePattern idPattern
      faultPatternValue : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [idPattern]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (dropFaulted :
      dropDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodesPatternValue nextIdPattern
        rootPatternValue serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodesPatternValue] := by
  cases rootState with
  | none =>
      simp [rootPattern?] at rootEncoded
      subst rootPatternValue
      exact drop_fault_rewriteAt_exact_root_none host record remainingRecords
        nodesPatternValue nextIdPattern serviceStatePattern idPattern
        faultPatternValue oldNodes id recordDecoded nodesDecoded idDecoded
        dropFaulted
  | some root =>
      rcases root with ⟨rootId, rootFormula, rootObligation⟩
      cases formulaEncoded : encodeFormula? host rootFormula with
      | none =>
          simp [rootPattern?, formulaEncoded] at rootEncoded
      | some rootFormulaPattern =>
          cases obligationEncoded : encodeObligation? host rootObligation with
          | none =>
              simp [rootPattern?, formulaEncoded, obligationEncoded] at rootEncoded
          | some rootObligationPattern =>
              simp [rootPattern?, formulaEncoded, obligationEncoded] at rootEncoded
              subst rootPatternValue
              exact drop_fault_rewriteAt_exact_root_some host record
                remainingRecords nodesPatternValue nextIdPattern
                serviceStatePattern (indexPattern rootId) rootFormulaPattern
                rootObligationPattern idPattern faultPatternValue oldNodes id
                recordDecoded nodesDecoded idDecoded dropFaulted

#print axioms drop_fault_rewriteAt_exact_encoded_root

theorem drop_accept_rewriteAt_exact_root_none
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodesPatternValue nextIdPattern serviceStatePattern idPattern
      nextNodesPattern : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [idPattern]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (dropAccepted :
      dropDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-nodes"
          [nextNodesPattern]) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodesPatternValue nextIdPattern
        DerivationCheckMachineLanguageDef.rootNone serviceStatePattern) =
      [run (recordsPattern remainingRecords) nextNodesPattern nextIdPattern
        DerivationCheckMachineLanguageDef.rootNone serviceStatePattern] := by
  rw [drop_record_rewriteAt_partition_root_none host record remainingRecords
    nodesPatternValue nextIdPattern serviceStatePattern idPattern
    recordDecoded]
  rw [drop_fault_applyRule_empty_of_accept host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    nextNodesPattern oldNodes id recordDecoded nodesDecoded idDecoded
    dropAccepted]
  rw [drop_accept_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    nextNodesPattern oldNodes id recordDecoded nodesDecoded idDecoded
    dropAccepted]
  simp

#print axioms drop_accept_rewriteAt_exact_root_none

theorem drop_accept_rewriteAt_exact_root_some
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodesPatternValue nextIdPattern serviceStatePattern priorIdPattern
      priorFormulaPattern priorObligationPattern idPattern nextNodesPattern :
      Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [idPattern]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (dropAccepted :
      dropDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-nodes"
          [nextNodesPattern]) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodesPatternValue nextIdPattern
        (DerivationCheckMachineLanguageDef.rootSome priorIdPattern
          priorFormulaPattern priorObligationPattern)
        serviceStatePattern) =
      [run (recordsPattern remainingRecords) nextNodesPattern nextIdPattern
        (DerivationCheckMachineLanguageDef.rootSome priorIdPattern
          priorFormulaPattern priorObligationPattern)
        serviceStatePattern] := by
  rw [drop_record_rewriteAt_partition_root_some host record remainingRecords
    nodesPatternValue nextIdPattern serviceStatePattern priorIdPattern
    priorFormulaPattern priorObligationPattern idPattern recordDecoded]
  rw [drop_fault_applyRule_empty_of_accept host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    (DerivationCheckMachineLanguageDef.rootSome priorIdPattern
      priorFormulaPattern priorObligationPattern)
    serviceStatePattern idPattern nextNodesPattern oldNodes id recordDecoded
    nodesDecoded idDecoded dropAccepted]
  rw [drop_accept_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    (DerivationCheckMachineLanguageDef.rootSome priorIdPattern
      priorFormulaPattern priorObligationPattern)
    serviceStatePattern idPattern nextNodesPattern oldNodes id recordDecoded
    nodesDecoded idDecoded dropAccepted]
  simp

#print axioms drop_accept_rewriteAt_exact_root_some

theorem drop_accept_rewriteAt_exact_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodesPatternValue nextIdPattern serviceStatePattern idPattern
      nextNodesPattern : Pattern)
    (oldNodes : List (Node Formula)) (id : Nat)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop" [idPattern]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some oldNodes)
    (idDecoded : decodeIndex? idPattern = some id)
    (dropAccepted :
      dropDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-nodes"
          [nextNodesPattern]) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodesPatternValue nextIdPattern
        rootPatternValue serviceStatePattern) =
      [run (recordsPattern remainingRecords) nextNodesPattern nextIdPattern
        rootPatternValue serviceStatePattern] := by
  cases rootState with
  | none =>
      simp [rootPattern?] at rootEncoded
      subst rootPatternValue
      exact drop_accept_rewriteAt_exact_root_none host record
        remainingRecords nodesPatternValue nextIdPattern serviceStatePattern
        idPattern nextNodesPattern oldNodes id recordDecoded nodesDecoded
        idDecoded dropAccepted
  | some root =>
      rcases root with ⟨rootId, rootFormula, rootObligation⟩
      cases formulaEncoded : encodeFormula? host rootFormula with
      | none =>
          simp [rootPattern?, formulaEncoded] at rootEncoded
      | some rootFormulaPattern =>
          cases obligationEncoded : encodeObligation? host rootObligation with
          | none =>
              simp [rootPattern?, formulaEncoded, obligationEncoded] at rootEncoded
          | some rootObligationPattern =>
              simp [rootPattern?, formulaEncoded, obligationEncoded] at rootEncoded
              subst rootPatternValue
              exact drop_accept_rewriteAt_exact_root_some host record
                remainingRecords nodesPatternValue nextIdPattern
                serviceStatePattern (indexPattern rootId) rootFormulaPattern
                rootObligationPattern idPattern nextNodesPattern oldNodes id
                recordDecoded nodesDecoded idDecoded dropAccepted

#print axioms drop_accept_rewriteAt_exact_encoded_root

/- Dropping a node never creates a new formula-encoding obligation: every
successful result is a sublist of an already representable node arena. -/
omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem nodesPattern_exists_of_dropNode_some
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (id : Nat) (nodes nextNodes : List (Node Formula)) (nodesPatternValue : Pattern)
    (nodesEncoded : nodesPattern? host nodes = some nodesPatternValue)
    (dropped : dropNode? id nodes = some nextNodes) :
    ∃ nextNodesPattern, nodesPattern? host nextNodes = some nextNodesPattern := by
  induction nodes generalizing nextNodes nodesPatternValue with
  | nil =>
      simp [dropNode?] at dropped
  | cons node nodes induction =>
      unfold nodesPattern? at nodesEncoded
      cases nodeEncoded : nodePattern? host node with
      | none => simp [nodeEncoded] at nodesEncoded
      | some nodePatternValue =>
          cases restEncoded : nodesPattern? host nodes with
          | none => simp [nodeEncoded, restEncoded] at nodesEncoded
          | some restPatternValue =>
              simp [nodeEncoded, restEncoded] at nodesEncoded
              by_cases idMatches : node.id = id
              · cases linkedValue : node.linked with
                | false => simp [dropNode?, idMatches, linkedValue] at dropped
                | true =>
                    simp [dropNode?, idMatches, linkedValue] at dropped
                    subst nextNodes
                    exact ⟨restPatternValue, restEncoded⟩
              · cases tailResult : dropNode? id nodes with
                | none =>
                    simp [dropNode?, idMatches, tailResult] at dropped
                | some tailNodes =>
                    simp [dropNode?, idMatches, tailResult] at dropped
                    subst nextNodes
                    obtain ⟨tailPattern, tailEncoded⟩ :=
                      induction tailNodes restPatternValue restEncoded tailResult
                    refine ⟨DerivationCheckMachineLanguageDef.nodesCons
                      nodePatternValue tailPattern, ?_⟩
                    simp [nodesPattern?, nodeEncoded, tailEncoded,
                      DerivationCheckMachineLanguageDef.nodesCons,
                      DerivationCheckMachineLanguageDef.a,
                      DerivationWordMachineRelationEnv.a]

#print axioms nodesPattern_exists_of_dropNode_some

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance] in
theorem drop_source_encodes_running
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (nextId id : Nat)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some (.drop id))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .drop id :: remainingInstructions
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

#print axioms drop_source_encodes_running

theorem drop_fault_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (nextId id : Nat)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (dropMissing : dropNode? id oldNodes = none)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some (.drop id))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .drop id :: remainingInstructions
      nodes := oldNodes
      nextId := nextId
      root? := rootState
      serviceState := serviceState
    }
    let failure := Fault.dropRejected id
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern nextId) rootPatternValue
      serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault (faultPattern failure))
      nodesPatternValue
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault failure)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.halted (.fault failure))
        target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host (.drop id) =
        some (DerivationCheckMachineLanguageDef.a "dcm:drop"
          [indexPattern id]) := by
    simp [instructionPattern?, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop"
          [indexPattern id]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:drop" [indexPattern id]]
    exact decodeDecision_wordsPattern_exact host record (.drop id)
      (DerivationCheckMachineLanguageDef.a "dcm:drop" [indexPattern id])
      recordInstructionDecoded instructionPatternEncoded
  have nodesDecoded :=
    decodeNodes_nodesPattern host oldNodes nodesPatternValue nodesEncoded
  have dropFaulted :
      dropDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.decisionFault
          (faultPattern (.dropRejected id)) := by
    simp [dropDecision, dropMissing, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact drop_source_encodes_running host rootState rootPatternValue record
      remainingRecords remainingInstructions oldNodes nextId id serviceState
      serviceStatePattern nodesPatternValue recordInstructionDecoded
      remainingDecoded rootEncoded serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault, dropMissing]
  constructor
  · exact drop_fault_rewriteAt_exact_encoded_root host rootState
      rootPatternValue record remainingRecords nodesPatternValue
      (indexPattern nextId) serviceStatePattern (indexPattern id)
      (faultPattern (.dropRejected id)) oldNodes id rootEncoded recordDecoded
      nodesDecoded (decodeIndex_indexPattern id) dropFaulted
  · exact fault_target_encodes_halted host remainingRecords oldNodes
      (.dropRejected id) nodesPatternValue nodesEncoded

#print axioms drop_fault_semantic_square_encoded_root

theorem drop_accept_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes nextNodes : List (Node Formula)) (nextId id : Nat)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue nextNodesPattern : Pattern)
    (dropAcceptedNodes : dropNode? id oldNodes = some nextNodes)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some (.drop id))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (nextNodesEncoded : nodesPattern? host nextNodes = some nextNodesPattern)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .drop id :: remainingInstructions
      nodes := oldNodes
      nextId := nextId
      root? := rootState
      serviceState := serviceState
    }
    let after :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := remainingInstructions
      nodes := nextNodes
      nextId := nextId
      root? := rootState
      serviceState := serviceState
    }
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern nextId) rootPatternValue
      serviceStatePattern
    let target := run (recordsPattern remainingRecords) nextNodesPattern
      (indexPattern nextId) rootPatternValue serviceStatePattern
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) = some (.running after) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.running after) target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host (.drop id) =
        some (DerivationCheckMachineLanguageDef.a "dcm:drop"
          [indexPattern id]) := by
    simp [instructionPattern?, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:drop"
          [indexPattern id]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:drop" [indexPattern id]]
    exact decodeDecision_wordsPattern_exact host record (.drop id)
      (DerivationCheckMachineLanguageDef.a "dcm:drop" [indexPattern id])
      recordInstructionDecoded instructionPatternEncoded
  have nodesDecoded :=
    decodeNodes_nodesPattern host oldNodes nodesPatternValue nodesEncoded
  have dropAccepted :
      dropDecision host oldNodes id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-nodes"
          [nextNodesPattern] := by
    simp [dropDecision, dropAcceptedNodes, nextNodesEncoded,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact drop_source_encodes_running host rootState rootPatternValue record
      remainingRecords remainingInstructions oldNodes nextId id serviceState
      serviceStatePattern nodesPatternValue recordInstructionDecoded
      remainingDecoded rootEncoded serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, dropAcceptedNodes]
  constructor
  · exact drop_accept_rewriteAt_exact_encoded_root host rootState
      rootPatternValue record remainingRecords nodesPatternValue
      (indexPattern nextId) serviceStatePattern (indexPattern id)
      nextNodesPattern oldNodes id rootEncoded recordDecoded nodesDecoded
      (decodeIndex_indexPattern id) dropAccepted
  · constructor
    · exact remainingDecoded
    · simp [runningPattern?, nextNodesEncoded, serviceStateEncoded,
        rootEncoded]

#print axioms drop_accept_semantic_square_encoded_root

/-- Every representable drop instruction takes exactly one authored target
step matching the deterministic semantic-machine step.  Successful dropping
inherits representability from the original finite node arena. -/
theorem drop_one_record_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (nextId id : Nat)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some (.drop id))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .drop id :: remainingInstructions
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
      ∃ next target,
        step? host.services (.running before) = some next ∧
          rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
            [target] ∧
          EncodesConfig host remainingRecords next target := by
  dsimp only
  cases dropResult : dropNode? id oldNodes with
  | none =>
      rcases drop_fault_semantic_square_encoded_root host rootState
          rootPatternValue record remainingRecords remainingInstructions
          oldNodes nextId id serviceState serviceStatePattern
          nodesPatternValue dropResult recordInstructionDecoded
          remainingDecoded serviceStateEncoded nodesEncoded rootEncoded with
        ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
      exact ⟨sourceEncodes, _, _, semanticStep, authoredStep, targetEncodes⟩
  | some nextNodes =>
      obtain ⟨nextNodesPattern, nextNodesEncoded⟩ :=
        nodesPattern_exists_of_dropNode_some host id oldNodes nextNodes
          nodesPatternValue nodesEncoded dropResult
      rcases drop_accept_semantic_square_encoded_root host rootState
          rootPatternValue record remainingRecords remainingInstructions
          oldNodes nextNodes nextId id serviceState serviceStatePattern
          nodesPatternValue nextNodesPattern dropResult
          recordInstructionDecoded remainingDecoded serviceStateEncoded
          nodesEncoded nextNodesEncoded rootEncoded with
        ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
      exact ⟨sourceEncodes, _, _, semanticStep, authoredStep, targetEncodes⟩

#print axioms drop_one_record_semantic_square_encoded_root

/- A successful root lookup points into the already encoded node arena, so its
formula is representable without adding a fresh codec-side witness. -/
omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem formulaPattern_exists_of_lookupNode_some
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (id : Nat) (nodes : List (Node Formula)) (node : Node Formula)
    (nodesPatternValue : Pattern)
    (nodesEncoded : nodesPattern? host nodes = some nodesPatternValue)
    (found : lookupNode? id nodes = some node) :
    exists formulaPattern,
      encodeFormula? host node.formula = some formulaPattern := by
  induction nodes generalizing nodesPatternValue with
  | nil =>
      simp [lookupNode?] at found
  | cons head tail induction =>
      unfold nodesPattern? at nodesEncoded
      cases headEncoded : nodePattern? host head with
      | none => simp [headEncoded] at nodesEncoded
      | some headPattern =>
          cases tailEncoded : nodesPattern? host tail with
          | none => simp [headEncoded, tailEncoded] at nodesEncoded
          | some tailPattern =>
              simp [headEncoded, tailEncoded] at nodesEncoded
              by_cases same : head.id = id
              · have headEq : head = node := by
                  simpa [lookupNode?, same] using found
                subst node
                unfold nodePattern? at headEncoded
                cases formulaEncoded : encodeFormula? host head.formula with
                | none => simp [formulaEncoded] at headEncoded
                | some formulaPattern =>
                    exact ⟨formulaPattern, rfl⟩
              · have tailFound : lookupNode? id tail = some node := by
                  simpa [lookupNode?, same] using found
                exact induction tailPattern tailEncoded tailFound

#print axioms formulaPattern_exists_of_lookupNode_some

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance] in
theorem root_source_encodes_running
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (nextId id : Nat)
    (obligation : Obligation)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some (.root id obligation))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .root id obligation :: remainingInstructions
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

#print axioms root_source_encodes_running

theorem duplicate_root_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (priorRoot : RootClaim Formula Obligation)
    (priorFormulaPattern priorObligationPattern : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (nextId id : Nat)
    (obligation : Obligation) (obligationPattern : Pattern)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some (.root id obligation))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (priorFormulaEncoded :
      encodeFormula? host priorRoot.formula = some priorFormulaPattern)
    (priorObligationEncoded :
      encodeObligation? host priorRoot.obligation = some priorObligationPattern)
    (obligationEncoded :
      encodeObligation? host obligation = some obligationPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .root id obligation :: remainingInstructions
      nodes := oldNodes
      nextId := nextId
      root? := some priorRoot
      serviceState := serviceState
    }
    let failure := Fault.duplicateRoot
    let rootPatternValue := DerivationCheckMachineLanguageDef.rootSome
      (indexPattern priorRoot.id) priorFormulaPattern priorObligationPattern
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern nextId) rootPatternValue
      serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault (faultPattern failure))
      nodesPatternValue
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault failure)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.halted (.fault failure))
        target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host (.root id obligation) =
        some (DerivationCheckMachineLanguageDef.a "dcm:root"
          [indexPattern id, obligationPattern]) := by
    simp [instructionPattern?, obligationEncoded,
      DerivationCheckMachineLanguageDef.a, DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [indexPattern id, obligationPattern]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:root"
          [indexPattern id, obligationPattern]]
    exact decodeDecision_wordsPattern_exact host record (.root id obligation)
      (DerivationCheckMachineLanguageDef.a "dcm:root"
        [indexPattern id, obligationPattern])
      recordInstructionDecoded instructionPatternEncoded
  have rootEncoded : rootPattern? host (some priorRoot) =
      some (DerivationCheckMachineLanguageDef.rootSome
        (indexPattern priorRoot.id) priorFormulaPattern
        priorObligationPattern) := by
    rcases priorRoot with ⟨id, formula, priorObligation⟩
    simp [rootPattern?, priorFormulaEncoded, priorObligationEncoded]
  constructor
  · exact root_source_encodes_running host (some priorRoot)
      (DerivationCheckMachineLanguageDef.rootSome
        (indexPattern priorRoot.id) priorFormulaPattern
        priorObligationPattern)
      record remainingRecords remainingInstructions oldNodes nextId id
      obligation serviceState serviceStatePattern
      nodesPatternValue recordInstructionDecoded remainingDecoded
      rootEncoded serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault]
  constructor
  · exact duplicate_root_rewriteAt_exact host record remainingRecords
      nodesPatternValue (indexPattern nextId) serviceStatePattern
      (indexPattern priorRoot.id) priorFormulaPattern priorObligationPattern
      (indexPattern id) obligationPattern recordDecoded
  · exact fault_target_encodes_halted host remainingRecords oldNodes
      .duplicateRoot nodesPatternValue nodesEncoded

#print axioms duplicate_root_semantic_square

theorem missing_root_node_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (nextId id : Nat)
    (obligation : Obligation) (obligationPattern : Pattern)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (missing : lookupNode? id oldNodes = none)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some (.root id obligation))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (obligationEncoded :
      encodeObligation? host obligation = some obligationPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .root id obligation :: remainingInstructions
      nodes := oldNodes
      nextId := nextId
      root? := none
      serviceState := serviceState
    }
    let failure := Fault.missingRootNode id
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern nextId)
      DerivationCheckMachineLanguageDef.rootNone serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault (faultPattern failure))
      nodesPatternValue
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault failure)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.halted (.fault failure))
        target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host (.root id obligation) =
        some (DerivationCheckMachineLanguageDef.a "dcm:root"
          [indexPattern id, obligationPattern]) := by
    simp [instructionPattern?, obligationEncoded,
      DerivationCheckMachineLanguageDef.a, DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [indexPattern id, obligationPattern]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:root"
          [indexPattern id, obligationPattern]]
    exact decodeDecision_wordsPattern_exact host record (.root id obligation)
      (DerivationCheckMachineLanguageDef.a "dcm:root"
        [indexPattern id, obligationPattern])
      recordInstructionDecoded instructionPatternEncoded
  have nodesDecoded :=
    decodeNodes_nodesPattern host oldNodes nodesPatternValue nodesEncoded
  have rootFaulted : rootShapeDecision host oldNodes id =
      DerivationCheckMachineLanguageDef.decisionFault
        (faultPattern (.missingRootNode id)) := by
    simp [rootShapeDecision, missing, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact root_source_encodes_running host none
      DerivationCheckMachineLanguageDef.rootNone record remainingRecords
      remainingInstructions oldNodes nextId id obligation serviceState
      serviceStatePattern nodesPatternValue recordInstructionDecoded
      remainingDecoded rfl
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault, missing]
  constructor
  · exact root_fault_rewriteAt_exact_root_none host record remainingRecords
      nodesPatternValue (indexPattern nextId) serviceStatePattern
      (indexPattern id) obligationPattern (faultPattern (.missingRootNode id))
      oldNodes id recordDecoded nodesDecoded (decodeIndex_indexPattern id)
      rootFaulted
  · exact fault_target_encodes_halted host remainingRecords oldNodes
      (.missingRootNode id) nodesPatternValue nodesEncoded

#print axioms missing_root_node_semantic_square

theorem malformed_root_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (node : Node Formula)
    (nextId id : Nat) (obligation : Obligation) (obligationPattern : Pattern)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (found : lookupNode? id oldNodes = some node)
    (malformed :
      (node.relevance.towardRoot.isSome || node.relevance.distance != 0) =
        true)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some (.root id obligation))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (obligationEncoded :
      encodeObligation? host obligation = some obligationPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .root id obligation :: remainingInstructions
      nodes := oldNodes
      nextId := nextId
      root? := none
      serviceState := serviceState
    }
    let failure := Fault.malformedRelevance id
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern nextId)
      DerivationCheckMachineLanguageDef.rootNone serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault (faultPattern failure))
      nodesPatternValue
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault failure)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.halted (.fault failure))
        target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host (.root id obligation) =
        some (DerivationCheckMachineLanguageDef.a "dcm:root"
          [indexPattern id, obligationPattern]) := by
    simp [instructionPattern?, obligationEncoded,
      DerivationCheckMachineLanguageDef.a, DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [indexPattern id, obligationPattern]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:root"
          [indexPattern id, obligationPattern]]
    exact decodeDecision_wordsPattern_exact host record (.root id obligation)
      (DerivationCheckMachineLanguageDef.a "dcm:root"
        [indexPattern id, obligationPattern])
      recordInstructionDecoded instructionPatternEncoded
  have nodesDecoded :=
    decodeNodes_nodesPattern host oldNodes nodesPatternValue nodesEncoded
  have rootFaulted : rootShapeDecision host oldNodes id =
      DerivationCheckMachineLanguageDef.decisionFault
        (faultPattern (.malformedRelevance id)) := by
    simp [rootShapeDecision, found, malformed, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact root_source_encodes_running host none
      DerivationCheckMachineLanguageDef.rootNone record remainingRecords
      remainingInstructions oldNodes nextId id obligation serviceState
      serviceStatePattern nodesPatternValue recordInstructionDecoded
      remainingDecoded rfl
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault, found, malformed]
  constructor
  · exact root_fault_rewriteAt_exact_root_none host record remainingRecords
      nodesPatternValue (indexPattern nextId) serviceStatePattern
      (indexPattern id) obligationPattern (faultPattern (.malformedRelevance id))
      oldNodes id recordDecoded nodesDecoded (decodeIndex_indexPattern id)
      rootFaulted
  · exact fault_target_encodes_halted host remainingRecords oldNodes
      (.malformedRelevance id) nodesPatternValue nodesEncoded

#print axioms malformed_root_semantic_square

theorem root_accept_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (node : Node Formula)
    (nextId id : Nat) (obligation : Obligation) (obligationPattern : Pattern)
    (formulaPattern : Pattern) (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (found : lookupNode? id oldNodes = some node)
    (wellShaped :
      (node.relevance.towardRoot.isSome || node.relevance.distance != 0) =
        false)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some (.root id obligation))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (formulaEncoded :
      encodeFormula? host node.formula = some formulaPattern)
    (obligationEncoded :
      encodeObligation? host obligation = some obligationPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .root id obligation :: remainingInstructions
      nodes := oldNodes
      nextId := nextId
      root? := none
      serviceState := serviceState
    }
    let rootClaim : RootClaim Formula Obligation := {
      id := id
      formula := node.formula
      obligation := obligation
    }
    let after :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := remainingInstructions
      nodes := oldNodes
      nextId := nextId
      root? := some rootClaim
      serviceState := serviceState
    }
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern nextId)
      DerivationCheckMachineLanguageDef.rootNone serviceStatePattern
    let rootPatternValue := DerivationCheckMachineLanguageDef.rootSome
      (indexPattern id) formulaPattern obligationPattern
    let target := run (recordsPattern remainingRecords) nodesPatternValue
      (indexPattern nextId) rootPatternValue serviceStatePattern
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) = some (.running after) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.running after) target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host (.root id obligation) =
        some (DerivationCheckMachineLanguageDef.a "dcm:root"
          [indexPattern id, obligationPattern]) := by
    simp [instructionPattern?, obligationEncoded,
      DerivationCheckMachineLanguageDef.a, DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:root"
          [indexPattern id, obligationPattern]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:root"
          [indexPattern id, obligationPattern]]
    exact decodeDecision_wordsPattern_exact host record (.root id obligation)
      (DerivationCheckMachineLanguageDef.a "dcm:root"
        [indexPattern id, obligationPattern])
      recordInstructionDecoded instructionPatternEncoded
  have nodesDecoded :=
    decodeNodes_nodesPattern host oldNodes nodesPatternValue nodesEncoded
  have rootAccepted : rootShapeDecision host oldNodes id =
      DerivationCheckMachineLanguageDef.a "dcm:decision-root"
        [formulaPattern] := by
    simp [rootShapeDecision, found, wellShaped, formulaEncoded,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact root_source_encodes_running host none
      DerivationCheckMachineLanguageDef.rootNone record remainingRecords
      remainingInstructions oldNodes nextId id obligation serviceState
      serviceStatePattern nodesPatternValue recordInstructionDecoded
      remainingDecoded rfl
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, found, wellShaped]
  constructor
  · exact root_accept_rewriteAt_exact_root_none host record remainingRecords
      nodesPatternValue (indexPattern nextId) serviceStatePattern
      (indexPattern id) obligationPattern formulaPattern oldNodes id
      recordDecoded nodesDecoded (decodeIndex_indexPattern id) rootAccepted
  · constructor
    · exact remainingDecoded
    · simp [runningPattern?, rootPattern?, nodesEncoded, serviceStateEncoded,
        formulaEncoded, obligationEncoded]

#print axioms root_accept_semantic_square

/- Every representable root instruction follows exactly one of the semantic
machine's four branches.  The accepted root formula is recovered from the
already encoded node arena rather than supplied as target-side evidence. -/
theorem root_one_record_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula)) (nextId id : Nat)
    (obligation : Obligation) (obligationPattern : Pattern)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record = some (.root id obligation))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords = some remainingInstructions)
    (obligationEncoded :
      encodeObligation? host obligation = some obligationPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .root id obligation :: remainingInstructions
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
  cases rootState with
  | some priorRoot =>
      rcases priorRoot with ⟨priorId, priorFormula, priorObligation⟩
      unfold rootPattern? at rootEncoded
      cases priorFormulaResult : encodeFormula? host priorFormula with
      | none => simp [priorFormulaResult] at rootEncoded
      | some priorFormulaPattern =>
          cases priorObligationResult :
              encodeObligation? host priorObligation with
          | none =>
              simp [priorFormulaResult, priorObligationResult] at rootEncoded
          | some priorObligationPattern =>
              simp [priorFormulaResult, priorObligationResult] at rootEncoded
              subst rootPatternValue
              rcases duplicate_root_semantic_square host
                  { id := priorId, formula := priorFormula,
                    obligation := priorObligation }
                  priorFormulaPattern priorObligationPattern record
                  remainingRecords remainingInstructions oldNodes nextId id
                  obligation obligationPattern serviceState
                  serviceStatePattern nodesPatternValue
                  recordInstructionDecoded remainingDecoded
                  priorFormulaResult priorObligationResult obligationEncoded
                  serviceStateEncoded nodesEncoded with
                ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
              exact ⟨sourceEncodes, _, _, semanticStep, authoredStep,
                targetEncodes⟩
  | none =>
      simp [rootPattern?] at rootEncoded
      subst rootPatternValue
      cases found : lookupNode? id oldNodes with
      | none =>
          rcases missing_root_node_semantic_square host record
              remainingRecords remainingInstructions oldNodes nextId id
              obligation obligationPattern serviceState serviceStatePattern
              nodesPatternValue found recordInstructionDecoded remainingDecoded
              obligationEncoded serviceStateEncoded nodesEncoded with
            ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
          exact ⟨sourceEncodes, _, _, semanticStep, authoredStep,
            targetEncodes⟩
      | some node =>
          cases malformed :
              (node.relevance.towardRoot.isSome ||
                node.relevance.distance != 0) with
          | true =>
              rcases malformed_root_semantic_square host record
                  remainingRecords remainingInstructions oldNodes node nextId id
                  obligation obligationPattern serviceState
                  serviceStatePattern nodesPatternValue found malformed
                  recordInstructionDecoded remainingDecoded obligationEncoded
                  serviceStateEncoded nodesEncoded with
                ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
              exact ⟨sourceEncodes, _, _, semanticStep, authoredStep,
                targetEncodes⟩
          | false =>
              obtain ⟨formulaPattern, formulaEncoded⟩ :=
                formulaPattern_exists_of_lookupNode_some host id oldNodes node
                  nodesPatternValue nodesEncoded found
              rcases root_accept_semantic_square host record remainingRecords
                  remainingInstructions oldNodes node nextId id obligation
                  obligationPattern formulaPattern serviceState
                  serviceStatePattern nodesPatternValue found malformed
                  recordInstructionDecoded remainingDecoded formulaEncoded
                  obligationEncoded serviceStateEncoded nodesEncoded with
                ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
              exact ⟨sourceEncodes, _, _, semanticStep, authoredStep,
                targetEncodes⟩

#print axioms root_one_record_semantic_square_encoded_root

end Mettapedia.GSLT.LanguageDef.DerivationWordMachineControlSimulation
