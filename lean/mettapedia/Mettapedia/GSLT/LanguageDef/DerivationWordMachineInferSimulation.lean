import Mettapedia.GSLT.LanguageDef.DerivationWordMachineInputSimulation

/-!
# Exact infer simulation for the derivation-word machine

This module proves the one-record operational square for inference records.
The word machine remains calculus-neutral: parent resolution is structural,
while inference acceptance is supplied by the declared calculus service.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationWordMachineInferSimulation

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

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}
variable [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation]
  [DecidableEq ServiceState]

def genericNonInferSourceRules : List RewriteRule := [
  DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
  DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
  DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
  DerivationCheckMachineLanguageDef.inputAcceptTransition,
  DerivationCheckMachineLanguageDef.dropFaultTransition,
  DerivationCheckMachineLanguageDef.dropAcceptTransition
]

/-- Every generic-root input or drop row is excluded by the record decoder
when the current record decodes as infer. -/
theorem generic_non_infer_lifted_rule_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState id rule parents evidence
      conclusion relevance : Pattern)
    (membership : sourceRule ∈ genericNonInferSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [id, rule, parents, evidence, conclusion, relevance])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  simp only [genericNonInferSourceRules, List.mem_cons, List.mem_nil_iff,
    or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.inputIndexFaultTransition record rest
      nodes nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [v "id", v "formula", v "provenance", v "relevance"])
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [id, rule, parents, evidence, conclusion, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
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
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition record
      rest nodes nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [v "id", v "formula", v "provenance", v "relevance"])
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [id, rule, parents, evidence, conclusion, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
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
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.inputDecisionFaultTransition record
      rest nodes nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [v "id", v "formula", v "provenance", v "relevance"])
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [id, rule, parents, evidence, conclusion, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
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
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.inputAcceptTransition record rest
      nodes nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [v "id", v "formula", v "provenance", v "relevance"])
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [id, rule, parents, evidence, conclusion, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.inputAcceptTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
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
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.dropFaultTransition record rest nodes
      nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:drop" [v "id"])
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [id, rule, parents, evidence, conclusion, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.dropFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.dropFaultTransition,
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
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.dropAcceptTransition record rest nodes
      nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:drop" [v "id"])
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [id, rule, parents, evidence, conclusion, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.dropAcceptTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
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

#print axioms generic_non_infer_lifted_rule_empty

theorem duplicate_root_on_infer_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId serviceState priorId priorFormula
      priorObligation id rule parents evidence conclusion relevance : Pattern)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [id, rule, parents, evidence, conclusion, relevance])) :
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

#print axioms duplicate_root_on_infer_record_root_some_empty

theorem root_rules_on_infer_record_root_none_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId serviceState id rule parents evidence conclusion
      relevance : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.rootFaultTransition,
      DerivationCheckMachineLanguageDef.rootAcceptTransition])
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [id, rule, parents, evidence, conclusion, relevance])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
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

#print axioms root_rules_on_infer_record_root_none_empty

theorem finish_shape_rules_on_infer_record_root_none_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState id rule parents evidence conclusion relevance :
      Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishTrailingTransition,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [id, rule, parents, evidence, conclusion, relevance])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId DerivationCheckMachineLanguageDef.rootNone
        serviceState) = [] := by
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
          Bindings.lookup]
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
          Bindings.lookup]
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

#print axioms finish_shape_rules_on_infer_record_root_none_empty

theorem finish_shape_rules_on_infer_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation id rule
      parents evidence conclusion relevance : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishTrailingTransition,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [id, rule, parents, evidence, conclusion, relevance])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) = [] := by
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
          Bindings.lookup]
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

#print axioms finish_shape_rules_on_infer_record_root_some_empty

theorem finish_root_some_rules_on_infer_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation id rule
      parents evidence conclusion relevance : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [id, rule, parents, evidence, conclusion, relevance])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · cases remainingRecords with
    | nil =>
        simp [applyRuleUsing, premisesUsing, premiseStepUsing,
          engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern, liftPremise,
          DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
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
          Bindings.lookup]
    | cons nextRecord trailingRecords =>
        simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern,
          DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.instructionsNil,
          DerivationCheckMachineLanguageDef.rootSome,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          run, recordsCons, recordsNil, recordsPattern,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, matchPattern, matchArgs,
          mergeBindings]
  · cases remainingRecords with
    | nil =>
        simp [applyRuleUsing, premisesUsing, premiseStepUsing,
          engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern, liftPremise,
          DerivationCheckMachineLanguageDef.finishRootFaultTransition,
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
          Bindings.lookup]
    | cons nextRecord trailingRecords =>
        simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern,
          DerivationCheckMachineLanguageDef.finishRootFaultTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.instructionsNil,
          DerivationCheckMachineLanguageDef.rootSome,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          run, recordsCons, recordsNil, recordsPattern,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, matchPattern, matchArgs,
          mergeBindings]
  · cases remainingRecords with
    | nil =>
        simp [applyRuleUsing, premisesUsing, premiseStepUsing,
          engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern, liftPremise,
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
          Bindings.lookup]
    | cons nextRecord trailingRecords =>
        apply applyRuleUsing_empty_of_no_left_match
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
        rw [show
          (liftRewrite
              DerivationCheckMachineLanguageDef.finishVerifiedTransition).left =
            liftLeft
              DerivationCheckMachineLanguageDef.finishVerifiedTransition.left
          by rfl]
        rw [show
          liftLeft
              DerivationCheckMachineLanguageDef.finishVerifiedTransition.left =
            run (recordsCons (v "record") recordsNil) (v "nodes")
              (v "nextId")
              (DerivationCheckMachineLanguageDef.rootSome (v "id")
                (v "formula") (v "obligation"))
              (v "serviceState")
          by
            simp [liftLeft, liftPattern,
              DerivationCheckMachineLanguageDef.finishVerifiedTransition,
              DerivationCheckMachineLanguageDef.run,
              DerivationCheckMachineLanguageDef.instructionsCons,
              DerivationCheckMachineLanguageDef.instructionsNil,
              DerivationCheckMachineLanguageDef.rootSome,
              DerivationCheckMachineLanguageDef.a,
              DerivationCheckMachineLanguageDef.v,
              run, recordsCons, recordsNil,
              DerivationWordMachineLanguageDef.a, v]]
        have recordsMismatch :
            matchPattern (recordsCons (v "record") recordsNil)
              (recordsCons (wordsPattern record)
                (recordsPattern (nextRecord :: trailingRecords))) = [] := by
          simp [recordsPattern, recordsCons, recordsNil,
            DerivationWordMachineLanguageDef.a,
            DerivationWordMachineRelationEnv.a, v, matchPattern, matchArgs,
            mergeBindings]
        simp [run, DerivationCheckMachineLanguageDef.rootSome,
          DerivationCheckMachineLanguageDef.a,
          DerivationWordMachineLanguageDef.a, matchPattern, matchArgs,
          recordsMismatch]

#print axioms finish_root_some_rules_on_infer_record_root_some_empty

def beforeInferRows : List RewriteRule := [
  malformedRecordTransition,
  liftRewrite DerivationCheckMachineLanguageDef.missingFinishTransition,
  liftRewrite DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
  liftRewrite DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
  liftRewrite DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
  liftRewrite DerivationCheckMachineLanguageDef.inputAcceptTransition
]

def inferRows : List RewriteRule := [
  liftRewrite DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
  liftRewrite DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
  liftRewrite DerivationCheckMachineLanguageDef.inferParentFaultTransition,
  liftRewrite DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
  liftRewrite DerivationCheckMachineLanguageDef.inferAcceptTransition
]

def afterInferRows : List RewriteRule := [
  liftRewrite DerivationCheckMachineLanguageDef.dropFaultTransition,
  liftRewrite DerivationCheckMachineLanguageDef.dropAcceptTransition,
  liftRewrite DerivationCheckMachineLanguageDef.duplicateRootTransition,
  liftRewrite DerivationCheckMachineLanguageDef.rootFaultTransition,
  liftRewrite DerivationCheckMachineLanguageDef.rootAcceptTransition,
  liftRewrite DerivationCheckMachineLanguageDef.finishTrailingTransition,
  liftRewrite DerivationCheckMachineLanguageDef.finishMissingRootTransition,
  liftRewrite
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
  liftRewrite DerivationCheckMachineLanguageDef.finishRootFaultTransition,
  liftRewrite DerivationCheckMachineLanguageDef.finishVerifiedTransition
]

theorem transitions_split_around_infer :
    transitions = beforeInferRows ++ inferRows ++ afterInferRows := by
  rfl

#print axioms transitions_split_around_infer

/-- The authored word-machine language exposes the same exact three-block
decomposition as its transition inventory.  Naming this boundary prevents
each operational theorem from re-normalizing the entire fixed table. -/
theorem language_rewrites_split_around_infer :
    language.rewrites = beforeInferRows ++ inferRows ++ afterInferRows := by
  exact transitions_split_around_infer

#print axioms language_rewrites_split_around_infer

theorem flatMap_middle_of_outer_empty
    {Alpha Beta : Type}
    (before middle after : List Alpha) (step : Alpha -> List Beta)
    (beforeEmpty : before.flatMap step = [])
    (afterEmpty : after.flatMap step = []) :
    (before ++ middle ++ after).flatMap step = middle.flatMap step := by
  simp only [List.flatMap_append, beforeEmpty, afterEmpty, List.nil_append,
    List.append_nil]

#print axioms flatMap_middle_of_outer_empty

theorem applyRuleUsing_empty_of_unique_match
    (base : BasePremiseEvaluator) (targetLanguage : LanguageDef)
    (recursiveStep : Pattern -> List Pattern) (rule : RewriteRule)
    (term : Pattern) (initialBindings : Bindings)
    (leftExact :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
          targetLanguage rule term = [initialBindings])
    (premisesEmpty :
      premisesUsing base targetLanguage recursiveStep rule.premises
        initialBindings = []) :
    applyRuleUsing base targetLanguage recursiveStep rule term = [] := by
  change
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
      targetLanguage rule term).flatMap (fun bindings =>
        (premisesUsing base targetLanguage recursiveStep rule.premises
          bindings).map (fun finalBindings =>
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
              targetLanguage rule finalBindings)) = []
  rw [leftExact]
  simp [premisesEmpty]

#print axioms applyRuleUsing_empty_of_unique_match

theorem before_infer_rows_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern rootPatternValue serviceStatePattern idPattern
      rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue : Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue])) :
    beforeInferRows.flatMap (fun row =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) row
        (run (recordsCons (wordsPattern record)
          (recordsPattern remainingRecords)) nodes nextIdPattern
          rootPatternValue serviceStatePattern)) = [] := by
  simp only [beforeInferRows, List.flatMap_cons, List.flatMap_nil]
  rw [malformed_record_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern
    (DerivationCheckMachineLanguageDef.a "dcm:infer"
      [idPattern, rulePattern, parentsPattern, evidencePattern,
       conclusionPattern, relevancePatternValue]) recordDecoded]
  rw [missing_finish_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern]
  rw [generic_non_infer_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue
    (by simp [genericNonInferSourceRules]) recordDecoded]
  rw [generic_non_infer_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue
    (by simp [genericNonInferSourceRules]) recordDecoded]
  rw [generic_non_infer_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue
    (by simp [genericNonInferSourceRules]) recordDecoded]
  rw [generic_non_infer_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inputAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue
    (by simp [genericNonInferSourceRules]) recordDecoded]
  simp

#print axioms before_infer_rows_empty

theorem after_infer_rows_empty_root_none
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue :
      Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue])) :
    afterInferRows.flatMap (fun row =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) row
        (run (recordsCons (wordsPattern record)
          (recordsPattern remainingRecords)) nodes nextIdPattern
          DerivationCheckMachineLanguageDef.rootNone
          serviceStatePattern)) = [] := by
  simp only [afterInferRows, List.flatMap_cons, List.flatMap_nil]
  rw [generic_non_infer_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.dropFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    rulePattern parentsPattern evidencePattern conclusionPattern
    relevancePatternValue (by simp [genericNonInferSourceRules])
    recordDecoded]
  rw [generic_non_infer_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.dropAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    rulePattern parentsPattern evidencePattern conclusionPattern
    relevancePatternValue (by simp [genericNonInferSourceRules])
    recordDecoded]
  rw [duplicate_root_on_root_none_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern serviceStatePattern]
  rw [root_rules_on_infer_record_root_none_empty host
    DerivationCheckMachineLanguageDef.rootFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
    conclusionPattern relevancePatternValue (by simp) recordDecoded]
  rw [root_rules_on_infer_record_root_none_empty host
    DerivationCheckMachineLanguageDef.rootAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
    conclusionPattern relevancePatternValue (by simp) recordDecoded]
  rw [finish_shape_rules_on_infer_record_root_none_empty host
    DerivationCheckMachineLanguageDef.finishTrailingTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern idPattern
    rulePattern parentsPattern evidencePattern conclusionPattern
    relevancePatternValue (by simp) recordDecoded]
  rw [finish_shape_rules_on_infer_record_root_none_empty host
    DerivationCheckMachineLanguageDef.finishMissingRootTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern idPattern
    rulePattern parentsPattern evidencePattern conclusionPattern
    relevancePatternValue (by simp) recordDecoded]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern (by simp)]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishRootFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern (by simp)]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishVerifiedTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern (by simp)]
  simp

#print axioms after_infer_rows_empty_root_none

theorem after_infer_rows_empty_root_some
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern priorIdPattern
      priorFormulaPattern priorObligationPattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue :
      Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue])) :
    afterInferRows.flatMap (fun row =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) row
        (run (recordsCons (wordsPattern record)
          (recordsPattern remainingRecords)) nodes nextIdPattern
          (DerivationCheckMachineLanguageDef.rootSome priorIdPattern
            priorFormulaPattern priorObligationPattern)
          serviceStatePattern)) = [] := by
  simp only [afterInferRows, List.flatMap_cons, List.flatMap_nil]
  rw [generic_non_infer_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.dropFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    (DerivationCheckMachineLanguageDef.rootSome priorIdPattern
      priorFormulaPattern priorObligationPattern)
    serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
    conclusionPattern relevancePatternValue
    (by simp [genericNonInferSourceRules]) recordDecoded]
  rw [generic_non_infer_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.dropAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    (DerivationCheckMachineLanguageDef.rootSome priorIdPattern
      priorFormulaPattern priorObligationPattern)
    serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
    conclusionPattern relevancePatternValue
    (by simp [genericNonInferSourceRules]) recordDecoded]
  rw [duplicate_root_on_infer_record_root_some_empty host
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern priorIdPattern priorFormulaPattern
    priorObligationPattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue recordDecoded]
  rw [root_rules_on_root_some_empty host
    DerivationCheckMachineLanguageDef.rootFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern priorIdPattern priorFormulaPattern
    priorObligationPattern (by simp)]
  rw [root_rules_on_root_some_empty host
    DerivationCheckMachineLanguageDef.rootAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern priorIdPattern priorFormulaPattern
    priorObligationPattern (by simp)]
  rw [finish_shape_rules_on_infer_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishTrailingTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern priorIdPattern
    priorFormulaPattern priorObligationPattern idPattern rulePattern
    parentsPattern evidencePattern conclusionPattern relevancePatternValue
    (by simp) recordDecoded]
  rw [finish_shape_rules_on_infer_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishMissingRootTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern priorIdPattern
    priorFormulaPattern priorObligationPattern idPattern rulePattern
    parentsPattern evidencePattern conclusionPattern relevancePatternValue
    (by simp) recordDecoded]
  rw [finish_root_some_rules_on_infer_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern priorIdPattern
    priorFormulaPattern priorObligationPattern idPattern rulePattern
    parentsPattern evidencePattern conclusionPattern relevancePatternValue
    (by simp) recordDecoded]
  rw [finish_root_some_rules_on_infer_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishRootFaultTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern priorIdPattern
    priorFormulaPattern priorObligationPattern idPattern rulePattern
    parentsPattern evidencePattern conclusionPattern relevancePatternValue
    (by simp) recordDecoded]
  rw [finish_root_some_rules_on_infer_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishVerifiedTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern priorIdPattern
    priorFormulaPattern priorObligationPattern idPattern rulePattern
    parentsPattern evidencePattern conclusionPattern relevancePatternValue
    (by simp) recordDecoded]
  simp

#print axioms after_infer_rows_empty_root_some

/-- With no selected root, a decoded infer record restricts the full authored
transition table exactly to the five infer rows. -/
theorem infer_record_rewriteAt_partition_root_none
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue :
      Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue])) :
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodes nextIdPattern DerivationCheckMachineLanguageDef.rootNone
      serviceStatePattern
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      inferRows.flatMap (fun row =>
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) row source) := by
  dsimp only
  change language.rewrites.flatMap (fun row =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) row
        (run (recordsCons (wordsPattern record)
          (recordsPattern remainingRecords)) nodes nextIdPattern
          DerivationCheckMachineLanguageDef.rootNone
          serviceStatePattern)) = _
  rw [language_rewrites_split_around_infer]
  apply flatMap_middle_of_outer_empty
  · exact before_infer_rows_empty host record remainingRecords nodes
      nextIdPattern DerivationCheckMachineLanguageDef.rootNone
      serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
      conclusionPattern relevancePatternValue recordDecoded
  · exact after_infer_rows_empty_root_none host record remainingRecords nodes
      nextIdPattern serviceStatePattern idPattern rulePattern parentsPattern
      evidencePattern conclusionPattern relevancePatternValue recordDecoded

#print axioms infer_record_rewriteAt_partition_root_none

/-- With a selected root, a decoded infer record restricts the full authored
transition table to the same five infer rows and preserves that root in every
successful case. -/
theorem infer_record_rewriteAt_partition_root_some
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern priorIdPattern
      priorFormulaPattern priorObligationPattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue :
      Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue])) :
    let root := DerivationCheckMachineLanguageDef.rootSome priorIdPattern
      priorFormulaPattern priorObligationPattern
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodes nextIdPattern root serviceStatePattern
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      inferRows.flatMap (fun row =>
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) row source) := by
  dsimp only
  let root := DerivationCheckMachineLanguageDef.rootSome priorIdPattern
    priorFormulaPattern priorObligationPattern
  change language.rewrites.flatMap (fun row =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) row
        (run (recordsCons (wordsPattern record)
          (recordsPattern remainingRecords)) nodes nextIdPattern root
          serviceStatePattern)) = _
  rw [language_rewrites_split_around_infer]
  apply flatMap_middle_of_outer_empty
  · exact before_infer_rows_empty host record remainingRecords nodes
      nextIdPattern root serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      recordDecoded
  · exact after_infer_rows_empty_root_some host record remainingRecords nodes
      nextIdPattern serviceStatePattern priorIdPattern priorFormulaPattern
      priorObligationPattern idPattern rulePattern parentsPattern
      evidencePattern conclusionPattern relevancePatternValue recordDecoded

#print axioms infer_record_rewriteAt_partition_root_some

/-- The infer transition-table partition is independent of whether the
semantic configuration has selected a root.  The target root is the canonical
encoding of that exact semantic root state. -/
theorem infer_record_rewriteAt_partition_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue :
      Pattern)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue])) :
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodes nextIdPattern rootPatternValue serviceStatePattern
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      inferRows.flatMap (fun row =>
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) row source) := by
  cases rootState with
  | none =>
      simp [rootPattern?] at rootEncoded
      subst rootPatternValue
      exact infer_record_rewriteAt_partition_root_none host record
        remainingRecords nodes nextIdPattern serviceStatePattern idPattern
        rulePattern parentsPattern evidencePattern conclusionPattern
        relevancePatternValue recordDecoded
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
              exact infer_record_rewriteAt_partition_root_some host record
                remainingRecords nodes nextIdPattern serviceStatePattern
                (indexPattern rootId) rootFormulaPattern rootObligationPattern
                idPattern rulePattern parentsPattern evidencePattern
                conclusionPattern relevancePatternValue recordDecoded

#print axioms infer_record_rewriteAt_partition_encoded_root

def inferDecodedBindings
    (record rest nodes nextId root serviceState id rule parents evidence
      conclusion relevance : Pattern) : Bindings :=
  [("rule", rule), ("evidence", evidence), ("relevance", relevance),
   ("conclusion", conclusion), ("parents", parents),
   ("id", id)] ++
    inputStartBindings record rest nodes nextId root serviceState

theorem liftedInferAccept_premises :
    (liftRewrite
      DerivationCheckMachineLanguageDef.inferAcceptTransition).premises =
    [query "DWMDecodeRecord" [v "record", decoded
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [v "id", v "rule", v "parents", v "evidence", v "conclusion",
         v "relevance"])],
     query "DCMIndexAdvance" [v "nextId", v "id",
       DerivationCheckMachineLanguageDef.a "dcm:decision-index"
         [v "advanced"]],
     query "DCMRelevanceShapeDecision" [v "id", v "relevance",
       DerivationCheckMachineLanguageDef.a "dcm:decision-accept"],
     query "DCMResolveParents" [v "nodes", v "id", v "relevance",
       v "parents", DerivationCheckMachineLanguageDef.a
         "dcm:decision-parents" [v "parentFormulas", v "nextNodes"]],
     query "DCMRuleDecision" [v "id", v "serviceState", v "rule",
       v "parentFormulas", v "evidence", v "conclusion",
       DerivationCheckMachineLanguageDef.decisionState
         (v "nextServiceState")]] := by
  simp [liftRewrite, DerivationCheckMachineLanguageDef.inferAcceptTransition,
    sourceInstruction?, liftPremise, liftPattern,
    DerivationWordMachineLanguageDef.query,
    DerivationWordMachineLanguageDef.v,
    DerivationWordMachineLanguageDef.decoded,
    DerivationWordMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionState,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query]

#print axioms liftedInferAccept_premises

theorem liftedInferAccept_left :
    (liftRewrite DerivationCheckMachineLanguageDef.inferAcceptTransition).left =
      run (recordsCons (v "record") (v "rest")) (v "nodes")
        (v "nextId") (v "root") (v "serviceState") := by
  simp [liftRewrite, DerivationCheckMachineLanguageDef.inferAcceptTransition,
    sourceInstruction?, liftLeft, liftPattern,
    DerivationWordMachineLanguageDef.run,
    DerivationWordMachineLanguageDef.recordsCons,
    DerivationWordMachineLanguageDef.v,
    DerivationWordMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v]

#print axioms liftedInferAccept_left

theorem liftedInferRuleFault_premises :
    (liftRewrite
      DerivationCheckMachineLanguageDef.inferRuleFaultTransition).premises =
    [query "DWMDecodeRecord" [v "record", decoded
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [v "id", v "rule", v "parents", v "evidence", v "conclusion",
         v "relevance"])],
     query "DCMIndexAdvance" [v "nextId", v "id",
       DerivationCheckMachineLanguageDef.a "dcm:decision-index"
         [v "advanced"]],
     query "DCMRelevanceShapeDecision" [v "id", v "relevance",
       DerivationCheckMachineLanguageDef.a "dcm:decision-accept"],
     query "DCMResolveParents" [v "nodes", v "id", v "relevance",
       v "parents", DerivationCheckMachineLanguageDef.a
         "dcm:decision-parents" [v "parentFormulas", v "nextNodes"]],
     query "DCMRuleDecision" [v "id", v "serviceState", v "rule",
       v "parentFormulas", v "evidence", v "conclusion",
       DerivationCheckMachineLanguageDef.decisionFault (v "fault")]] := by
  simp [liftRewrite,
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
    sourceInstruction?, liftPremise, liftPattern,
    DerivationWordMachineLanguageDef.query,
    DerivationWordMachineLanguageDef.v,
    DerivationWordMachineLanguageDef.decoded,
    DerivationWordMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query]

#print axioms liftedInferRuleFault_premises

theorem liftedInferRuleFault_left :
    (liftRewrite
      DerivationCheckMachineLanguageDef.inferRuleFaultTransition).left =
      run (recordsCons (v "record") (v "rest")) (v "nodes")
        (v "nextId") (v "root") (v "serviceState") := by
  simp [liftRewrite,
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
    sourceInstruction?, liftLeft, liftPattern,
    DerivationWordMachineLanguageDef.run,
    DerivationWordMachineLanguageDef.recordsCons,
    DerivationWordMachineLanguageDef.v,
    DerivationWordMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v]

#print axioms liftedInferRuleFault_left

theorem infer_decode_premise_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId root serviceState id rule parents evidence
      conclusion relevance : Pattern)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [id, rule, parents, evidence, conclusion, relevance])) :
    premiseStepWithEnv (relationEnv host) language
      (inputStartBindings record rest nodes nextId root serviceState)
      (query "DWMDecodeRecord" [v "record", decoded
        (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [v "id", v "rule", v "parents", v "evidence", v "conclusion",
           v "relevance"])]) =
      [inferDecodedBindings record rest nodes nextId root serviceState id rule
        parents evidence conclusion relevance] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, relationTuples, recordDecoded, inputStartBindings,
    inferDecodedBindings, query, v, decoded,
    DerivationWordMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.a, matchRelationArgs,
    matchRelationArgument, matchPattern, matchArgs, mergeBindings,
    applyBindings, Bindings.lookup]

#print axioms infer_decode_premise_exact

theorem infer_index_accept_premise_empty_of_fault
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern faultPatternValue : Pattern)
    (expectedId actualId : Nat)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (indexFaulted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    premiseStepWithEnv (relationEnv host) language
      (inferDecodedBindings record rest nodes nextIdPattern root
        serviceStatePattern idPattern rulePattern parentsPattern
        evidencePattern conclusionPattern relevancePatternValue)
      (query "DCMIndexAdvance" [v "nextId", v "id",
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern]]) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, relationTuples, nextIdDecoded, idDecoded, indexFaulted,
    inferDecodedBindings, inputStartBindings, query, v,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.a, matchRelationArgs,
    matchRelationArgument, matchPattern, mergeBindings,
    applyBindings, Bindings.lookup]

#print axioms infer_index_accept_premise_empty_of_fault

def inferIndexedBindings
    (record rest nodes nextId root serviceState id rule parents evidence
      conclusion relevance advanced : Pattern) : Bindings :=
  ("advanced", advanced) ::
    inferDecodedBindings record rest nodes nextId root serviceState id rule
      parents evidence conclusion relevance

theorem infer_index_premise_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern : Pattern)
    (expectedId actualId : Nat)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern]) :
    premiseStepWithEnv (relationEnv host) language
      (inferDecodedBindings record rest nodes nextIdPattern root
        serviceStatePattern idPattern rulePattern parentsPattern
        evidencePattern conclusionPattern relevancePatternValue)
      (query "DCMIndexAdvance" [v "nextId", v "id",
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [v "advanced"]]) =
      [inferIndexedBindings record rest nodes nextIdPattern root
        serviceStatePattern idPattern rulePattern parentsPattern
        evidencePattern conclusionPattern relevancePatternValue
        advancedPattern] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, relationTuples, nextIdDecoded, idDecoded, indexAccepted,
    inferDecodedBindings, inferIndexedBindings, inputStartBindings, query, v,
    DerivationCheckMachineLanguageDef.a, matchRelationArgs,
    matchRelationArgument, matchPattern, matchArgs, mergeBindings,
    applyBindings, Bindings.lookup]

#print axioms infer_index_premise_exact

theorem infer_relevance_accept_premise_empty_of_fault
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId root serviceState idPattern rule parents evidence
      conclusion relevancePatternValue advanced faultPatternValue : Pattern)
    (actualId : Nat) (relevance : RelevanceWitness)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (relevanceFaulted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    premiseStepWithEnv (relationEnv host) language
      (inferIndexedBindings record rest nodes nextId root serviceState
        idPattern rule parents evidence conclusion relevancePatternValue
        advanced)
      (query "DCMRelevanceShapeDecision" [v "id", v "relevance",
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept"]) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, relationTuples, idDecoded, relevanceDecoded,
    relevanceFaulted, inferIndexedBindings, inferDecodedBindings,
    inputStartBindings, query, v,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.a, matchRelationArgs,
    matchRelationArgument, matchPattern, mergeBindings, applyBindings,
    Bindings.lookup]

#print axioms infer_relevance_accept_premise_empty_of_fault

theorem infer_relevance_premise_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId root serviceState idPattern rule parents evidence
      conclusion relevancePatternValue advanced : Pattern)
    (actualId : Nat) (relevance : RelevanceWitness)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept") :
    premiseStepWithEnv (relationEnv host) language
      (inferIndexedBindings record rest nodes nextId root serviceState
        idPattern rule parents evidence conclusion relevancePatternValue
        advanced)
      (query "DCMRelevanceShapeDecision" [v "id", v "relevance",
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept"]) =
      [inferIndexedBindings record rest nodes nextId root serviceState
        idPattern rule parents evidence conclusion relevancePatternValue
        advanced] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, relationTuples, idDecoded, relevanceDecoded,
    relevanceAccepted, inferIndexedBindings, inferDecodedBindings,
    inputStartBindings, query, v, DerivationCheckMachineLanguageDef.a,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms infer_relevance_premise_exact

theorem infer_parent_accept_premise_empty_of_fault
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodesPatternValue nextId root serviceState idPattern
      rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advanced parentFormulasPattern nextNodesPattern
      faultPatternValue : Pattern)
    (nodes : List (Node Formula)) (actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (parentFaulted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    premiseStepWithEnv (relationEnv host) language
      (inferIndexedBindings record rest nodesPatternValue nextId root
        serviceState idPattern rulePattern parentsPattern evidencePattern
        conclusionPattern relevancePatternValue advanced)
      (query "DCMResolveParents" [v "nodes", v "id", v "relevance",
        v "parents", DerivationCheckMachineLanguageDef.a
          "dcm:decision-parents"
          [parentFormulasPattern, nextNodesPattern]]) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, relationTuples, nodesDecoded, idDecoded, relevanceDecoded,
    parentsDecoded, parentFaulted, inferIndexedBindings,
    inferDecodedBindings, inputStartBindings, query, v,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.a, matchRelationArgs,
    matchRelationArgument, matchPattern, mergeBindings, applyBindings,
    Bindings.lookup]

#print axioms infer_parent_accept_premise_empty_of_fault

def inferParentBindings
    (record rest nodes nextId root serviceState id rule parents evidence
      conclusion relevance advanced parentFormulas nextNodes : Pattern) :
    Bindings :=
  [("parentFormulas", parentFormulas), ("nextNodes", nextNodes)] ++
    inferIndexedBindings record rest nodes nextId root serviceState id rule
      parents evidence conclusion relevance advanced

theorem infer_parent_premise_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodesPatternValue nextId root serviceState idPattern
      rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advanced parentFormulasPattern nextNodesPattern :
      Pattern)
    (nodes : List (Node Formula)) (actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (parentAccepted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.a "dcm:decision-parents"
          [parentFormulasPattern, nextNodesPattern]) :
    premiseStepWithEnv (relationEnv host) language
      (inferIndexedBindings record rest nodesPatternValue nextId root
        serviceState idPattern rulePattern parentsPattern evidencePattern
        conclusionPattern relevancePatternValue advanced)
      (query "DCMResolveParents" [v "nodes", v "id", v "relevance",
        v "parents", DerivationCheckMachineLanguageDef.a
          "dcm:decision-parents"
          [v "parentFormulas", v "nextNodes"]]) =
      [inferParentBindings record rest nodesPatternValue nextId root
        serviceState idPattern rulePattern parentsPattern evidencePattern
        conclusionPattern relevancePatternValue advanced
        parentFormulasPattern nextNodesPattern] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, relationTuples, nodesDecoded, idDecoded, relevanceDecoded,
    parentsDecoded, parentAccepted, inferParentBindings,
    inferIndexedBindings, inferDecodedBindings, inputStartBindings, query, v,
    DerivationCheckMachineLanguageDef.a, matchRelationArgs,
    matchRelationArgument, matchPattern, matchArgs, mergeBindings,
    applyBindings, Bindings.lookup]

#print axioms infer_parent_premise_exact

theorem infer_rule_accept_premise_empty_of_fault
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId root serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      advanced parentFormulasPattern nextNodesPattern nextServiceStatePattern
      faultPatternValue : Pattern)
    (actualId : Nat) (serviceState : ServiceState) (rule : Rule)
    (parentFormulas : List Formula) (evidence : Evidence)
    (conclusion : Formula)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (ruleDecoded : decodeRule? host rulePattern = some rule)
    (parentFormulasDecoded :
      decodeFormulas? host parentFormulasPattern = some parentFormulas)
    (evidenceDecoded : decodeEvidence? host evidencePattern = some evidence)
    (conclusionDecoded :
      decodeFormula? host conclusionPattern = some conclusion)
    (ruleFaulted :
      ruleDecision host actualId serviceState rule parentFormulas evidence
          conclusion =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    premiseStepWithEnv (relationEnv host) language
      (inferParentBindings record rest nodes nextId root serviceStatePattern
        idPattern rulePattern parentsPattern evidencePattern conclusionPattern
        relevancePatternValue advanced parentFormulasPattern nextNodesPattern)
      (query "DCMRuleDecision" [v "id", v "serviceState", v "rule",
        v "parentFormulas", v "evidence", v "conclusion",
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern]) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, relationTuples, idDecoded, serviceStateDecoded, ruleDecoded,
    parentFormulasDecoded, evidenceDecoded, conclusionDecoded, ruleFaulted,
    inferParentBindings, inferIndexedBindings, inferDecodedBindings,
    inputStartBindings, query, v,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.decisionState,
    DerivationCheckMachineLanguageDef.a, matchRelationArgs,
    matchRelationArgument, matchPattern, mergeBindings,
    applyBindings, Bindings.lookup]

#print axioms infer_rule_accept_premise_empty_of_fault

theorem infer_rule_fault_premise_empty_of_accept
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId root serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      advanced parentFormulasPattern nextNodesPattern faultPatternValue
      nextServiceStatePattern : Pattern)
    (actualId : Nat) (serviceState : ServiceState) (rule : Rule)
    (parentFormulas : List Formula) (evidence : Evidence)
    (conclusion : Formula)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (ruleDecoded : decodeRule? host rulePattern = some rule)
    (parentFormulasDecoded :
      decodeFormulas? host parentFormulasPattern = some parentFormulas)
    (evidenceDecoded : decodeEvidence? host evidencePattern = some evidence)
    (conclusionDecoded :
      decodeFormula? host conclusionPattern = some conclusion)
    (ruleAccepted :
      ruleDecision host actualId serviceState rule parentFormulas evidence
          conclusion =
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern) :
    premiseStepWithEnv (relationEnv host) language
      (inferParentBindings record rest nodes nextId root serviceStatePattern
        idPattern rulePattern parentsPattern evidencePattern conclusionPattern
        relevancePatternValue advanced parentFormulasPattern nextNodesPattern)
      (query "DCMRuleDecision" [v "id", v "serviceState", v "rule",
        v "parentFormulas", v "evidence", v "conclusion",
        DerivationCheckMachineLanguageDef.decisionFault
          faultPatternValue]) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, relationTuples, idDecoded, serviceStateDecoded, ruleDecoded,
    parentFormulasDecoded, evidenceDecoded, conclusionDecoded, ruleAccepted,
    inferParentBindings, inferIndexedBindings, inferDecodedBindings,
    inputStartBindings, query, v,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.decisionState,
    DerivationCheckMachineLanguageDef.a, matchRelationArgs,
    matchRelationArgument, matchPattern, mergeBindings,
    applyBindings, Bindings.lookup]

#print axioms infer_rule_fault_premise_empty_of_accept

theorem infer_index_fault_applyRule_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern : Pattern)
    (expectedId actualId : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern]) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.inferIndexFaultTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded, DerivationWordMachineLanguageDef.a,
    relationEnv, relationTuples, recordDecoded, nextIdDecoded, idDecoded,
    indexAccepted, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms infer_index_fault_applyRule_empty

theorem infer_index_fault_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue faultPatternValue : Pattern)
    (expectedId actualId : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (indexFaulted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.inferIndexFaultTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
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
    recordDecoded, nextIdDecoded, idDecoded, indexFaulted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms infer_index_fault_applyRule_exact

def inferIndexSuccessSourceRules : List RewriteRule := [
  DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
  DerivationCheckMachineLanguageDef.inferParentFaultTransition,
  DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
  DerivationCheckMachineLanguageDef.inferAcceptTransition
]

theorem infer_index_fault_excludes_later_rule
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue faultPatternValue : Pattern)
    (expectedId actualId : Nat)
    (membership : sourceRule ∈ inferIndexSuccessSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (indexFaulted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) = [] := by
  simp only [inferIndexSuccessSourceRules, List.mem_cons, List.mem_nil_iff,
    or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl
  · simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.outcomeFault,
      DerivationCheckMachineLanguageDef.halted,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.query,
      query, v, run, recordsCons, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, nextIdDecoded, idDecoded, indexFaulted,
      premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
      mergeBindings, applyBindings, Bindings.lookup]
  · simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.inferParentFaultTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.outcomeFault,
      DerivationCheckMachineLanguageDef.halted,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.query,
      query, v, run, recordsCons, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, nextIdDecoded, idDecoded, indexFaulted,
      premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
      mergeBindings, applyBindings, Bindings.lookup]
  · simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.outcomeFault,
      DerivationCheckMachineLanguageDef.halted,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.query,
      query, v, run, recordsCons, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, nextIdDecoded, idDecoded, indexFaulted,
      premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
      mergeBindings, applyBindings, Bindings.lookup]
  · apply applyRuleUsing_empty_of_unique_match
      (initialBindings := inputStartBindings record rest nodes nextIdPattern
        root serviceStatePattern)
    · apply generic_record_left_match_exact
      exact liftedInferAccept_left
    · rw [liftedInferAccept_premises]
      let afterDecode := inferDecodedBindings record rest nodes nextIdPattern
        root serviceStatePattern idPattern rulePattern parentsPattern
        evidencePattern conclusionPattern relevancePatternValue
      have decodeStep :
          premiseStepUsing (engineBasePremises (relationEnv host)) language
            (fun _ => [])
            (inputStartBindings record rest nodes nextIdPattern root
              serviceStatePattern)
            (query "DWMDecodeRecord" [v "record", decoded
              (DerivationCheckMachineLanguageDef.a "dcm:infer"
                [v "id", v "rule", v "parents", v "evidence",
                 v "conclusion", v "relevance"])]) = [afterDecode] := by
        simpa only [query, premiseStepUsing, engineBasePremises] using
          infer_decode_premise_exact host record rest nodes nextIdPattern root
            serviceStatePattern idPattern rulePattern parentsPattern
            evidencePattern conclusionPattern relevancePatternValue
            recordDecoded
      have indexStep :
          premiseStepUsing (engineBasePremises (relationEnv host)) language
            (fun _ => []) afterDecode
            (query "DCMIndexAdvance" [v "nextId", v "id",
              DerivationCheckMachineLanguageDef.a "dcm:decision-index"
                [v "advanced"]]) = [] := by
        simpa only [query, premiseStepUsing, engineBasePremises] using
          infer_index_accept_premise_empty_of_fault host record rest nodes
            nextIdPattern root serviceStatePattern idPattern rulePattern
            parentsPattern evidencePattern conclusionPattern
            relevancePatternValue (v "advanced") faultPatternValue
            expectedId actualId nextIdDecoded idDecoded indexFaulted
      simp only [premisesUsing, decodeStep, List.flatMap_singleton, indexStep,
        List.flatMap_nil]

#print axioms infer_index_fault_excludes_later_rule

theorem infer_relevance_fault_applyRule_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept") :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite
        DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded, DerivationWordMachineLanguageDef.a,
    relationEnv, relationTuples, recordDecoded, nextIdDecoded, idDecoded,
    relevanceDecoded, indexAccepted, relevanceAccepted, premiseStepWithEnv,
    relationQueryStep, builtinRelationTuples, matchRelationArgs,
    matchRelationArgument, matchPattern, matchArgs, mergeBindings,
    applyBindings, Bindings.lookup]

#print axioms infer_relevance_fault_applyRule_empty

theorem infer_relevance_fault_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern faultPatternValue : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceFaulted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite
        DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
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
    recordDecoded, nextIdDecoded, idDecoded, relevanceDecoded,
    indexAccepted, relevanceFaulted, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms infer_relevance_fault_applyRule_exact

def inferRelevanceSuccessSourceRules : List RewriteRule := [
  DerivationCheckMachineLanguageDef.inferParentFaultTransition,
  DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
  DerivationCheckMachineLanguageDef.inferAcceptTransition
]

theorem infer_relevance_fault_excludes_later_rule
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern faultPatternValue : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (membership : sourceRule ∈ inferRelevanceSuccessSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceFaulted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) = [] := by
  simp only [inferRelevanceSuccessSourceRules, List.mem_cons,
    List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.inferParentFaultTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.outcomeFault,
      DerivationCheckMachineLanguageDef.halted,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.query,
      query, v, run, recordsCons, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, nextIdDecoded, idDecoded, relevanceDecoded,
      indexAccepted, relevanceFaulted, premiseStepWithEnv,
      relationQueryStep, builtinRelationTuples, matchRelationArgs,
      matchRelationArgument, matchPattern, matchArgs, mergeBindings,
      applyBindings, Bindings.lookup]
  · simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.outcomeFault,
      DerivationCheckMachineLanguageDef.halted,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.query,
      query, v, run, recordsCons, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, nextIdDecoded, idDecoded, relevanceDecoded,
      indexAccepted, relevanceFaulted, premiseStepWithEnv,
      relationQueryStep, builtinRelationTuples, matchRelationArgs,
      matchRelationArgument, matchPattern, matchArgs, mergeBindings,
      applyBindings, Bindings.lookup]
  · apply applyRuleUsing_empty_of_unique_match
      (initialBindings := inputStartBindings record rest nodes nextIdPattern
        root serviceStatePattern)
    · apply generic_record_left_match_exact
      exact liftedInferAccept_left
    · rw [liftedInferAccept_premises]
      let afterDecode := inferDecodedBindings record rest nodes nextIdPattern
        root serviceStatePattern idPattern rulePattern parentsPattern
        evidencePattern conclusionPattern relevancePatternValue
      let afterIndex := inferIndexedBindings record rest nodes nextIdPattern
        root serviceStatePattern idPattern rulePattern parentsPattern
        evidencePattern conclusionPattern relevancePatternValue advancedPattern
      have decodeStep :
          premiseStepUsing (engineBasePremises (relationEnv host)) language
            (fun _ => [])
            (inputStartBindings record rest nodes nextIdPattern root
              serviceStatePattern)
            (query "DWMDecodeRecord" [v "record", decoded
              (DerivationCheckMachineLanguageDef.a "dcm:infer"
                [v "id", v "rule", v "parents", v "evidence",
                 v "conclusion", v "relevance"])]) = [afterDecode] := by
        simpa only [query, premiseStepUsing, engineBasePremises] using
          infer_decode_premise_exact host record rest nodes nextIdPattern root
            serviceStatePattern idPattern rulePattern parentsPattern
            evidencePattern conclusionPattern relevancePatternValue
            recordDecoded
      have indexStep :
          premiseStepUsing (engineBasePremises (relationEnv host)) language
            (fun _ => []) afterDecode
            (query "DCMIndexAdvance" [v "nextId", v "id",
              DerivationCheckMachineLanguageDef.a "dcm:decision-index"
                [v "advanced"]]) = [afterIndex] := by
        simpa only [query, premiseStepUsing, engineBasePremises] using
          infer_index_premise_exact host record rest nodes nextIdPattern root
            serviceStatePattern idPattern rulePattern parentsPattern
            evidencePattern conclusionPattern relevancePatternValue
            advancedPattern expectedId actualId nextIdDecoded idDecoded
            indexAccepted
      have relevanceStep :
          premiseStepUsing (engineBasePremises (relationEnv host)) language
            (fun _ => []) afterIndex
            (query "DCMRelevanceShapeDecision" [v "id", v "relevance",
              DerivationCheckMachineLanguageDef.a
                "dcm:decision-accept"]) = [] := by
        simpa only [query, premiseStepUsing, engineBasePremises] using
          infer_relevance_accept_premise_empty_of_fault host record rest nodes
            nextIdPattern root serviceStatePattern idPattern rulePattern
            parentsPattern evidencePattern conclusionPattern
            relevancePatternValue advancedPattern faultPatternValue actualId
            relevance idDecoded relevanceDecoded relevanceFaulted
      simp only [premisesUsing, decodeStep, indexStep, relevanceStep,
        List.flatMap_singleton, List.flatMap_nil]

#print axioms infer_relevance_fault_excludes_later_rule

theorem infer_parent_fault_applyRule_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodesPatternValue nextIdPattern root serviceStatePattern
      idPattern rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern parentFormulasPattern
      nextNodesPattern : Pattern)
    (nodes : List (Node Formula)) (expectedId actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (parentAccepted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.a "dcm:decision-parents"
          [parentFormulasPattern, nextNodesPattern]) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.inferParentFaultTransition)
      (run (recordsCons record rest) nodesPatternValue nextIdPattern root
        serviceStatePattern) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inferParentFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded, DerivationWordMachineLanguageDef.a,
    relationEnv, relationTuples, recordDecoded, nodesDecoded, nextIdDecoded,
    idDecoded, relevanceDecoded, parentsDecoded, indexAccepted,
    relevanceAccepted, parentAccepted, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms infer_parent_fault_applyRule_empty

theorem infer_parent_fault_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodesPatternValue nextIdPattern root serviceStatePattern
      idPattern rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern faultPatternValue : Pattern)
    (nodes : List (Node Formula)) (expectedId actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (parentFaulted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.inferParentFaultTransition)
      (run (recordsCons record rest) nodesPatternValue nextIdPattern root
        serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodesPatternValue] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inferParentFaultTransition,
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
    recordDecoded, nodesDecoded, nextIdDecoded, idDecoded, relevanceDecoded,
    parentsDecoded, indexAccepted, relevanceAccepted, parentFaulted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms infer_parent_fault_applyRule_exact

theorem infer_rule_fault_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodesPatternValue nextIdPattern root serviceStatePattern
      idPattern rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern parentFormulasPattern
      nextNodesPattern faultPatternValue : Pattern)
    (nodes : List (Node Formula)) (expectedId actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (serviceState : ServiceState) (rule : Rule)
    (parentFormulas : List Formula) (evidence : Evidence)
    (conclusion : Formula)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (ruleDecoded : decodeRule? host rulePattern = some rule)
    (parentFormulasDecoded :
      decodeFormulas? host parentFormulasPattern = some parentFormulas)
    (evidenceDecoded : decodeEvidence? host evidencePattern = some evidence)
    (conclusionDecoded :
      decodeFormula? host conclusionPattern = some conclusion)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (parentAccepted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.a "dcm:decision-parents"
          [parentFormulasPattern, nextNodesPattern])
    (ruleFaulted :
      ruleDecision host actualId serviceState rule parentFormulas evidence
          conclusion =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.inferRuleFaultTransition)
      (run (recordsCons record rest) nodesPatternValue nextIdPattern root
        serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nextNodesPattern] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
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
    recordDecoded, nodesDecoded, nextIdDecoded, idDecoded, relevanceDecoded,
    parentsDecoded, serviceStateDecoded, ruleDecoded, parentFormulasDecoded,
    evidenceDecoded, conclusionDecoded, indexAccepted, relevanceAccepted,
    parentAccepted, ruleFaulted, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms infer_rule_fault_applyRule_exact

theorem infer_accept_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodesPatternValue nextIdPattern root serviceStatePattern
      idPattern rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern parentFormulasPattern
      nextNodesPattern nextServiceStatePattern : Pattern)
    (nodes : List (Node Formula)) (expectedId actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (serviceState : ServiceState) (rule : Rule)
    (parentFormulas : List Formula) (evidence : Evidence)
    (conclusion : Formula)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (ruleDecoded : decodeRule? host rulePattern = some rule)
    (parentFormulasDecoded :
      decodeFormulas? host parentFormulasPattern = some parentFormulas)
    (evidenceDecoded : decodeEvidence? host evidencePattern = some evidence)
    (conclusionDecoded :
      decodeFormula? host conclusionPattern = some conclusion)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (parentAccepted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.a "dcm:decision-parents"
          [parentFormulasPattern, nextNodesPattern])
    (ruleAccepted :
      ruleDecision host actualId serviceState rule parentFormulas evidence
          conclusion =
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.inferAcceptTransition)
      (run (recordsCons record rest) nodesPatternValue nextIdPattern root
        serviceStatePattern) =
      [run rest
        (DerivationCheckMachineLanguageDef.nodesCons
          (DerivationCheckMachineLanguageDef.node idPattern conclusionPattern
            relevancePatternValue
            (DerivationCheckMachineLanguageDef.a "dcm:unlinked"))
          nextNodesPattern)
        advancedPattern root nextServiceStatePattern] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inferAcceptTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionState,
    DerivationCheckMachineLanguageDef.nodesCons,
    DerivationCheckMachineLanguageDef.node,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nodesDecoded, nextIdDecoded, idDecoded, relevanceDecoded,
    parentsDecoded, serviceStateDecoded, ruleDecoded, parentFormulasDecoded,
    evidenceDecoded, conclusionDecoded, indexAccepted, relevanceAccepted,
    parentAccepted, ruleAccepted, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms infer_accept_applyRule_exact

theorem infer_rule_with_parent_accept_empty_of_parent_fault
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule) (remainingPremises : List Premise)
    (record rest nodesPatternValue nextIdPattern root serviceStatePattern
      idPattern rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern faultPatternValue : Pattern)
    (nodes : List (Node Formula)) (expectedId actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (premisesExact :
      (liftRewrite sourceRule).premises =
        [query "DWMDecodeRecord" [v "record", decoded
          (DerivationCheckMachineLanguageDef.a "dcm:infer"
            [v "id", v "rule", v "parents", v "evidence",
             v "conclusion", v "relevance"])],
         query "DCMIndexAdvance" [v "nextId", v "id",
           DerivationCheckMachineLanguageDef.a "dcm:decision-index"
             [v "advanced"]],
         query "DCMRelevanceShapeDecision" [v "id", v "relevance",
           DerivationCheckMachineLanguageDef.a "dcm:decision-accept"],
         query "DCMResolveParents" [v "nodes", v "id", v "relevance",
           v "parents", DerivationCheckMachineLanguageDef.a
             "dcm:decision-parents" [v "parentFormulas", v "nextNodes"]]] ++
          remainingPremises)
    (leftExact :
      (liftRewrite sourceRule).left =
        run (recordsCons (v "record") (v "rest")) (v "nodes")
          (v "nextId") (v "root") (v "serviceState"))
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (parentFaulted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodesPatternValue nextIdPattern root
        serviceStatePattern) = [] := by
  apply applyRuleUsing_empty_of_unique_match
    (initialBindings := inputStartBindings record rest nodesPatternValue
      nextIdPattern root serviceStatePattern)
  · apply generic_record_left_match_exact
    exact leftExact
  · rw [premisesExact]
    simp only [List.cons_append, List.nil_append]
    let afterDecode := inferDecodedBindings record rest nodesPatternValue
      nextIdPattern root serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
    let afterIndex := inferIndexedBindings record rest nodesPatternValue
      nextIdPattern root serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      advancedPattern
    have decodeStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (inputStartBindings record rest nodesPatternValue nextIdPattern root
            serviceStatePattern)
          (query "DWMDecodeRecord" [v "record", decoded
            (DerivationCheckMachineLanguageDef.a "dcm:infer"
              [v "id", v "rule", v "parents", v "evidence",
               v "conclusion", v "relevance"])]) = [afterDecode] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_decode_premise_exact host record rest nodesPatternValue
          nextIdPattern root serviceStatePattern idPattern rulePattern
          parentsPattern evidencePattern conclusionPattern
          relevancePatternValue recordDecoded
    have indexStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) afterDecode
          (query "DCMIndexAdvance" [v "nextId", v "id",
            DerivationCheckMachineLanguageDef.a "dcm:decision-index"
              [v "advanced"]]) = [afterIndex] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_index_premise_exact host record rest nodesPatternValue
          nextIdPattern root serviceStatePattern idPattern rulePattern
          parentsPattern evidencePattern conclusionPattern
          relevancePatternValue advancedPattern expectedId actualId
          nextIdDecoded idDecoded indexAccepted
    have relevanceStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) afterIndex
          (query "DCMRelevanceShapeDecision" [v "id", v "relevance",
            DerivationCheckMachineLanguageDef.a
              "dcm:decision-accept"]) = [afterIndex] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_relevance_premise_exact host record rest nodesPatternValue
          nextIdPattern root serviceStatePattern idPattern rulePattern
          parentsPattern evidencePattern conclusionPattern
          relevancePatternValue advancedPattern actualId relevance idDecoded
          relevanceDecoded relevanceAccepted
    have parentStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) afterIndex
          (query "DCMResolveParents" [v "nodes", v "id", v "relevance",
            v "parents", DerivationCheckMachineLanguageDef.a
              "dcm:decision-parents"
              [v "parentFormulas", v "nextNodes"]]) = [] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_parent_accept_premise_empty_of_fault host record rest
          nodesPatternValue nextIdPattern root serviceStatePattern idPattern
          rulePattern parentsPattern evidencePattern conclusionPattern
          relevancePatternValue advancedPattern (v "parentFormulas")
          (v "nextNodes") faultPatternValue nodes actualId relevance parents
          nodesDecoded idDecoded relevanceDecoded parentsDecoded parentFaulted
    simp only [premisesUsing.eq_def, decodeStep, indexStep, relevanceStep,
      parentStep, List.flatMap_singleton, List.flatMap_nil]

#print axioms infer_rule_with_parent_accept_empty_of_parent_fault

def inferParentSuccessSourceRules : List RewriteRule := [
  DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
  DerivationCheckMachineLanguageDef.inferAcceptTransition
]

theorem infer_parent_fault_excludes_later_rule
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodesPatternValue nextIdPattern root serviceStatePattern
      idPattern rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern faultPatternValue : Pattern)
    (nodes : List (Node Formula)) (expectedId actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (membership : sourceRule ∈ inferParentSuccessSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (parentFaulted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodesPatternValue nextIdPattern root
        serviceStatePattern) = [] := by
  simp only [inferParentSuccessSourceRules, List.mem_cons, List.mem_nil_iff,
    or_false] at membership
  rcases membership with rfl | rfl
  · apply infer_rule_with_parent_accept_empty_of_parent_fault host
      DerivationCheckMachineLanguageDef.inferRuleFaultTransition
      [query "DCMRuleDecision" [v "id", v "serviceState", v "rule",
        v "parentFormulas", v "evidence", v "conclusion",
        DerivationCheckMachineLanguageDef.decisionFault (v "fault")]]
      record rest nodesPatternValue nextIdPattern root serviceStatePattern
      idPattern rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern faultPatternValue nodes expectedId
      actualId relevance parents
    · simp [liftRewrite,
        DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
        sourceInstruction?, liftPremise, liftPattern,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.decisionFault,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationCheckMachineLanguageDef.query,
        DerivationWordMachineLanguageDef.query,
        DerivationWordMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.decoded,
        DerivationWordMachineLanguageDef.a]
    · simp [liftRewrite, liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v, run, recordsCons, v,
        DerivationWordMachineLanguageDef.a]
    · exact recordDecoded
    · exact nodesDecoded
    · exact nextIdDecoded
    · exact idDecoded
    · exact relevanceDecoded
    · exact parentsDecoded
    · exact indexAccepted
    · exact relevanceAccepted
    · exact parentFaulted
  · apply infer_rule_with_parent_accept_empty_of_parent_fault host
      DerivationCheckMachineLanguageDef.inferAcceptTransition
      [query "DCMRuleDecision" [v "id", v "serviceState", v "rule",
        v "parentFormulas", v "evidence", v "conclusion",
        DerivationCheckMachineLanguageDef.decisionState
          (v "nextServiceState")]]
      record rest nodesPatternValue nextIdPattern root serviceStatePattern
      idPattern rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern faultPatternValue nodes expectedId
      actualId relevance parents
    · exact liftedInferAccept_premises
    · exact liftedInferAccept_left
    · exact recordDecoded
    · exact nodesDecoded
    · exact nextIdDecoded
    · exact idDecoded
    · exact relevanceDecoded
    · exact parentsDecoded
    · exact indexAccepted
    · exact relevanceAccepted
    · exact parentFaulted

#print axioms infer_parent_fault_excludes_later_rule

theorem infer_accept_applyRule_empty_of_rule_fault
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodesPatternValue nextIdPattern root serviceStatePattern
      idPattern rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern parentFormulasPattern
      nextNodesPattern faultPatternValue : Pattern)
    (nodes : List (Node Formula)) (expectedId actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (serviceState : ServiceState) (rule : Rule)
    (parentFormulas : List Formula) (evidence : Evidence)
    (conclusion : Formula)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (ruleDecoded : decodeRule? host rulePattern = some rule)
    (parentFormulasDecoded :
      decodeFormulas? host parentFormulasPattern = some parentFormulas)
    (evidenceDecoded : decodeEvidence? host evidencePattern = some evidence)
    (conclusionDecoded :
      decodeFormula? host conclusionPattern = some conclusion)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (parentAccepted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.a "dcm:decision-parents"
          [parentFormulasPattern, nextNodesPattern])
    (ruleFaulted :
      ruleDecision host actualId serviceState rule parentFormulas evidence
          conclusion =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.inferAcceptTransition)
      (run (recordsCons record rest) nodesPatternValue nextIdPattern root
        serviceStatePattern) = [] := by
  apply applyRuleUsing_empty_of_unique_match
    (initialBindings := inputStartBindings record rest nodesPatternValue
      nextIdPattern root serviceStatePattern)
  · apply generic_record_left_match_exact
    exact liftedInferAccept_left
  · rw [liftedInferAccept_premises]
    let afterDecode := inferDecodedBindings record rest nodesPatternValue
      nextIdPattern root serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
    let afterIndex := inferIndexedBindings record rest nodesPatternValue
      nextIdPattern root serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      advancedPattern
    let afterParents := inferParentBindings record rest nodesPatternValue
      nextIdPattern root serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      advancedPattern parentFormulasPattern nextNodesPattern
    have decodeStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (inputStartBindings record rest nodesPatternValue nextIdPattern root
            serviceStatePattern)
          (query "DWMDecodeRecord" [v "record", decoded
            (DerivationCheckMachineLanguageDef.a "dcm:infer"
              [v "id", v "rule", v "parents", v "evidence",
               v "conclusion", v "relevance"])]) = [afterDecode] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_decode_premise_exact host record rest nodesPatternValue
          nextIdPattern root serviceStatePattern idPattern rulePattern
          parentsPattern evidencePattern conclusionPattern
          relevancePatternValue recordDecoded
    have indexStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) afterDecode
          (query "DCMIndexAdvance" [v "nextId", v "id",
            DerivationCheckMachineLanguageDef.a "dcm:decision-index"
              [v "advanced"]]) = [afterIndex] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_index_premise_exact host record rest nodesPatternValue
          nextIdPattern root serviceStatePattern idPattern rulePattern
          parentsPattern evidencePattern conclusionPattern
          relevancePatternValue advancedPattern expectedId actualId
          nextIdDecoded idDecoded indexAccepted
    have relevanceStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) afterIndex
          (query "DCMRelevanceShapeDecision" [v "id", v "relevance",
            DerivationCheckMachineLanguageDef.a
              "dcm:decision-accept"]) = [afterIndex] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_relevance_premise_exact host record rest nodesPatternValue
          nextIdPattern root serviceStatePattern idPattern rulePattern
          parentsPattern evidencePattern conclusionPattern
          relevancePatternValue advancedPattern actualId relevance idDecoded
          relevanceDecoded relevanceAccepted
    have parentStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) afterIndex
          (query "DCMResolveParents" [v "nodes", v "id", v "relevance",
            v "parents", DerivationCheckMachineLanguageDef.a
              "dcm:decision-parents"
              [v "parentFormulas", v "nextNodes"]]) = [afterParents] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_parent_premise_exact host record rest nodesPatternValue
          nextIdPattern root serviceStatePattern idPattern rulePattern
          parentsPattern evidencePattern conclusionPattern
          relevancePatternValue advancedPattern parentFormulasPattern
          nextNodesPattern nodes actualId relevance parents nodesDecoded
          idDecoded relevanceDecoded parentsDecoded parentAccepted
    have ruleStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) afterParents
          (query "DCMRuleDecision" [v "id", v "serviceState", v "rule",
            v "parentFormulas", v "evidence", v "conclusion",
            DerivationCheckMachineLanguageDef.decisionState
              (v "nextServiceState")]) = [] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_rule_accept_premise_empty_of_fault host record rest
          nodesPatternValue nextIdPattern root serviceStatePattern idPattern
          rulePattern parentsPattern evidencePattern conclusionPattern
          relevancePatternValue advancedPattern parentFormulasPattern
          nextNodesPattern (v "nextServiceState") faultPatternValue actualId
          serviceState rule parentFormulas evidence conclusion idDecoded
          serviceStateDecoded ruleDecoded parentFormulasDecoded
          evidenceDecoded conclusionDecoded ruleFaulted
    simp only [premisesUsing, decodeStep, indexStep, relevanceStep, parentStep,
      ruleStep, List.flatMap_singleton, List.flatMap_nil]

#print axioms infer_accept_applyRule_empty_of_rule_fault

theorem infer_rule_fault_applyRule_empty_of_accept
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodesPatternValue nextIdPattern root serviceStatePattern
      idPattern rulePattern parentsPattern evidencePattern conclusionPattern
      relevancePatternValue advancedPattern parentFormulasPattern
      nextNodesPattern nextServiceStatePattern : Pattern)
    (nodes : List (Node Formula)) (expectedId actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (serviceState : ServiceState) (rule : Rule)
    (parentFormulas : List Formula) (evidence : Evidence)
    (conclusion : Formula)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (ruleDecoded : decodeRule? host rulePattern = some rule)
    (parentFormulasDecoded :
      decodeFormulas? host parentFormulasPattern = some parentFormulas)
    (evidenceDecoded : decodeEvidence? host evidencePattern = some evidence)
    (conclusionDecoded :
      decodeFormula? host conclusionPattern = some conclusion)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (parentAccepted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.a "dcm:decision-parents"
          [parentFormulasPattern, nextNodesPattern])
    (ruleAccepted :
      ruleDecision host actualId serviceState rule parentFormulas evidence
          conclusion =
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.inferRuleFaultTransition)
      (run (recordsCons record rest) nodesPatternValue nextIdPattern root
        serviceStatePattern) = [] := by
  apply applyRuleUsing_empty_of_unique_match
    (initialBindings := inputStartBindings record rest nodesPatternValue
      nextIdPattern root serviceStatePattern)
  · apply generic_record_left_match_exact
    exact liftedInferRuleFault_left
  · rw [liftedInferRuleFault_premises]
    let afterDecode := inferDecodedBindings record rest nodesPatternValue
      nextIdPattern root serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
    let afterIndex := inferIndexedBindings record rest nodesPatternValue
      nextIdPattern root serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      advancedPattern
    let afterParents := inferParentBindings record rest nodesPatternValue
      nextIdPattern root serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      advancedPattern parentFormulasPattern nextNodesPattern
    have decodeStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (inputStartBindings record rest nodesPatternValue nextIdPattern root
            serviceStatePattern)
          (query "DWMDecodeRecord" [v "record", decoded
            (DerivationCheckMachineLanguageDef.a "dcm:infer"
              [v "id", v "rule", v "parents", v "evidence",
               v "conclusion", v "relevance"])]) = [afterDecode] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_decode_premise_exact host record rest nodesPatternValue
          nextIdPattern root serviceStatePattern idPattern rulePattern
          parentsPattern evidencePattern conclusionPattern
          relevancePatternValue recordDecoded
    have indexStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) afterDecode
          (query "DCMIndexAdvance" [v "nextId", v "id",
            DerivationCheckMachineLanguageDef.a "dcm:decision-index"
              [v "advanced"]]) = [afterIndex] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_index_premise_exact host record rest nodesPatternValue
          nextIdPattern root serviceStatePattern idPattern rulePattern
          parentsPattern evidencePattern conclusionPattern
          relevancePatternValue advancedPattern expectedId actualId
          nextIdDecoded idDecoded indexAccepted
    have relevanceStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) afterIndex
          (query "DCMRelevanceShapeDecision" [v "id", v "relevance",
            DerivationCheckMachineLanguageDef.a
              "dcm:decision-accept"]) = [afterIndex] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_relevance_premise_exact host record rest nodesPatternValue
          nextIdPattern root serviceStatePattern idPattern rulePattern
          parentsPattern evidencePattern conclusionPattern
          relevancePatternValue advancedPattern actualId relevance idDecoded
          relevanceDecoded relevanceAccepted
    have parentStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) afterIndex
          (query "DCMResolveParents" [v "nodes", v "id", v "relevance",
            v "parents", DerivationCheckMachineLanguageDef.a
              "dcm:decision-parents"
              [v "parentFormulas", v "nextNodes"]]) = [afterParents] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_parent_premise_exact host record rest nodesPatternValue
          nextIdPattern root serviceStatePattern idPattern rulePattern
          parentsPattern evidencePattern conclusionPattern
          relevancePatternValue advancedPattern parentFormulasPattern
          nextNodesPattern nodes actualId relevance parents nodesDecoded
          idDecoded relevanceDecoded parentsDecoded parentAccepted
    have ruleStep :
        premiseStepUsing (engineBasePremises (relationEnv host)) language
          (fun _ => []) afterParents
          (query "DCMRuleDecision" [v "id", v "serviceState", v "rule",
            v "parentFormulas", v "evidence", v "conclusion",
            DerivationCheckMachineLanguageDef.decisionFault
              (v "fault")]) = [] := by
      simpa only [query, premiseStepUsing, engineBasePremises] using
        infer_rule_fault_premise_empty_of_accept host record rest
          nodesPatternValue nextIdPattern root serviceStatePattern idPattern
          rulePattern parentsPattern evidencePattern conclusionPattern
          relevancePatternValue advancedPattern parentFormulasPattern
          nextNodesPattern (v "fault") nextServiceStatePattern actualId
          serviceState rule parentFormulas evidence conclusion idDecoded
          serviceStateDecoded ruleDecoded parentFormulasDecoded
          evidenceDecoded conclusionDecoded ruleAccepted
    simp only [premisesUsing, decodeStep, indexStep, relevanceStep, parentStep,
      ruleStep, List.flatMap_singleton, List.flatMap_nil]

#print axioms infer_rule_fault_applyRule_empty_of_accept

/-- Rejection by the selected calculus service is the unique authored
successor after parent resolution has succeeded. -/
theorem infer_rule_fault_rewriteAt_exact_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodesPatternValue nextIdPattern serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      advancedPattern parentFormulasPattern nextNodesPattern
      faultPatternValue : Pattern)
    (nodes : List (Node Formula)) (expectedId actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (serviceState : ServiceState) (rule : Rule)
    (parentFormulas : List Formula) (evidence : Evidence)
    (conclusion : Formula)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (ruleDecoded : decodeRule? host rulePattern = some rule)
    (parentFormulasDecoded :
      decodeFormulas? host parentFormulasPattern = some parentFormulas)
    (evidenceDecoded : decodeEvidence? host evidencePattern = some evidence)
    (conclusionDecoded :
      decodeFormula? host conclusionPattern = some conclusion)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (parentAccepted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.a "dcm:decision-parents"
          [parentFormulasPattern, nextNodesPattern])
    (ruleFaulted :
      ruleDecision host actualId serviceState rule parentFormulas evidence
          conclusion =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodesPatternValue nextIdPattern
        rootPatternValue serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nextNodesPattern] := by
  rw [infer_record_rewriteAt_partition_encoded_root host rootState
    rootPatternValue record remainingRecords nodesPatternValue nextIdPattern
    serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
    conclusionPattern relevancePatternValue rootEncoded recordDecoded]
  simp only [inferRows, List.flatMap_cons, List.flatMap_nil]
  rw [infer_index_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    expectedId actualId recordDecoded nextIdDecoded idDecoded indexAccepted]
  rw [infer_relevance_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    expectedId actualId relevance recordDecoded nextIdDecoded idDecoded
    relevanceDecoded indexAccepted relevanceAccepted]
  rw [infer_parent_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    parentFormulasPattern nextNodesPattern nodes expectedId actualId relevance
    parents recordDecoded nodesDecoded nextIdDecoded idDecoded
    relevanceDecoded parentsDecoded indexAccepted relevanceAccepted
    parentAccepted]
  rw [infer_rule_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    parentFormulasPattern nextNodesPattern faultPatternValue nodes expectedId
    actualId relevance parents serviceState rule parentFormulas evidence
    conclusion recordDecoded nodesDecoded nextIdDecoded idDecoded
    relevanceDecoded parentsDecoded serviceStateDecoded ruleDecoded
    parentFormulasDecoded evidenceDecoded conclusionDecoded indexAccepted
    relevanceAccepted parentAccepted ruleFaulted]
  rw [infer_accept_applyRule_empty_of_rule_fault host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    parentFormulasPattern nextNodesPattern faultPatternValue nodes expectedId
    actualId relevance parents serviceState rule parentFormulas evidence
    conclusion recordDecoded nodesDecoded nextIdDecoded idDecoded
    relevanceDecoded parentsDecoded serviceStateDecoded ruleDecoded
    parentFormulasDecoded evidenceDecoded conclusionDecoded indexAccepted
    relevanceAccepted parentAccepted ruleFaulted]
  simp

#print axioms infer_rule_fault_rewriteAt_exact_encoded_root

/-- A successful calculus service result is the unique authored successor and
preserves the encoded root while advancing the node and service frontiers. -/
theorem infer_accept_rewriteAt_exact_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodesPatternValue nextIdPattern serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      advancedPattern parentFormulasPattern nextNodesPattern
      nextServiceStatePattern : Pattern)
    (nodes : List (Node Formula)) (expectedId actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (serviceState : ServiceState) (rule : Rule)
    (parentFormulas : List Formula) (evidence : Evidence)
    (conclusion : Formula)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (ruleDecoded : decodeRule? host rulePattern = some rule)
    (parentFormulasDecoded :
      decodeFormulas? host parentFormulasPattern = some parentFormulas)
    (evidenceDecoded : decodeEvidence? host evidencePattern = some evidence)
    (conclusionDecoded :
      decodeFormula? host conclusionPattern = some conclusion)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (parentAccepted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.a "dcm:decision-parents"
          [parentFormulasPattern, nextNodesPattern])
    (ruleAccepted :
      ruleDecision host actualId serviceState rule parentFormulas evidence
          conclusion =
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodesPatternValue nextIdPattern
        rootPatternValue serviceStatePattern) =
      [run (recordsPattern remainingRecords)
        (DerivationCheckMachineLanguageDef.nodesCons
          (DerivationCheckMachineLanguageDef.node idPattern conclusionPattern
            relevancePatternValue
            (DerivationCheckMachineLanguageDef.a "dcm:unlinked"))
          nextNodesPattern)
        advancedPattern rootPatternValue nextServiceStatePattern] := by
  rw [infer_record_rewriteAt_partition_encoded_root host rootState
    rootPatternValue record remainingRecords nodesPatternValue nextIdPattern
    serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
    conclusionPattern relevancePatternValue rootEncoded recordDecoded]
  simp only [inferRows, List.flatMap_cons, List.flatMap_nil]
  rw [infer_index_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    expectedId actualId recordDecoded nextIdDecoded idDecoded indexAccepted]
  rw [infer_relevance_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    expectedId actualId relevance recordDecoded nextIdDecoded idDecoded
    relevanceDecoded indexAccepted relevanceAccepted]
  rw [infer_parent_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    parentFormulasPattern nextNodesPattern nodes expectedId actualId relevance
    parents recordDecoded nodesDecoded nextIdDecoded idDecoded
    relevanceDecoded parentsDecoded indexAccepted relevanceAccepted
    parentAccepted]
  rw [infer_rule_fault_applyRule_empty_of_accept host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    parentFormulasPattern nextNodesPattern nextServiceStatePattern nodes
    expectedId actualId relevance parents serviceState rule parentFormulas
    evidence conclusion recordDecoded nodesDecoded nextIdDecoded idDecoded
    relevanceDecoded parentsDecoded serviceStateDecoded ruleDecoded
    parentFormulasDecoded evidenceDecoded conclusionDecoded indexAccepted
    relevanceAccepted parentAccepted ruleAccepted]
  rw [infer_accept_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    parentFormulasPattern nextNodesPattern nextServiceStatePattern nodes
    expectedId actualId relevance parents serviceState rule parentFormulas
    evidence conclusion recordDecoded nodesDecoded nextIdDecoded idDecoded
    relevanceDecoded parentsDecoded serviceStateDecoded ruleDecoded
    parentFormulasDecoded evidenceDecoded conclusionDecoded indexAccepted
    relevanceAccepted parentAccepted ruleAccepted]
  simp

#print axioms infer_accept_rewriteAt_exact_encoded_root

/-- Failure while resolving an infer record's declared parents is the unique
authored successor, independently of the encoded root state. -/
theorem infer_parent_fault_rewriteAt_exact_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodesPatternValue nextIdPattern serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      advancedPattern faultPatternValue : Pattern)
    (nodes : List (Node Formula)) (expectedId actualId : Nat)
    (relevance : RelevanceWitness) (parents : List Nat)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nodesDecoded : decodeNodes? host nodesPatternValue = some nodes)
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (parentsDecoded : decodeParentIds? parentsPattern = some parents)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (parentFaulted :
      parentDecision host nodes actualId relevance parents =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodesPatternValue nextIdPattern
        rootPatternValue serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodesPatternValue] := by
  rw [infer_record_rewriteAt_partition_encoded_root host rootState
    rootPatternValue record remainingRecords nodesPatternValue nextIdPattern
    serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
    conclusionPattern relevancePatternValue rootEncoded recordDecoded]
  simp only [inferRows, List.flatMap_cons, List.flatMap_nil]
  rw [infer_index_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    expectedId actualId recordDecoded nextIdDecoded idDecoded indexAccepted]
  rw [infer_relevance_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    expectedId actualId relevance recordDecoded nextIdDecoded idDecoded
    relevanceDecoded indexAccepted relevanceAccepted]
  rw [infer_parent_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodesPatternValue nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    faultPatternValue nodes expectedId actualId relevance parents
    recordDecoded nodesDecoded nextIdDecoded idDecoded relevanceDecoded
    parentsDecoded indexAccepted relevanceAccepted parentFaulted]
  rw [infer_parent_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodesPatternValue
    nextIdPattern rootPatternValue serviceStatePattern idPattern rulePattern
    parentsPattern evidencePattern conclusionPattern relevancePatternValue
    advancedPattern faultPatternValue nodes expectedId actualId relevance
    parents (by simp [inferParentSuccessSourceRules]) recordDecoded
    nodesDecoded nextIdDecoded idDecoded relevanceDecoded parentsDecoded
    indexAccepted relevanceAccepted parentFaulted]
  rw [infer_parent_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodesPatternValue
    nextIdPattern rootPatternValue serviceStatePattern idPattern rulePattern
    parentsPattern evidencePattern conclusionPattern relevancePatternValue
    advancedPattern faultPatternValue nodes expectedId actualId relevance
    parents (by simp [inferParentSuccessSourceRules]) recordDecoded
    nodesDecoded nextIdDecoded idDecoded relevanceDecoded parentsDecoded
    indexAccepted relevanceAccepted parentFaulted]
  simp

#print axioms infer_parent_fault_rewriteAt_exact_encoded_root

theorem infer_relevance_fault_rewriteAt_exact_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      advancedPattern faultPatternValue : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceFaulted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodes nextIdPattern
        rootPatternValue serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  rw [infer_record_rewriteAt_partition_encoded_root host rootState
    rootPatternValue record remainingRecords nodes nextIdPattern
    serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
    conclusionPattern relevancePatternValue rootEncoded recordDecoded]
  simp only [inferRows, List.flatMap_cons, List.flatMap_nil]
  rw [infer_index_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
    conclusionPattern relevancePatternValue advancedPattern expectedId
    actualId recordDecoded nextIdDecoded idDecoded indexAccepted]
  rw [infer_relevance_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
    conclusionPattern relevancePatternValue advancedPattern faultPatternValue
    expectedId actualId relevance recordDecoded nextIdDecoded idDecoded
    relevanceDecoded indexAccepted relevanceFaulted]
  rw [infer_relevance_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inferParentFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    faultPatternValue expectedId actualId relevance
    (by simp [inferRelevanceSuccessSourceRules]) recordDecoded nextIdDecoded
    idDecoded relevanceDecoded indexAccepted relevanceFaulted]
  rw [infer_relevance_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    faultPatternValue expectedId actualId relevance
    (by simp [inferRelevanceSuccessSourceRules]) recordDecoded nextIdDecoded
    idDecoded relevanceDecoded indexAccepted relevanceFaulted]
  rw [infer_relevance_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue advancedPattern
    faultPatternValue expectedId actualId relevance
    (by simp [inferRelevanceSuccessSourceRules]) recordDecoded nextIdDecoded
    idDecoded relevanceDecoded indexAccepted relevanceFaulted]
  simp

#print axioms infer_relevance_fault_rewriteAt_exact_encoded_root

theorem infer_index_fault_rewriteAt_exact_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern rulePattern
      parentsPattern evidencePattern conclusionPattern relevancePatternValue
      faultPatternValue : Pattern)
    (expectedId actualId : Nat)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [idPattern, rulePattern, parentsPattern, evidencePattern,
           conclusionPattern, relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (indexFaulted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodes nextIdPattern
        rootPatternValue serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  rw [infer_record_rewriteAt_partition_encoded_root host rootState
    rootPatternValue record remainingRecords nodes nextIdPattern
    serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
    conclusionPattern relevancePatternValue rootEncoded recordDecoded]
  simp only [inferRows, List.flatMap_cons, List.flatMap_nil]
  rw [infer_index_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern rulePattern parentsPattern evidencePattern
    conclusionPattern relevancePatternValue faultPatternValue expectedId
    actualId recordDecoded nextIdDecoded idDecoded indexFaulted]
  rw [infer_index_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue faultPatternValue
    expectedId actualId (by simp [inferIndexSuccessSourceRules]) recordDecoded
    nextIdDecoded idDecoded indexFaulted]
  rw [infer_index_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inferParentFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue faultPatternValue
    expectedId actualId (by simp [inferIndexSuccessSourceRules]) recordDecoded
    nextIdDecoded idDecoded indexFaulted]
  rw [infer_index_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue faultPatternValue
    expectedId actualId (by simp [inferIndexSuccessSourceRules]) recordDecoded
    nextIdDecoded idDecoded indexFaulted]
  rw [infer_index_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern rulePattern parentsPattern
    evidencePattern conclusionPattern relevancePatternValue faultPatternValue
    expectedId actualId (by simp [inferIndexSuccessSourceRules]) recordDecoded
    nextIdDecoded idDecoded indexFaulted]
  simp

#print axioms infer_index_fault_rewriteAt_exact_encoded_root

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance] in
theorem infer_source_encodes_running
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (expectedId actualId : Nat) (rule : Rule) (parents : List Nat)
    (evidence : Evidence) (conclusion : Formula)
    (relevance : RelevanceWitness) (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.infer actualId rule parents evidence conclusion relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .infer actualId rule parents evidence conclusion
        relevance :: remainingInstructions
      nodes := oldNodes
      nextId := expectedId
      root? := rootState
      serviceState := serviceState
    }
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern expectedId) rootPatternValue
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

#print axioms infer_source_encodes_running

/-- A bad inferred node id commutes for every canonically encoded root state;
no relevance, parent, or calculus service is consulted. -/
theorem infer_index_fault_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (expectedId actualId : Nat) (rule : Rule) (parents : List Nat)
    (evidence : Evidence) (conclusion : Formula)
    (relevance : RelevanceWitness) (serviceState : ServiceState)
    (rulePattern evidencePattern conclusionPattern serviceStatePattern
      nodesPatternValue : Pattern)
    (idsDiffer : actualId ≠ expectedId)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.infer actualId rule parents evidence conclusion relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (ruleEncoded : encodeRule? host rule = some rulePattern)
    (evidenceEncoded : encodeEvidence? host evidence = some evidencePattern)
    (conclusionEncoded :
      encodeFormula? host conclusion = some conclusionPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .infer actualId rule parents evidence conclusion
        relevance :: remainingInstructions
      nodes := oldNodes
      nextId := expectedId
      root? := rootState
      serviceState := serviceState
    }
    let failure := Fault.badNodeId expectedId actualId
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern expectedId) rootPatternValue
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
      instructionPattern? host
          (.infer actualId rule parents evidence conclusion relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern actualId, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]) := by
    simp [instructionPattern?, ruleEncoded, evidenceEncoded,
      conclusionEncoded, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern actualId, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern actualId, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.infer actualId rule parents evidence conclusion relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [indexPattern actualId, rulePattern, parentIdsPattern parents,
         evidencePattern, conclusionPattern, relevancePattern relevance])
      recordInstructionDecoded instructionPatternEncoded
  have expectedIdDiffers : expectedId ≠ actualId := Ne.symm idsDiffer
  have indexFaulted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.decisionFault
          (faultPattern (.badNodeId expectedId actualId)) := by
    simp [indexDecision, expectedIdDiffers, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact infer_source_encodes_running host rootState rootPatternValue record
      remainingRecords remainingInstructions oldNodes expectedId actualId rule
      parents evidence conclusion relevance serviceState serviceStatePattern
      nodesPatternValue recordInstructionDecoded remainingDecoded rootEncoded
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault, idsDiffer]
  constructor
  · exact infer_index_fault_rewriteAt_exact_encoded_root host rootState
      rootPatternValue record remainingRecords nodesPatternValue
      (indexPattern expectedId) serviceStatePattern (indexPattern actualId)
      rulePattern (parentIdsPattern parents) evidencePattern conclusionPattern
      (relevancePattern relevance)
      (faultPattern (.badNodeId expectedId actualId)) expectedId actualId
      rootEncoded recordDecoded (decodeIndex_indexPattern expectedId)
      (decodeIndex_indexPattern actualId) indexFaulted
  · exact fault_target_encodes_halted host remainingRecords oldNodes
      (.badNodeId expectedId actualId) nodesPatternValue nodesEncoded

#print axioms infer_index_fault_semantic_square_encoded_root

/-- A malformed infer relevance witness commutes for every canonically encoded
root state and stops before parent resolution or calculus service dispatch. -/
theorem infer_relevance_fault_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (id : Nat) (rule : Rule) (parents : List Nat) (evidence : Evidence)
    (conclusion : Formula) (relevance : RelevanceWitness)
    (serviceState : ServiceState)
    (rulePattern evidencePattern conclusionPattern serviceStatePattern
      nodesPatternValue : Pattern)
    (relevanceMalformed : relevance.wellFormedFor id = false)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.infer id rule parents evidence conclusion relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (ruleEncoded : encodeRule? host rule = some rulePattern)
    (evidenceEncoded : encodeEvidence? host evidence = some evidencePattern)
    (conclusionEncoded :
      encodeFormula? host conclusion = some conclusionPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .infer id rule parents evidence conclusion relevance ::
        remainingInstructions
      nodes := oldNodes
      nextId := id
      root? := rootState
      serviceState := serviceState
    }
    let failure := Fault.malformedRelevance id
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern id) rootPatternValue serviceStatePattern
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
      instructionPattern? host
          (.infer id rule parents evidence conclusion relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern id, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]) := by
    simp [instructionPattern?, ruleEncoded, evidenceEncoded,
      conclusionEncoded, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern id, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern id, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.infer id rule parents evidence conclusion relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [indexPattern id, rulePattern, parentIdsPattern parents,
         evidencePattern, conclusionPattern, relevancePattern relevance])
      recordInstructionDecoded instructionPatternEncoded
  have indexAccepted :
      indexDecision id id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [indexPattern (id + 1)] := by
    simp [indexDecision, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have relevanceFaulted :
      relevanceDecision id relevance =
        DerivationCheckMachineLanguageDef.decisionFault
          (faultPattern (.malformedRelevance id)) := by
    simp [relevanceDecision, relevanceMalformed, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact infer_source_encodes_running host rootState rootPatternValue record
      remainingRecords remainingInstructions oldNodes id id rule parents
      evidence conclusion relevance serviceState serviceStatePattern
      nodesPatternValue recordInstructionDecoded remainingDecoded rootEncoded
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault,
      relevanceMalformed]
  constructor
  · exact infer_relevance_fault_rewriteAt_exact_encoded_root host
      rootState rootPatternValue record remainingRecords nodesPatternValue
      (indexPattern id) serviceStatePattern (indexPattern id) rulePattern
      (parentIdsPattern parents) evidencePattern conclusionPattern
      (relevancePattern relevance) (indexPattern (id + 1))
      (faultPattern (.malformedRelevance id)) id id relevance rootEncoded
      recordDecoded (decodeIndex_indexPattern id)
      (decodeIndex_indexPattern id) (decodeRelevance_relevancePattern relevance)
      indexAccepted relevanceFaulted
  · exact fault_target_encodes_halted host remainingRecords oldNodes
      (.malformedRelevance id) nodesPatternValue nodesEncoded

#print axioms infer_relevance_fault_semantic_square_encoded_root

theorem decodeParentIds_parentIdsPattern (parents : List Nat) :
    decodeParentIds? (parentIdsPattern parents) = some parents := by
  induction parents with
  | nil => rfl
  | cons parent parents induction =>
      simp only [parentIdsPattern, DerivationWordMachineRelationEnv.a,
        decodeParentIds?, decodeIndex_indexPattern, induction]
      rfl

#print axioms decodeParentIds_parentIdsPattern

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance]
  [DecidableEq Obligation] [DecidableEq ServiceState] in
theorem decodeFormulas_formulasPattern
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (formulas : List Formula) (pattern : Pattern)
    (encoded : formulasPattern? host formulas = some pattern) :
    decodeFormulas? host pattern = some formulas := by
  induction formulas generalizing pattern with
  | nil =>
      simp [formulasPattern?] at encoded
      subst pattern
      rfl
  | cons formula formulas induction =>
      unfold formulasPattern? at encoded
      cases formulaEncoded : encodeFormula? host formula with
      | none => simp [formulaEncoded] at encoded
      | some formulaPatternValue =>
          cases formulasEncoded : formulasPattern? host formulas with
          | none => simp [formulaEncoded, formulasEncoded] at encoded
          | some formulasPatternValue =>
              simp [formulaEncoded, formulasEncoded] at encoded
              subst pattern
              simp [decodeFormulas?,
                decodeFormula_encodeFormula host formula formulaPatternValue
                  formulaEncoded,
                induction formulasPatternValue formulasEncoded,
                DerivationWordMachineRelationEnv.a]

#print axioms decodeFormulas_formulasPattern

/-- A parent-resolution failure commutes for every canonically encoded root
state and prevents every later calculus-service row from firing. -/
theorem infer_parent_fault_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (id : Nat) (rule : Rule) (parents : List Nat) (evidence : Evidence)
    (conclusion : Formula) (relevance : RelevanceWitness)
    (serviceState : ServiceState) (failure : Fault)
    (rulePattern evidencePattern conclusionPattern serviceStatePattern
      nodesPatternValue : Pattern)
    (relevanceWellFormed : relevance.wellFormedFor id = true)
    (parentResolutionFault :
      resolveParents? id relevance.distance parents oldNodes = .error failure)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.infer id rule parents evidence conclusion relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (ruleEncoded : encodeRule? host rule = some rulePattern)
    (evidenceEncoded : encodeEvidence? host evidence = some evidencePattern)
    (conclusionEncoded :
      encodeFormula? host conclusion = some conclusionPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .infer id rule parents evidence conclusion relevance ::
        remainingInstructions
      nodes := oldNodes
      nextId := id
      root? := rootState
      serviceState := serviceState
    }
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern id) rootPatternValue serviceStatePattern
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
      instructionPattern? host
          (.infer id rule parents evidence conclusion relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern id, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]) := by
    simp [instructionPattern?, ruleEncoded, evidenceEncoded,
      conclusionEncoded, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern id, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern id, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.infer id rule parents evidence conclusion relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [indexPattern id, rulePattern, parentIdsPattern parents,
         evidencePattern, conclusionPattern, relevancePattern relevance])
      recordInstructionDecoded instructionPatternEncoded
  have nodesDecoded : decodeNodes? host nodesPatternValue = some oldNodes :=
    decodeNodes_nodesPattern host oldNodes nodesPatternValue nodesEncoded
  have indexAccepted :
      indexDecision id id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [indexPattern (id + 1)] := by
    simp [indexDecision, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have relevanceAccepted :
      relevanceDecision id relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept" := by
    simp [relevanceDecision, relevanceWellFormed,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have parentFaulted :
      parentDecision host oldNodes id relevance parents =
        DerivationCheckMachineLanguageDef.decisionFault
          (faultPattern failure) := by
    simp [parentDecision, parentResolutionFault, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact infer_source_encodes_running host rootState rootPatternValue record
      remainingRecords remainingInstructions oldNodes id id rule parents
      evidence conclusion relevance serviceState serviceStatePattern
      nodesPatternValue recordInstructionDecoded remainingDecoded rootEncoded
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault,
      relevanceWellFormed, parentResolutionFault]
  constructor
  · exact infer_parent_fault_rewriteAt_exact_encoded_root host rootState
      rootPatternValue record remainingRecords nodesPatternValue
      (indexPattern id) serviceStatePattern (indexPattern id) rulePattern
      (parentIdsPattern parents) evidencePattern conclusionPattern
      (relevancePattern relevance) (indexPattern (id + 1))
      (faultPattern failure) oldNodes id id relevance parents rootEncoded
      recordDecoded nodesDecoded (decodeIndex_indexPattern id)
      (decodeIndex_indexPattern id) (decodeRelevance_relevancePattern relevance)
      (decodeParentIds_parentIdsPattern parents) indexAccepted
      relevanceAccepted parentFaulted
  · exact fault_target_encodes_halted host remainingRecords oldNodes failure
      nodesPatternValue nodesEncoded

#print axioms infer_parent_fault_semantic_square_encoded_root

/-- A calculus service rejection commutes exactly after successful parent
resolution; the word machine itself remains calculus-neutral. -/
theorem infer_rule_fault_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes nextNodes : List (Node Formula))
    (id : Nat) (rule : Rule) (parents : List Nat) (evidence : Evidence)
    (conclusion : Formula) (relevance : RelevanceWitness)
    (serviceState : ServiceState) (parentFormulas : List Formula)
    (rulePattern evidencePattern conclusionPattern serviceStatePattern
      nodesPatternValue parentFormulasPattern nextNodesPattern : Pattern)
    (relevanceWellFormed : relevance.wellFormedFor id = true)
    (parentResolution :
      resolveParents? id relevance.distance parents oldNodes =
        .ok (parentFormulas, nextNodes))
    (ruleRejected :
      host.services.infer serviceState rule parentFormulas evidence
        conclusion = none)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.infer id rule parents evidence conclusion relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (ruleEncoded : encodeRule? host rule = some rulePattern)
    (evidenceEncoded : encodeEvidence? host evidence = some evidencePattern)
    (conclusionEncoded :
      encodeFormula? host conclusion = some conclusionPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (parentFormulasEncoded :
      formulasPattern? host parentFormulas = some parentFormulasPattern)
    (nextNodesEncoded :
      nodesPattern? host nextNodes = some nextNodesPattern)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .infer id rule parents evidence conclusion relevance ::
        remainingInstructions
      nodes := oldNodes
      nextId := id
      root? := rootState
      serviceState := serviceState
    }
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern id) rootPatternValue serviceStatePattern
    let failure := Fault.ruleRejected id
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault (faultPattern failure))
      nextNodesPattern
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault failure)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.halted (.fault failure))
        target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host
          (.infer id rule parents evidence conclusion relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern id, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]) := by
    simp [instructionPattern?, ruleEncoded, evidenceEncoded,
      conclusionEncoded, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern id, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern id, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.infer id rule parents evidence conclusion relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [indexPattern id, rulePattern, parentIdsPattern parents,
         evidencePattern, conclusionPattern, relevancePattern relevance])
      recordInstructionDecoded instructionPatternEncoded
  have nodesDecoded : decodeNodes? host nodesPatternValue = some oldNodes :=
    decodeNodes_nodesPattern host oldNodes nodesPatternValue nodesEncoded
  have serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState :=
    decodeServiceState_encodeServiceState host serviceState serviceStatePattern
      serviceStateEncoded
  have ruleDecoded : decodeRule? host rulePattern = some rule :=
    decodeRule_encodeRule host rule rulePattern ruleEncoded
  have parentFormulasDecoded :
      decodeFormulas? host parentFormulasPattern = some parentFormulas :=
    decodeFormulas_formulasPattern host parentFormulas parentFormulasPattern
      parentFormulasEncoded
  have evidenceDecoded :
      decodeEvidence? host evidencePattern = some evidence :=
    decodeEvidence_encodeEvidence host evidence evidencePattern
      evidenceEncoded
  have conclusionDecoded :
      decodeFormula? host conclusionPattern = some conclusion :=
    decodeFormula_encodeFormula host conclusion conclusionPattern
      conclusionEncoded
  have indexAccepted :
      indexDecision id id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [indexPattern (id + 1)] := by
    simp [indexDecision, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have relevanceAccepted :
      relevanceDecision id relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept" := by
    simp [relevanceDecision, relevanceWellFormed,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have parentAccepted :
      parentDecision host oldNodes id relevance parents =
        DerivationCheckMachineLanguageDef.a "dcm:decision-parents"
          [parentFormulasPattern, nextNodesPattern] := by
    simp [parentDecision, parentResolution, parentFormulasEncoded,
      nextNodesEncoded, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have ruleFaulted :
      ruleDecision host id serviceState rule parentFormulas evidence
          conclusion =
        DerivationCheckMachineLanguageDef.decisionFault
          (faultPattern (.ruleRejected id)) := by
    simp [ruleDecision, ruleRejected, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact infer_source_encodes_running host rootState rootPatternValue record
      remainingRecords remainingInstructions oldNodes id id rule parents
      evidence conclusion relevance serviceState serviceStatePattern
      nodesPatternValue recordInstructionDecoded remainingDecoded rootEncoded
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault,
      relevanceWellFormed, parentResolution, ruleRejected]
  constructor
  · exact infer_rule_fault_rewriteAt_exact_encoded_root host rootState
      rootPatternValue record remainingRecords nodesPatternValue
      (indexPattern id) serviceStatePattern (indexPattern id) rulePattern
      (parentIdsPattern parents) evidencePattern conclusionPattern
      (relevancePattern relevance) (indexPattern (id + 1))
      parentFormulasPattern nextNodesPattern (faultPattern (.ruleRejected id))
      oldNodes id id relevance parents serviceState rule parentFormulas
      evidence conclusion rootEncoded recordDecoded nodesDecoded
      (decodeIndex_indexPattern id) (decodeIndex_indexPattern id)
      (decodeRelevance_relevancePattern relevance)
      (decodeParentIds_parentIdsPattern parents) serviceStateDecoded
      ruleDecoded parentFormulasDecoded evidenceDecoded conclusionDecoded
      indexAccepted relevanceAccepted parentAccepted ruleFaulted
  · exact fault_target_encodes_halted host remainingRecords nextNodes
      (.ruleRejected id) nextNodesPattern nextNodesEncoded

#print axioms infer_rule_fault_semantic_square_encoded_root

/-- A successful calculus service step commutes exactly with the authored
infer-accept row and its canonically encoded running successor. -/
theorem infer_accept_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes nextNodes : List (Node Formula))
    (id : Nat) (rule : Rule) (parents : List Nat) (evidence : Evidence)
    (conclusion : Formula) (relevance : RelevanceWitness)
    (serviceState nextServiceState : ServiceState)
    (parentFormulas : List Formula)
    (rulePattern evidencePattern conclusionPattern serviceStatePattern
      nextServiceStatePattern nodesPatternValue parentFormulasPattern
      nextNodesPattern : Pattern)
    (relevanceWellFormed : relevance.wellFormedFor id = true)
    (parentResolution :
      resolveParents? id relevance.distance parents oldNodes =
        .ok (parentFormulas, nextNodes))
    (serviceAccepted :
      host.services.infer serviceState rule parentFormulas evidence
        conclusion = some nextServiceState)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.infer id rule parents evidence conclusion relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (ruleEncoded : encodeRule? host rule = some rulePattern)
    (evidenceEncoded : encodeEvidence? host evidence = some evidencePattern)
    (conclusionEncoded :
      encodeFormula? host conclusion = some conclusionPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nextServiceStateEncoded :
      encodeServiceState? host nextServiceState =
        some nextServiceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (parentFormulasEncoded :
      formulasPattern? host parentFormulas = some parentFormulasPattern)
    (nextNodesEncoded :
      nodesPattern? host nextNodes = some nextNodesPattern)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .infer id rule parents evidence conclusion relevance ::
        remainingInstructions
      nodes := oldNodes
      nextId := id
      root? := rootState
      serviceState := serviceState
    }
    let after :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := remainingInstructions
      nodes := { id, formula := conclusion, relevance } :: nextNodes
      nextId := id + 1
      root? := rootState
      serviceState := nextServiceState
    }
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern id) rootPatternValue serviceStatePattern
    let target := run (recordsPattern remainingRecords)
      (DerivationCheckMachineLanguageDef.nodesCons
        (DerivationCheckMachineLanguageDef.node (indexPattern id)
          conclusionPattern (relevancePattern relevance)
          (DerivationCheckMachineLanguageDef.a "dcm:unlinked"))
        nextNodesPattern)
      (indexPattern (id + 1)) rootPatternValue nextServiceStatePattern
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) = some (.running after) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.running after) target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host
          (.infer id rule parents evidence conclusion relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern id, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]) := by
    simp [instructionPattern?, ruleEncoded, evidenceEncoded,
      conclusionEncoded, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern id, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:infer"
          [indexPattern id, rulePattern, parentIdsPattern parents,
           evidencePattern, conclusionPattern, relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.infer id rule parents evidence conclusion relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [indexPattern id, rulePattern, parentIdsPattern parents,
         evidencePattern, conclusionPattern, relevancePattern relevance])
      recordInstructionDecoded instructionPatternEncoded
  have nodesDecoded : decodeNodes? host nodesPatternValue = some oldNodes :=
    decodeNodes_nodesPattern host oldNodes nodesPatternValue nodesEncoded
  have serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState :=
    decodeServiceState_encodeServiceState host serviceState serviceStatePattern
      serviceStateEncoded
  have ruleDecoded : decodeRule? host rulePattern = some rule :=
    decodeRule_encodeRule host rule rulePattern ruleEncoded
  have parentFormulasDecoded :
      decodeFormulas? host parentFormulasPattern = some parentFormulas :=
    decodeFormulas_formulasPattern host parentFormulas parentFormulasPattern
      parentFormulasEncoded
  have evidenceDecoded :
      decodeEvidence? host evidencePattern = some evidence :=
    decodeEvidence_encodeEvidence host evidence evidencePattern
      evidenceEncoded
  have conclusionDecoded :
      decodeFormula? host conclusionPattern = some conclusion :=
    decodeFormula_encodeFormula host conclusion conclusionPattern
      conclusionEncoded
  have indexAccepted :
      indexDecision id id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [indexPattern (id + 1)] := by
    simp [indexDecision, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have relevanceAccepted :
      relevanceDecision id relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept" := by
    simp [relevanceDecision, relevanceWellFormed,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have parentAccepted :
      parentDecision host oldNodes id relevance parents =
        DerivationCheckMachineLanguageDef.a "dcm:decision-parents"
          [parentFormulasPattern, nextNodesPattern] := by
    simp [parentDecision, parentResolution, parentFormulasEncoded,
      nextNodesEncoded, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have ruleAccepted :
      ruleDecision host id serviceState rule parentFormulas evidence
          conclusion =
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern := by
    simp [ruleDecision, serviceAccepted, nextServiceStateEncoded,
      DerivationCheckMachineLanguageDef.decisionState,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact infer_source_encodes_running host rootState rootPatternValue record
      remainingRecords remainingInstructions oldNodes id id rule parents
      evidence conclusion relevance serviceState serviceStatePattern
      nodesPatternValue recordInstructionDecoded remainingDecoded rootEncoded
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, relevanceWellFormed,
      parentResolution, serviceAccepted]
  constructor
  · exact infer_accept_rewriteAt_exact_encoded_root host rootState
      rootPatternValue record remainingRecords nodesPatternValue
      (indexPattern id) serviceStatePattern (indexPattern id) rulePattern
      (parentIdsPattern parents) evidencePattern conclusionPattern
      (relevancePattern relevance) (indexPattern (id + 1))
      parentFormulasPattern nextNodesPattern nextServiceStatePattern oldNodes
      id id relevance parents serviceState rule parentFormulas evidence
      conclusion rootEncoded recordDecoded nodesDecoded
      (decodeIndex_indexPattern id) (decodeIndex_indexPattern id)
      (decodeRelevance_relevancePattern relevance)
      (decodeParentIds_parentIdsPattern parents) serviceStateDecoded
      ruleDecoded parentFormulasDecoded evidenceDecoded conclusionDecoded
      indexAccepted relevanceAccepted parentAccepted ruleAccepted
  · constructor
    · exact remainingDecoded
    · simp [runningPattern?, nodesPattern?, nodePattern?, conclusionEncoded,
        nextNodesEncoded, nextServiceStateEncoded, rootEncoded, linkPattern,
        DerivationCheckMachineLanguageDef.nodesCons,
        DerivationCheckMachineLanguageDef.node,
        DerivationCheckMachineLanguageDef.a,
        DerivationWordMachineRelationEnv.a]

#print axioms infer_accept_semantic_square_encoded_root

/-- Every representable infer instruction takes exactly one authored target
step matching the deterministic semantic-machine step.  The only additional
hypotheses are local codec-totality obligations for values produced after
parent resolution or calculus-service acceptance; no branch evidence is
stored in the target configuration. -/
theorem infer_one_record_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (expectedId actualId : Nat) (rule : Rule) (parents : List Nat)
    (evidence : Evidence) (conclusion : Formula)
    (relevance : RelevanceWitness) (serviceState : ServiceState)
    (rulePattern evidencePattern conclusionPattern serviceStatePattern
      nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.infer actualId rule parents evidence conclusion relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (ruleEncoded : encodeRule? host rule = some rulePattern)
    (evidenceEncoded : encodeEvidence? host evidence = some evidencePattern)
    (conclusionEncoded :
      encodeFormula? host conclusion = some conclusionPattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (parentOutputsEncodable :
      ∀ parentFormulas nextNodes,
        resolveParents? expectedId relevance.distance parents oldNodes =
            .ok (parentFormulas, nextNodes) →
          ∃ parentFormulasPattern nextNodesPattern,
            formulasPattern? host parentFormulas =
                some parentFormulasPattern ∧
              nodesPattern? host nextNodes = some nextNodesPattern)
    (serviceOutputsEncodable :
      ∀ parentFormulas nextServiceState,
        host.services.infer serviceState rule parentFormulas evidence
            conclusion = some nextServiceState →
          ∃ nextServiceStatePattern,
            encodeServiceState? host nextServiceState =
              some nextServiceStatePattern) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .infer actualId rule parents evidence conclusion
        relevance :: remainingInstructions
      nodes := oldNodes
      nextId := expectedId
      root? := rootState
      serviceState := serviceState
    }
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern expectedId) rootPatternValue
      serviceStatePattern
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      ∃ next target,
        step? host.services (.running before) = some next ∧
          rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
            [target] ∧
          EncodesConfig host remainingRecords next target := by
  dsimp only
  by_cases idsEqual : actualId = expectedId
  · subst actualId
    cases relevanceValue : relevance.wellFormedFor expectedId with
    | false =>
        rcases infer_relevance_fault_semantic_square_encoded_root host
            rootState rootPatternValue record remainingRecords
            remainingInstructions oldNodes expectedId rule parents evidence
            conclusion relevance serviceState rulePattern evidencePattern
            conclusionPattern serviceStatePattern nodesPatternValue
            relevanceValue recordInstructionDecoded remainingDecoded
            ruleEncoded evidenceEncoded conclusionEncoded serviceStateEncoded
            nodesEncoded rootEncoded with
          ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
        exact ⟨sourceEncodes, _, _, semanticStep, authoredStep, targetEncodes⟩
    | true =>
        cases parentResult :
            resolveParents? expectedId relevance.distance parents oldNodes with
        | error failure =>
            rcases infer_parent_fault_semantic_square_encoded_root host
                rootState rootPatternValue record remainingRecords
                remainingInstructions oldNodes expectedId rule parents evidence
                conclusion relevance serviceState failure rulePattern
                evidencePattern conclusionPattern serviceStatePattern
                nodesPatternValue relevanceValue parentResult
                recordInstructionDecoded remainingDecoded ruleEncoded
                evidenceEncoded conclusionEncoded serviceStateEncoded
                nodesEncoded rootEncoded with
              ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
            exact
              ⟨sourceEncodes, _, _, semanticStep, authoredStep, targetEncodes⟩
        | ok result =>
            rcases result with ⟨parentFormulas, nextNodes⟩
            obtain ⟨parentFormulasPattern, nextNodesPattern,
                parentFormulasEncoded, nextNodesEncoded⟩ :=
              parentOutputsEncodable parentFormulas nextNodes parentResult
            cases serviceResult :
                host.services.infer serviceState rule parentFormulas evidence
                  conclusion with
            | none =>
                rcases infer_rule_fault_semantic_square_encoded_root host
                    rootState rootPatternValue record remainingRecords
                    remainingInstructions oldNodes nextNodes expectedId rule
                    parents evidence conclusion relevance serviceState
                    parentFormulas rulePattern evidencePattern
                    conclusionPattern serviceStatePattern nodesPatternValue
                    parentFormulasPattern nextNodesPattern relevanceValue
                    parentResult serviceResult recordInstructionDecoded
                    remainingDecoded ruleEncoded evidenceEncoded
                    conclusionEncoded serviceStateEncoded nodesEncoded
                    parentFormulasEncoded nextNodesEncoded rootEncoded with
                  ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
                exact
                  ⟨sourceEncodes, _, _, semanticStep, authoredStep,
                    targetEncodes⟩
            | some nextServiceState =>
                obtain ⟨nextServiceStatePattern, nextServiceStateEncoded⟩ :=
                  serviceOutputsEncodable parentFormulas nextServiceState
                    serviceResult
                rcases infer_accept_semantic_square_encoded_root host rootState
                    rootPatternValue record remainingRecords
                    remainingInstructions oldNodes nextNodes expectedId rule
                    parents evidence conclusion relevance serviceState
                    nextServiceState parentFormulas rulePattern evidencePattern
                    conclusionPattern serviceStatePattern
                    nextServiceStatePattern nodesPatternValue
                    parentFormulasPattern nextNodesPattern relevanceValue
                    parentResult serviceResult recordInstructionDecoded
                    remainingDecoded ruleEncoded evidenceEncoded
                    conclusionEncoded serviceStateEncoded
                    nextServiceStateEncoded nodesEncoded parentFormulasEncoded
                    nextNodesEncoded rootEncoded with
                  ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
                exact
                  ⟨sourceEncodes, _, _, semanticStep, authoredStep,
                    targetEncodes⟩
  · rcases infer_index_fault_semantic_square_encoded_root host rootState
        rootPatternValue record remainingRecords remainingInstructions oldNodes
        expectedId actualId rule parents evidence conclusion relevance
        serviceState rulePattern evidencePattern conclusionPattern
        serviceStatePattern nodesPatternValue idsEqual recordInstructionDecoded
        remainingDecoded ruleEncoded evidenceEncoded conclusionEncoded
        serviceStateEncoded nodesEncoded rootEncoded with
      ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
    exact ⟨sourceEncodes, _, _, semanticStep, authoredStep, targetEncodes⟩

#print axioms infer_one_record_semantic_square_encoded_root

end Mettapedia.GSLT.LanguageDef.DerivationWordMachineInferSimulation
