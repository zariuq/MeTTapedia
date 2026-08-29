import Mettapedia.GSLT.LanguageDef.DerivationWordMachineSimulation

/-!
# Root-polymorphic input simulation for the derivation-word machine

The base simulation module proves the exact input transition table from the
initial `root-none` state.  This module proves the corresponding partition
after a root has already been selected and then joins the two cases through
the canonical `rootPattern?` encoding.  An input instruction preserves an
existing root claim, so excluding this state would strengthen the authored
semantic machine rather than simulate it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationWordMachineInputSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineSimulation

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}
variable [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation]
  [DecidableEq ServiceState]

theorem applyRuleUsing_empty_of_no_left_match
    (base : BasePremiseEvaluator) (targetLanguage : LanguageDef)
    (recursiveStep : Pattern → List Pattern) (rule : RewriteRule)
    (term : Pattern)
    (noMatch :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        targetLanguage rule term = []) :
    applyRuleUsing base targetLanguage recursiveStep rule term = [] := by
  unfold applyRuleUsing
  rw [noMatch]
  simp only [List.flatMap_nil]

#print axioms applyRuleUsing_empty_of_no_left_match

theorem duplicate_root_on_input_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId serviceState priorId priorFormula
      priorObligation id formula provenance relevance : Pattern)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [id, formula, provenance, relevance])) :
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

#print axioms duplicate_root_on_input_record_root_some_empty

theorem root_rules_on_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId serviceState priorId priorFormula
      priorObligation : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.rootFaultTransition,
      DerivationCheckMachineLanguageDef.rootAcceptTransition]) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId
        (DerivationCheckMachineLanguageDef.rootSome priorId priorFormula
          priorObligation)
        serviceState) = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  · simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern,
      DerivationCheckMachineLanguageDef.rootFaultTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.rootNone,
      DerivationCheckMachineLanguageDef.rootSome,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      run, recordsCons, DerivationWordMachineLanguageDef.a,
      matchPattern, matchArgs, mergeBindings]
  · simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern,
      DerivationCheckMachineLanguageDef.rootAcceptTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.rootNone,
      DerivationCheckMachineLanguageDef.rootSome,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      run, recordsCons, DerivationWordMachineLanguageDef.a,
      matchPattern, matchArgs, mergeBindings]

#print axioms root_rules_on_root_some_empty

theorem finish_shape_rules_on_input_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation id formula
      provenance relevance : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishTrailingTransition,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [id, formula, provenance, relevance])) :
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

#print axioms finish_shape_rules_on_input_record_root_some_empty

theorem finish_root_some_rules_on_input_record_root_some_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState priorId priorFormula priorObligation id formula
      provenance relevance : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [id, formula, provenance, relevance])) :
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

#print axioms finish_root_some_rules_on_input_record_root_some_empty

/-- Once a root has been selected, a decoded input record still restricts the
full authored transition table to the same four input rows.  The root pattern
is preserved by every successful input row. -/
theorem input_record_rewriteAt_partition_root_some
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern priorIdPattern
      priorFormulaPattern priorObligationPattern idPattern formulaPattern
      provenancePattern relevancePatternValue : Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue])) :
    let root := DerivationCheckMachineLanguageDef.rootSome priorIdPattern
      priorFormulaPattern priorObligationPattern
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodes nextIdPattern root serviceStatePattern
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputIndexFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputDecisionFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite DerivationCheckMachineLanguageDef.inputAcceptTransition)
          source := by
  dsimp only
  let root := DerivationCheckMachineLanguageDef.rootSome priorIdPattern
    priorFormulaPattern priorObligationPattern
  change language.rewrites.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) rule
        (run (recordsCons (wordsPattern record)
          (recordsPattern remainingRecords)) nodes nextIdPattern root
          serviceStatePattern)) = _
  rw [show language.rewrites = transitions by rfl]
  simp only [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil]
  rw [malformed_record_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern root
    serviceStatePattern
    (DerivationCheckMachineLanguageDef.a "dcm:input"
      [idPattern, formulaPattern, provenancePattern, relevancePatternValue])
    recordDecoded]
  rw [missing_finish_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern root
    serviceStatePattern]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    root serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue (by simp [genericNonInputSourceRules])
    recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    root serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue (by simp [genericNonInputSourceRules])
    recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferParentFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    root serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue (by simp [genericNonInputSourceRules])
    recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    root serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue (by simp [genericNonInputSourceRules])
    recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    root serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue (by simp [genericNonInputSourceRules])
    recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.dropFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    root serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue (by simp [genericNonInputSourceRules])
    recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.dropAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    root serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue (by simp [genericNonInputSourceRules])
    recordDecoded]
  rw [duplicate_root_on_input_record_root_some_empty host
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern priorIdPattern priorFormulaPattern
    priorObligationPattern idPattern formulaPattern provenancePattern
    relevancePatternValue recordDecoded]
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
  rw [finish_shape_rules_on_input_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishTrailingTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern priorIdPattern
    priorFormulaPattern priorObligationPattern idPattern formulaPattern
    provenancePattern relevancePatternValue (by simp) recordDecoded]
  rw [finish_shape_rules_on_input_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishMissingRootTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern priorIdPattern
    priorFormulaPattern priorObligationPattern idPattern formulaPattern
    provenancePattern relevancePatternValue (by simp) recordDecoded]
  rw [finish_root_some_rules_on_input_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern priorIdPattern
    priorFormulaPattern priorObligationPattern idPattern formulaPattern
    provenancePattern relevancePatternValue (by simp) recordDecoded]
  rw [finish_root_some_rules_on_input_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishRootFaultTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern priorIdPattern
    priorFormulaPattern priorObligationPattern idPattern formulaPattern
    provenancePattern relevancePatternValue (by simp) recordDecoded]
  rw [finish_root_some_rules_on_input_record_root_some_empty host
    DerivationCheckMachineLanguageDef.finishVerifiedTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern priorIdPattern
    priorFormulaPattern priorObligationPattern idPattern formulaPattern
    provenancePattern relevancePatternValue (by simp) recordDecoded]
  simp [root]

#print axioms input_record_rewriteAt_partition_root_some

/-- The input transition-table partition is independent of whether the
semantic configuration has selected a root.  The target root must be the
canonical encoding of that exact semantic root state. -/
theorem input_record_rewriteAt_partition_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern formulaPattern
      provenancePattern relevancePatternValue : Pattern)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue])) :
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodes nextIdPattern rootPatternValue serviceStatePattern
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputIndexFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputDecisionFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite DerivationCheckMachineLanguageDef.inputAcceptTransition)
          source := by
  cases rootState with
  | none =>
      simp [rootPattern?] at rootEncoded
      subst rootPatternValue
      exact input_record_rewriteAt_partition host record remainingRecords nodes
        nextIdPattern serviceStatePattern idPattern formulaPattern
        provenancePattern relevancePatternValue recordDecoded
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
              exact input_record_rewriteAt_partition_root_some host record
                remainingRecords nodes nextIdPattern serviceStatePattern
                (indexPattern rootId) rootFormulaPattern rootObligationPattern
                idPattern formulaPattern provenancePattern
                relevancePatternValue recordDecoded

#print axioms input_record_rewriteAt_partition_encoded_root

theorem input_index_fault_rewriteAt_exact_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern formulaPattern
      provenancePattern relevancePatternValue faultPatternValue : Pattern)
    (expectedId actualId : Nat)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
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
  rw [input_record_rewriteAt_partition_encoded_root host rootState
    rootPatternValue record remainingRecords nodes nextIdPattern
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue rootEncoded recordDecoded]
  rw [input_index_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue faultPatternValue expectedId actualId recordDecoded
    nextIdDecoded idDecoded indexFaulted]
  rw [input_index_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern formulaPattern
    provenancePattern relevancePatternValue faultPatternValue expectedId
    actualId (by simp [inputIndexSuccessSourceRules]) recordDecoded
    nextIdDecoded idDecoded indexFaulted]
  rw [input_index_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern formulaPattern
    provenancePattern relevancePatternValue faultPatternValue expectedId
    actualId (by simp [inputIndexSuccessSourceRules]) recordDecoded
    nextIdDecoded idDecoded indexFaulted]
  rw [input_index_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inputAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern formulaPattern
    provenancePattern relevancePatternValue faultPatternValue expectedId
    actualId (by simp [inputIndexSuccessSourceRules]) recordDecoded
    nextIdDecoded idDecoded indexFaulted]
  simp

#print axioms input_index_fault_rewriteAt_exact_encoded_root

theorem input_relevance_fault_rewriteAt_exact_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern formulaPattern
      provenancePattern relevancePatternValue advancedPattern
      faultPatternValue : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
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
  rw [input_record_rewriteAt_partition_encoded_root host rootState
    rootPatternValue record remainingRecords nodes nextIdPattern
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue rootEncoded recordDecoded]
  rw [input_index_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern expectedId actualId recordDecoded
    nextIdDecoded idDecoded indexAccepted]
  rw [input_relevance_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern faultPatternValue expectedId actualId
    relevance recordDecoded nextIdDecoded idDecoded relevanceDecoded
    indexAccepted relevanceFaulted]
  rw [input_relevance_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern formulaPattern
    provenancePattern relevancePatternValue advancedPattern faultPatternValue
    expectedId actualId relevance
    (by simp [inputRelevanceSuccessSourceRules]) recordDecoded nextIdDecoded
    idDecoded relevanceDecoded indexAccepted relevanceFaulted]
  rw [input_relevance_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inputAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    rootPatternValue serviceStatePattern idPattern formulaPattern
    provenancePattern relevancePatternValue advancedPattern faultPatternValue
    expectedId actualId relevance
    (by simp [inputRelevanceSuccessSourceRules]) recordDecoded nextIdDecoded
    idDecoded relevanceDecoded indexAccepted relevanceFaulted]
  simp

#print axioms input_relevance_fault_rewriteAt_exact_encoded_root

theorem input_decision_fault_rewriteAt_exact_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern formulaPattern
      provenancePattern relevancePatternValue advancedPattern
      faultPatternValue : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (serviceState : ServiceState) (provenance : Provenance)
    (formula : Formula)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (provenanceDecoded :
      decodeProvenance? host provenancePattern = some provenance)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (inputFaulted :
      inputDecision host actualId serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionFault faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodes nextIdPattern
        rootPatternValue serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  rw [input_record_rewriteAt_partition_encoded_root host rootState
    rootPatternValue record remainingRecords nodes nextIdPattern
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue rootEncoded recordDecoded]
  rw [input_index_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern expectedId actualId recordDecoded
    nextIdDecoded idDecoded indexAccepted]
  rw [input_relevance_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern expectedId actualId relevance
    recordDecoded nextIdDecoded idDecoded relevanceDecoded indexAccepted
    relevanceAccepted]
  rw [input_decision_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern faultPatternValue expectedId actualId
    relevance serviceState provenance formula recordDecoded nextIdDecoded
    idDecoded relevanceDecoded serviceStateDecoded provenanceDecoded
    formulaDecoded indexAccepted relevanceAccepted inputFaulted]
  rw [input_decision_fault_excludes_accept host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern faultPatternValue expectedId actualId
    relevance serviceState provenance formula recordDecoded nextIdDecoded
    idDecoded relevanceDecoded serviceStateDecoded provenanceDecoded
    formulaDecoded indexAccepted relevanceAccepted inputFaulted]
  simp

#print axioms input_decision_fault_rewriteAt_exact_encoded_root

theorem input_accept_rewriteAt_exact_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern formulaPattern
      provenancePattern relevancePatternValue advancedPattern
      nextServiceStatePattern : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (serviceState : ServiceState) (provenance : Provenance)
    (formula : Formula)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (provenanceDecoded :
      decodeProvenance? host provenancePattern = some provenance)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (inputAccepted :
      inputDecision host actualId serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodes nextIdPattern
        rootPatternValue serviceStatePattern) =
      [run (recordsPattern remainingRecords)
        (DerivationCheckMachineLanguageDef.nodesCons
          (DerivationCheckMachineLanguageDef.node idPattern formulaPattern
            relevancePatternValue
            (DerivationCheckMachineLanguageDef.a "dcm:unlinked"))
          nodes)
        advancedPattern rootPatternValue nextServiceStatePattern] := by
  rw [input_record_rewriteAt_partition_encoded_root host rootState
    rootPatternValue record remainingRecords nodes nextIdPattern
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue rootEncoded recordDecoded]
  rw [input_index_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern expectedId actualId recordDecoded
    nextIdDecoded idDecoded indexAccepted]
  rw [input_relevance_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern expectedId actualId relevance
    recordDecoded nextIdDecoded idDecoded relevanceDecoded indexAccepted
    relevanceAccepted]
  rw [input_decision_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern nextServiceStatePattern expectedId
    actualId relevance serviceState provenance formula recordDecoded
    nextIdDecoded idDecoded relevanceDecoded serviceStateDecoded
    provenanceDecoded formulaDecoded indexAccepted relevanceAccepted
    inputAccepted]
  rw [input_accept_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern rootPatternValue
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern nextServiceStatePattern expectedId
    actualId relevance serviceState provenance formula recordDecoded
    nextIdDecoded idDecoded relevanceDecoded serviceStateDecoded
    provenanceDecoded formulaDecoded indexAccepted relevanceAccepted
    inputAccepted]
  simp

#print axioms input_accept_rewriteAt_exact_encoded_root

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance] in
theorem input_source_encodes_running
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (expectedId actualId : Nat) (formula : Formula)
    (provenance : Provenance) (relevance : RelevanceWitness)
    (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.input actualId formula provenance relevance))
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
      instructions := .input actualId formula provenance relevance ::
        remainingInstructions
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

#print axioms input_source_encodes_running

omit [DecidableEq Rule] [DecidableEq Evidence] [DecidableEq Provenance] in
theorem fault_target_encodes_halted
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (oldNodes : List (Node Formula)) (failure : Fault)
    (nodesPatternValue : Pattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    EncodesConfig host remainingRecords (.halted (.fault failure))
      (halted
        (DerivationCheckMachineLanguageDef.outcomeFault
          (faultPattern failure))
        nodesPatternValue) := by
  refine ⟨oldNodes, ?_⟩
  constructor
  simp [haltedPattern?, outcomePattern?, nodesEncoded, faultPattern,
    halted, DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.a,
    DerivationWordMachineLanguageDef.a,
    DerivationWordMachineRelationEnv.a]

#print axioms fault_target_encodes_halted

/-- A bad input node id commutes for every canonically encoded root state. -/
theorem input_index_fault_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (expectedId actualId : Nat) (formula : Formula)
    (provenance : Provenance) (relevance : RelevanceWitness)
    (serviceState : ServiceState)
    (formulaPattern provenancePattern serviceStatePattern nodesPatternValue :
      Pattern)
    (idsDiffer : actualId ≠ expectedId)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.input actualId formula provenance relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (formulaEncoded : encodeFormula? host formula = some formulaPattern)
    (provenanceEncoded :
      encodeProvenance? host provenance = some provenancePattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .input actualId formula provenance relevance ::
        remainingInstructions
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
          (.input actualId formula provenance relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern actualId, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    simp [instructionPattern?, formulaEncoded, provenanceEncoded,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern actualId, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern actualId, formulaPattern, provenancePattern,
           relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.input actualId formula provenance relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [indexPattern actualId, formulaPattern, provenancePattern,
         relevancePattern relevance])
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
  · exact input_source_encodes_running host rootState rootPatternValue
      record remainingRecords remainingInstructions oldNodes expectedId
      actualId formula provenance relevance serviceState serviceStatePattern
      nodesPatternValue recordInstructionDecoded remainingDecoded rootEncoded
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault, idsDiffer]
  constructor
  · exact input_index_fault_rewriteAt_exact_encoded_root host rootState
      rootPatternValue record remainingRecords nodesPatternValue
      (indexPattern expectedId) serviceStatePattern (indexPattern actualId)
      formulaPattern provenancePattern (relevancePattern relevance)
      (faultPattern (.badNodeId expectedId actualId)) expectedId actualId
      rootEncoded recordDecoded (decodeIndex_indexPattern expectedId)
      (decodeIndex_indexPattern actualId) indexFaulted
  · exact fault_target_encodes_halted host remainingRecords oldNodes
      (.badNodeId expectedId actualId) nodesPatternValue nodesEncoded

#print axioms input_index_fault_semantic_square_encoded_root

theorem input_relevance_fault_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (id : Nat) (formula : Formula) (provenance : Provenance)
    (relevance : RelevanceWitness) (serviceState : ServiceState)
    (formulaPattern provenancePattern serviceStatePattern nodesPatternValue :
      Pattern)
    (relevanceMalformed : relevance.wellFormedFor id = false)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.input id formula provenance relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (formulaEncoded : encodeFormula? host formula = some formulaPattern)
    (provenanceEncoded :
      encodeProvenance? host provenance = some provenancePattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .input id formula provenance relevance ::
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
      instructionPattern? host (.input id formula provenance relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    simp [instructionPattern?, formulaEncoded, provenanceEncoded,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.input id formula provenance relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [indexPattern id, formulaPattern, provenancePattern,
         relevancePattern relevance])
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
  · exact input_source_encodes_running host rootState rootPatternValue
      record remainingRecords remainingInstructions oldNodes id id formula
      provenance relevance serviceState serviceStatePattern nodesPatternValue
      recordInstructionDecoded remainingDecoded rootEncoded
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault,
      relevanceMalformed]
  constructor
  · exact input_relevance_fault_rewriteAt_exact_encoded_root host
      rootState rootPatternValue record remainingRecords nodesPatternValue
      (indexPattern id) serviceStatePattern (indexPattern id) formulaPattern
      provenancePattern (relevancePattern relevance) (indexPattern (id + 1))
      (faultPattern (.malformedRelevance id)) id id relevance rootEncoded
      recordDecoded (decodeIndex_indexPattern id)
      (decodeIndex_indexPattern id) (decodeRelevance_relevancePattern relevance)
      indexAccepted relevanceFaulted
  · exact fault_target_encodes_halted host remainingRecords oldNodes
      (.malformedRelevance id) nodesPatternValue nodesEncoded

#print axioms input_relevance_fault_semantic_square_encoded_root

theorem input_decision_fault_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (id : Nat) (formula : Formula) (provenance : Provenance)
    (relevance : RelevanceWitness) (serviceState : ServiceState)
    (formulaPattern provenancePattern serviceStatePattern nodesPatternValue :
      Pattern)
    (relevanceWellFormed : relevance.wellFormedFor id = true)
    (serviceRejected :
      host.services.input serviceState provenance formula = none)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.input id formula provenance relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (formulaEncoded : encodeFormula? host formula = some formulaPattern)
    (provenanceEncoded :
      encodeProvenance? host provenance = some provenancePattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .input id formula provenance relevance ::
        remainingInstructions
      nodes := oldNodes
      nextId := id
      root? := rootState
      serviceState := serviceState
    }
    let failure := Fault.inputRejected id
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
      instructionPattern? host (.input id formula provenance relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    simp [instructionPattern?, formulaEncoded, provenanceEncoded,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.input id formula provenance relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [indexPattern id, formulaPattern, provenancePattern,
         relevancePattern relevance])
      recordInstructionDecoded instructionPatternEncoded
  have serviceStateDecoded :=
    decodeServiceState_encodeServiceState host serviceState
      serviceStatePattern serviceStateEncoded
  have formulaDecoded :=
    decodeFormula_encodeFormula host formula formulaPattern formulaEncoded
  have provenanceDecoded :=
    decodeProvenance_encodeProvenance host provenance provenancePattern
      provenanceEncoded
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
  have inputFaulted :
      inputDecision host id serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionFault
          (faultPattern (.inputRejected id)) := by
    simp [inputDecision, serviceRejected, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact input_source_encodes_running host rootState rootPatternValue
      record remainingRecords remainingInstructions oldNodes id id formula
      provenance relevance serviceState serviceStatePattern nodesPatternValue
      recordInstructionDecoded remainingDecoded rootEncoded
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, haltFault,
      relevanceWellFormed, serviceRejected]
  constructor
  · exact input_decision_fault_rewriteAt_exact_encoded_root host rootState
      rootPatternValue record remainingRecords nodesPatternValue
      (indexPattern id) serviceStatePattern (indexPattern id) formulaPattern
      provenancePattern (relevancePattern relevance) (indexPattern (id + 1))
      (faultPattern (.inputRejected id)) id id relevance serviceState
      provenance formula rootEncoded recordDecoded (decodeIndex_indexPattern id)
      (decodeIndex_indexPattern id) (decodeRelevance_relevancePattern relevance)
      serviceStateDecoded provenanceDecoded formulaDecoded indexAccepted
      relevanceAccepted inputFaulted
  · exact fault_target_encodes_halted host remainingRecords oldNodes
      (.inputRejected id) nodesPatternValue nodesEncoded

#print axioms input_decision_fault_semantic_square_encoded_root

/-- An admitted input record preserves an existing root claim and commutes
exactly between semantic execution and the authored word-machine relation. -/
theorem input_accept_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (id : Nat) (formula : Formula) (provenance : Provenance)
    (relevance : RelevanceWitness)
    (serviceState nextServiceState : ServiceState)
    (formulaPattern provenancePattern serviceStatePattern
      nextServiceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.input id formula provenance relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (formulaEncoded : encodeFormula? host formula = some formulaPattern)
    (provenanceEncoded :
      encodeProvenance? host provenance = some provenancePattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nextServiceStateEncoded :
      encodeServiceState? host nextServiceState =
        some nextServiceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (relevanceWellFormed : relevance.wellFormedFor id = true)
    (serviceAccepted :
      host.services.input serviceState provenance formula =
        some nextServiceState) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .input id formula provenance relevance ::
        remainingInstructions
      nodes := oldNodes
      nextId := id
      root? := rootState
      serviceState := serviceState
    }
    let after :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := remainingInstructions
      nodes := { id, formula, relevance } :: oldNodes
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
          formulaPattern (relevancePattern relevance)
          (DerivationCheckMachineLanguageDef.a "dcm:unlinked"))
        nodesPatternValue)
      (indexPattern (id + 1)) rootPatternValue nextServiceStatePattern
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) = some (.running after) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.running after) target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host (.input id formula provenance relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    simp [instructionPattern?, formulaEncoded, provenanceEncoded,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.input id formula provenance relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [indexPattern id, formulaPattern, provenancePattern,
         relevancePattern relevance])
      recordInstructionDecoded instructionPatternEncoded
  have serviceStateDecoded :=
    decodeServiceState_encodeServiceState host serviceState
      serviceStatePattern serviceStateEncoded
  have formulaDecoded :=
    decodeFormula_encodeFormula host formula formulaPattern formulaEncoded
  have provenanceDecoded :=
    decodeProvenance_encodeProvenance host provenance provenancePattern
      provenanceEncoded
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
  have inputAccepted :
      inputDecision host id serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern := by
    simp [inputDecision, serviceAccepted, nextServiceStateEncoded,
      DerivationCheckMachineLanguageDef.decisionState,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · exact input_source_encodes_running host rootState rootPatternValue
      record remainingRecords remainingInstructions oldNodes id id formula
      provenance relevance serviceState serviceStatePattern nodesPatternValue
      recordInstructionDecoded remainingDecoded rootEncoded
      serviceStateEncoded nodesEncoded
  constructor
  · simp [step?, advance, replaceInstructions, relevanceWellFormed,
      serviceAccepted]
  constructor
  · exact input_accept_rewriteAt_exact_encoded_root host rootState
      rootPatternValue record remainingRecords nodesPatternValue
      (indexPattern id) serviceStatePattern (indexPattern id) formulaPattern
      provenancePattern (relevancePattern relevance) (indexPattern (id + 1))
      nextServiceStatePattern id id relevance serviceState provenance formula
      rootEncoded recordDecoded (decodeIndex_indexPattern id)
      (decodeIndex_indexPattern id) (decodeRelevance_relevancePattern relevance)
      serviceStateDecoded provenanceDecoded formulaDecoded indexAccepted
      relevanceAccepted inputAccepted
  · constructor
    · exact remainingDecoded
    · simp [runningPattern?, nodesPattern?, nodePattern?, formulaEncoded,
        nodesEncoded, nextServiceStateEncoded, rootEncoded, linkPattern,
        DerivationCheckMachineLanguageDef.nodesCons,
        DerivationCheckMachineLanguageDef.node,
        DerivationCheckMachineLanguageDef.a,
        DerivationWordMachineRelationEnv.a]

#print axioms input_accept_semantic_square_encoded_root

/-- Every representable input instruction takes exactly one authored target
step matching the deterministic semantic-machine step.  Successful service
states need only satisfy the local output-codec obligation. -/
theorem input_one_record_semantic_square_encoded_root
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (expectedId actualId : Nat) (formula : Formula)
    (provenance : Provenance) (relevance : RelevanceWitness)
    (serviceState : ServiceState)
    (formulaPattern provenancePattern serviceStatePattern nodesPatternValue :
      Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.input actualId formula provenance relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (formulaEncoded : encodeFormula? host formula = some formulaPattern)
    (provenanceEncoded :
      encodeProvenance? host provenance = some provenancePattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (serviceOutputsEncodable :
      ∀ nextServiceState,
        host.services.input serviceState provenance formula =
            some nextServiceState →
          ∃ nextServiceStatePattern,
            encodeServiceState? host nextServiceState =
              some nextServiceStatePattern) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .input actualId formula provenance relevance ::
        remainingInstructions
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
        rcases input_relevance_fault_semantic_square_encoded_root host
            rootState rootPatternValue record remainingRecords
            remainingInstructions oldNodes expectedId formula provenance
            relevance serviceState formulaPattern provenancePattern
            serviceStatePattern nodesPatternValue relevanceValue
            recordInstructionDecoded remainingDecoded formulaEncoded
            provenanceEncoded serviceStateEncoded nodesEncoded rootEncoded with
          ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
        exact ⟨sourceEncodes, _, _, semanticStep, authoredStep, targetEncodes⟩
    | true =>
        cases serviceResult :
            host.services.input serviceState provenance formula with
        | none =>
            rcases input_decision_fault_semantic_square_encoded_root host
                rootState rootPatternValue record remainingRecords
                remainingInstructions oldNodes expectedId formula provenance
                relevance serviceState formulaPattern provenancePattern
                serviceStatePattern nodesPatternValue relevanceValue
                serviceResult recordInstructionDecoded remainingDecoded
                formulaEncoded provenanceEncoded serviceStateEncoded
                nodesEncoded rootEncoded with
              ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
            exact
              ⟨sourceEncodes, _, _, semanticStep, authoredStep, targetEncodes⟩
        | some nextServiceState =>
            obtain ⟨nextServiceStatePattern, nextServiceStateEncoded⟩ :=
              serviceOutputsEncodable nextServiceState serviceResult
            rcases input_accept_semantic_square_encoded_root host rootState
                rootPatternValue record remainingRecords remainingInstructions
                oldNodes expectedId formula provenance relevance serviceState
                nextServiceState formulaPattern provenancePattern
                serviceStatePattern nextServiceStatePattern nodesPatternValue
                recordInstructionDecoded remainingDecoded formulaEncoded
                provenanceEncoded serviceStateEncoded nextServiceStateEncoded
                nodesEncoded rootEncoded relevanceValue serviceResult with
              ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
            exact
              ⟨sourceEncodes, _, _, semanticStep, authoredStep, targetEncodes⟩
  · rcases input_index_fault_semantic_square_encoded_root host rootState
        rootPatternValue record remainingRecords remainingInstructions oldNodes
        expectedId actualId formula provenance relevance serviceState
        formulaPattern provenancePattern serviceStatePattern nodesPatternValue
        idsEqual recordInstructionDecoded remainingDecoded formulaEncoded
        provenanceEncoded serviceStateEncoded nodesEncoded rootEncoded with
      ⟨sourceEncodes, semanticStep, authoredStep, targetEncodes⟩
    exact ⟨sourceEncodes, _, _, semanticStep, authoredStep, targetEncodes⟩

#print axioms input_one_record_semantic_square_encoded_root

end Mettapedia.GSLT.LanguageDef.DerivationWordMachineInputSimulation
