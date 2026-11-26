import Mettapedia.GSLT.LanguageDef.DerivationWordMachineSimulation

/-!
# Finish exclusion for decoded word records

A finish rule requires a match of the finish instruction. The shared proofs
use the decoder result and the actual negative match under the given root
and remaining records.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationWordMachineFinishGuards

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

theorem applyRuleUsing_eq_nil_of_no_left_match
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

theorem finish_shape_rules_reject_nonfinish_root_none
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
        actualInstruction = [])
    (unannotated : sourceRule.bindings = none := by first | rfl | assumption) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule unannotated)
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

theorem finish_shape_rules_reject_nonfinish_root_some
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
        actualInstruction = [])
    (unannotated : sourceRule.bindings = none := by first | rfl | assumption) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule unannotated)
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

theorem finish_root_some_rules_reject_nonfinish_root_some
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
        actualInstruction = [])
    (unannotated : sourceRule.bindings = none := by first | rfl | assumption) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule unannotated)
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
        apply applyRuleUsing_eq_nil_of_no_left_match
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

/-- The finish matcher accepts its own instruction, so the exclusion
hypothesis is essential to the nonfinish specializations. -/
example :
    matchPattern (DerivationCheckMachineLanguageDef.a "dcm:finish")
      (DerivationCheckMachineLanguageDef.a "dcm:finish") = [[]] := by
  simp [DerivationCheckMachineLanguageDef.a, matchPattern, matchArgs]


end Mettapedia.GSLT.LanguageDef.DerivationWordMachineFinishGuards
