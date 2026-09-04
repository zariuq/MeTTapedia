import Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedExecution
import Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedFormulaExecution

/-!
# Exact agreement for named-to-resolved FOF

This module connects the independent nearest-binder resolver to the authored
GSLT transformation. Exact singleton results preserve order and multiplicity;
free-variable failure remains absence of a reduct rather than an invented
default index.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open LO FirstOrder
open TptpFofSymbolIdentity

attribute [local simp]
  TptpFofSymbolLanguageDef.a
  TptpFofSymbolLanguageDef.encodeFunctionHead
  TptpFofSymbolLanguageDef.encodePredicateHead

/-- Exact results remain stable once the contextual recursion budget reaches
the structural depth required by the source term. -/
def EventuallyExact (source result : Pattern) : Prop :=
  ∃ requiredFuel, ∀ fuel, requiredFuel ≤ fuel →
    rewriteAt (engineBasePremises relations) language fuel source = [result]

def encodeEnvironment : List String → Pattern
  | [] => environmentNil
  | name :: environment =>
      environmentCons (a name) (encodeEnvironment environment)

@[simp] theorem encodeEnvironment_nil :
    encodeEnvironment [] = environmentNil := rfl

@[simp] theorem encodeEnvironment_cons (name : String)
    (environment : List String) :
    encodeEnvironment (name :: environment) =
      environmentCons (a name) (encodeEnvironment environment) := rfl

theorem encodeIndex_zero {depth : Nat} :
    TptpResolvedFofLanguageDef.encodeIndex (0 : Fin (depth + 1)) =
      targetIndexZero := by
  rfl

theorem encodeIndex_succ {depth : Nat} (index : Fin depth) :
    TptpResolvedFofLanguageDef.encodeIndex index.succ =
      targetIndexSucc (TptpResolvedFofLanguageDef.encodeIndex index) := by
  rfl

theorem encodeTerm_bvar {depth : Nat} (index : Fin depth) :
    TptpResolvedFofLanguageDef.encodeTerm (Semiterm.bvar index) =
      targetVariable (TptpResolvedFofLanguageDef.encodeIndex index) := by
  rfl

theorem encodeTerms_nil {depth : Nat} :
    TptpResolvedFofLanguageDef.encodeTerms
        ([] : List (TptpFofNormalizationSemantics.Term depth)) =
      targetTermsNil := by
  rfl

theorem encodeTerms_cons {depth : Nat}
    (head : TptpFofNormalizationSemantics.Term depth)
    (tail : List (TptpFofNormalizationSemantics.Term depth)) :
    TptpResolvedFofLanguageDef.encodeTerms (head :: tail) =
      targetTermsCons (TptpResolvedFofLanguageDef.encodeTerm head)
        (TptpResolvedFofLanguageDef.encodeTerms tail) := by
  rfl

theorem encodeTerm_function {depth : Nat} (head : FunctionHead)
    (arguments : List (TptpFofNormalizationSemantics.Term depth)) :
    TptpResolvedFofLanguageDef.encodeTerm
        (.func
          ({ name := head.lexeme, kind := head.kind } :
            TptpFofNormalizationSemantics.FunctionSymbol arguments.length)
          (fun index => arguments.get index)) =
      targetFunction (TptpFofSymbolLanguageDef.encodeFunctionHead head)
        (TptpResolvedFofLanguageDef.encodeTerms arguments) := by
  unfold TptpResolvedFofLanguageDef.encodeTerms
  unfold TptpResolvedFofLanguageDef.encodeTerm
  simp [targetFunction, a]
  rfl

theorem encodeNamedTerm_variable (name : String) :
    TptpNamedFofLanguageDef.encodeTerm (.variable name) =
      sourceVariable (a name) := by
  rfl

theorem encodeNamedTerm_function (head : FunctionHead)
    (arguments : List TptpFofBinderResolution.NamedTerm) :
    TptpNamedFofLanguageDef.encodeTerm (.function head arguments) =
      sourceFunction (TptpFofSymbolLanguageDef.encodeFunctionHead head)
        (TptpNamedFofLanguageDef.encodeTerms arguments) := by
  rfl

theorem encodeNamedTerms_nil :
    TptpNamedFofLanguageDef.encodeTerms [] = sourceTermsNil := by
  rfl

theorem encodeNamedTerms_cons
    (head : TptpFofBinderResolution.NamedTerm)
    (tail : List TptpFofBinderResolution.NamedTerm) :
    TptpNamedFofLanguageDef.encodeTerms (head :: tail) =
      sourceTermsCons (TptpNamedFofLanguageDef.encodeTerm head)
        (TptpNamedFofLanguageDef.encodeTerms tail) := by
  rfl

theorem encodeNamedFormula_verum :
    TptpNamedFofLanguageDef.encodeFormula .verum =
      sourceFormula "verum" := by rfl

theorem encodeNamedFormula_falsum :
    TptpNamedFofLanguageDef.encodeFormula .falsum =
      sourceFormula "falsum" := by rfl

theorem encodeNamedFormula_predicate (head : PredicateHead)
    (arguments : List TptpFofBinderResolution.NamedTerm) :
    TptpNamedFofLanguageDef.encodeFormula (.predicate head arguments) =
      sourceFormula "predicate"
        [TptpFofSymbolLanguageDef.encodePredicateHead head,
         TptpNamedFofLanguageDef.encodeTerms arguments] :=
  by rfl

theorem encodeNamedFormula_equal
    (left right : TptpFofBinderResolution.NamedTerm) :
    TptpNamedFofLanguageDef.encodeFormula (.equal left right) =
      sourceFormula "equal"
        [TptpNamedFofLanguageDef.encodeTerm left,
         TptpNamedFofLanguageDef.encodeTerm right] := by rfl

theorem encodeNamedFormula_not
    (body : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.not body) =
      sourceFormula "not" [TptpNamedFofLanguageDef.encodeFormula body] := by rfl

theorem encodeNamedFormula_and (left right :
    TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.and left right) =
      sourceFormula "and" [TptpNamedFofLanguageDef.encodeFormula left,
        TptpNamedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeNamedFormula_or (left right :
    TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.or left right) =
      sourceFormula "or" [TptpNamedFofLanguageDef.encodeFormula left,
        TptpNamedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeNamedFormula_iff (left right :
    TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.iff left right) =
      sourceFormula "iff" [TptpNamedFofLanguageDef.encodeFormula left,
        TptpNamedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeNamedFormula_implies (left right :
    TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.implies left right) =
      sourceFormula "implies" [TptpNamedFofLanguageDef.encodeFormula left,
        TptpNamedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeNamedFormula_reverseImplies (left right :
    TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.reverseImplies left right) =
      sourceFormula "reverse-implies"
        [TptpNamedFofLanguageDef.encodeFormula left,
         TptpNamedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeNamedFormula_xor (left right :
    TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.xor left right) =
      sourceFormula "xor" [TptpNamedFofLanguageDef.encodeFormula left,
        TptpNamedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeNamedFormula_nor (left right :
    TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.nor left right) =
      sourceFormula "nor" [TptpNamedFofLanguageDef.encodeFormula left,
        TptpNamedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeNamedFormula_nand (left right :
    TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.nand left right) =
      sourceFormula "nand" [TptpNamedFofLanguageDef.encodeFormula left,
        TptpNamedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeNamedFormula_all (binder : String)
    (body : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.all binder body) =
      sourceFormula "all"
        [sourceName (a binder), TptpNamedFofLanguageDef.encodeFormula body] :=
  by rfl

theorem encodeNamedFormula_ex (binder : String)
    (body : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.ex binder body) =
      sourceFormula "ex"
        [sourceName (a binder), TptpNamedFofLanguageDef.encodeFormula body] :=
  by rfl

theorem encodeResolvedFormula_verum {depth : Nat} :
    TptpResolvedFofLanguageDef.encodeFormula
        (.verum : TptpFofNormalizationSemantics.Formula depth) =
      targetFormula "verum" := by rfl

theorem encodeResolvedFormula_falsum {depth : Nat} :
    TptpResolvedFofLanguageDef.encodeFormula
        (.falsum : TptpFofNormalizationSemantics.Formula depth) =
      targetFormula "falsum" := by rfl

theorem encodeResolvedFormula_predicate {depth : Nat} (head : PredicateHead)
    (arguments : List (TptpFofNormalizationSemantics.Term depth)) :
    TptpResolvedFofLanguageDef.encodeFormula
        (.predicate
          ({ name := head.lexeme, kind := head.kind } :
            TptpFofNormalizationSemantics.PredicateSymbol arguments.length)
          (fun index => arguments.get index)) =
      targetFormula "predicate"
        [TptpFofSymbolLanguageDef.encodePredicateHead head,
         TptpResolvedFofLanguageDef.encodeTerms arguments] := by
  unfold TptpResolvedFofLanguageDef.encodeTerms
  unfold TptpResolvedFofLanguageDef.encodeFormula
  simp [targetFormula, a]
  rfl

theorem encodeResolvedFormula_equal {depth : Nat}
    (left right : TptpFofNormalizationSemantics.Term depth) :
    TptpResolvedFofLanguageDef.encodeFormula (.equal left right) =
      targetFormula "equal"
        [TptpResolvedFofLanguageDef.encodeTerm left,
         TptpResolvedFofLanguageDef.encodeTerm right] := by rfl

theorem encodeResolvedFormula_not {depth : Nat}
    (body : TptpFofNormalizationSemantics.Formula depth) :
    TptpResolvedFofLanguageDef.encodeFormula (.not body) =
      targetFormula "not"
        [TptpResolvedFofLanguageDef.encodeFormula body] := by rfl

theorem encodeResolvedFormula_and {depth : Nat} (left right :
    TptpFofNormalizationSemantics.Formula depth) :
    TptpResolvedFofLanguageDef.encodeFormula (.and left right) =
      targetFormula "and" [TptpResolvedFofLanguageDef.encodeFormula left,
        TptpResolvedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeResolvedFormula_or {depth : Nat} (left right :
    TptpFofNormalizationSemantics.Formula depth) :
    TptpResolvedFofLanguageDef.encodeFormula (.or left right) =
      targetFormula "or" [TptpResolvedFofLanguageDef.encodeFormula left,
        TptpResolvedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeResolvedFormula_iff {depth : Nat} (left right :
    TptpFofNormalizationSemantics.Formula depth) :
    TptpResolvedFofLanguageDef.encodeFormula (.iff left right) =
      targetFormula "iff" [TptpResolvedFofLanguageDef.encodeFormula left,
        TptpResolvedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeResolvedFormula_implies {depth : Nat} (left right :
    TptpFofNormalizationSemantics.Formula depth) :
    TptpResolvedFofLanguageDef.encodeFormula (.implies left right) =
      targetFormula "implies"
        [TptpResolvedFofLanguageDef.encodeFormula left,
         TptpResolvedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeResolvedFormula_reverseImplies {depth : Nat} (left right :
    TptpFofNormalizationSemantics.Formula depth) :
    TptpResolvedFofLanguageDef.encodeFormula (.reverseImplies left right) =
      targetFormula "reverse-implies"
        [TptpResolvedFofLanguageDef.encodeFormula left,
         TptpResolvedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeResolvedFormula_xor {depth : Nat} (left right :
    TptpFofNormalizationSemantics.Formula depth) :
    TptpResolvedFofLanguageDef.encodeFormula (.xor left right) =
      targetFormula "xor" [TptpResolvedFofLanguageDef.encodeFormula left,
        TptpResolvedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeResolvedFormula_nor {depth : Nat} (left right :
    TptpFofNormalizationSemantics.Formula depth) :
    TptpResolvedFofLanguageDef.encodeFormula (.nor left right) =
      targetFormula "nor" [TptpResolvedFofLanguageDef.encodeFormula left,
        TptpResolvedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeResolvedFormula_nand {depth : Nat} (left right :
    TptpFofNormalizationSemantics.Formula depth) :
    TptpResolvedFofLanguageDef.encodeFormula (.nand left right) =
      targetFormula "nand" [TptpResolvedFofLanguageDef.encodeFormula left,
        TptpResolvedFofLanguageDef.encodeFormula right] := by rfl

theorem encodeResolvedFormula_all {depth : Nat}
    (body : TptpFofNormalizationSemantics.Formula (depth + 1)) :
    TptpResolvedFofLanguageDef.encodeFormula (.all body :
      TptpFofNormalizationSemantics.Formula depth) =
      targetFormula "all"
        [TptpResolvedFofLanguageDef.encodeFormula body] := by rfl

theorem encodeResolvedFormula_ex {depth : Nat}
    (body : TptpFofNormalizationSemantics.Formula (depth + 1)) :
    TptpResolvedFofLanguageDef.encodeFormula (.ex body :
      TptpFofNormalizationSemantics.Formula depth) =
      targetFormula "ex"
        [TptpResolvedFofLanguageDef.encodeFormula body] := by rfl

private theorem lookupRootRules :
    language.rewrites.filter
        (TptpOfficialFofToNamedFormulaLanguageDef.rootMatches
          "tptp-fof-resolve:lookup") =
      [lookupRules.get ⟨0, by decide⟩] := by
  rfl

private theorem lookupDecisionRootRules :
    language.rewrites.filter
        (TptpOfficialFofToNamedFormulaLanguageDef.rootMatches
          "tptp-fof-resolve:lookup-decision") =
      [lookupRules.get ⟨1, by decide⟩,
       lookupRules.get ⟨2, by decide⟩] := by
  rfl

private theorem termRootRules :
    language.rewrites.filter
        (TptpOfficialFofToNamedFormulaLanguageDef.rootMatches
          "tptp-fof-resolve:term") =
      termRules.take 2 := by
  rfl

private theorem termsRootRules :
    language.rewrites.filter
        (TptpOfficialFofToNamedFormulaLanguageDef.rootMatches
          "tptp-fof-resolve:terms") =
      termRules.drop 2 := by
  rfl

private theorem formulaRootRules :
    language.rewrites.filter
        (TptpOfficialFofToNamedFormulaLanguageDef.rootMatches
          "tptp-fof-resolve:formula") =
      formulaLeafRules ++ formulaAtomRules ++ [unaryFormulaRule] ++
        binaryFormulaRules ++ binderFormulaRules := by
  rfl

private theorem closedRootRules :
    language.rewrites.filter
        (TptpOfficialFofToNamedFormulaLanguageDef.rootMatches
          "tptp-fof-resolve:closed") =
      [closedRule] := by
  rfl

private theorem equalityPremise_equal_exact (name tail : Pattern) :
    engineBasePremises relations language
        [("head", name), ("tail", tail), ("name", name)]
        (.relationQuery PatternEqualityDecision.relationName
          [v "name", v "head", v "decision"]) =
      [[("decision", PatternEqualityDecision.equal),
        ("head", name), ("tail", tail), ("name", name)]] := by
  simp [engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relations, PatternEqualityDecision.relationEnv,
    PatternEqualityDecision.relationName,
    PatternEqualityDecision.relationTuples, matchRelationArgs,
    matchRelationArgument, Bindings.lookup, mergeBindings, applyBindings, v]

private theorem equalityPremise_different_exact (name binder tail : Pattern)
    (different : name ≠ binder) :
    engineBasePremises relations language
        [("head", binder), ("tail", tail), ("name", name)]
        (.relationQuery PatternEqualityDecision.relationName
          [v "name", v "head", v "decision"]) =
      [[("decision", PatternEqualityDecision.different),
        ("head", binder), ("tail", tail), ("name", name)]] := by
  simp [engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relations, PatternEqualityDecision.relationEnv,
    PatternEqualityDecision.relationName,
    PatternEqualityDecision.relationTuples, matchRelationArgs,
    matchRelationArgument, Bindings.lookup, mergeBindings, applyBindings, v,
    different]

theorem lookupDecision_equal_rewriteAt_exact (fuel : Nat)
    (name tail : Pattern) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (lookupDecision PatternEqualityDecision.equal name tail) =
      [targetIndexZero] := by
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:lookup-decision"
      [PatternEqualityDecision.equal, name, tail]) = [targetIndexZero]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    lookupDecisionRootRules]
  simp [lookupRules, mkRule, lookupDecision, targetIndexZero, a, v,
    PatternEqualityDecision.equal, PatternEqualityDecision.different,
    applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
    premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings]

theorem lookupDecision_different_rewriteAt_exact (fuel : Nat)
    (name tail index : Pattern)
    (recursive :
      rewriteAt (engineBasePremises relations) language fuel
        (lookup name tail) = [index]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (lookupDecision PatternEqualityDecision.different name tail) =
      [targetIndexSucc index] := by
  simp only [lookup, a] at recursive
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:lookup-decision"
      [PatternEqualityDecision.different, name, tail]) =
        [targetIndexSucc index]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    lookupDecisionRootRules]
  simp [lookupRules, mkRule, congruence, lookupDecision, lookup,
    targetIndexZero, targetIndexSucc, a, v, applyRuleUsing,
    PatternEqualityDecision.equal, PatternEqualityDecision.different,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings, recursive]

theorem lookup_head_rewriteAt_exact (fuel : Nat)
    (name tail : Pattern) :
    rewriteAt (engineBasePremises relations) language (fuel + 2)
        (lookup name (environmentCons name tail)) = [targetIndexZero] := by
  change rewriteAt (engineBasePremises relations) language (fuel + 2)
    (.apply "tptp-fof-resolve:lookup"
      [name, .apply "tptp-fof-resolve:environment-cons" [name, tail]]) =
        [targetIndexZero]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    lookupRootRules]
  simp [lookupRules, mkRule, congruence, lookup, lookupDecision,
    environmentCons, targetIndexZero, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]
  have relationStep := equalityPremise_equal_exact name tail
  simp only [v] at relationStep
  rw [relationStep]
  simp
  have decisionStep :=
    lookupDecision_equal_rewriteAt_exact fuel name tail
  simp only [lookupDecision, a] at decisionStep
  rw [decisionStep]
  simp [targetIndexZero, a]

theorem lookup_tail_rewriteAt_exact (fuel : Nat)
    (name binder tail index : Pattern) (different : name ≠ binder)
    (recursive :
      rewriteAt (engineBasePremises relations) language fuel
        (lookup name tail) = [index]) :
    rewriteAt (engineBasePremises relations) language (fuel + 2)
        (lookup name (environmentCons binder tail)) =
      [targetIndexSucc index] := by
  simp only [lookup, a] at recursive
  change rewriteAt (engineBasePremises relations) language (fuel + 2)
    (.apply "tptp-fof-resolve:lookup"
      [name, .apply "tptp-fof-resolve:environment-cons" [binder, tail]]) =
        [targetIndexSucc index]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    lookupRootRules]
  simp [lookupRules, mkRule, congruence, lookup, lookupDecision,
    environmentCons, targetIndexSucc, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]
  have relationStep :=
    equalityPremise_different_exact name binder tail different
  simp only [v] at relationStep
  rw [relationStep]
  simp
  have decisionStep :=
    lookupDecision_different_rewriteAt_exact fuel name tail index recursive
  simp only [lookupDecision, a] at decisionStep
  rw [decisionStep]
  simp [targetIndexSucc, a]

theorem term_variable_rewriteAt_exact (fuel : Nat)
    (environment name index : Pattern)
    (lookupStep :
      rewriteAt (engineBasePremises relations) language fuel
        (lookup name environment) = [index]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveTerm environment (sourceVariable name)) =
      [targetVariable index] := by
  simp only [lookup, a] at lookupStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:term"
      [environment,
       .apply "tptp-fof-named:term-variable"
         [.apply "tptp-fof-named:name" [name]]]) =
      [targetVariable index]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    termRootRules]
  simp [termRules, mkRule, congruence, resolveTerm, resolveTerms, lookup,
    sourceVariable, sourceFunction, sourceName, targetVariable,
    targetFunction, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings, lookupStep]

theorem term_function_rewriteAt_exact (fuel : Nat)
    (environment name arguments argumentsResult : Pattern)
    (argumentsStep :
      rewriteAt (engineBasePremises relations) language fuel
        (resolveTerms environment arguments) = [argumentsResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveTerm environment (sourceFunction name arguments)) =
      [targetFunction name argumentsResult] := by
  simp only [resolveTerms, a] at argumentsStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:term"
      [environment,
       .apply "tptp-fof-named:term-function"
         [name, arguments]]) =
      [targetFunction name argumentsResult]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    termRootRules]
  simp [termRules, mkRule, congruence, resolveTerm, resolveTerms,
    sourceVariable, sourceFunction, sourceName, targetVariable,
    targetFunction, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings, argumentsStep]

theorem terms_nil_rewriteAt_exact (fuel : Nat) (environment : Pattern) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveTerms environment sourceTermsNil) = [targetTermsNil] := by
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:terms"
      [environment, .apply "tptp-fof-named:terms-nil" []]) =
      [targetTermsNil]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    termsRootRules]
  simp [termRules, mkRule, congruence, resolveTerm, resolveTerms,
    sourceTermsNil, sourceTermsCons, targetTermsNil, targetTermsCons,
    a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]

theorem terms_cons_rewriteAt_exact (fuel : Nat)
    (environment head tail headResult tailResult : Pattern)
    (headStep :
      rewriteAt (engineBasePremises relations) language fuel
        (resolveTerm environment head) = [headResult])
    (tailStep :
      rewriteAt (engineBasePremises relations) language fuel
        (resolveTerms environment tail) = [tailResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveTerms environment (sourceTermsCons head tail)) =
      [targetTermsCons headResult tailResult] := by
  simp only [resolveTerm, resolveTerms, a] at headStep tailStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:terms"
      [environment,
       .apply "tptp-fof-named:terms-cons" [head, tail]]) =
      [targetTermsCons headResult tailResult]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    termsRootRules]
  simp [termRules, mkRule, congruence, resolveTerm, resolveTerms,
    sourceTermsNil, sourceTermsCons, targetTermsNil, targetTermsCons,
    a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings, headStep, tailStep]

theorem term_variable_eventuallyExact
    (environment name index : Pattern)
    (lookupExact : EventuallyExact (lookup name environment) index) :
    EventuallyExact (resolveTerm environment (sourceVariable name))
      (targetVariable index) := by
  rcases lookupExact with ⟨requiredFuel, lookupExact⟩
  refine ⟨requiredFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ fuel =>
      apply term_variable_rewriteAt_exact
      apply lookupExact
      omega

theorem term_function_eventuallyExact
    (environment name arguments argumentsResult : Pattern)
    (argumentsExact :
      EventuallyExact (resolveTerms environment arguments) argumentsResult) :
    EventuallyExact (resolveTerm environment (sourceFunction name arguments))
      (targetFunction name argumentsResult) := by
  rcases argumentsExact with ⟨requiredFuel, argumentsExact⟩
  refine ⟨requiredFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ fuel =>
      apply term_function_rewriteAt_exact
      apply argumentsExact
      omega

theorem terms_nil_eventuallyExact (environment : Pattern) :
    EventuallyExact (resolveTerms environment sourceTermsNil)
      targetTermsNil := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ fuel =>
      simpa [Nat.succ_eq_add_one] using
        terms_nil_rewriteAt_exact fuel environment

theorem terms_cons_eventuallyExact
    (environment head tail headResult tailResult : Pattern)
    (headExact :
      EventuallyExact (resolveTerm environment head) headResult)
    (tailExact :
      EventuallyExact (resolveTerms environment tail) tailResult) :
    EventuallyExact (resolveTerms environment (sourceTermsCons head tail))
      (targetTermsCons headResult tailResult) := by
  rcases headExact with ⟨headFuel, headExact⟩
  rcases tailExact with ⟨tailFuel, tailExact⟩
  refine ⟨max headFuel tailFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ fuel =>
      apply terms_cons_rewriteAt_exact
      · apply headExact
        omega
      · apply tailExact
        omega

local macro "simplify_formula_rows" : tactic =>
  `(tactic|
    simp [formulaLeafRules, formulaAtomRules, unaryFormulaRule,
      binaryFormulaRules, binaryFormulaRule, binderFormulaRules,
      binderFormulaRule, mkRule, congruence, resolveFormula, resolveTerm,
      resolveTerms, sourceFormula, sourceName, sourceVariable,
      sourceFunction, sourceTermsNil, sourceTermsCons, targetFormula,
      targetVariable, targetFunction, targetTermsNil, targetTermsCons,
      environmentCons, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings])

theorem formula_verum_rewriteAt_exact (fuel : Nat)
    (environment : Pattern) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "verum")) =
      [targetFormula "verum"] := by
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:verum" []]) =
      [.apply "tptp-fof-resolved:verum" []]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows

theorem formula_falsum_rewriteAt_exact (fuel : Nat)
    (environment : Pattern) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "falsum")) =
      [targetFormula "falsum"] := by
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:falsum" []]) =
      [.apply "tptp-fof-resolved:falsum" []]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows

theorem formula_predicate_rewriteAt_exact (fuel : Nat)
    (environment name arguments argumentsResult : Pattern)
    (argumentsStep :
      rewriteAt (engineBasePremises relations) language fuel
        (resolveTerms environment arguments) = [argumentsResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment
          (sourceFormula "predicate" [name, arguments])) =
      [targetFormula "predicate" [name, argumentsResult]] := by
  simp only [resolveTerms, a] at argumentsStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment,
       .apply "tptp-fof-named:predicate"
         [name, arguments]]) =
      [.apply "tptp-fof-resolved:predicate" [name, argumentsResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [argumentsStep]
  simp

theorem formula_equal_rewriteAt_exact (fuel : Nat)
    (environment left right leftResult rightResult : Pattern)
    (leftStep :
      rewriteAt (engineBasePremises relations) language fuel
        (resolveTerm environment left) = [leftResult])
    (rightStep :
      rewriteAt (engineBasePremises relations) language fuel
        (resolveTerm environment right) = [rightResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "equal" [left, right])) =
      [targetFormula "equal" [leftResult, rightResult]] := by
  simp only [resolveTerm, a] at leftStep rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:equal" [left, right]]) =
      [.apply "tptp-fof-resolved:equal" [leftResult, rightResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp
  rw [rightStep]
  simp

theorem formula_not_rewriteAt_exact (fuel : Nat)
    (environment body bodyResult : Pattern)
    (bodyStep :
      rewriteAt (engineBasePremises relations) language fuel
        (resolveFormula environment body) = [bodyResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "not" [body])) =
      [targetFormula "not" [bodyResult]] := by
  simp only [resolveFormula, a] at bodyStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:not" [body]]) =
      [.apply "tptp-fof-resolved:not" [bodyResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [bodyStep]
  simp

theorem formula_and_rewriteAt_exact (fuel : Nat)
    (environment left right leftResult rightResult : Pattern)
    (leftStep :
      rewriteAt (engineBasePremises relations) language fuel
        (resolveFormula environment left) = [leftResult])
    (rightStep :
      rewriteAt (engineBasePremises relations) language fuel
        (resolveFormula environment right) = [rightResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "and" [left, right])) =
      [targetFormula "and" [leftResult, rightResult]] := by
  simp only [resolveFormula, a] at leftStep rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:and" [left, right]]) =
      [.apply "tptp-fof-resolved:and" [leftResult, rightResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp
  rw [rightStep]
  simp

theorem formula_or_rewriteAt_exact (fuel : Nat)
    (environment left right leftResult rightResult : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = [leftResult])
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = [rightResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "or" [left, right])) =
      [targetFormula "or" [leftResult, rightResult]] := by
  simp only [resolveFormula, a] at leftStep rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:or" [left, right]]) =
      [.apply "tptp-fof-resolved:or" [leftResult, rightResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp
  rw [rightStep]
  simp

theorem formula_iff_rewriteAt_exact (fuel : Nat)
    (environment left right leftResult rightResult : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = [leftResult])
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = [rightResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "iff" [left, right])) =
      [targetFormula "iff" [leftResult, rightResult]] := by
  simp only [resolveFormula, a] at leftStep rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:iff" [left, right]]) =
      [.apply "tptp-fof-resolved:iff" [leftResult, rightResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp
  rw [rightStep]
  simp

theorem formula_implies_rewriteAt_exact (fuel : Nat)
    (environment left right leftResult rightResult : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = [leftResult])
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = [rightResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment
          (sourceFormula "implies" [left, right])) =
      [targetFormula "implies" [leftResult, rightResult]] := by
  simp only [resolveFormula, a] at leftStep rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:implies" [left, right]]) =
      [.apply "tptp-fof-resolved:implies" [leftResult, rightResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp
  rw [rightStep]
  simp

theorem formula_reverseImplies_rewriteAt_exact (fuel : Nat)
    (environment left right leftResult rightResult : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = [leftResult])
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = [rightResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment
          (sourceFormula "reverse-implies" [left, right])) =
      [targetFormula "reverse-implies" [leftResult, rightResult]] := by
  simp only [resolveFormula, a] at leftStep rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment,
       .apply "tptp-fof-named:reverse-implies" [left, right]]) =
      [.apply "tptp-fof-resolved:reverse-implies"
        [leftResult, rightResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp
  rw [rightStep]
  simp

theorem formula_xor_rewriteAt_exact (fuel : Nat)
    (environment left right leftResult rightResult : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = [leftResult])
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = [rightResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "xor" [left, right])) =
      [targetFormula "xor" [leftResult, rightResult]] := by
  simp only [resolveFormula, a] at leftStep rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:xor" [left, right]]) =
      [.apply "tptp-fof-resolved:xor" [leftResult, rightResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp
  rw [rightStep]
  simp

theorem formula_nor_rewriteAt_exact (fuel : Nat)
    (environment left right leftResult rightResult : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = [leftResult])
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = [rightResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "nor" [left, right])) =
      [targetFormula "nor" [leftResult, rightResult]] := by
  simp only [resolveFormula, a] at leftStep rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:nor" [left, right]]) =
      [.apply "tptp-fof-resolved:nor" [leftResult, rightResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp
  rw [rightStep]
  simp

theorem formula_nand_rewriteAt_exact (fuel : Nat)
    (environment left right leftResult rightResult : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = [leftResult])
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = [rightResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "nand" [left, right])) =
      [targetFormula "nand" [leftResult, rightResult]] := by
  simp only [resolveFormula, a] at leftStep rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:nand" [left, right]]) =
      [.apply "tptp-fof-resolved:nand" [leftResult, rightResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp
  rw [rightStep]
  simp

theorem formula_all_rewriteAt_exact (fuel : Nat)
    (environment binder body bodyResult : Pattern)
    (bodyStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula (environmentCons binder environment) body) =
        [bodyResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment
          (sourceFormula "all" [sourceName binder, body])) =
      [targetFormula "all" [bodyResult]] := by
  simp only [resolveFormula, environmentCons, a] at bodyStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment,
       .apply "tptp-fof-named:all"
         [.apply "tptp-fof-named:name" [binder], body]]) =
      [.apply "tptp-fof-resolved:all" [bodyResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [bodyStep]
  simp

theorem formula_ex_rewriteAt_exact (fuel : Nat)
    (environment binder body bodyResult : Pattern)
    (bodyStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula (environmentCons binder environment) body) =
        [bodyResult]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment
          (sourceFormula "ex" [sourceName binder, body])) =
      [targetFormula "ex" [bodyResult]] := by
  simp only [resolveFormula, environmentCons, a] at bodyStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment,
       .apply "tptp-fof-named:ex"
         [.apply "tptp-fof-named:name" [binder], body]]) =
      [.apply "tptp-fof-resolved:ex" [bodyResult]]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [bodyStep]
  simp

/-! ## Exact failure propagation -/

/-- A request is operationally absent at every contextual fuel. -/
def AlwaysEmpty (source : Pattern) : Prop :=
  ∀ fuel, rewriteAt (engineBasePremises relations) language fuel source = []

theorem lookup_nil_rewriteAt_empty (fuel : Nat) (name : Pattern) :
    rewriteAt (engineBasePremises relations) language fuel
        (lookup name environmentNil) = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      change rewriteAt (engineBasePremises relations) language (fuel + 1)
        (.apply "tptp-fof-resolve:lookup"
          [name, .apply "tptp-fof-resolve:environment-nil" []]) = []
      rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
        lookupRootRules]
      simp [lookupRules, mkRule, congruence, lookup, environmentCons,
        a, v, applyRuleUsing,
        matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
        matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
        applyBindings]

theorem lookupDecision_different_rewriteAt_empty (fuel : Nat)
    (name tail : Pattern)
    (recursive : rewriteAt (engineBasePremises relations) language fuel
      (lookup name tail) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (lookupDecision PatternEqualityDecision.different name tail) = [] := by
  simp only [lookup, a] at recursive
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:lookup-decision"
      [PatternEqualityDecision.different, name, tail]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    lookupDecisionRootRules]
  simp [lookupRules, mkRule, congruence, lookupDecision, lookup,
    targetIndexZero, targetIndexSucc, a, v, applyRuleUsing,
    PatternEqualityDecision.equal, PatternEqualityDecision.different,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings, recursive]

theorem lookup_tail_rewriteAt_empty (fuel : Nat)
    (name binder tail : Pattern) (different : name ≠ binder)
    (recursive : rewriteAt (engineBasePremises relations) language fuel
      (lookup name tail) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 2)
        (lookup name (environmentCons binder tail)) = [] := by
  change rewriteAt (engineBasePremises relations) language (fuel + 2)
    (.apply "tptp-fof-resolve:lookup"
      [name, .apply "tptp-fof-resolve:environment-cons" [binder, tail]]) = []
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    lookupRootRules]
  simp [lookupRules, mkRule, congruence, lookup, lookupDecision,
    environmentCons, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]
  have relationStep :=
    equalityPremise_different_exact name binder tail different
  simp only [v] at relationStep
  rw [relationStep]
  simp
  have decisionStep :=
    lookupDecision_different_rewriteAt_empty fuel name tail recursive
  simp only [lookupDecision, a] at decisionStep
  rw [decisionStep]
  simp

theorem term_variable_rewriteAt_empty (fuel : Nat)
    (environment name : Pattern)
    (lookupStep : rewriteAt (engineBasePremises relations) language fuel
      (lookup name environment) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveTerm environment (sourceVariable name)) = [] := by
  simp only [lookup, a] at lookupStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:term"
      [environment,
       .apply "tptp-fof-named:term-variable"
         [.apply "tptp-fof-named:name" [name]]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    termRootRules]
  simp [termRules, mkRule, congruence, resolveTerm, resolveTerms, lookup,
    sourceVariable, sourceFunction, sourceName, targetVariable,
    targetFunction, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings, lookupStep]

theorem term_function_rewriteAt_empty (fuel : Nat)
    (environment name arguments : Pattern)
    (argumentsStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveTerms environment arguments) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveTerm environment (sourceFunction name arguments)) = [] := by
  simp only [resolveTerms, a] at argumentsStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:term"
      [environment,
       .apply "tptp-fof-named:term-function"
         [name, arguments]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    termRootRules]
  simp [termRules, mkRule, congruence, resolveTerm, resolveTerms,
    sourceVariable, sourceFunction, sourceName, targetVariable,
    targetFunction, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings, argumentsStep]

theorem terms_cons_head_rewriteAt_empty (fuel : Nat)
    (environment head tail : Pattern)
    (headStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveTerm environment head) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveTerms environment (sourceTermsCons head tail)) = [] := by
  simp only [resolveTerm, a] at headStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:terms"
      [environment, .apply "tptp-fof-named:terms-cons" [head, tail]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    termsRootRules]
  simp [termRules, mkRule, congruence, resolveTerm, resolveTerms,
    sourceTermsNil, sourceTermsCons, targetTermsNil, targetTermsCons,
    a, v, applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
    premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, headStep]

theorem terms_cons_tail_rewriteAt_empty (fuel : Nat)
    (environment head tail : Pattern)
    (tailStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveTerms environment tail) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveTerms environment (sourceTermsCons head tail)) = [] := by
  simp only [resolveTerms, a] at tailStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:terms"
      [environment, .apply "tptp-fof-named:terms-cons" [head, tail]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    termsRootRules]
  simp [termRules, mkRule, congruence, resolveTerm, resolveTerms,
    sourceTermsNil, sourceTermsCons, targetTermsNil, targetTermsCons,
    a, v, applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
    premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings]
  intro bindings headResult headMember bindingsEquality
  subst bindings
  intro tailResult tailMember
  have impossible : tailResult ∈
      rewriteAt (engineBasePremises relations) language fuel
        (.apply "tptp-fof-resolve:terms" [environment, tail]) := by
    simpa [Bindings.lookup] using tailMember
  rw [tailStep] at impossible
  simp at impossible

theorem formula_predicate_rewriteAt_empty (fuel : Nat)
    (environment name arguments : Pattern)
    (argumentsStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveTerms environment arguments) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment
          (sourceFormula "predicate" [name, arguments])) = [] := by
  simp only [resolveTerms, a] at argumentsStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment,
       .apply "tptp-fof-named:predicate"
         [name, arguments]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [argumentsStep]
  simp

theorem formula_equal_left_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveTerm environment left) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "equal" [left, right])) = [] := by
  simp only [resolveTerm, a] at leftStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:equal" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp

theorem formula_equal_right_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveTerm environment right) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "equal" [left, right])) = [] := by
  simp only [resolveTerm, a] at rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:equal" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  intro bindings leftResult leftMember bindingsEquality
  subst bindings
  intro rightResult rightMember
  have impossible : rightResult ∈
      rewriteAt (engineBasePremises relations) language fuel
        (.apply "tptp-fof-resolve:term" [environment, right]) := by
    simpa [Bindings.lookup] using rightMember
  rw [rightStep] at impossible
  simp at impossible

theorem formula_not_rewriteAt_empty (fuel : Nat)
    (environment body : Pattern)
    (bodyStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment body) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "not" [body])) = [] := by
  simp only [resolveFormula, a] at bodyStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:not" [body]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [bodyStep]
  simp

private theorem formula_and_left_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "and" [left, right])) = [] := by
  simp only [resolveFormula, a] at leftStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:and" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp

private theorem formula_and_right_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "and" [left, right])) = [] := by
  simp only [resolveFormula, a] at rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:and" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  intro bindings leftResult leftMember bindingsEquality
  subst bindings
  intro rightResult rightMember
  have impossible : rightResult ∈
      rewriteAt (engineBasePremises relations) language fuel
        (.apply "tptp-fof-resolve:formula" [environment, right]) := by
    simpa [Bindings.lookup] using rightMember
  rw [rightStep] at impossible
  simp at impossible

private theorem formula_or_left_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "or" [left, right])) = [] := by
  simp only [resolveFormula, a] at leftStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:or" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp

private theorem formula_or_right_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "or" [left, right])) = [] := by
  simp only [resolveFormula, a] at rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:or" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  intro bindings leftResult leftMember bindingsEquality
  subst bindings
  intro rightResult rightMember
  have impossible : rightResult ∈
      rewriteAt (engineBasePremises relations) language fuel
        (.apply "tptp-fof-resolve:formula" [environment, right]) := by
    simpa [Bindings.lookup] using rightMember
  rw [rightStep] at impossible
  simp at impossible

private theorem formula_iff_left_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "iff" [left, right])) = [] := by
  simp only [resolveFormula, a] at leftStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:iff" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp

private theorem formula_iff_right_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "iff" [left, right])) = [] := by
  simp only [resolveFormula, a] at rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:iff" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  intro bindings leftResult leftMember bindingsEquality
  subst bindings
  intro rightResult rightMember
  have impossible : rightResult ∈
      rewriteAt (engineBasePremises relations) language fuel
        (.apply "tptp-fof-resolve:formula" [environment, right]) := by
    simpa [Bindings.lookup] using rightMember
  rw [rightStep] at impossible
  simp at impossible

private theorem formula_implies_left_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "implies" [left, right])) = [] := by
  simp only [resolveFormula, a] at leftStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:implies" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp

private theorem formula_implies_right_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "implies" [left, right])) = [] := by
  simp only [resolveFormula, a] at rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:implies" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  intro bindings leftResult leftMember bindingsEquality
  subst bindings
  intro rightResult rightMember
  have impossible : rightResult ∈
      rewriteAt (engineBasePremises relations) language fuel
        (.apply "tptp-fof-resolve:formula" [environment, right]) := by
    simpa [Bindings.lookup] using rightMember
  rw [rightStep] at impossible
  simp at impossible

private theorem formula_reverseImplies_left_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "reverse-implies" [left, right])) = [] := by
  simp only [resolveFormula, a] at leftStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:reverse-implies" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp

private theorem formula_reverseImplies_right_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "reverse-implies" [left, right])) = [] := by
  simp only [resolveFormula, a] at rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:reverse-implies" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  intro bindings leftResult leftMember bindingsEquality
  subst bindings
  intro rightResult rightMember
  have impossible : rightResult ∈
      rewriteAt (engineBasePremises relations) language fuel
        (.apply "tptp-fof-resolve:formula" [environment, right]) := by
    simpa [Bindings.lookup] using rightMember
  rw [rightStep] at impossible
  simp at impossible

private theorem formula_xor_left_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "xor" [left, right])) = [] := by
  simp only [resolveFormula, a] at leftStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:xor" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp

private theorem formula_xor_right_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "xor" [left, right])) = [] := by
  simp only [resolveFormula, a] at rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:xor" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  intro bindings leftResult leftMember bindingsEquality
  subst bindings
  intro rightResult rightMember
  have impossible : rightResult ∈
      rewriteAt (engineBasePremises relations) language fuel
        (.apply "tptp-fof-resolve:formula" [environment, right]) := by
    simpa [Bindings.lookup] using rightMember
  rw [rightStep] at impossible
  simp at impossible

private theorem formula_nor_left_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "nor" [left, right])) = [] := by
  simp only [resolveFormula, a] at leftStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:nor" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp

private theorem formula_nor_right_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "nor" [left, right])) = [] := by
  simp only [resolveFormula, a] at rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:nor" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  intro bindings leftResult leftMember bindingsEquality
  subst bindings
  intro rightResult rightMember
  have impossible : rightResult ∈
      rewriteAt (engineBasePremises relations) language fuel
        (.apply "tptp-fof-resolve:formula" [environment, right]) := by
    simpa [Bindings.lookup] using rightMember
  rw [rightStep] at impossible
  simp at impossible

private theorem formula_nand_left_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "nand" [left, right])) = [] := by
  simp only [resolveFormula, a] at leftStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:nand" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  rw [leftStep]
  simp

private theorem formula_nand_right_rewriteAt_empty (fuel : Nat)
    (environment left right : Pattern)
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula "nand" [left, right])) = [] := by
  simp only [resolveFormula, a] at rightStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:formula"
      [environment, .apply "tptp-fof-named:nand" [left, right]]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    formulaRootRules]
  simplify_formula_rows
  intro bindings leftResult leftMember bindingsEquality
  subst bindings
  intro rightResult rightMember
  have impossible : rightResult ∈
      rewriteAt (engineBasePremises relations) language fuel
        (.apply "tptp-fof-resolve:formula" [environment, right]) := by
    simpa [Bindings.lookup] using rightMember
  rw [rightStep] at impossible
  simp at impossible

theorem formula_binary_left_rewriteAt_empty (fuel : Nat)
    (constructor : String)
    (supported : constructor ∈
      ["and", "or", "iff", "implies", "reverse-implies", "xor", "nor", "nand"])
    (environment left right : Pattern)
    (leftStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment left) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula constructor [left, right])) = [] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact formula_and_left_rewriteAt_empty fuel environment left right leftStep
  · exact formula_or_left_rewriteAt_empty fuel environment left right leftStep
  · exact formula_iff_left_rewriteAt_empty fuel environment left right leftStep
  · exact formula_implies_left_rewriteAt_empty fuel environment left right leftStep
  · exact formula_reverseImplies_left_rewriteAt_empty fuel environment left right leftStep
  · exact formula_xor_left_rewriteAt_empty fuel environment left right leftStep
  · exact formula_nor_left_rewriteAt_empty fuel environment left right leftStep
  · exact formula_nand_left_rewriteAt_empty fuel environment left right leftStep

theorem formula_binary_right_rewriteAt_empty (fuel : Nat)
    (constructor : String)
    (supported : constructor ∈
      ["and", "or", "iff", "implies", "reverse-implies", "xor", "nor", "nand"])
    (environment left right : Pattern)
    (rightStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environment right) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment (sourceFormula constructor [left, right])) = [] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact formula_and_right_rewriteAt_empty fuel environment left right rightStep
  · exact formula_or_right_rewriteAt_empty fuel environment left right rightStep
  · exact formula_iff_right_rewriteAt_empty fuel environment left right rightStep
  · exact formula_implies_right_rewriteAt_empty fuel environment left right rightStep
  · exact formula_reverseImplies_right_rewriteAt_empty fuel environment left right rightStep
  · exact formula_xor_right_rewriteAt_empty fuel environment left right rightStep
  · exact formula_nor_right_rewriteAt_empty fuel environment left right rightStep
  · exact formula_nand_right_rewriteAt_empty fuel environment left right rightStep

theorem formula_binder_rewriteAt_empty (fuel : Nat)
    (constructor : String) (supported : constructor ∈ ["all", "ex"])
    (environment binder body : Pattern)
    (bodyStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula (environmentCons binder environment) body) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveFormula environment
          (sourceFormula constructor [sourceName binder, body])) = [] := by
  simp only [resolveFormula, environmentCons, a] at bodyStep
  simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with (rfl | rfl) <;>
    simp only [resolveFormula, sourceFormula, sourceName, a] <;>
    rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
      formulaRootRules] <;>
    simplify_formula_rows <;>
    rw [bodyStep] <;>
    simp

theorem closed_rewriteAt_empty (fuel : Nat) (formula : Pattern)
    (formulaStep : rewriteAt (engineBasePremises relations) language fuel
      (resolveFormula environmentNil formula) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveClosed formula) = [] := by
  simp only [resolveFormula, environmentNil, a] at formulaStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:closed" [formula]) = []
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    closedRootRules]
  simp [closedRule, mkRule, congruence, resolveClosed, resolveFormula,
    environmentNil, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings, formulaStep]

private theorem leaf_eventuallyExact (source result : Pattern)
    (step : ∀ fuel,
      rewriteAt (engineBasePremises relations) language (fuel + 1) source =
        [result]) :
    EventuallyExact source result := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ fuel => simpa [Nat.succ_eq_add_one] using step fuel

private theorem unary_eventuallyExact
    (childSource childResult source result : Pattern)
    (childExact : EventuallyExact childSource childResult)
    (step : ∀ fuel,
      rewriteAt (engineBasePremises relations) language fuel childSource =
          [childResult] →
        rewriteAt (engineBasePremises relations) language (fuel + 1) source =
          [result]) :
    EventuallyExact source result := by
  rcases childExact with ⟨requiredFuel, childExact⟩
  refine ⟨requiredFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ fuel =>
      apply step
      apply childExact
      omega

private theorem binary_eventuallyExact
    (leftSource leftResult rightSource rightResult source result : Pattern)
    (leftExact : EventuallyExact leftSource leftResult)
    (rightExact : EventuallyExact rightSource rightResult)
    (step : ∀ fuel,
      rewriteAt (engineBasePremises relations) language fuel leftSource =
          [leftResult] →
        rewriteAt (engineBasePremises relations) language fuel rightSource =
            [rightResult] →
          rewriteAt (engineBasePremises relations) language (fuel + 1)
            source = [result]) :
    EventuallyExact source result := by
  rcases leftExact with ⟨leftFuel, leftExact⟩
  rcases rightExact with ⟨rightFuel, rightExact⟩
  refine ⟨max leftFuel rightFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ fuel =>
      apply step
      · apply leftExact
        omega
      · apply rightExact
        omega

theorem closed_rewriteAt_exact (fuel : Nat) (formula result : Pattern)
    (formulaStep :
      rewriteAt (engineBasePremises relations) language fuel
        (resolveFormula environmentNil formula) = [result]) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
        (resolveClosed formula) = [result] := by
  simp only [resolveFormula, environmentNil, a] at formulaStep
  change rewriteAt (engineBasePremises relations) language (fuel + 1)
    (.apply "tptp-fof-resolve:closed" [formula]) = [result]
  rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter,
    closedRootRules]
  simp [closedRule, mkRule, congruence, resolveClosed, resolveFormula,
    environmentNil, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings, formulaStep]

theorem closed_eventuallyExact (formula result : Pattern)
    (formulaExact : EventuallyExact
      (resolveFormula environmentNil formula) result) :
    EventuallyExact (resolveClosed formula) result := by
  rcases formulaExact with ⟨requiredFuel, formulaExact⟩
  refine ⟨requiredFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ fuel =>
      apply closed_rewriteAt_exact
      apply formulaExact
      omega

private theorem stepAt_mono_fuel
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {fuel largerFuel : Nat} {source target : Pattern}
    (evidence : StepAt base lang fuel source target)
    (enough : fuel ≤ largerFuel) :
    StepAt base lang largerFuel source target := by
  induction fuel generalizing source target largerFuel with
  | zero => cases evidence
  | succ fuel inductionHypothesis =>
      cases largerFuel with
      | zero => omega
      | succ largerFuel =>
          have premiseMono :
              ∀ {initial final : Bindings} {premise : Premise},
                PremiseAt base lang fuel initial premise final →
                  PremiseAt base lang largerFuel initial premise final := by
            intro initial final premise premiseEvidence
            cases premiseEvidence with
            | freshness member => exact .freshness member
            | relationQuery member => exact .relationQuery member
            | forAll member => exact .forAll member
            | congruence recursive matched merged =>
                exact .congruence
                  (inductionHypothesis recursive (by omega)) matched merged
          have premisesMono :
              ∀ {initial final : Bindings} {premises : List Premise},
                PremisesAt base lang fuel initial premises final →
                  PremisesAt base lang largerFuel initial premises final := by
            intro initial final premises premiseEvidence
            induction premises generalizing initial final with
            | nil =>
                cases premiseEvidence
                exact .nil initial
            | cons premise premises inductionHypothesis =>
                cases premiseEvidence with
                | cons first rest =>
                    exact .cons (premiseMono first) (inductionHypothesis rest)
          cases evidence with
          | rule ruleMember matched premises targetEq =>
              exact .rule ruleMember matched (premisesMono premises) targetEq

private theorem mem_rewriteAt_mono_fuel
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {fuel largerFuel : Nat} {source target : Pattern}
    (member : target ∈ rewriteAt base lang fuel source)
    (enough : fuel ≤ largerFuel) :
    target ∈ rewriteAt base lang largerFuel source := by
  apply mem_rewriteAt_iff_stepAt.mpr
  exact stepAt_mono_fuel (mem_rewriteAt_iff_stepAt.mp member) enough

private theorem alwaysEmpty_of_eventually_empty (source : Pattern)
    (requiredFuel : Nat)
    (empty : ∀ fuel, requiredFuel ≤ fuel →
      rewriteAt (engineBasePremises relations) language fuel source = []) :
    AlwaysEmpty source := by
  intro fuel
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro target member
  have lifted := mem_rewriteAt_mono_fuel member
    (Nat.le_max_left fuel requiredFuel)
  rw [empty (max fuel requiredFuel)
    (Nat.le_max_right fuel requiredFuel)] at lifted
  simp at lifted

private theorem alwaysEmpty_of_offset_step
    (child source : Pattern) (offset : Nat)
    (childEmpty : AlwaysEmpty child)
    (step : ∀ fuel,
      rewriteAt (engineBasePremises relations) language fuel child = [] →
        rewriteAt (engineBasePremises relations) language (fuel + offset)
          source = []) :
    AlwaysEmpty source := by
  apply alwaysEmpty_of_eventually_empty source offset
  intro fuel enough
  rw [show fuel = (fuel - offset) + offset by omega]
  exact step (fuel - offset) (childEmpty (fuel - offset))

/-- A successful semantic resolution is the only authored result at every
fuel. This excludes alternative binder indices, reordered children, and
duplicate semantic targets even below the successful structural threshold. -/
theorem EventuallyExact.no_invention {source result target : Pattern}
    (exact : EventuallyExact source result) (fuel : Nat)
    (member : target ∈
      rewriteAt (engineBasePremises relations) language fuel source) :
    target = result := by
  rcases exact with ⟨requiredFuel, exact⟩
  have lifted := mem_rewriteAt_mono_fuel member
    (Nat.le_max_left fuel requiredFuel)
  rw [exact (max fuel requiredFuel)
    (Nat.le_max_right fuel requiredFuel)] at lifted
  simpa using lifted

theorem lookupBinder?_eventuallyExact (name : String)
    (environment : List String) (index : Fin environment.length)
    (resolved :
      TptpFofBinderResolution.lookupBinder? name environment = some index) :
    EventuallyExact
      (lookup (a name) (encodeEnvironment environment))
      (TptpResolvedFofLanguageDef.encodeIndex index) := by
  induction environment generalizing name with
  | nil =>
      simp [TptpFofBinderResolution.lookupBinder?] at resolved
  | cons binder environment inductionHypothesis =>
      by_cases same : name = binder
      · subst binder
        rw [TptpFofBinderResolution.lookupBinder?_head] at resolved
        have indexEquality := Option.some.inj resolved
        subst index
        refine ⟨2, ?_⟩
        intro fuel enough
        rw [show fuel = (fuel - 2) + 2 by omega]
        simpa only [encodeEnvironment_cons, encodeIndex_zero]
          using lookup_head_rewriteAt_exact (fuel - 2) (a name)
            (encodeEnvironment environment)
      · rw [TptpFofBinderResolution.lookupBinder?_tail same] at resolved
        cases inner : TptpFofBinderResolution.lookupBinder? name environment with
        | none => simp [inner] at resolved
        | some predecessor =>
            have mapped : some (Fin.succ predecessor) = some index := by
              simpa [inner] using resolved
            have indexEquality : Fin.succ predecessor = index :=
              Option.some.inj mapped
            subst index
            rcases inductionHypothesis name predecessor inner with
              ⟨requiredFuel, innerExact⟩
            have patternDifferent : a name ≠ a binder := by
              intro equality
              injection equality with equality
              exact same equality
            refine ⟨requiredFuel + 2, ?_⟩
            intro fuel enough
            have recursive := innerExact (fuel - 2) (by omega)
            rw [show fuel = (fuel - 2) + 2 by omega]
            simpa only [encodeEnvironment_cons, encodeIndex_succ] using
              lookup_tail_rewriteAt_exact (fuel - 2) (a name) (a binder)
                (encodeEnvironment environment)
                (TptpResolvedFofLanguageDef.encodeIndex predecessor)
                patternDifferent recursive

private def TermAgreement (environment : List String)
    (source : TptpFofBinderResolution.NamedTerm) : Prop :=
  ∀ result,
    TptpFofBinderResolution.resolveTerm? environment source = some result →
      EventuallyExact
        (resolveTerm (encodeEnvironment environment)
          (TptpNamedFofLanguageDef.encodeTerm source))
        (TptpResolvedFofLanguageDef.encodeTerm result)

private def TermsAgreement (environment : List String)
    (sources : List TptpFofBinderResolution.NamedTerm) : Prop :=
  ∀ results,
    sources.mapM (TptpFofBinderResolution.resolveTerm? environment) =
        some results →
      EventuallyExact
        (resolveTerms (encodeEnvironment environment)
          (TptpNamedFofLanguageDef.encodeTerms sources))
        (TptpResolvedFofLanguageDef.encodeTerms results)

private theorem variableAgreement (environment : List String)
    (name : String) :
    TermAgreement environment (.variable name) := by
  intro result resolved
  cases found : TptpFofBinderResolution.lookupBinder? name environment with
  | none => simp [TptpFofBinderResolution.resolveTerm?, found] at resolved
  | some index =>
      have mapped : some (Semiterm.bvar index) = some result := by
        simpa [TptpFofBinderResolution.resolveTerm?, found] using resolved
      have resultEquality : Semiterm.bvar index = result := by
        exact Option.some.inj mapped
      subst result
      simpa only [encodeNamedTerm_variable, encodeTerm_bvar] using
        term_variable_eventuallyExact
          (encodeEnvironment environment) (a name)
          (TptpResolvedFofLanguageDef.encodeIndex index)
          (lookupBinder?_eventuallyExact name environment index found)

private theorem functionAgreement (environment : List String)
    (head : FunctionHead) (arguments : List TptpFofBinderResolution.NamedTerm)
    (argumentsAgreement : TermsAgreement environment arguments) :
    TermAgreement environment (.function head arguments) := by
  intro result resolved
  cases found : arguments.mapM
      (TptpFofBinderResolution.resolveTerm? environment) with
  | none => simp [TptpFofBinderResolution.resolveTerm?, found] at resolved
  | some resolvedArguments =>
      have mapped : some
          (Semiterm.func
              ({ name := head.lexeme, kind := head.kind } :
                TptpFofNormalizationSemantics.FunctionSymbol
                  resolvedArguments.length)
              (fun index => resolvedArguments.get index)) = some result := by
        simpa [TptpFofBinderResolution.resolveTerm?, found] using resolved
      have resultEquality :
          Semiterm.func
              ({ name := head.lexeme, kind := head.kind } :
                TptpFofNormalizationSemantics.FunctionSymbol
                  resolvedArguments.length)
              (fun index => resolvedArguments.get index) = result := by
        exact Option.some.inj mapped
      subst result
      simpa only [encodeNamedTerm_function,
        encodeTerm_function] using
        term_function_eventuallyExact
          (encodeEnvironment environment)
          (TptpFofSymbolLanguageDef.encodeFunctionHead head)
          (TptpNamedFofLanguageDef.encodeTerms arguments)
          (TptpResolvedFofLanguageDef.encodeTerms resolvedArguments)
          (argumentsAgreement resolvedArguments found)

private theorem nilAgreement (environment : List String) :
    TermsAgreement environment [] := by
  intro results resolved
  have resultsEquality : ([] : List
      (TptpFofNormalizationSemantics.Term environment.length)) = results := by
    simpa using Option.some.inj resolved
  subst results
  simpa only [encodeNamedTerms_nil, encodeTerms_nil] using
    terms_nil_eventuallyExact (encodeEnvironment environment)

private theorem consAgreement (environment : List String)
    (head : TptpFofBinderResolution.NamedTerm)
    (tail : List TptpFofBinderResolution.NamedTerm)
    (headAgreement : TermAgreement environment head)
    (tailAgreement : TermsAgreement environment tail) :
    TermsAgreement environment (head :: tail) := by
  intro results resolved
  cases headFound : TptpFofBinderResolution.resolveTerm? environment head with
  | none => simp [headFound] at resolved
  | some headResult =>
      cases tailFound : tail.mapM
          (TptpFofBinderResolution.resolveTerm? environment) with
      | none => simp [headFound, tailFound] at resolved
      | some tailResults =>
          have mapped : some (headResult :: tailResults) = some results := by
            simpa [headFound, tailFound] using resolved
          have resultsEquality : headResult :: tailResults = results := by
            exact Option.some.inj mapped
          subst results
          simpa only [encodeNamedTerms_cons,
            encodeTerms_cons] using
            terms_cons_eventuallyExact
              (encodeEnvironment environment)
              (TptpNamedFofLanguageDef.encodeTerm head)
              (TptpNamedFofLanguageDef.encodeTerms tail)
              (TptpResolvedFofLanguageDef.encodeTerm headResult)
              (TptpResolvedFofLanguageDef.encodeTerms tailResults)
              (headAgreement headResult headFound)
              (tailAgreement tailResults tailFound)

theorem resolveTerm?_eventuallyExact (environment : List String)
    (source : TptpFofBinderResolution.NamedTerm) :
    TermAgreement environment source := by
  exact TptpFofBinderResolution.NamedTerm.rec
    (motive_1 := TermAgreement environment)
    (motive_2 := TermsAgreement environment)
    (variableAgreement environment)
    (functionAgreement environment)
    (nilAgreement environment)
    (consAgreement environment)
    source

theorem resolveTerms?_eventuallyExact (environment : List String)
    (sources : List TptpFofBinderResolution.NamedTerm) :
    TermsAgreement environment sources := by
  exact TptpFofBinderResolution.NamedTerm.rec_1
    (motive_1 := TermAgreement environment)
    (motive_2 := TermsAgreement environment)
    (variableAgreement environment)
    (functionAgreement environment)
    (nilAgreement environment)
    (consAgreement environment)
    sources

private def FormulaAgreement (environment : List String)
    (source : TptpFofBinderResolution.NamedFormula) : Prop :=
  ∀ result,
    TptpFofBinderResolution.resolveFormula? environment source = some result →
      EventuallyExact
        (resolveFormula (encodeEnvironment environment)
          (TptpNamedFofLanguageDef.encodeFormula source))
        (TptpResolvedFofLanguageDef.encodeFormula result)

theorem resolveFormula?_eventuallyExact (environment : List String)
    (source : TptpFofBinderResolution.NamedFormula) :
    FormulaAgreement environment source := by
  induction source generalizing environment with
  | verum =>
      intro result resolved
      have mapped : some
          (TptpFofNormalizationSemantics.Formula.verum) = some result := by
        simpa [TptpFofBinderResolution.resolveFormula?] using resolved
      have equality := Option.some.inj mapped
      subst result
      simpa only [encodeNamedFormula_verum, encodeResolvedFormula_verum] using
        leaf_eventuallyExact
          (resolveFormula (encodeEnvironment environment)
            (sourceFormula "verum"))
          (targetFormula "verum")
          (fun fuel => formula_verum_rewriteAt_exact fuel
            (encodeEnvironment environment))
  | falsum =>
      intro result resolved
      have mapped : some
          (TptpFofNormalizationSemantics.Formula.falsum) = some result := by
        simpa [TptpFofBinderResolution.resolveFormula?] using resolved
      have equality := Option.some.inj mapped
      subst result
      simpa only [encodeNamedFormula_falsum, encodeResolvedFormula_falsum]
        using leaf_eventuallyExact
          (resolveFormula (encodeEnvironment environment)
            (sourceFormula "falsum"))
          (targetFormula "falsum")
          (fun fuel => formula_falsum_rewriteAt_exact fuel
            (encodeEnvironment environment))
  | predicate head arguments =>
      intro result resolved
      cases found : arguments.mapM
          (TptpFofBinderResolution.resolveTerm? environment) with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, found] at resolved
      | some resolvedArguments =>
          have mapped : some
                (TptpFofNormalizationSemantics.Formula.predicate
                  ({ name := head.lexeme, kind := head.kind } :
                    TptpFofNormalizationSemantics.PredicateSymbol
                      resolvedArguments.length)
                  (fun index => resolvedArguments.get index)) = some result := by
            simpa [TptpFofBinderResolution.resolveFormula?, found] using resolved
          have equality := Option.some.inj mapped
          subst result
          simpa only [encodeNamedFormula_predicate,
            encodeResolvedFormula_predicate] using
            unary_eventuallyExact
              (resolveTerms (encodeEnvironment environment)
                (TptpNamedFofLanguageDef.encodeTerms arguments))
              (TptpResolvedFofLanguageDef.encodeTerms resolvedArguments)
              (resolveFormula (encodeEnvironment environment)
                (sourceFormula "predicate"
                  [TptpFofSymbolLanguageDef.encodePredicateHead head,
                   TptpNamedFofLanguageDef.encodeTerms arguments]))
              (targetFormula "predicate"
                [TptpFofSymbolLanguageDef.encodePredicateHead head,
                 TptpResolvedFofLanguageDef.encodeTerms resolvedArguments])
              (resolveTerms?_eventuallyExact environment arguments
                resolvedArguments found)
              (fun fuel step =>
                formula_predicate_rewriteAt_exact fuel
                  (encodeEnvironment environment)
                  (TptpFofSymbolLanguageDef.encodePredicateHead head)
                  (TptpNamedFofLanguageDef.encodeTerms arguments)
                  (TptpResolvedFofLanguageDef.encodeTerms resolvedArguments)
                  step)
  | equal left right =>
      intro result resolved
      cases leftFound : TptpFofBinderResolution.resolveTerm? environment left with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, leftFound] at resolved
      | some leftResult =>
          cases rightFound :
              TptpFofBinderResolution.resolveTerm? environment right with
          | none =>
              simp [TptpFofBinderResolution.resolveFormula?, leftFound,
                rightFound] at resolved
          | some rightResult =>
              have mapped : some
                    (TptpFofNormalizationSemantics.Formula.equal
                      leftResult rightResult) = some result := by
                simpa [TptpFofBinderResolution.resolveFormula?, leftFound,
                  rightFound] using resolved
              have equality := Option.some.inj mapped
              subst result
              simpa only [encodeNamedFormula_equal,
                encodeResolvedFormula_equal] using
                binary_eventuallyExact
                  (resolveTerm (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeTerm left))
                  (TptpResolvedFofLanguageDef.encodeTerm leftResult)
                  (resolveTerm (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeTerm right))
                  (TptpResolvedFofLanguageDef.encodeTerm rightResult)
                  (resolveFormula (encodeEnvironment environment)
                    (sourceFormula "equal"
                      [TptpNamedFofLanguageDef.encodeTerm left,
                       TptpNamedFofLanguageDef.encodeTerm right]))
                  (targetFormula "equal"
                    [TptpResolvedFofLanguageDef.encodeTerm leftResult,
                     TptpResolvedFofLanguageDef.encodeTerm rightResult])
                  (resolveTerm?_eventuallyExact environment left
                    leftResult leftFound)
                  (resolveTerm?_eventuallyExact environment right
                    rightResult rightFound)
                  (fun fuel leftStep rightStep =>
                    formula_equal_rewriteAt_exact fuel
                      (encodeEnvironment environment)
                      (TptpNamedFofLanguageDef.encodeTerm left)
                      (TptpNamedFofLanguageDef.encodeTerm right)
                      (TptpResolvedFofLanguageDef.encodeTerm leftResult)
                      (TptpResolvedFofLanguageDef.encodeTerm rightResult)
                      leftStep rightStep)
  | not body inductionHypothesis =>
      intro result resolved
      cases found : TptpFofBinderResolution.resolveFormula? environment body with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, found] at resolved
      | some bodyResult =>
          have mapped : some
                (TptpFofNormalizationSemantics.Formula.not bodyResult) =
              some result := by
            simpa [TptpFofBinderResolution.resolveFormula?, found] using resolved
          have equality := Option.some.inj mapped
          subst result
          simpa only [encodeNamedFormula_not,
            encodeResolvedFormula_not] using
            unary_eventuallyExact
              (resolveFormula (encodeEnvironment environment)
                (TptpNamedFofLanguageDef.encodeFormula body))
              (TptpResolvedFofLanguageDef.encodeFormula bodyResult)
              (resolveFormula (encodeEnvironment environment)
                (sourceFormula "not"
                  [TptpNamedFofLanguageDef.encodeFormula body]))
              (targetFormula "not"
                [TptpResolvedFofLanguageDef.encodeFormula bodyResult])
              (inductionHypothesis environment bodyResult found)
              (fun fuel step =>
                formula_not_rewriteAt_exact fuel
                  (encodeEnvironment environment)
                  (TptpNamedFofLanguageDef.encodeFormula body)
                  (TptpResolvedFofLanguageDef.encodeFormula bodyResult)
                  step)
  | and left right leftAgreement rightAgreement =>
      intro result resolved
      cases leftFound : TptpFofBinderResolution.resolveFormula?
          environment left with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, leftFound] at resolved
      | some leftResult =>
          cases rightFound : TptpFofBinderResolution.resolveFormula?
              environment right with
          | none =>
              simp [TptpFofBinderResolution.resolveFormula?, leftFound,
                rightFound] at resolved
          | some rightResult =>
              have mapped : some
                    (TptpFofNormalizationSemantics.Formula.and
                      leftResult rightResult) = some result := by
                simpa [TptpFofBinderResolution.resolveFormula?, leftFound,
                  rightFound] using resolved
              have equality := Option.some.inj mapped
              subst result
              simpa only [encodeNamedFormula_and,
                encodeResolvedFormula_and] using
                binary_eventuallyExact
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula left))
                  (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula right))
                  (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                  (resolveFormula (encodeEnvironment environment)
                    (sourceFormula "and"
                      [TptpNamedFofLanguageDef.encodeFormula left,
                       TptpNamedFofLanguageDef.encodeFormula right]))
                  (targetFormula "and"
                    [TptpResolvedFofLanguageDef.encodeFormula leftResult,
                     TptpResolvedFofLanguageDef.encodeFormula rightResult])
                  (leftAgreement environment leftResult leftFound)
                  (rightAgreement environment rightResult rightFound)
                  (fun fuel leftStep rightStep =>
                    formula_and_rewriteAt_exact fuel
                      (encodeEnvironment environment)
                      (TptpNamedFofLanguageDef.encodeFormula left)
                      (TptpNamedFofLanguageDef.encodeFormula right)
                      (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                      (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                      leftStep rightStep)
  | or left right leftAgreement rightAgreement =>
      intro result resolved
      cases leftFound : TptpFofBinderResolution.resolveFormula?
          environment left with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, leftFound] at resolved
      | some leftResult =>
          cases rightFound : TptpFofBinderResolution.resolveFormula?
              environment right with
          | none =>
              simp [TptpFofBinderResolution.resolveFormula?, leftFound,
                rightFound] at resolved
          | some rightResult =>
              have mapped : some
                    (TptpFofNormalizationSemantics.Formula.or
                      leftResult rightResult) = some result := by
                simpa [TptpFofBinderResolution.resolveFormula?, leftFound,
                  rightFound] using resolved
              have equality := Option.some.inj mapped
              subst result
              simpa only [encodeNamedFormula_or,
                encodeResolvedFormula_or] using
                binary_eventuallyExact
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula left))
                  (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula right))
                  (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                  (resolveFormula (encodeEnvironment environment)
                    (sourceFormula "or"
                      [TptpNamedFofLanguageDef.encodeFormula left,
                       TptpNamedFofLanguageDef.encodeFormula right]))
                  (targetFormula "or"
                    [TptpResolvedFofLanguageDef.encodeFormula leftResult,
                     TptpResolvedFofLanguageDef.encodeFormula rightResult])
                  (leftAgreement environment leftResult leftFound)
                  (rightAgreement environment rightResult rightFound)
                  (fun fuel leftStep rightStep =>
                    formula_or_rewriteAt_exact fuel
                      (encodeEnvironment environment)
                      (TptpNamedFofLanguageDef.encodeFormula left)
                      (TptpNamedFofLanguageDef.encodeFormula right)
                      (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                      (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                      leftStep rightStep)
  | iff left right leftAgreement rightAgreement =>
      intro result resolved
      cases leftFound : TptpFofBinderResolution.resolveFormula?
          environment left with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, leftFound] at resolved
      | some leftResult =>
          cases rightFound : TptpFofBinderResolution.resolveFormula?
              environment right with
          | none =>
              simp [TptpFofBinderResolution.resolveFormula?, leftFound,
                rightFound] at resolved
          | some rightResult =>
              have mapped : some
                    (TptpFofNormalizationSemantics.Formula.iff
                      leftResult rightResult) = some result := by
                simpa [TptpFofBinderResolution.resolveFormula?, leftFound,
                  rightFound] using resolved
              have equality := Option.some.inj mapped
              subst result
              simpa only [encodeNamedFormula_iff,
                encodeResolvedFormula_iff] using
                binary_eventuallyExact
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula left))
                  (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula right))
                  (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                  (resolveFormula (encodeEnvironment environment)
                    (sourceFormula "iff"
                      [TptpNamedFofLanguageDef.encodeFormula left,
                       TptpNamedFofLanguageDef.encodeFormula right]))
                  (targetFormula "iff"
                    [TptpResolvedFofLanguageDef.encodeFormula leftResult,
                     TptpResolvedFofLanguageDef.encodeFormula rightResult])
                  (leftAgreement environment leftResult leftFound)
                  (rightAgreement environment rightResult rightFound)
                  (fun fuel leftStep rightStep =>
                    formula_iff_rewriteAt_exact fuel
                      (encodeEnvironment environment)
                      (TptpNamedFofLanguageDef.encodeFormula left)
                      (TptpNamedFofLanguageDef.encodeFormula right)
                      (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                      (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                      leftStep rightStep)
  | implies left right leftAgreement rightAgreement =>
      intro result resolved
      cases leftFound : TptpFofBinderResolution.resolveFormula?
          environment left with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, leftFound] at resolved
      | some leftResult =>
          cases rightFound : TptpFofBinderResolution.resolveFormula?
              environment right with
          | none =>
              simp [TptpFofBinderResolution.resolveFormula?, leftFound,
                rightFound] at resolved
          | some rightResult =>
              have mapped : some
                    (TptpFofNormalizationSemantics.Formula.implies
                      leftResult rightResult) = some result := by
                simpa [TptpFofBinderResolution.resolveFormula?, leftFound,
                  rightFound] using resolved
              have equality := Option.some.inj mapped
              subst result
              simpa only [encodeNamedFormula_implies,
                encodeResolvedFormula_implies] using
                binary_eventuallyExact
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula left))
                  (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula right))
                  (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                  (resolveFormula (encodeEnvironment environment)
                    (sourceFormula "implies"
                      [TptpNamedFofLanguageDef.encodeFormula left,
                       TptpNamedFofLanguageDef.encodeFormula right]))
                  (targetFormula "implies"
                    [TptpResolvedFofLanguageDef.encodeFormula leftResult,
                     TptpResolvedFofLanguageDef.encodeFormula rightResult])
                  (leftAgreement environment leftResult leftFound)
                  (rightAgreement environment rightResult rightFound)
                  (fun fuel leftStep rightStep =>
                    formula_implies_rewriteAt_exact fuel
                      (encodeEnvironment environment)
                      (TptpNamedFofLanguageDef.encodeFormula left)
                      (TptpNamedFofLanguageDef.encodeFormula right)
                      (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                      (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                      leftStep rightStep)
  | reverseImplies left right leftAgreement rightAgreement =>
      intro result resolved
      cases leftFound : TptpFofBinderResolution.resolveFormula?
          environment left with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, leftFound] at resolved
      | some leftResult =>
          cases rightFound : TptpFofBinderResolution.resolveFormula?
              environment right with
          | none =>
              simp [TptpFofBinderResolution.resolveFormula?, leftFound,
                rightFound] at resolved
          | some rightResult =>
              have mapped : some
                    (TptpFofNormalizationSemantics.Formula.reverseImplies
                      leftResult rightResult) = some result := by
                simpa [TptpFofBinderResolution.resolveFormula?, leftFound,
                  rightFound] using resolved
              have equality := Option.some.inj mapped
              subst result
              simpa only [encodeNamedFormula_reverseImplies,
                encodeResolvedFormula_reverseImplies] using
                binary_eventuallyExact
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula left))
                  (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula right))
                  (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                  (resolveFormula (encodeEnvironment environment)
                    (sourceFormula "reverse-implies"
                      [TptpNamedFofLanguageDef.encodeFormula left,
                       TptpNamedFofLanguageDef.encodeFormula right]))
                  (targetFormula "reverse-implies"
                    [TptpResolvedFofLanguageDef.encodeFormula leftResult,
                     TptpResolvedFofLanguageDef.encodeFormula rightResult])
                  (leftAgreement environment leftResult leftFound)
                  (rightAgreement environment rightResult rightFound)
                  (fun fuel leftStep rightStep =>
                    formula_reverseImplies_rewriteAt_exact fuel
                      (encodeEnvironment environment)
                      (TptpNamedFofLanguageDef.encodeFormula left)
                      (TptpNamedFofLanguageDef.encodeFormula right)
                      (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                      (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                      leftStep rightStep)
  | xor left right leftAgreement rightAgreement =>
      intro result resolved
      cases leftFound : TptpFofBinderResolution.resolveFormula?
          environment left with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, leftFound] at resolved
      | some leftResult =>
          cases rightFound : TptpFofBinderResolution.resolveFormula?
              environment right with
          | none =>
              simp [TptpFofBinderResolution.resolveFormula?, leftFound,
                rightFound] at resolved
          | some rightResult =>
              have mapped : some
                    (TptpFofNormalizationSemantics.Formula.xor
                      leftResult rightResult) = some result := by
                simpa [TptpFofBinderResolution.resolveFormula?, leftFound,
                  rightFound] using resolved
              have equality := Option.some.inj mapped
              subst result
              simpa only [encodeNamedFormula_xor,
                encodeResolvedFormula_xor] using
                binary_eventuallyExact
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula left))
                  (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula right))
                  (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                  (resolveFormula (encodeEnvironment environment)
                    (sourceFormula "xor"
                      [TptpNamedFofLanguageDef.encodeFormula left,
                       TptpNamedFofLanguageDef.encodeFormula right]))
                  (targetFormula "xor"
                    [TptpResolvedFofLanguageDef.encodeFormula leftResult,
                     TptpResolvedFofLanguageDef.encodeFormula rightResult])
                  (leftAgreement environment leftResult leftFound)
                  (rightAgreement environment rightResult rightFound)
                  (fun fuel leftStep rightStep =>
                    formula_xor_rewriteAt_exact fuel
                      (encodeEnvironment environment)
                      (TptpNamedFofLanguageDef.encodeFormula left)
                      (TptpNamedFofLanguageDef.encodeFormula right)
                      (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                      (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                      leftStep rightStep)
  | nor left right leftAgreement rightAgreement =>
      intro result resolved
      cases leftFound : TptpFofBinderResolution.resolveFormula?
          environment left with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, leftFound] at resolved
      | some leftResult =>
          cases rightFound : TptpFofBinderResolution.resolveFormula?
              environment right with
          | none =>
              simp [TptpFofBinderResolution.resolveFormula?, leftFound,
                rightFound] at resolved
          | some rightResult =>
              have mapped : some
                    (TptpFofNormalizationSemantics.Formula.nor
                      leftResult rightResult) = some result := by
                simpa [TptpFofBinderResolution.resolveFormula?, leftFound,
                  rightFound] using resolved
              have equality := Option.some.inj mapped
              subst result
              simpa only [encodeNamedFormula_nor,
                encodeResolvedFormula_nor] using
                binary_eventuallyExact
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula left))
                  (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula right))
                  (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                  (resolveFormula (encodeEnvironment environment)
                    (sourceFormula "nor"
                      [TptpNamedFofLanguageDef.encodeFormula left,
                       TptpNamedFofLanguageDef.encodeFormula right]))
                  (targetFormula "nor"
                    [TptpResolvedFofLanguageDef.encodeFormula leftResult,
                     TptpResolvedFofLanguageDef.encodeFormula rightResult])
                  (leftAgreement environment leftResult leftFound)
                  (rightAgreement environment rightResult rightFound)
                  (fun fuel leftStep rightStep =>
                    formula_nor_rewriteAt_exact fuel
                      (encodeEnvironment environment)
                      (TptpNamedFofLanguageDef.encodeFormula left)
                      (TptpNamedFofLanguageDef.encodeFormula right)
                      (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                      (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                      leftStep rightStep)
  | nand left right leftAgreement rightAgreement =>
      intro result resolved
      cases leftFound : TptpFofBinderResolution.resolveFormula?
          environment left with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, leftFound] at resolved
      | some leftResult =>
          cases rightFound : TptpFofBinderResolution.resolveFormula?
              environment right with
          | none =>
              simp [TptpFofBinderResolution.resolveFormula?, leftFound,
                rightFound] at resolved
          | some rightResult =>
              have mapped : some
                    (TptpFofNormalizationSemantics.Formula.nand
                      leftResult rightResult) = some result := by
                simpa [TptpFofBinderResolution.resolveFormula?, leftFound,
                  rightFound] using resolved
              have equality := Option.some.inj mapped
              subst result
              simpa only [encodeNamedFormula_nand,
                encodeResolvedFormula_nand] using
                binary_eventuallyExact
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula left))
                  (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                  (resolveFormula (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeFormula right))
                  (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                  (resolveFormula (encodeEnvironment environment)
                    (sourceFormula "nand"
                      [TptpNamedFofLanguageDef.encodeFormula left,
                       TptpNamedFofLanguageDef.encodeFormula right]))
                  (targetFormula "nand"
                    [TptpResolvedFofLanguageDef.encodeFormula leftResult,
                     TptpResolvedFofLanguageDef.encodeFormula rightResult])
                  (leftAgreement environment leftResult leftFound)
                  (rightAgreement environment rightResult rightFound)
                  (fun fuel leftStep rightStep =>
                    formula_nand_rewriteAt_exact fuel
                      (encodeEnvironment environment)
                      (TptpNamedFofLanguageDef.encodeFormula left)
                      (TptpNamedFofLanguageDef.encodeFormula right)
                      (TptpResolvedFofLanguageDef.encodeFormula leftResult)
                      (TptpResolvedFofLanguageDef.encodeFormula rightResult)
                      leftStep rightStep)
  | all binder body inductionHypothesis =>
      intro result resolved
      cases found : TptpFofBinderResolution.resolveFormula?
          (binder :: environment) body with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, found] at resolved
      | some bodyResult =>
          have mapped : some
                (TptpFofNormalizationSemantics.Formula.all bodyResult) =
              some result := by
            simpa [TptpFofBinderResolution.resolveFormula?, found] using resolved
          have equality := Option.some.inj mapped
          subst result
          simpa only [encodeNamedFormula_all, encodeResolvedFormula_all,
            encodeEnvironment_cons] using
            unary_eventuallyExact
              (resolveFormula (encodeEnvironment (binder :: environment))
                (TptpNamedFofLanguageDef.encodeFormula body))
              (TptpResolvedFofLanguageDef.encodeFormula bodyResult)
              (resolveFormula (encodeEnvironment environment)
                (sourceFormula "all"
                  [sourceName (a binder),
                   TptpNamedFofLanguageDef.encodeFormula body]))
              (targetFormula "all"
                [TptpResolvedFofLanguageDef.encodeFormula bodyResult])
              (inductionHypothesis (binder :: environment) bodyResult found)
              (fun fuel step =>
                formula_all_rewriteAt_exact fuel
                  (encodeEnvironment environment) (a binder)
                  (TptpNamedFofLanguageDef.encodeFormula body)
                  (TptpResolvedFofLanguageDef.encodeFormula bodyResult)
                  (by simpa only [encodeEnvironment_cons] using step))
  | ex binder body inductionHypothesis =>
      intro result resolved
      cases found : TptpFofBinderResolution.resolveFormula?
          (binder :: environment) body with
      | none =>
          simp [TptpFofBinderResolution.resolveFormula?, found] at resolved
      | some bodyResult =>
          have mapped : some
                (TptpFofNormalizationSemantics.Formula.ex bodyResult) =
              some result := by
            simpa [TptpFofBinderResolution.resolveFormula?, found] using resolved
          have equality := Option.some.inj mapped
          subst result
          simpa only [encodeNamedFormula_ex, encodeResolvedFormula_ex,
            encodeEnvironment_cons] using
            unary_eventuallyExact
              (resolveFormula (encodeEnvironment (binder :: environment))
                (TptpNamedFofLanguageDef.encodeFormula body))
              (TptpResolvedFofLanguageDef.encodeFormula bodyResult)
              (resolveFormula (encodeEnvironment environment)
                (sourceFormula "ex"
                  [sourceName (a binder),
                   TptpNamedFofLanguageDef.encodeFormula body]))
              (targetFormula "ex"
                [TptpResolvedFofLanguageDef.encodeFormula bodyResult])
              (inductionHypothesis (binder :: environment) bodyResult found)
              (fun fuel step =>
                formula_ex_rewriteAt_exact fuel
                  (encodeEnvironment environment) (a binder)
                  (TptpNamedFofLanguageDef.encodeFormula body)
                  (TptpResolvedFofLanguageDef.encodeFormula bodyResult)
                  (by simpa only [encodeEnvironment_cons] using step))

theorem resolveClosedFormula?_eventuallyExact
    (source : TptpFofBinderResolution.NamedFormula)
    (result : TptpFofNormalizationSemantics.Formula 0)
    (resolved :
      TptpFofBinderResolution.resolveClosedFormula? source = some result) :
    EventuallyExact
      (resolveClosed (TptpNamedFofLanguageDef.encodeFormula source))
      (TptpResolvedFofLanguageDef.encodeFormula result) := by
  apply closed_eventuallyExact
  simpa only [encodeEnvironment_nil] using
    resolveFormula?_eventuallyExact [] source result resolved

theorem resolveClosedFormula?_no_invention
    (source : TptpFofBinderResolution.NamedFormula)
    (result : TptpFofNormalizationSemantics.Formula 0)
    (resolved :
      TptpFofBinderResolution.resolveClosedFormula? source = some result)
    (fuel : Nat) (target : Pattern)
    (member : target ∈ rewriteAt (engineBasePremises relations) language fuel
      (resolveClosed (TptpNamedFofLanguageDef.encodeFormula source))) :
    target = TptpResolvedFofLanguageDef.encodeFormula result := by
  exact EventuallyExact.no_invention
    (resolveClosedFormula?_eventuallyExact source result resolved) fuel member

/-! ## Exact semantic failure reflection -/

theorem lookupBinder?_none_alwaysEmpty (name : String)
    (environment : List String)
    (missing : TptpFofBinderResolution.lookupBinder? name environment = none) :
    AlwaysEmpty (lookup (a name) (encodeEnvironment environment)) := by
  induction environment generalizing name with
  | nil =>
      intro fuel
      simpa only [encodeEnvironment_nil] using
        lookup_nil_rewriteAt_empty fuel (a name)
  | cons binder environment inductionHypothesis =>
      by_cases same : name = binder
      · subst binder
        simp [TptpFofBinderResolution.lookupBinder?] at missing
      · rw [TptpFofBinderResolution.lookupBinder?_tail same] at missing
        cases inner : TptpFofBinderResolution.lookupBinder? name environment with
        | some index => simp [inner] at missing
        | none =>
            have recursive := inductionHypothesis name inner
            have patternDifferent : a name ≠ a binder := by
              intro equality
              injection equality with equality
              exact same equality
            simpa only [encodeEnvironment_cons] using
              alwaysEmpty_of_offset_step
                (lookup (a name) (encodeEnvironment environment))
                (lookup (a name)
                  (environmentCons (a binder)
                    (encodeEnvironment environment)))
                2 recursive
                (fun fuel recursiveStep =>
                  lookup_tail_rewriteAt_empty fuel (a name) (a binder)
                    (encodeEnvironment environment) patternDifferent
                    recursiveStep)

private def TermFailure (environment : List String)
    (source : TptpFofBinderResolution.NamedTerm) : Prop :=
  TptpFofBinderResolution.resolveTerm? environment source = none →
    AlwaysEmpty
      (resolveTerm (encodeEnvironment environment)
        (TptpNamedFofLanguageDef.encodeTerm source))

private def TermsFailure (environment : List String)
    (sources : List TptpFofBinderResolution.NamedTerm) : Prop :=
  sources.mapM (TptpFofBinderResolution.resolveTerm? environment) = none →
    AlwaysEmpty
      (resolveTerms (encodeEnvironment environment)
        (TptpNamedFofLanguageDef.encodeTerms sources))

private theorem variableFailure (environment : List String) (name : String) :
    TermFailure environment (.variable name) := by
  intro missing
  cases found : TptpFofBinderResolution.lookupBinder? name environment with
  | some index =>
      simp [TptpFofBinderResolution.resolveTerm?, found] at missing
  | none =>
      simpa only [encodeNamedTerm_variable] using
        alwaysEmpty_of_offset_step
          (lookup (a name) (encodeEnvironment environment))
          (resolveTerm (encodeEnvironment environment) (sourceVariable (a name)))
          1 (lookupBinder?_none_alwaysEmpty name environment found)
          (fun fuel lookupStep =>
            term_variable_rewriteAt_empty fuel
              (encodeEnvironment environment) (a name) lookupStep)

private theorem functionFailure (environment : List String) (head : FunctionHead)
    (arguments : List TptpFofBinderResolution.NamedTerm)
    (argumentsFailure : TermsFailure environment arguments) :
    TermFailure environment (.function head arguments) := by
  intro missing
  cases found : arguments.mapM
      (TptpFofBinderResolution.resolveTerm? environment) with
  | some resolvedArguments =>
      simp [TptpFofBinderResolution.resolveTerm?, found] at missing
  | none =>
      simpa only [encodeNamedTerm_function] using
        alwaysEmpty_of_offset_step
          (resolveTerms (encodeEnvironment environment)
            (TptpNamedFofLanguageDef.encodeTerms arguments))
          (resolveTerm (encodeEnvironment environment)
            (sourceFunction
              (TptpFofSymbolLanguageDef.encodeFunctionHead head)
              (TptpNamedFofLanguageDef.encodeTerms arguments)))
          1 (argumentsFailure found)
          (fun fuel argumentsStep =>
            term_function_rewriteAt_empty fuel
              (encodeEnvironment environment)
              (TptpFofSymbolLanguageDef.encodeFunctionHead head)
              (TptpNamedFofLanguageDef.encodeTerms arguments) argumentsStep)

private theorem nilFailure (environment : List String) :
    TermsFailure environment [] := by
  intro missing
  simp at missing

private theorem consFailure (environment : List String)
    (head : TptpFofBinderResolution.NamedTerm)
    (tail : List TptpFofBinderResolution.NamedTerm)
    (headFailure : TermFailure environment head)
    (tailFailure : TermsFailure environment tail) :
    TermsFailure environment (head :: tail) := by
  intro missing
  cases headFound : TptpFofBinderResolution.resolveTerm? environment head with
  | none =>
      simpa only [encodeNamedTerms_cons] using
        alwaysEmpty_of_offset_step
          (resolveTerm (encodeEnvironment environment)
            (TptpNamedFofLanguageDef.encodeTerm head))
          (resolveTerms (encodeEnvironment environment)
            (sourceTermsCons (TptpNamedFofLanguageDef.encodeTerm head)
              (TptpNamedFofLanguageDef.encodeTerms tail)))
          1 (headFailure headFound)
          (fun fuel headStep =>
            terms_cons_head_rewriteAt_empty fuel
              (encodeEnvironment environment)
              (TptpNamedFofLanguageDef.encodeTerm head)
              (TptpNamedFofLanguageDef.encodeTerms tail) headStep)
  | some headResult =>
      cases tailFound : tail.mapM
          (TptpFofBinderResolution.resolveTerm? environment) with
      | some tailResults => simp [headFound, tailFound] at missing
      | none =>
          simpa only [encodeNamedTerms_cons] using
            alwaysEmpty_of_offset_step
              (resolveTerms (encodeEnvironment environment)
                (TptpNamedFofLanguageDef.encodeTerms tail))
              (resolveTerms (encodeEnvironment environment)
                (sourceTermsCons (TptpNamedFofLanguageDef.encodeTerm head)
                  (TptpNamedFofLanguageDef.encodeTerms tail)))
              1 (tailFailure tailFound)
              (fun fuel tailStep =>
                terms_cons_tail_rewriteAt_empty fuel
                  (encodeEnvironment environment)
                  (TptpNamedFofLanguageDef.encodeTerm head)
                  (TptpNamedFofLanguageDef.encodeTerms tail) tailStep)

theorem resolveTerm?_none_alwaysEmpty (environment : List String)
    (source : TptpFofBinderResolution.NamedTerm) :
    TermFailure environment source := by
  exact TptpFofBinderResolution.NamedTerm.rec
    (motive_1 := TermFailure environment)
    (motive_2 := TermsFailure environment)
    (variableFailure environment)
    (functionFailure environment)
    (nilFailure environment)
    (consFailure environment)
    source

theorem resolveTerms?_none_alwaysEmpty (environment : List String)
    (sources : List TptpFofBinderResolution.NamedTerm) :
    TermsFailure environment sources := by
  exact TptpFofBinderResolution.NamedTerm.rec_1
    (motive_1 := TermFailure environment)
    (motive_2 := TermsFailure environment)
    (variableFailure environment)
    (functionFailure environment)
    (nilFailure environment)
    (consFailure environment)
    sources

private theorem binaryFormulaFailure (constructor : String)
    (supported : constructor ∈
      ["and", "or", "iff", "implies", "reverse-implies", "xor", "nor", "nand"])
    (environment : List String)
    (left right : TptpFofBinderResolution.NamedFormula)
    (leftFailure :
      TptpFofBinderResolution.resolveFormula? environment left = none →
        AlwaysEmpty
          (resolveFormula (encodeEnvironment environment)
            (TptpNamedFofLanguageDef.encodeFormula left)))
    (rightFailure :
      TptpFofBinderResolution.resolveFormula? environment right = none →
        AlwaysEmpty
          (resolveFormula (encodeEnvironment environment)
            (TptpNamedFofLanguageDef.encodeFormula right)))
    (missing : (do
      let _ ← TptpFofBinderResolution.resolveFormula? environment left
      let _ ← TptpFofBinderResolution.resolveFormula? environment right
      pure ()) = none) :
    AlwaysEmpty
      (resolveFormula (encodeEnvironment environment)
        (sourceFormula constructor
          [TptpNamedFofLanguageDef.encodeFormula left,
           TptpNamedFofLanguageDef.encodeFormula right])) := by
  cases leftFound : TptpFofBinderResolution.resolveFormula? environment left with
  | none =>
      exact alwaysEmpty_of_offset_step
        (resolveFormula (encodeEnvironment environment)
          (TptpNamedFofLanguageDef.encodeFormula left))
        (resolveFormula (encodeEnvironment environment)
          (sourceFormula constructor
            [TptpNamedFofLanguageDef.encodeFormula left,
             TptpNamedFofLanguageDef.encodeFormula right]))
        1 (leftFailure leftFound)
        (fun fuel leftStep =>
          formula_binary_left_rewriteAt_empty fuel constructor supported
            (encodeEnvironment environment)
            (TptpNamedFofLanguageDef.encodeFormula left)
            (TptpNamedFofLanguageDef.encodeFormula right) leftStep)
  | some leftResult =>
      cases rightFound : TptpFofBinderResolution.resolveFormula?
          environment right with
      | none =>
          exact alwaysEmpty_of_offset_step
            (resolveFormula (encodeEnvironment environment)
              (TptpNamedFofLanguageDef.encodeFormula right))
            (resolveFormula (encodeEnvironment environment)
              (sourceFormula constructor
                [TptpNamedFofLanguageDef.encodeFormula left,
                 TptpNamedFofLanguageDef.encodeFormula right]))
            1 (rightFailure rightFound)
            (fun fuel rightStep =>
              formula_binary_right_rewriteAt_empty fuel constructor supported
                (encodeEnvironment environment)
                (TptpNamedFofLanguageDef.encodeFormula left)
                (TptpNamedFofLanguageDef.encodeFormula right) rightStep)
      | some rightResult => simp [leftFound, rightFound] at missing

theorem resolveFormula?_none_alwaysEmpty (environment : List String)
    (source : TptpFofBinderResolution.NamedFormula)
    (missing : TptpFofBinderResolution.resolveFormula? environment source = none) :
    AlwaysEmpty
      (resolveFormula (encodeEnvironment environment)
        (TptpNamedFofLanguageDef.encodeFormula source)) := by
  induction source generalizing environment with
  | verum => simp [TptpFofBinderResolution.resolveFormula?] at missing
  | falsum => simp [TptpFofBinderResolution.resolveFormula?] at missing
  | predicate head arguments =>
      cases found : arguments.mapM
          (TptpFofBinderResolution.resolveTerm? environment) with
      | some resolvedArguments =>
          simp [TptpFofBinderResolution.resolveFormula?, found] at missing
      | none =>
          simpa only [encodeNamedFormula_predicate] using
            alwaysEmpty_of_offset_step
              (resolveTerms (encodeEnvironment environment)
                (TptpNamedFofLanguageDef.encodeTerms arguments))
              (resolveFormula (encodeEnvironment environment)
                (sourceFormula "predicate"
                  [TptpFofSymbolLanguageDef.encodePredicateHead head,
                   TptpNamedFofLanguageDef.encodeTerms arguments]))
              1 (resolveTerms?_none_alwaysEmpty environment arguments found)
              (fun fuel argumentsStep =>
                formula_predicate_rewriteAt_empty fuel
                  (encodeEnvironment environment)
                  (TptpFofSymbolLanguageDef.encodePredicateHead head)
                  (TptpNamedFofLanguageDef.encodeTerms arguments)
                  argumentsStep)
  | equal left right =>
      cases leftFound : TptpFofBinderResolution.resolveTerm? environment left with
      | none =>
          simpa only [encodeNamedFormula_equal] using
            alwaysEmpty_of_offset_step
              (resolveTerm (encodeEnvironment environment)
                (TptpNamedFofLanguageDef.encodeTerm left))
              (resolveFormula (encodeEnvironment environment)
                (sourceFormula "equal"
                  [TptpNamedFofLanguageDef.encodeTerm left,
                   TptpNamedFofLanguageDef.encodeTerm right]))
              1 (resolveTerm?_none_alwaysEmpty environment left leftFound)
              (fun fuel leftStep =>
                formula_equal_left_rewriteAt_empty fuel
                  (encodeEnvironment environment)
                  (TptpNamedFofLanguageDef.encodeTerm left)
                  (TptpNamedFofLanguageDef.encodeTerm right) leftStep)
      | some leftResult =>
          cases rightFound : TptpFofBinderResolution.resolveTerm?
              environment right with
          | none =>
              simpa only [encodeNamedFormula_equal] using
                alwaysEmpty_of_offset_step
                  (resolveTerm (encodeEnvironment environment)
                    (TptpNamedFofLanguageDef.encodeTerm right))
                  (resolveFormula (encodeEnvironment environment)
                    (sourceFormula "equal"
                      [TptpNamedFofLanguageDef.encodeTerm left,
                       TptpNamedFofLanguageDef.encodeTerm right]))
                  1 (resolveTerm?_none_alwaysEmpty environment right rightFound)
                  (fun fuel rightStep =>
                    formula_equal_right_rewriteAt_empty fuel
                      (encodeEnvironment environment)
                      (TptpNamedFofLanguageDef.encodeTerm left)
                      (TptpNamedFofLanguageDef.encodeTerm right) rightStep)
          | some rightResult =>
              simp [TptpFofBinderResolution.resolveFormula?, leftFound,
                rightFound] at missing
  | not body inductionHypothesis =>
      cases found : TptpFofBinderResolution.resolveFormula? environment body with
      | some bodyResult =>
          simp [TptpFofBinderResolution.resolveFormula?, found] at missing
      | none =>
          simpa only [encodeNamedFormula_not] using
            alwaysEmpty_of_offset_step
              (resolveFormula (encodeEnvironment environment)
                (TptpNamedFofLanguageDef.encodeFormula body))
              (resolveFormula (encodeEnvironment environment)
                (sourceFormula "not"
                  [TptpNamedFofLanguageDef.encodeFormula body]))
              1 (inductionHypothesis environment found)
              (fun fuel bodyStep =>
                formula_not_rewriteAt_empty fuel
                  (encodeEnvironment environment)
                  (TptpNamedFofLanguageDef.encodeFormula body) bodyStep)
  | and left right leftHypothesis rightHypothesis =>
      simpa only [encodeNamedFormula_and] using
        binaryFormulaFailure "and" (by simp) environment left right
          (leftHypothesis environment) (rightHypothesis environment)
          (by simpa [TptpFofBinderResolution.resolveFormula?] using missing)
  | or left right leftHypothesis rightHypothesis =>
      simpa only [encodeNamedFormula_or] using
        binaryFormulaFailure "or" (by simp) environment left right
          (leftHypothesis environment) (rightHypothesis environment)
          (by simpa [TptpFofBinderResolution.resolveFormula?] using missing)
  | iff left right leftHypothesis rightHypothesis =>
      simpa only [encodeNamedFormula_iff] using
        binaryFormulaFailure "iff" (by simp) environment left right
          (leftHypothesis environment) (rightHypothesis environment)
          (by simpa [TptpFofBinderResolution.resolveFormula?] using missing)
  | implies left right leftHypothesis rightHypothesis =>
      simpa only [encodeNamedFormula_implies] using
        binaryFormulaFailure "implies" (by simp) environment left right
          (leftHypothesis environment) (rightHypothesis environment)
          (by simpa [TptpFofBinderResolution.resolveFormula?] using missing)
  | reverseImplies left right leftHypothesis rightHypothesis =>
      simpa only [encodeNamedFormula_reverseImplies] using
        binaryFormulaFailure "reverse-implies" (by simp) environment left right
          (leftHypothesis environment) (rightHypothesis environment)
          (by simpa [TptpFofBinderResolution.resolveFormula?] using missing)
  | xor left right leftHypothesis rightHypothesis =>
      simpa only [encodeNamedFormula_xor] using
        binaryFormulaFailure "xor" (by simp) environment left right
          (leftHypothesis environment) (rightHypothesis environment)
          (by simpa [TptpFofBinderResolution.resolveFormula?] using missing)
  | nor left right leftHypothesis rightHypothesis =>
      simpa only [encodeNamedFormula_nor] using
        binaryFormulaFailure "nor" (by simp) environment left right
          (leftHypothesis environment) (rightHypothesis environment)
          (by simpa [TptpFofBinderResolution.resolveFormula?] using missing)
  | nand left right leftHypothesis rightHypothesis =>
      simpa only [encodeNamedFormula_nand] using
        binaryFormulaFailure "nand" (by simp) environment left right
          (leftHypothesis environment) (rightHypothesis environment)
          (by simpa [TptpFofBinderResolution.resolveFormula?] using missing)
  | all binder body inductionHypothesis =>
      cases found : TptpFofBinderResolution.resolveFormula?
          (binder :: environment) body with
      | some bodyResult =>
          simp [TptpFofBinderResolution.resolveFormula?, found] at missing
      | none =>
          simpa only [encodeNamedFormula_all, encodeEnvironment_cons] using
            alwaysEmpty_of_offset_step
              (resolveFormula (encodeEnvironment (binder :: environment))
                (TptpNamedFofLanguageDef.encodeFormula body))
              (resolveFormula (encodeEnvironment environment)
                (sourceFormula "all"
                  [sourceName (a binder),
                   TptpNamedFofLanguageDef.encodeFormula body]))
              1 (inductionHypothesis (binder :: environment) found)
              (fun fuel bodyStep =>
                formula_binder_rewriteAt_empty fuel "all" (by simp)
                  (encodeEnvironment environment) (a binder)
                  (TptpNamedFofLanguageDef.encodeFormula body)
                  (by simpa only [encodeEnvironment_cons] using bodyStep))
  | ex binder body inductionHypothesis =>
      cases found : TptpFofBinderResolution.resolveFormula?
          (binder :: environment) body with
      | some bodyResult =>
          simp [TptpFofBinderResolution.resolveFormula?, found] at missing
      | none =>
          simpa only [encodeNamedFormula_ex, encodeEnvironment_cons] using
            alwaysEmpty_of_offset_step
              (resolveFormula (encodeEnvironment (binder :: environment))
                (TptpNamedFofLanguageDef.encodeFormula body))
              (resolveFormula (encodeEnvironment environment)
                (sourceFormula "ex"
                  [sourceName (a binder),
                   TptpNamedFofLanguageDef.encodeFormula body]))
              1 (inductionHypothesis (binder :: environment) found)
              (fun fuel bodyStep =>
                formula_binder_rewriteAt_empty fuel "ex" (by simp)
                  (encodeEnvironment environment) (a binder)
                  (TptpNamedFofLanguageDef.encodeFormula body)
                  (by simpa only [encodeEnvironment_cons] using bodyStep))

theorem resolveClosedFormula?_none_alwaysEmpty
    (source : TptpFofBinderResolution.NamedFormula)
    (missing : TptpFofBinderResolution.resolveClosedFormula? source = none) :
    AlwaysEmpty
      (resolveClosed (TptpNamedFofLanguageDef.encodeFormula source)) := by
  exact alwaysEmpty_of_offset_step
    (resolveFormula environmentNil
      (TptpNamedFofLanguageDef.encodeFormula source))
    (resolveClosed (TptpNamedFofLanguageDef.encodeFormula source))
    1
    (by
      simpa only [encodeEnvironment_nil] using
        resolveFormula?_none_alwaysEmpty [] source
          (by simpa [TptpFofBinderResolution.resolveClosedFormula?] using missing))
    (fun fuel formulaStep =>
      closed_rewriteAt_empty fuel
        (TptpNamedFofLanguageDef.encodeFormula source) formulaStep)

#print axioms lookupBinder?_eventuallyExact
#print axioms resolveTerm?_eventuallyExact
#print axioms resolveTerms?_eventuallyExact
#print axioms resolveFormula?_eventuallyExact
#print axioms resolveClosedFormula?_eventuallyExact
#print axioms resolveClosedFormula?_no_invention
#print axioms lookupBinder?_none_alwaysEmpty
#print axioms resolveTerm?_none_alwaysEmpty
#print axioms resolveTerms?_none_alwaysEmpty
#print axioms resolveFormula?_none_alwaysEmpty
#print axioms resolveClosedFormula?_none_alwaysEmpty

end Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedLanguageDef
