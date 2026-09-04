import Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationLanguageDef

/-!
# Exact execution of authored FOF Skolemization

This module connects the authored term and formula traversal to an independent
syntax-directed derivation.  The derivation does not call the rewrite engine;
the execution theorem proves that every derivation has exactly one reduct in
the combined LanguageDef, preserving result order and multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpFofSkolemTermLanguageDef
open Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationLanguageDef

local macro "skolemization_root" : tactic =>
  `(tactic|
    simp [rewriteAt,
      TptpFofSkolemizationLanguageDef.language_rewrites,
      TptpFofSkolemTermLanguageDef.rewrites,
      TptpFofSkolemTermLanguageDef.translateTermsConsRule,
      TptpFofSkolemizationLanguageDef.rewrites,
      matrixRewrites, formRewrites, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      TptpFofSkolemTermLanguageDef.mkRule,
      TptpFofSkolemTermLanguageDef.congruence,
      TptpFofSkolemTermLanguageDef.termShiftRequest,
      TptpFofSkolemTermLanguageDef.termShiftResult,
      TptpFofSkolemTermLanguageDef.termsShiftRequest,
      TptpFofSkolemTermLanguageDef.termsShiftResult,
      TptpFofSkolemTermLanguageDef.envShiftRequest,
      TptpFofSkolemTermLanguageDef.envShiftResult,
      TptpFofSkolemTermLanguageDef.variablesRequest,
      TptpFofSkolemTermLanguageDef.variablesResult,
      TptpFofSkolemTermLanguageDef.lookupRequest,
      TptpFofSkolemTermLanguageDef.lookupResult,
      TptpFofSkolemTermLanguageDef.translateTermRequest,
      TptpFofSkolemTermLanguageDef.translateTermResult,
      TptpFofSkolemTermLanguageDef.translateTermsRequest,
      TptpFofSkolemTermLanguageDef.translateTermsResult,
      TptpFofSkolemTermLanguageDef.indexZero,
      TptpFofSkolemTermLanguageDef.indexSucc,
      TptpFofSkolemTermLanguageDef.sourceTermVariable,
      TptpFofSkolemTermLanguageDef.sourceTermFunction,
      TptpFofSkolemTermLanguageDef.sourceTermsNil,
      TptpFofSkolemTermLanguageDef.sourceTermsCons,
      TptpResolvedFofLanguageDef.encodeTermPatterns,
      TptpFofSkolemTermLanguageDef.targetTermVariable,
      TptpFofSkolemTermLanguageDef.targetTermOriginal,
      TptpFofSkolemTermLanguageDef.targetTermGenerated,
      TptpFofSkolemTermLanguageDef.targetTermsNil,
      TptpFofSkolemTermLanguageDef.targetTermsCons,
      TptpFofSkolemTermLanguageDef.envNil,
      TptpFofSkolemTermLanguageDef.envCons,
      TptpFofSkolemTermLanguageDef.a,
      TptpFofSkolemTermLanguageDef.v,
      TptpFofSkolemizationLanguageDef.mkRule,
      TptpFofSkolemizationLanguageDef.congruence,
      matrixRequest, matrixResult, formRequest, formResult,
      TptpFofSkolemizationLanguageDef.a,
      TptpFofSkolemizationLanguageDef.v,
      TptpFofPrenexLanguageDef.matrixVerum,
      TptpFofPrenexLanguageDef.matrixFalsum,
      TptpFofPrenexLanguageDef.matrixPositive,
      TptpFofPrenexLanguageDef.matrixNegative,
      TptpFofPrenexLanguageDef.matrixEqual,
      TptpFofPrenexLanguageDef.matrixNotEqual,
      TptpFofPrenexLanguageDef.matrixAnd,
      TptpFofPrenexLanguageDef.matrixOr,
      TptpFofPrenexLanguageDef.matrix,
      TptpFofPrenexLanguageDef.all,
      TptpFofPrenexLanguageDef.ex,
      TptpFofPrenexLanguageDef.a,
      TptpFofSkolemLanguageDef.termVariable,
      TptpFofSkolemLanguageDef.termOriginal,
      TptpFofSkolemLanguageDef.termGenerated,
      TptpFofSkolemLanguageDef.termsNil,
      TptpFofSkolemLanguageDef.termsCons,
      TptpFofSkolemLanguageDef.verum,
      TptpFofSkolemLanguageDef.falsum,
      TptpFofSkolemLanguageDef.positive,
      TptpFofSkolemLanguageDef.negative,
      TptpFofSkolemLanguageDef.equal,
      TptpFofSkolemLanguageDef.notEqual,
      TptpFofSkolemLanguageDef.and,
      TptpFofSkolemLanguageDef.or,
      TptpFofSkolemLanguageDef.all,
      TptpFofSkolemLanguageDef.introducedSymbol,
      TptpFofSkolemLanguageDef.introducedNil,
      TptpFofSkolemLanguageDef.introducedCons,
      TptpFofSkolemLanguageDef.a,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

local syntax "skolemization_root_using " term,* : tactic
local macro_rules
  | `(tactic| skolemization_root_using $_proofs:term,*) =>
      `(tactic|
        simp only [TptpFofSkolemTermLanguageDef.termShiftRequest,
          TptpFofSkolemTermLanguageDef.termShiftResult,
          TptpFofSkolemTermLanguageDef.termsShiftRequest,
          TptpFofSkolemTermLanguageDef.termsShiftResult,
          TptpFofSkolemTermLanguageDef.envShiftRequest,
          TptpFofSkolemTermLanguageDef.envShiftResult,
          TptpFofSkolemTermLanguageDef.variablesRequest,
          TptpFofSkolemTermLanguageDef.variablesResult,
          TptpFofSkolemTermLanguageDef.lookupRequest,
          TptpFofSkolemTermLanguageDef.lookupResult,
          TptpFofSkolemTermLanguageDef.translateTermRequest,
          TptpFofSkolemTermLanguageDef.translateTermResult,
          TptpFofSkolemTermLanguageDef.translateTermsRequest,
          TptpFofSkolemTermLanguageDef.translateTermsResult,
          matrixRequest, matrixResult, formRequest, formResult,
          TptpFofSkolemTermLanguageDef.indexZero,
          TptpFofSkolemTermLanguageDef.indexSucc,
          TptpFofSkolemTermLanguageDef.sourceTermVariable,
          TptpFofSkolemTermLanguageDef.sourceTermFunction,
          TptpFofSkolemTermLanguageDef.sourceTermsNil,
          TptpFofSkolemTermLanguageDef.sourceTermsCons,
          TptpResolvedFofLanguageDef.encodeTermPatterns,
          TptpFofSkolemTermLanguageDef.targetTermVariable,
          TptpFofSkolemTermLanguageDef.targetTermOriginal,
          TptpFofSkolemTermLanguageDef.targetTermGenerated,
          TptpFofSkolemTermLanguageDef.targetTermsNil,
          TptpFofSkolemTermLanguageDef.targetTermsCons,
          TptpFofSkolemTermLanguageDef.envNil,
          TptpFofSkolemTermLanguageDef.envCons,
          TptpFofSkolemTermLanguageDef.a,
          TptpFofSkolemTermLanguageDef.v,
          TptpFofSkolemizationLanguageDef.a,
          TptpFofSkolemizationLanguageDef.v] at * <;>
        simp [*, rewriteAt,
          TptpFofSkolemizationLanguageDef.language_rewrites,
          TptpFofSkolemTermLanguageDef.rewrites,
          TptpFofSkolemTermLanguageDef.translateTermsConsRule,
          TptpFofSkolemizationLanguageDef.rewrites,
          matrixRewrites, formRewrites, applyRuleUsing,
          matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
          TptpFofSkolemTermLanguageDef.mkRule,
          TptpFofSkolemTermLanguageDef.congruence,
          TptpFofSkolemizationLanguageDef.mkRule,
          TptpFofSkolemizationLanguageDef.congruence,
          TptpFofSkolemTermLanguageDef.termShiftRequest,
          TptpFofSkolemTermLanguageDef.termShiftResult,
          TptpFofSkolemTermLanguageDef.termsShiftRequest,
          TptpFofSkolemTermLanguageDef.termsShiftResult,
          TptpFofSkolemTermLanguageDef.envShiftRequest,
          TptpFofSkolemTermLanguageDef.envShiftResult,
          TptpFofSkolemTermLanguageDef.variablesRequest,
          TptpFofSkolemTermLanguageDef.variablesResult,
          TptpFofSkolemTermLanguageDef.lookupRequest,
          TptpFofSkolemTermLanguageDef.lookupResult,
          TptpFofSkolemTermLanguageDef.translateTermRequest,
          TptpFofSkolemTermLanguageDef.translateTermResult,
          TptpFofSkolemTermLanguageDef.translateTermsRequest,
          TptpFofSkolemTermLanguageDef.translateTermsResult,
          matrixRequest, matrixResult, formRequest, formResult,
          TptpFofSkolemTermLanguageDef.indexZero,
          TptpFofSkolemTermLanguageDef.indexSucc,
          TptpFofSkolemTermLanguageDef.sourceTermVariable,
          TptpFofSkolemTermLanguageDef.sourceTermFunction,
          TptpFofSkolemTermLanguageDef.sourceTermsNil,
          TptpFofSkolemTermLanguageDef.sourceTermsCons,
          TptpFofSkolemTermLanguageDef.targetTermVariable,
          TptpFofSkolemTermLanguageDef.targetTermOriginal,
          TptpFofSkolemTermLanguageDef.targetTermGenerated,
          TptpFofSkolemTermLanguageDef.targetTermsNil,
          TptpFofSkolemTermLanguageDef.targetTermsCons,
          TptpFofSkolemTermLanguageDef.envNil,
          TptpFofSkolemTermLanguageDef.envCons,
          TptpFofSkolemTermLanguageDef.a,
          TptpFofSkolemTermLanguageDef.v,
          TptpFofSkolemizationLanguageDef.a,
          TptpFofSkolemizationLanguageDef.v,
          TptpFofPrenexLanguageDef.matrixVerum,
          TptpFofPrenexLanguageDef.matrixFalsum,
          TptpFofPrenexLanguageDef.matrixPositive,
          TptpFofPrenexLanguageDef.matrixNegative,
          TptpFofPrenexLanguageDef.matrixEqual,
          TptpFofPrenexLanguageDef.matrixNotEqual,
          TptpFofPrenexLanguageDef.matrixAnd,
          TptpFofPrenexLanguageDef.matrixOr,
          TptpFofPrenexLanguageDef.matrix,
          TptpFofPrenexLanguageDef.all,
          TptpFofPrenexLanguageDef.ex,
          TptpFofPrenexLanguageDef.a,
          TptpFofSkolemLanguageDef.termVariable,
          TptpFofSkolemLanguageDef.termOriginal,
          TptpFofSkolemLanguageDef.termGenerated,
          TptpFofSkolemLanguageDef.termsNil,
          TptpFofSkolemLanguageDef.termsCons,
          TptpFofSkolemLanguageDef.verum,
          TptpFofSkolemLanguageDef.falsum,
          TptpFofSkolemLanguageDef.positive,
          TptpFofSkolemLanguageDef.negative,
          TptpFofSkolemLanguageDef.equal,
          TptpFofSkolemLanguageDef.notEqual,
          TptpFofSkolemLanguageDef.and,
          TptpFofSkolemLanguageDef.or,
          TptpFofSkolemLanguageDef.all,
          TptpFofSkolemLanguageDef.introducedSymbol,
          TptpFofSkolemLanguageDef.introducedNil,
          TptpFofSkolemLanguageDef.introducedCons,
          TptpFofSkolemLanguageDef.a,
          matchPattern, matchArgs, mergeBindings,
          applyBindingsForRule, applyBindings])

local macro "term_extension_silent" : tactic =>
  `(tactic|
    simp only [rewriteAt,
      TptpFofSkolemizationLanguageDef.language_rewrites,
      List.flatMap_append] <;>
    simp [TptpFofSkolemizationLanguageDef.rewrites,
      matrixRewrites, formRewrites,
      TptpFofSkolemizationLanguageDef.mkRule,
      TptpFofSkolemizationLanguageDef.congruence,
      matrixRequest, matrixResult, formRequest, formResult,
      TptpFofSkolemizationLanguageDef.a,
      TptpFofSkolemizationLanguageDef.v,
      TptpFofPrenexLanguageDef.matrixVerum,
      TptpFofPrenexLanguageDef.matrixFalsum,
      TptpFofPrenexLanguageDef.matrixPositive,
      TptpFofPrenexLanguageDef.matrixNegative,
      TptpFofPrenexLanguageDef.matrixEqual,
      TptpFofPrenexLanguageDef.matrixNotEqual,
      TptpFofPrenexLanguageDef.matrixAnd,
      TptpFofPrenexLanguageDef.matrixOr,
      TptpFofPrenexLanguageDef.matrix,
      TptpFofPrenexLanguageDef.all,
      TptpFofPrenexLanguageDef.ex,
      TptpFofPrenexLanguageDef.a,
      TptpFofSkolemLanguageDef.a,
      applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing, matchPattern, matchArgs,
      mergeBindings, applyBindingsForRule, applyBindings])

local macro "term_extension_root" : tactic =>
  `(tactic|
    term_extension_silent <;>
    simp [TptpFofSkolemTermLanguageDef.rewrites, applyRuleUsing,
      TptpFofSkolemTermLanguageDef.translateTermsConsRule,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      TptpFofSkolemTermLanguageDef.mkRule,
      TptpFofSkolemTermLanguageDef.congruence,
      TptpFofSkolemTermLanguageDef.termShiftRequest,
      TptpFofSkolemTermLanguageDef.termShiftResult,
      TptpFofSkolemTermLanguageDef.termsShiftRequest,
      TptpFofSkolemTermLanguageDef.termsShiftResult,
      TptpFofSkolemTermLanguageDef.envShiftRequest,
      TptpFofSkolemTermLanguageDef.envShiftResult,
      TptpFofSkolemTermLanguageDef.variablesRequest,
      TptpFofSkolemTermLanguageDef.variablesResult,
      TptpFofSkolemTermLanguageDef.lookupRequest,
      TptpFofSkolemTermLanguageDef.lookupResult,
      TptpFofSkolemTermLanguageDef.translateTermRequest,
      TptpFofSkolemTermLanguageDef.translateTermResult,
      TptpFofSkolemTermLanguageDef.translateTermsRequest,
      TptpFofSkolemTermLanguageDef.translateTermsResult,
      TptpFofSkolemTermLanguageDef.indexZero,
      TptpFofSkolemTermLanguageDef.indexSucc,
      TptpFofSkolemTermLanguageDef.sourceTermVariable,
      TptpFofSkolemTermLanguageDef.sourceTermFunction,
      TptpFofSkolemTermLanguageDef.sourceTermsNil,
      TptpFofSkolemTermLanguageDef.sourceTermsCons,
      TptpResolvedFofLanguageDef.encodeTermPatterns,
      TptpFofSkolemTermLanguageDef.targetTermVariable,
      TptpFofSkolemTermLanguageDef.targetTermOriginal,
      TptpFofSkolemTermLanguageDef.targetTermGenerated,
      TptpFofSkolemTermLanguageDef.targetTermsNil,
      TptpFofSkolemTermLanguageDef.targetTermsCons,
      TptpFofSkolemTermLanguageDef.envNil,
      TptpFofSkolemTermLanguageDef.envCons,
      TptpFofSkolemTermLanguageDef.a,
      TptpFofSkolemTermLanguageDef.v,
      TptpFofSkolemLanguageDef.termVariable,
      TptpFofSkolemLanguageDef.termOriginal,
      TptpFofSkolemLanguageDef.termGenerated,
      TptpFofSkolemLanguageDef.termsNil,
      TptpFofSkolemLanguageDef.termsCons,
      TptpFofSkolemLanguageDef.a,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

local syntax "term_extension_root_using " term,* : tactic
local macro_rules
  | `(tactic| term_extension_root_using $_proofs:term,*) =>
      `(tactic|
        simp only [TptpFofSkolemTermLanguageDef.termShiftRequest,
          TptpFofSkolemTermLanguageDef.termShiftResult,
          TptpFofSkolemTermLanguageDef.termsShiftRequest,
          TptpFofSkolemTermLanguageDef.termsShiftResult,
          TptpFofSkolemTermLanguageDef.envShiftRequest,
          TptpFofSkolemTermLanguageDef.envShiftResult,
          TptpFofSkolemTermLanguageDef.variablesRequest,
          TptpFofSkolemTermLanguageDef.variablesResult,
          TptpFofSkolemTermLanguageDef.lookupRequest,
          TptpFofSkolemTermLanguageDef.lookupResult,
          TptpFofSkolemTermLanguageDef.translateTermRequest,
          TptpFofSkolemTermLanguageDef.translateTermResult,
          TptpFofSkolemTermLanguageDef.translateTermsRequest,
          TptpFofSkolemTermLanguageDef.translateTermsResult,
          TptpFofSkolemTermLanguageDef.indexZero,
          TptpFofSkolemTermLanguageDef.indexSucc,
          TptpFofSkolemTermLanguageDef.sourceTermVariable,
          TptpFofSkolemTermLanguageDef.sourceTermFunction,
          TptpFofSkolemTermLanguageDef.sourceTermsNil,
          TptpFofSkolemTermLanguageDef.sourceTermsCons,
          TptpResolvedFofLanguageDef.encodeTermPatterns,
          TptpFofSkolemTermLanguageDef.targetTermVariable,
          TptpFofSkolemTermLanguageDef.targetTermOriginal,
          TptpFofSkolemTermLanguageDef.targetTermGenerated,
          TptpFofSkolemTermLanguageDef.targetTermsNil,
          TptpFofSkolemTermLanguageDef.targetTermsCons,
          TptpFofSkolemTermLanguageDef.envNil,
          TptpFofSkolemTermLanguageDef.envCons,
          TptpFofSkolemTermLanguageDef.a] at * <;>
        term_extension_silent <;>
        simp [*, TptpFofSkolemTermLanguageDef.rewrites, applyRuleUsing,
          TptpFofSkolemTermLanguageDef.translateTermsConsRule,
          matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
          TptpFofSkolemTermLanguageDef.mkRule,
          TptpFofSkolemTermLanguageDef.congruence,
          TptpFofSkolemTermLanguageDef.termShiftRequest,
          TptpFofSkolemTermLanguageDef.termShiftResult,
          TptpFofSkolemTermLanguageDef.termsShiftRequest,
          TptpFofSkolemTermLanguageDef.termsShiftResult,
          TptpFofSkolemTermLanguageDef.envShiftRequest,
          TptpFofSkolemTermLanguageDef.envShiftResult,
          TptpFofSkolemTermLanguageDef.variablesRequest,
          TptpFofSkolemTermLanguageDef.variablesResult,
          TptpFofSkolemTermLanguageDef.lookupRequest,
          TptpFofSkolemTermLanguageDef.lookupResult,
          TptpFofSkolemTermLanguageDef.translateTermRequest,
          TptpFofSkolemTermLanguageDef.translateTermResult,
          TptpFofSkolemTermLanguageDef.translateTermsRequest,
          TptpFofSkolemTermLanguageDef.translateTermsResult,
          TptpFofSkolemTermLanguageDef.indexZero,
          TptpFofSkolemTermLanguageDef.indexSucc,
          TptpFofSkolemTermLanguageDef.sourceTermVariable,
          TptpFofSkolemTermLanguageDef.sourceTermFunction,
          TptpFofSkolemTermLanguageDef.sourceTermsNil,
          TptpFofSkolemTermLanguageDef.sourceTermsCons,
          TptpFofSkolemTermLanguageDef.targetTermVariable,
          TptpFofSkolemTermLanguageDef.targetTermOriginal,
          TptpFofSkolemTermLanguageDef.targetTermGenerated,
          TptpFofSkolemTermLanguageDef.targetTermsNil,
          TptpFofSkolemTermLanguageDef.targetTermsCons,
          TptpFofSkolemTermLanguageDef.envNil,
          TptpFofSkolemTermLanguageDef.envCons,
          TptpFofSkolemTermLanguageDef.a,
          TptpFofSkolemTermLanguageDef.v,
          TptpFofSkolemLanguageDef.termVariable,
          TptpFofSkolemLanguageDef.termOriginal,
          TptpFofSkolemLanguageDef.termGenerated,
          TptpFofSkolemLanguageDef.termsNil,
          TptpFofSkolemLanguageDef.termsCons,
          TptpFofSkolemLanguageDef.a,
          matchPattern, matchArgs, mergeBindings,
          applyBindingsForRule, applyBindings])

/-! ## The inherited term substrate remains exact in the extension -/

attribute [-simp] TptpFofSkolemTermAgreement.Semantic.sourceTermsNil_eq

set_option maxHeartbeats 5000000 in
theorem embeddedTerm_rewriteAt_exact {source target : Pattern}
    (derivation : TptpFofSkolemTermAgreement.Derivation source target)
    (fuel : Nat) (enough : derivation.height <= fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofSkolemizationLanguageDef.language fuel source =
      [target] := by
  induction derivation generalizing fuel with
  | shiftVariable index =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel => term_extension_root
  | shiftOriginal arguments inductionHypothesis =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel =>
          have childEnough : arguments.height <= fuel := by
            simpa [TptpFofSkolemTermAgreement.Derivation.height,
              Nat.succ_eq_add_one] using enough
          term_extension_root_using inductionHypothesis fuel childEnough
  | shiftGenerated arguments inductionHypothesis =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel =>
          have childEnough : arguments.height <= fuel := by
            simpa [TptpFofSkolemTermAgreement.Derivation.height,
              Nat.succ_eq_add_one] using enough
          term_extension_root_using inductionHypothesis fuel childEnough
  | shiftTermsNil =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel => term_extension_root
  | shiftTermsCons head tail headHypothesis tailHypothesis =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max head.height tail.height <= fuel := by
            simpa [TptpFofSkolemTermAgreement.Derivation.height,
              Nat.succ_eq_add_one] using enough
          have headExact := headHypothesis fuel
            (le_trans (Nat.le_max_left _ _) maximumEnough)
          have tailExact := tailHypothesis fuel
            (le_trans (Nat.le_max_right _ _) maximumEnough)
          term_extension_root_using headExact, tailExact
  | shiftEnvNil =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel => term_extension_root
  | shiftEnvCons head tail headHypothesis tailHypothesis =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max head.height tail.height <= fuel := by
            simpa [TptpFofSkolemTermAgreement.Derivation.height,
              Nat.succ_eq_add_one] using enough
          have headExact := headHypothesis fuel
            (le_trans (Nat.le_max_left _ _) maximumEnough)
          have tailExact := tailHypothesis fuel
            (le_trans (Nat.le_max_right _ _) maximumEnough)
          term_extension_root_using headExact, tailExact
  | variablesZero =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel => term_extension_root
  | variablesSucc prior shift priorHypothesis shiftHypothesis =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max prior.height shift.height <= fuel := by
            simpa [TptpFofSkolemTermAgreement.Derivation.height,
              Nat.succ_eq_add_one] using enough
          have priorExact := priorHypothesis fuel
            (le_trans (Nat.le_max_left _ _) maximumEnough)
          have shiftExact := shiftHypothesis fuel
            (le_trans (Nat.le_max_right _ _) maximumEnough)
          term_extension_root_using priorExact, shiftExact
  | lookupZero head tail =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel => term_extension_root
  | lookupSucc prior inductionHypothesis =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel =>
          have childEnough : prior.height <= fuel := by
            simpa [TptpFofSkolemTermAgreement.Derivation.height,
              Nat.succ_eq_add_one] using enough
          term_extension_root_using inductionHypothesis fuel childEnough
  | translateVariable lookup inductionHypothesis =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel =>
          have childEnough : lookup.height <= fuel := by
            simpa [TptpFofSkolemTermAgreement.Derivation.height,
              Nat.succ_eq_add_one] using enough
          term_extension_root_using inductionHypothesis fuel childEnough
  | translateFunction arguments inductionHypothesis =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel =>
          have childEnough : arguments.height <= fuel := by
            simpa [TptpFofSkolemTermAgreement.Derivation.height,
              Nat.succ_eq_add_one] using enough
          term_extension_root_using inductionHypothesis fuel childEnough
  | translateTermsNil environment =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel => term_extension_root
  | translateTermsCons head tail headHypothesis tailHypothesis =>
      cases fuel with
      | zero => simp [TptpFofSkolemTermAgreement.Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max head.height tail.height <= fuel := by
            simpa [TptpFofSkolemTermAgreement.Derivation.height,
              Nat.succ_eq_add_one] using enough
          have headExact := headHypothesis fuel
            (le_trans (Nat.le_max_left _ _) maximumEnough)
          have tailExact := tailHypothesis fuel
            (le_trans (Nat.le_max_right _ _) maximumEnough)
          term_extension_root_using headExact, tailExact
#print axioms embeddedTerm_rewriteAt_exact

/-! ## Independent formula traversal -/

inductive Derivation : Pattern -> Pattern -> Type
  | matrixVerum (environment : Pattern) :
      Derivation (matrixRequest environment
        TptpFofPrenexLanguageDef.matrixVerum)
        (matrixResult environment TptpFofPrenexLanguageDef.matrixVerum
          TptpFofSkolemLanguageDef.verum)
  | matrixFalsum (environment : Pattern) :
      Derivation (matrixRequest environment
        TptpFofPrenexLanguageDef.matrixFalsum)
        (matrixResult environment TptpFofPrenexLanguageDef.matrixFalsum
          TptpFofSkolemLanguageDef.falsum)
  | matrixPositive {environment relation arguments targetArguments : Pattern}
      (argumentsTranslation : TptpFofSkolemTermAgreement.Derivation
        (translateTermsRequest environment arguments)
        (translateTermsResult environment arguments targetArguments)) :
      Derivation (matrixRequest environment
        (TptpFofPrenexLanguageDef.matrixPositive relation arguments))
        (matrixResult environment
          (TptpFofPrenexLanguageDef.matrixPositive relation arguments)
          (TptpFofSkolemLanguageDef.positive relation targetArguments))
  | matrixNegative {environment relation arguments targetArguments : Pattern}
      (argumentsTranslation : TptpFofSkolemTermAgreement.Derivation
        (translateTermsRequest environment arguments)
        (translateTermsResult environment arguments targetArguments)) :
      Derivation (matrixRequest environment
        (TptpFofPrenexLanguageDef.matrixNegative relation arguments))
        (matrixResult environment
          (TptpFofPrenexLanguageDef.matrixNegative relation arguments)
          (TptpFofSkolemLanguageDef.negative relation targetArguments))
  | matrixEqual {environment left right targetLeft targetRight : Pattern}
      (leftTranslation : TptpFofSkolemTermAgreement.Derivation
        (translateTermRequest environment left)
        (translateTermResult environment left targetLeft))
      (rightTranslation : TptpFofSkolemTermAgreement.Derivation
        (translateTermRequest environment right)
        (translateTermResult environment right targetRight)) :
      Derivation (matrixRequest environment
        (TptpFofPrenexLanguageDef.matrixEqual left right))
        (matrixResult environment
          (TptpFofPrenexLanguageDef.matrixEqual left right)
          (TptpFofSkolemLanguageDef.equal targetLeft targetRight))
  | matrixNotEqual {environment left right targetLeft targetRight : Pattern}
      (leftTranslation : TptpFofSkolemTermAgreement.Derivation
        (translateTermRequest environment left)
        (translateTermResult environment left targetLeft))
      (rightTranslation : TptpFofSkolemTermAgreement.Derivation
        (translateTermRequest environment right)
        (translateTermResult environment right targetRight)) :
      Derivation (matrixRequest environment
        (TptpFofPrenexLanguageDef.matrixNotEqual left right))
        (matrixResult environment
          (TptpFofPrenexLanguageDef.matrixNotEqual left right)
          (TptpFofSkolemLanguageDef.notEqual targetLeft targetRight))
  | matrixAnd {environment left right targetLeft targetRight : Pattern}
      (leftDerivation : Derivation (matrixRequest environment left)
        (matrixResult environment left targetLeft))
      (rightDerivation : Derivation (matrixRequest environment right)
        (matrixResult environment right targetRight)) :
      Derivation (matrixRequest environment
        (TptpFofPrenexLanguageDef.matrixAnd left right))
        (matrixResult environment
          (TptpFofPrenexLanguageDef.matrixAnd left right)
          (TptpFofSkolemLanguageDef.and targetLeft targetRight))
  | matrixOr {environment left right targetLeft targetRight : Pattern}
      (leftDerivation : Derivation (matrixRequest environment left)
        (matrixResult environment left targetLeft))
      (rightDerivation : Derivation (matrixRequest environment right)
        (matrixResult environment right targetRight)) :
      Derivation (matrixRequest environment
        (TptpFofPrenexLanguageDef.matrixOr left right))
        (matrixResult environment
          (TptpFofPrenexLanguageDef.matrixOr left right)
          (TptpFofSkolemLanguageDef.or targetLeft targetRight))
  | formMatrix {environment targetDepth frontier matrix target : Pattern}
      (matrixDerivation : Derivation (matrixRequest environment matrix)
        (matrixResult environment matrix target)) :
      Derivation (formRequest environment targetDepth frontier
        (TptpFofPrenexLanguageDef.matrix matrix))
        (formResult environment targetDepth frontier
          (TptpFofPrenexLanguageDef.matrix matrix) target frontier
          TptpFofSkolemLanguageDef.introducedNil)
  | formAll {environment shiftedEnvironment targetDepth frontier body target
      next introduced : Pattern}
      (environmentShift : TptpFofSkolemTermAgreement.Derivation
        (envShiftRequest environment)
        (envShiftResult environment shiftedEnvironment))
      (bodyDerivation : Derivation
        (formRequest
          (envCons (targetTermVariable indexZero) shiftedEnvironment)
          (indexSucc targetDepth) frontier body)
        (formResult
          (envCons (targetTermVariable indexZero) shiftedEnvironment)
          (indexSucc targetDepth) frontier body target next introduced)) :
      Derivation (formRequest environment targetDepth frontier
        (TptpFofPrenexLanguageDef.all body))
        (formResult environment targetDepth frontier
          (TptpFofPrenexLanguageDef.all body)
          (TptpFofSkolemLanguageDef.all target) next introduced)
  | formEx {environment targetDepth frontier arguments body target next
      introduced : Pattern}
      (variableVector : TptpFofSkolemTermAgreement.Derivation
        (variablesRequest targetDepth)
        (variablesResult targetDepth arguments))
      (bodyDerivation : Derivation
        (formRequest
          (envCons (targetTermGenerated frontier arguments) environment)
          targetDepth (indexSucc frontier) body)
        (formResult
          (envCons (targetTermGenerated frontier arguments) environment)
          targetDepth (indexSucc frontier) body target next introduced)) :
      Derivation (formRequest environment targetDepth frontier
        (TptpFofPrenexLanguageDef.ex body))
        (formResult environment targetDepth frontier
          (TptpFofPrenexLanguageDef.ex body) target next
          (TptpFofSkolemLanguageDef.introducedCons
            (TptpFofSkolemLanguageDef.introducedSymbol frontier targetDepth)
            introduced))

def Derivation.height : {source target : Pattern} ->
    Derivation source target -> Nat
  | _, _, .matrixVerum _ | _, _, .matrixFalsum _ => 1
  | _, _, .matrixPositive arguments
  | _, _, .matrixNegative arguments => arguments.height + 1
  | _, _, .matrixEqual left right
  | _, _, .matrixNotEqual left right => max left.height right.height + 1
  | _, _, .matrixAnd left right
  | _, _, .matrixOr left right => max left.height right.height + 1
  | _, _, .formMatrix matrix => matrix.height + 1
  | _, _, .formAll shift body
  | _, _, .formEx shift body => max shift.height body.height + 1

set_option maxHeartbeats 5000000 in
theorem Derivation.rewriteAt_exact {source target : Pattern}
    (derivation : Derivation source target) (fuel : Nat)
    (enough : derivation.height <= fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofSkolemizationLanguageDef.language fuel source = [target] := by
  induction derivation generalizing fuel with
  | matrixVerum environment =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => skolemization_root
  | matrixFalsum environment =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => skolemization_root
  | matrixPositive arguments =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : arguments.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := embeddedTerm_rewriteAt_exact arguments fuel
            childEnough
          skolemization_root_using childExact
  | matrixNegative arguments =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : arguments.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := embeddedTerm_rewriteAt_exact arguments fuel
            childEnough
          skolemization_root_using childExact
  | matrixEqual left right =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have leftExact := embeddedTerm_rewriteAt_exact left fuel
            (le_trans (Nat.le_max_left _ _) maximumEnough)
          have rightExact := embeddedTerm_rewriteAt_exact right fuel
            (le_trans (Nat.le_max_right _ _) maximumEnough)
          skolemization_root_using leftExact, rightExact
  | matrixNotEqual left right =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have leftExact := embeddedTerm_rewriteAt_exact left fuel
            (le_trans (Nat.le_max_left _ _) maximumEnough)
          have rightExact := embeddedTerm_rewriteAt_exact right fuel
            (le_trans (Nat.le_max_right _ _) maximumEnough)
          skolemization_root_using leftExact, rightExact
  | matrixAnd left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have leftExact := leftHypothesis fuel
            (le_trans (Nat.le_max_left _ _) maximumEnough)
          have rightExact := rightHypothesis fuel
            (le_trans (Nat.le_max_right _ _) maximumEnough)
          skolemization_root_using leftExact, rightExact
  | matrixOr left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have leftExact := leftHypothesis fuel
            (le_trans (Nat.le_max_left _ _) maximumEnough)
          have rightExact := rightHypothesis fuel
            (le_trans (Nat.le_max_right _ _) maximumEnough)
          skolemization_root_using leftExact, rightExact
  | formMatrix matrix inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : matrix.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := inductionHypothesis fuel childEnough
          skolemization_root_using childExact
  | formAll shift body bodyHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max shift.height body.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have shiftExact := embeddedTerm_rewriteAt_exact shift fuel
            (le_trans (Nat.le_max_left _ _) maximumEnough)
          have bodyExact := bodyHypothesis fuel
            (le_trans (Nat.le_max_right _ _) maximumEnough)
          skolemization_root_using shiftExact, bodyExact
  | formEx variableVector body bodyHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max variableVector.height body.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have variableVectorExact := embeddedTerm_rewriteAt_exact variableVector fuel
            (le_trans (Nat.le_max_left _ _) maximumEnough)
          have bodyExact := bodyHypothesis fuel
            (le_trans (Nat.le_max_right _ _) maximumEnough)
          skolemization_root_using variableVectorExact, bodyExact

theorem Derivation.no_invention {source target invented : Pattern}
    (derivation : Derivation source target) (fuel : Nat)
    (enough : derivation.height <= fuel)
    (membership : invented ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpFofSkolemizationLanguageDef.language fuel source) :
    invented = target := by
  rw [derivation.rewriteAt_exact fuel enough] at membership
  simpa using membership

#print axioms Derivation.rewriteAt_exact
#print axioms Derivation.no_invention

end Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationAgreement
