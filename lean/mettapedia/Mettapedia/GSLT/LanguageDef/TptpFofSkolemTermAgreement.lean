import Mettapedia.GSLT.LanguageDef.TptpFofSkolemTermLanguageDef

/-!
# Exact execution of the authored Skolem term substrate

This module proves that every independent structural derivation of a target
term shift, environment operation, variable-vector construction, lookup, or
source-term translation has exactly one authored `LanguageDef` reduct.  The
relation below does not call the rewrite engine; the execution theorem is the
bridge between the two independently defined authorities.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofSkolemTermAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpFofSkolemTermLanguageDef

local macro "skolem_term_root" : tactic =>
  `(tactic|
    simp [rewriteAt, language_rewrites, rewrites, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      translateTermsConsRule, mkRule, congruence,
      termShiftRequest, termShiftResult,
      termsShiftRequest, termsShiftResult, envShiftRequest, envShiftResult,
      variablesRequest, variablesResult, lookupRequest, lookupResult,
      translateTermRequest, translateTermResult, translateTermsRequest,
      translateTermsResult, indexZero, indexSucc, sourceTermVariable,
      sourceTermFunction, sourceTermsNil, sourceTermsCons, targetTermVariable,
      targetTermOriginal, targetTermGenerated, targetTermsNil,
      targetTermsCons, envNil, envCons, a, v, matchPattern, matchArgs,
      mergeBindings, applyBindingsForRule, applyBindings])

local syntax "skolem_term_root_using " term,* : tactic
local macro_rules
  | `(tactic| skolem_term_root_using $_proofs:term,*) =>
      `(tactic|
        simp only [termShiftRequest, termShiftResult, termsShiftRequest,
          termsShiftResult, envShiftRequest, envShiftResult,
          variablesRequest, variablesResult, lookupRequest, lookupResult,
          translateTermRequest, translateTermResult, translateTermsRequest,
          translateTermsResult, indexZero, indexSucc, sourceTermVariable,
          sourceTermFunction, sourceTermsNil, sourceTermsCons,
          targetTermVariable, targetTermOriginal, targetTermGenerated,
          targetTermsNil, targetTermsCons, envNil, envCons, a] at * <;>
        simp [*, rewriteAt, language_rewrites, rewrites, applyRuleUsing,
          matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
          translateTermsConsRule, mkRule, congruence,
          termShiftRequest, termShiftResult,
          termsShiftRequest, termsShiftResult, envShiftRequest,
          envShiftResult, variablesRequest, variablesResult, lookupRequest,
          lookupResult, translateTermRequest, translateTermResult,
          translateTermsRequest, translateTermsResult, indexZero, indexSucc,
          sourceTermVariable, sourceTermFunction, sourceTermsNil,
          sourceTermsCons, targetTermVariable, targetTermOriginal,
          targetTermGenerated, targetTermsNil, targetTermsCons, envNil,
          envCons, a, v, matchPattern, matchArgs, mergeBindings,
          applyBindingsForRule, applyBindings])

/-! ## Exact root rules -/

theorem shift_variable_exact (fuel : Nat) (index : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termShiftRequest (targetTermVariable index)) =
      [termShiftResult (targetTermVariable index)
        (targetTermVariable (indexSucc index))] := by
  skolem_term_root

theorem shift_original_exact (fuel : Nat)
    (function arguments targetArguments : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termsShiftRequest arguments) =
        [termsShiftResult arguments targetArguments]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termShiftRequest (targetTermOriginal function arguments)) =
      [termShiftResult (targetTermOriginal function arguments)
        (targetTermOriginal function targetArguments)] := by
  skolem_term_root_using exact

theorem shift_generated_exact (fuel : Nat)
    (id arguments targetArguments : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termsShiftRequest arguments) =
        [termsShiftResult arguments targetArguments]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termShiftRequest (targetTermGenerated id arguments)) =
      [termShiftResult (targetTermGenerated id arguments)
        (targetTermGenerated id targetArguments)] := by
  skolem_term_root_using exact

theorem shift_terms_nil_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termsShiftRequest targetTermsNil) =
      [termsShiftResult targetTermsNil targetTermsNil] := by
  skolem_term_root

theorem shift_terms_cons_exact (fuel : Nat)
    (head tail targetHead targetTail : Pattern)
    (headExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termShiftRequest head) = [termShiftResult head targetHead])
    (tailExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termsShiftRequest tail) = [termsShiftResult tail targetTail]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termsShiftRequest (targetTermsCons head tail)) =
      [termsShiftResult (targetTermsCons head tail)
        (targetTermsCons targetHead targetTail)] := by
  skolem_term_root_using headExact, tailExact

theorem shift_env_nil_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (envShiftRequest envNil) = [envShiftResult envNil envNil] := by
  skolem_term_root

theorem shift_env_cons_exact (fuel : Nat)
    (head tail targetHead targetTail : Pattern)
    (headExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termShiftRequest head) = [termShiftResult head targetHead])
    (tailExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (envShiftRequest tail) = [envShiftResult tail targetTail]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (envShiftRequest (envCons head tail)) =
      [envShiftResult (envCons head tail) (envCons targetHead targetTail)] := by
  skolem_term_root_using headExact, tailExact

theorem variables_zero_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (variablesRequest indexZero) =
      [variablesResult indexZero targetTermsNil] := by
  skolem_term_root

theorem variables_succ_exact (fuel : Nat) (depth prior shifted : Pattern)
    (priorExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (variablesRequest depth) = [variablesResult depth prior])
    (shiftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termsShiftRequest prior) = [termsShiftResult prior shifted]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (variablesRequest (indexSucc depth)) =
      [variablesResult (indexSucc depth)
        (targetTermsCons (targetTermVariable indexZero) shifted)] := by
  skolem_term_root_using priorExact, shiftExact

theorem lookup_zero_exact (fuel : Nat) (head tail : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (lookupRequest (envCons head tail) indexZero) =
      [lookupResult (envCons head tail) indexZero head] := by
  skolem_term_root

theorem lookup_succ_exact (fuel : Nat)
    (head tail index target : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (lookupRequest tail index) = [lookupResult tail index target]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (lookupRequest (envCons head tail) (indexSucc index)) =
      [lookupResult (envCons head tail) (indexSucc index) target] := by
  skolem_term_root_using exact

theorem translate_variable_exact (fuel : Nat)
    (environment index target : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (lookupRequest environment index) =
        [lookupResult environment index target]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (translateTermRequest environment (sourceTermVariable index)) =
      [translateTermResult environment (sourceTermVariable index) target] := by
  skolem_term_root_using exact

theorem translate_function_exact (fuel : Nat)
    (environment function arguments targetArguments : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (translateTermsRequest environment arguments) =
        [translateTermsResult environment arguments targetArguments]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (translateTermRequest environment
          (sourceTermFunction function arguments)) =
      [translateTermResult environment
        (sourceTermFunction function arguments)
        (targetTermOriginal function targetArguments)] := by
  skolem_term_root_using exact

theorem translate_terms_nil_exact (fuel : Nat) (environment : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (translateTermsRequest environment sourceTermsNil) =
      [translateTermsResult environment sourceTermsNil targetTermsNil] := by
  skolem_term_root

theorem translate_terms_cons_exact (fuel : Nat)
    (environment head tail targetHead targetTail : Pattern)
    (headExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (translateTermRequest environment head) =
        [translateTermResult environment head targetHead])
    (tailExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (translateTermsRequest environment tail) =
        [translateTermsResult environment tail targetTail]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (translateTermsRequest environment (sourceTermsCons head tail)) =
      [translateTermsResult environment (sourceTermsCons head tail)
        (targetTermsCons targetHead targetTail)] := by
  skolem_term_root_using headExact, tailExact

/-! ## Independent structural derivations -/

inductive Derivation : Pattern -> Pattern -> Type
  | shiftVariable (index : Pattern) :
      Derivation (termShiftRequest (targetTermVariable index))
        (termShiftResult (targetTermVariable index)
          (targetTermVariable (indexSucc index)))
  | shiftOriginal {function arguments targetArguments : Pattern}
      (argumentsShift : Derivation (termsShiftRequest arguments)
        (termsShiftResult arguments targetArguments)) :
      Derivation (termShiftRequest (targetTermOriginal function arguments))
        (termShiftResult (targetTermOriginal function arguments)
          (targetTermOriginal function targetArguments))
  | shiftGenerated {id arguments targetArguments : Pattern}
      (argumentsShift : Derivation (termsShiftRequest arguments)
        (termsShiftResult arguments targetArguments)) :
      Derivation (termShiftRequest (targetTermGenerated id arguments))
        (termShiftResult (targetTermGenerated id arguments)
          (targetTermGenerated id targetArguments))
  | shiftTermsNil :
      Derivation (termsShiftRequest targetTermsNil)
        (termsShiftResult targetTermsNil targetTermsNil)
  | shiftTermsCons {head tail targetHead targetTail : Pattern}
      (headShift : Derivation (termShiftRequest head)
        (termShiftResult head targetHead))
      (tailShift : Derivation (termsShiftRequest tail)
        (termsShiftResult tail targetTail)) :
      Derivation (termsShiftRequest (targetTermsCons head tail))
        (termsShiftResult (targetTermsCons head tail)
          (targetTermsCons targetHead targetTail))
  | shiftEnvNil :
      Derivation (envShiftRequest envNil) (envShiftResult envNil envNil)
  | shiftEnvCons {head tail targetHead targetTail : Pattern}
      (headShift : Derivation (termShiftRequest head)
        (termShiftResult head targetHead))
      (tailShift : Derivation (envShiftRequest tail)
        (envShiftResult tail targetTail)) :
      Derivation (envShiftRequest (envCons head tail))
        (envShiftResult (envCons head tail) (envCons targetHead targetTail))
  | variablesZero :
      Derivation (variablesRequest indexZero)
        (variablesResult indexZero targetTermsNil)
  | variablesSucc {depth prior shifted : Pattern}
      (priorDerivation : Derivation (variablesRequest depth)
        (variablesResult depth prior))
      (shiftDerivation : Derivation (termsShiftRequest prior)
        (termsShiftResult prior shifted)) :
      Derivation (variablesRequest (indexSucc depth))
        (variablesResult (indexSucc depth)
          (targetTermsCons (targetTermVariable indexZero) shifted))
  | lookupZero (head tail : Pattern) :
      Derivation (lookupRequest (envCons head tail) indexZero)
        (lookupResult (envCons head tail) indexZero head)
  | lookupSucc {head tail index target : Pattern}
      (prior : Derivation (lookupRequest tail index)
        (lookupResult tail index target)) :
      Derivation (lookupRequest (envCons head tail) (indexSucc index))
        (lookupResult (envCons head tail) (indexSucc index) target)
  | translateVariable {environment index target : Pattern}
      (lookup : Derivation (lookupRequest environment index)
        (lookupResult environment index target)) :
      Derivation (translateTermRequest environment (sourceTermVariable index))
        (translateTermResult environment (sourceTermVariable index) target)
  | translateFunction {environment function arguments targetArguments : Pattern}
      (argumentsTranslation :
        Derivation (translateTermsRequest environment arguments)
          (translateTermsResult environment arguments targetArguments)) :
      Derivation
        (translateTermRequest environment
          (sourceTermFunction function arguments))
        (translateTermResult environment
          (sourceTermFunction function arguments)
          (targetTermOriginal function targetArguments))
  | translateTermsNil (environment : Pattern) :
      Derivation (translateTermsRequest environment sourceTermsNil)
        (translateTermsResult environment sourceTermsNil targetTermsNil)
  | translateTermsCons {environment head tail targetHead targetTail : Pattern}
      (headTranslation : Derivation (translateTermRequest environment head)
        (translateTermResult environment head targetHead))
      (tailTranslation : Derivation (translateTermsRequest environment tail)
        (translateTermsResult environment tail targetTail)) :
      Derivation (translateTermsRequest environment (sourceTermsCons head tail))
        (translateTermsResult environment (sourceTermsCons head tail)
          (targetTermsCons targetHead targetTail))

def Derivation.height : {source target : Pattern} ->
    Derivation source target -> Nat
  | _, _, .shiftVariable _ => 1
  | _, _, .shiftOriginal arguments => arguments.height + 1
  | _, _, .shiftGenerated arguments => arguments.height + 1
  | _, _, .shiftTermsNil => 1
  | _, _, .shiftTermsCons head tail => max head.height tail.height + 1
  | _, _, .shiftEnvNil => 1
  | _, _, .shiftEnvCons head tail => max head.height tail.height + 1
  | _, _, .variablesZero => 1
  | _, _, .variablesSucc prior shift => max prior.height shift.height + 1
  | _, _, .lookupZero _ _ => 1
  | _, _, .lookupSucc prior => prior.height + 1
  | _, _, .translateVariable lookup => lookup.height + 1
  | _, _, .translateFunction arguments => arguments.height + 1
  | _, _, .translateTermsNil _ => 1
  | _, _, .translateTermsCons head tail => max head.height tail.height + 1

theorem Derivation.rewriteAt_exact {source target : Pattern}
    (derivation : Derivation source target) (fuel : Nat)
    (enough : derivation.height <= fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty) language fuel source =
      [target] := by
  induction derivation generalizing fuel with
  | shiftVariable index =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using shift_variable_exact fuel index
  | shiftOriginal arguments inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : arguments.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact shift_original_exact fuel _ _ _
            (inductionHypothesis fuel childEnough)
  | shiftGenerated arguments inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : arguments.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact shift_generated_exact fuel _ _ _
            (inductionHypothesis fuel childEnough)
  | shiftTermsNil =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using shift_terms_nil_exact fuel
  | shiftTermsCons head tail headHypothesis tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max head.height tail.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact shift_terms_cons_exact fuel _ _ _ _
            (headHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (tailHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | shiftEnvNil =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using shift_env_nil_exact fuel
  | shiftEnvCons head tail headHypothesis tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max head.height tail.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact shift_env_cons_exact fuel _ _ _ _
            (headHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (tailHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | variablesZero =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using variables_zero_exact fuel
  | variablesSucc prior shift priorHypothesis shiftHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max prior.height shift.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact variables_succ_exact fuel _ _ _
            (priorHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (shiftHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | lookupZero head tail =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using lookup_zero_exact fuel head tail
  | lookupSucc prior inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : prior.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact lookup_succ_exact fuel _ _ _ _
            (inductionHypothesis fuel childEnough)
  | translateVariable lookup inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : lookup.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact translate_variable_exact fuel _ _ _
            (inductionHypothesis fuel childEnough)
  | translateFunction arguments inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : arguments.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact translate_function_exact fuel _ _ _ _
            (inductionHypothesis fuel childEnough)
  | translateTermsNil environment =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using translate_terms_nil_exact fuel environment
  | translateTermsCons head tail headHypothesis tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max head.height tail.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact translate_terms_cons_exact fuel _ _ _ _ _
            (headHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (tailHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))

theorem Derivation.no_invention {source target invented : Pattern}
    (derivation : Derivation source target) (fuel : Nat)
    (enough : derivation.height <= fuel)
    (membership : invented ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel source) :
    invented = target := by
  rw [derivation.rewriteAt_exact fuel enough] at membership
  simpa using membership

/-! ## Agreement with semantic target-term shifting -/

open LO FirstOrder
open scoped LO.FirstOrder

namespace Semantic

abbrev Term := TptpFofSkolemizationSemantics.Term
abbrev FunctionSymbol := TptpFofSkolemizationSemantics.FunctionSymbol

@[simp] theorem encodeNatIndex_succ (index : Nat) :
    TptpResolvedFofLanguageDef.encodeNatIndex (index + 1) =
      indexSucc (TptpResolvedFofLanguageDef.encodeNatIndex index) := by
  rfl

@[simp] theorem encodeNatIndex_zero :
    TptpResolvedFofLanguageDef.encodeNatIndex 0 = indexZero := by
  rfl

@[simp] theorem targetTermVariable_eq (index : Pattern) :
    targetTermVariable index = TptpFofSkolemLanguageDef.termVariable index := by
  rfl

@[simp] theorem targetTermsNil_eq :
    targetTermsNil = TptpFofSkolemLanguageDef.termsNil := by
  rfl

@[simp] theorem targetTermsCons_eq (head tail : Pattern) :
    targetTermsCons head tail =
      TptpFofSkolemLanguageDef.termsCons head tail := by
  rfl

@[simp] theorem sourceTermsNil_eq :
    sourceTermsNil = TptpResolvedFofLanguageDef.encodeTermPatterns [] := by
  rfl

@[simp] theorem sourceTermsCons_eq (head : Pattern) (tail : List Pattern) :
    sourceTermsCons head
        (TptpResolvedFofLanguageDef.encodeTermPatterns tail) =
      TptpResolvedFofLanguageDef.encodeTermPatterns (head :: tail) := by
  rfl

def encodePatternList : List Pattern -> Pattern
  | [] => targetTermsNil
  | head :: tail => targetTermsCons head (encodePatternList tail)

noncomputable def targetTermPattern {depth : Nat}
    (term : Term depth) : Pattern :=
  LO.FirstOrder.Semiterm.rec (motive := fun _ => Pattern)
    (fun index => targetTermVariable
      (TptpResolvedFofLanguageDef.encodeNatIndex index.val))
    (fun impossible => nomatch impossible)
    (fun {arity} (function : FunctionSymbol arity) _ encodedArguments =>
      match function with
      | .original sourceFunction =>
          targetTermOriginal
            (TptpFofSymbolLanguageDef.encodeFunctionHead
              ⟨sourceFunction.kind, sourceFunction.name⟩)
            (encodePatternList (List.ofFn encodedArguments))
      | .generated id =>
          targetTermGenerated
            (TptpResolvedFofLanguageDef.encodeNatIndex id)
            (encodePatternList (List.ofFn encodedArguments)))
    term

noncomputable def shiftedTargetTermPattern {depth : Nat}
    (term : Term depth) : Pattern :=
  LO.FirstOrder.Semiterm.rec (motive := fun _ => Pattern)
    (fun index => targetTermVariable
      (TptpResolvedFofLanguageDef.encodeNatIndex (index.val + 1)))
    (fun impossible => nomatch impossible)
    (fun {arity} (function : FunctionSymbol arity) _ shiftedArguments =>
      match function with
      | .original sourceFunction =>
          targetTermOriginal
            (TptpFofSymbolLanguageDef.encodeFunctionHead
              ⟨sourceFunction.kind, sourceFunction.name⟩)
            (encodePatternList (List.ofFn shiftedArguments))
      | .generated id =>
          targetTermGenerated
            (TptpResolvedFofLanguageDef.encodeNatIndex id)
            (encodePatternList (List.ofFn shiftedArguments)))
    term

@[simp] theorem targetTermPattern_bvar {depth : Nat} (index : Fin depth) :
    targetTermPattern (show Term depth from .bvar index) =
      targetTermVariable
        (TptpResolvedFofLanguageDef.encodeNatIndex index.val) := by
  rfl

@[simp] theorem shiftedTargetTermPattern_bvar {depth : Nat}
    (index : Fin depth) :
    shiftedTargetTermPattern (show Term depth from .bvar index) =
      targetTermVariable
        (TptpResolvedFofLanguageDef.encodeNatIndex (index.val + 1)) := by
  rfl

noncomputable def targetTermsPattern {depth : Nat}
    (terms : List (Term depth)) : Pattern :=
  encodePatternList (terms.map targetTermPattern)

noncomputable def shiftedTargetTermsPattern {depth : Nat}
    (terms : List (Term depth)) : Pattern :=
  encodePatternList (terms.map shiftedTargetTermPattern)

noncomputable def vectorTermsDerivation {depth : Nat} :
    {arity : Nat} -> (arguments : Fin arity -> Term depth) ->
    ((index : Fin arity) ->
      Derivation (termShiftRequest (targetTermPattern (arguments index)))
        (termShiftResult (targetTermPattern (arguments index))
          (shiftedTargetTermPattern (arguments index)))) ->
    Derivation
      (termsShiftRequest (encodePatternList
        (List.ofFn fun index => targetTermPattern (arguments index))))
      (termsShiftResult
        (encodePatternList
          (List.ofFn fun index => targetTermPattern (arguments index)))
        (encodePatternList
          (List.ofFn fun index => shiftedTargetTermPattern (arguments index))))
  | 0, _, _ => by
      simpa [List.ofFn_zero, encodePatternList] using Derivation.shiftTermsNil
  | arity + 1, arguments, children => by
      simpa [List.ofFn_succ, encodePatternList] using
        Derivation.shiftTermsCons (children 0)
          (vectorTermsDerivation (fun index => arguments index.succ)
            (fun index => children index.succ))

noncomputable def termDerivation {depth : Nat} (term : Term depth) :
    Derivation (termShiftRequest (targetTermPattern term))
      (termShiftResult (targetTermPattern term)
        (shiftedTargetTermPattern term)) :=
  LO.FirstOrder.Semiterm.rec
    (motive := fun term =>
      Derivation (termShiftRequest (targetTermPattern term))
        (termShiftResult (targetTermPattern term)
          (shiftedTargetTermPattern term)))
    (fun index => by
      simpa [targetTermPattern, shiftedTargetTermPattern] using
        Derivation.shiftVariable
          (TptpResolvedFofLanguageDef.encodeNatIndex index.val))
    (fun impossible => nomatch impossible)
    (fun {arity} function arguments children => by
      cases function with
      | original sourceFunction =>
          simpa [targetTermPattern, shiftedTargetTermPattern] using
            Derivation.shiftOriginal
              (vectorTermsDerivation arguments children)
      | generated id =>
          simpa [targetTermPattern, shiftedTargetTermPattern] using
            Derivation.shiftGenerated
              (vectorTermsDerivation arguments children))
    term

noncomputable def termsDerivation {depth : Nat} :
    (terms : List (Term depth)) ->
    Derivation (termsShiftRequest (targetTermsPattern terms))
      (termsShiftResult (targetTermsPattern terms)
        (shiftedTargetTermsPattern terms))
  | [] => by
      simpa [targetTermsPattern, shiftedTargetTermsPattern,
        encodePatternList] using Derivation.shiftTermsNil
  | head :: tail => by
      simpa [targetTermsPattern, shiftedTargetTermsPattern,
        encodePatternList] using
        Derivation.shiftTermsCons (termDerivation head)
          (termsDerivation tail)

theorem encodePatternList_exact (patterns : List Pattern) :
    encodePatternList patterns =
      TptpFofSkolemLanguageDef.encodeTermPatterns patterns := by
  induction patterns with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [encodePatternList, TptpFofSkolemLanguageDef.encodeTermPatterns,
        inductionHypothesis]

theorem targetTermPattern_exact {depth : Nat} (term : Term depth) :
    targetTermPattern term = TptpFofSkolemLanguageDef.encodeTerm term := by
  induction term with
  | bvar index => rfl
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      cases function with
      | original sourceFunction =>
          simp only [targetTermPattern,
            TptpFofSkolemLanguageDef.encodeTerm]
          rw [encodePatternList_exact]
          congr 2
          exact List.ofFn_inj.mpr (funext inductionHypothesis)
      | generated id =>
          simp only [targetTermPattern,
            TptpFofSkolemLanguageDef.encodeTerm]
          rw [encodePatternList_exact]
          congr 2
          exact List.ofFn_inj.mpr (funext inductionHypothesis)

theorem shiftedTargetTermPattern_exact {depth : Nat} (term : Term depth) :
    shiftedTargetTermPattern term =
      TptpFofSkolemLanguageDef.encodeTerm
        (LO.FirstOrder.Rew.bShift term) := by
  induction term with
  | bvar index =>
      simp [shiftedTargetTermPattern, LO.FirstOrder.Rew.bShift_bvar,
        TptpFofSkolemLanguageDef.encodeTerm,
        TptpResolvedFofLanguageDef.encodeIndex]
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      rw [LO.FirstOrder.Rew.func]
      cases function with
      | original sourceFunction =>
          simp only [shiftedTargetTermPattern,
            TptpFofSkolemLanguageDef.encodeTerm]
          rw [encodePatternList_exact]
          congr 2
          exact List.ofFn_inj.mpr (funext inductionHypothesis)
      | generated id =>
          simp only [shiftedTargetTermPattern,
            TptpFofSkolemLanguageDef.encodeTerm]
          rw [encodePatternList_exact]
          congr 2
          exact List.ofFn_inj.mpr (funext inductionHypothesis)

theorem rewriteAt_bShift_exact {depth : Nat} (term : Term depth) :
    rewriteAt (engineBasePremises RelationEnv.empty) language
        (termDerivation term).height
        (termShiftRequest (TptpFofSkolemLanguageDef.encodeTerm term)) =
      [termShiftResult (TptpFofSkolemLanguageDef.encodeTerm term)
        (TptpFofSkolemLanguageDef.encodeTerm
          (LO.FirstOrder.Rew.bShift term))] := by
  simpa [targetTermPattern_exact, shiftedTargetTermPattern_exact] using
    (termDerivation term).rewriteAt_exact (termDerivation term).height
      (le_refl _)

theorem rewriteAt_bShift_no_invention {depth : Nat} (term : Term depth)
    (invented : Pattern)
    (membership : invented ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language
        (termDerivation term).height
        (termShiftRequest (TptpFofSkolemLanguageDef.encodeTerm term))) :
    invented = termShiftResult (TptpFofSkolemLanguageDef.encodeTerm term)
      (TptpFofSkolemLanguageDef.encodeTerm
        (LO.FirstOrder.Rew.bShift term)) := by
  rw [rewriteAt_bShift_exact] at membership
  simpa using membership

/-! ## Environment shifting -/

def encodeEnvironmentPatterns : List Pattern -> Pattern
  | [] => envNil
  | head :: tail => envCons head (encodeEnvironmentPatterns tail)

noncomputable def environmentListPattern {depth : Nat}
    (environment : List (Term depth)) : Pattern :=
  encodeEnvironmentPatterns (environment.map targetTermPattern)

noncomputable def shiftedEnvironmentListPattern {depth : Nat}
    (environment : List (Term depth)) : Pattern :=
  encodeEnvironmentPatterns (environment.map shiftedTargetTermPattern)

noncomputable def environmentListDerivation {depth : Nat} :
    (environment : List (Term depth)) ->
    Derivation (envShiftRequest (environmentListPattern environment))
      (envShiftResult (environmentListPattern environment)
        (shiftedEnvironmentListPattern environment))
  | [] => by
      simpa [environmentListPattern, shiftedEnvironmentListPattern,
        encodeEnvironmentPatterns] using Derivation.shiftEnvNil
  | head :: tail => by
      simpa [environmentListPattern, shiftedEnvironmentListPattern,
        encodeEnvironmentPatterns] using
        Derivation.shiftEnvCons (termDerivation head)
          (environmentListDerivation tail)

noncomputable def environmentPattern {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) : Pattern :=
  environmentListPattern (List.ofFn environment)

noncomputable def shiftedEnvironmentPattern {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) : Pattern :=
  shiftedEnvironmentListPattern (List.ofFn environment)

noncomputable def environmentDerivation {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) :
    Derivation (envShiftRequest (environmentPattern environment))
      (envShiftResult (environmentPattern environment)
        (shiftedEnvironmentPattern environment)) :=
  environmentListDerivation (List.ofFn environment)

theorem rewriteAt_environmentShift_exact {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) :
    rewriteAt (engineBasePremises RelationEnv.empty) language
        (environmentDerivation environment).height
        (envShiftRequest (environmentPattern environment)) =
      [envShiftResult (environmentPattern environment)
        (shiftedEnvironmentPattern environment)] :=
  (environmentDerivation environment).rewriteAt_exact
    (environmentDerivation environment).height (le_refl _)

theorem shiftedEnvironmentPattern_semantic_exact
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) :
    shiftedEnvironmentPattern environment =
      environmentPattern
        (fun index => LO.FirstOrder.Rew.bShift (environment index)) := by
  unfold shiftedEnvironmentPattern environmentPattern
    shiftedEnvironmentListPattern environmentListPattern
  congr 1
  simp [List.map_ofFn, Function.comp_def, shiftedTargetTermPattern_exact,
    targetTermPattern_exact]

/-! ## The canonical in-scope universal-variable vector -/

def universalVariables (depth : Nat) : List (Term depth) :=
  List.ofFn fun index => (.bvar index : Term depth)

noncomputable def variablesPattern (depth : Nat) : Pattern :=
  targetTermsPattern (universalVariables depth)

theorem shifted_universalVariables_exact (depth : Nat) :
    shiftedTargetTermsPattern (universalVariables depth) =
      targetTermsPattern
        (List.ofFn fun index : Fin depth =>
          (.bvar index.succ : Term (depth + 1))) := by
  simp [shiftedTargetTermsPattern, targetTermsPattern, universalVariables,
    List.map_ofFn, Function.comp_def]

noncomputable def variablesDerivation : (depth : Nat) ->
    Derivation
      (variablesRequest (TptpResolvedFofLanguageDef.encodeNatIndex depth))
      (variablesResult (TptpResolvedFofLanguageDef.encodeNatIndex depth)
        (variablesPattern depth))
  | 0 => by
      simpa [variablesPattern, universalVariables, List.ofFn_zero,
        targetTermsPattern, encodePatternList] using Derivation.variablesZero
  | depth + 1 => by
      have shift := termsDerivation (universalVariables depth)
      rw [shifted_universalVariables_exact] at shift
      simpa [variablesPattern, universalVariables, List.ofFn_succ,
        targetTermsPattern, shiftedTargetTermsPattern, encodePatternList,
        shiftedTargetTermPattern] using
        Derivation.variablesSucc (variablesDerivation depth)
          shift

theorem targetTermsPattern_exact {depth : Nat} (terms : List (Term depth)) :
    targetTermsPattern terms = TptpFofSkolemLanguageDef.encodeTerms terms := by
  unfold targetTermsPattern TptpFofSkolemLanguageDef.encodeTerms
  rw [encodePatternList_exact]
  congr 1
  apply List.map_congr_left
  intro term membership
  exact targetTermPattern_exact term

theorem variablesPattern_generatedApplication_exact (depth id : Nat) :
    variablesPattern depth =
      match TptpFofSkolemizationSemantics.generatedApplication depth id with
      | .func (.generated _) arguments =>
          TptpFofSkolemLanguageDef.encodeTerms (List.ofFn arguments)
      | _ => targetTermsNil := by
  simp [variablesPattern, universalVariables,
    TptpFofSkolemizationSemantics.generatedApplication,
    targetTermsPattern_exact]

theorem rewriteAt_variables_exact (depth : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language
        (variablesDerivation depth).height
        (variablesRequest
          (TptpResolvedFofLanguageDef.encodeNatIndex depth)) =
      [variablesResult
        (TptpResolvedFofLanguageDef.encodeNatIndex depth)
        (variablesPattern depth)] :=
  (variablesDerivation depth).rewriteAt_exact
    (variablesDerivation depth).height (le_refl _)

/-! ## Environment lookup -/

noncomputable def lookupListDerivation {targetDepth : Nat} :
    (environment : List (Term targetDepth)) ->
    (index : Fin environment.length) ->
    Derivation
      (lookupRequest (environmentListPattern environment)
        (TptpResolvedFofLanguageDef.encodeNatIndex index.val))
      (lookupResult (environmentListPattern environment)
        (TptpResolvedFofLanguageDef.encodeNatIndex index.val)
        (targetTermPattern (environment.get index)))
  | [], index => nomatch index
  | head :: tail, index => by
      refine Fin.cases ?_ (fun prior => ?_) index
      · simpa [environmentListPattern, encodeEnvironmentPatterns] using
          Derivation.lookupZero (targetTermPattern head)
            (environmentListPattern tail)
      · simpa [environmentListPattern, encodeEnvironmentPatterns] using
          Derivation.lookupSucc (lookupListDerivation tail prior)

noncomputable def lookupEnvironmentDerivation
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (index : Fin sourceDepth) :
    Derivation
      (lookupRequest (environmentPattern environment)
        (TptpResolvedFofLanguageDef.encodeNatIndex index.val))
      (lookupResult (environmentPattern environment)
        (TptpResolvedFofLanguageDef.encodeNatIndex index.val)
        (targetTermPattern (environment index))) := by
  have derivation := lookupListDerivation (List.ofFn environment)
    (Fin.cast (by simp) index)
  simpa [environmentPattern, List.get_ofFn] using derivation

theorem rewriteAt_lookup_exact {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (index : Fin sourceDepth) :
    rewriteAt (engineBasePremises RelationEnv.empty) language
        (lookupEnvironmentDerivation environment index).height
        (lookupRequest (environmentPattern environment)
          (TptpResolvedFofLanguageDef.encodeNatIndex index.val)) =
      [lookupResult (environmentPattern environment)
        (TptpResolvedFofLanguageDef.encodeNatIndex index.val)
        (targetTermPattern (environment index))] :=
  (lookupEnvironmentDerivation environment index).rewriteAt_exact
    (lookupEnvironmentDerivation environment index).height (le_refl _)

/-! ## Source-term translation -/

def encodeSourcePatternList : List Pattern -> Pattern
  | [] => sourceTermsNil
  | head :: tail => sourceTermsCons head (encodeSourcePatternList tail)

noncomputable def sourceTermPattern {depth : Nat}
    (term : TptpFofSkolemizationSemantics.Source.Term depth) : Pattern :=
  LO.FirstOrder.Semiterm.rec (motive := fun _ => Pattern)
    (fun index => sourceTermVariable
      (TptpResolvedFofLanguageDef.encodeNatIndex index.val))
    (fun impossible => nomatch impossible)
    (fun {arity}
      (function : TptpFofSkolemizationSemantics.Source.FunctionSymbol arity)
      _ encodedArguments =>
      sourceTermFunction
        (TptpFofSymbolLanguageDef.encodeFunctionHead ⟨function.kind, function.name⟩)
        (encodeSourcePatternList (List.ofFn encodedArguments)))
    term

noncomputable def translatedTermPattern
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (term : TptpFofSkolemizationSemantics.Source.Term sourceDepth) : Pattern :=
  LO.FirstOrder.Semiterm.rec (motive := fun _ => Pattern)
    (fun index => targetTermPattern (environment index))
    (fun impossible => nomatch impossible)
    (fun {arity}
      (function : TptpFofSkolemizationSemantics.Source.FunctionSymbol arity)
      _ translatedArguments =>
      targetTermOriginal
        (TptpFofSymbolLanguageDef.encodeFunctionHead ⟨function.kind, function.name⟩)
        (encodePatternList (List.ofFn translatedArguments)))
    term

noncomputable def sourceTermsPattern {depth : Nat}
    (terms : List (TptpFofSkolemizationSemantics.Source.Term depth)) :
    Pattern := encodeSourcePatternList (terms.map sourceTermPattern)

noncomputable def translatedTermsPattern
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (terms : List (TptpFofSkolemizationSemantics.Source.Term sourceDepth)) :
    Pattern := encodePatternList (terms.map (translatedTermPattern environment))

noncomputable def vectorTranslationDerivation
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) :
    {arity : Nat} ->
    (arguments : Fin arity ->
      TptpFofSkolemizationSemantics.Source.Term sourceDepth) ->
    ((index : Fin arity) ->
      Derivation
        (translateTermRequest (environmentPattern environment)
          (sourceTermPattern (arguments index)))
        (translateTermResult (environmentPattern environment)
          (sourceTermPattern (arguments index))
          (translatedTermPattern environment (arguments index)))) ->
    Derivation
      (translateTermsRequest (environmentPattern environment)
        (encodeSourcePatternList
          (List.ofFn fun index => sourceTermPattern (arguments index))))
      (translateTermsResult (environmentPattern environment)
        (encodeSourcePatternList
          (List.ofFn fun index => sourceTermPattern (arguments index)))
        (encodePatternList
          (List.ofFn fun index =>
            translatedTermPattern environment (arguments index))))
  | 0, _, _ => by
      simpa [List.ofFn_zero, encodeSourcePatternList, encodePatternList] using
        Derivation.translateTermsNil (environmentPattern environment)
  | arity + 1, arguments, children => by
      simpa [List.ofFn_succ, encodeSourcePatternList, encodePatternList] using
        Derivation.translateTermsCons (children 0)
          (vectorTranslationDerivation environment
            (fun index => arguments index.succ)
            (fun index => children index.succ))

noncomputable def translationDerivation
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (term : TptpFofSkolemizationSemantics.Source.Term sourceDepth) :
    Derivation
      (translateTermRequest (environmentPattern environment)
        (sourceTermPattern term))
      (translateTermResult (environmentPattern environment)
        (sourceTermPattern term) (translatedTermPattern environment term)) :=
  LO.FirstOrder.Semiterm.rec
    (motive := fun term =>
      Derivation
        (translateTermRequest (environmentPattern environment)
          (sourceTermPattern term))
        (translateTermResult (environmentPattern environment)
          (sourceTermPattern term) (translatedTermPattern environment term)))
    (fun index => by
      simpa [sourceTermPattern, translatedTermPattern] using
        Derivation.translateVariable
          (lookupEnvironmentDerivation environment index))
    (fun impossible => nomatch impossible)
    (fun function arguments children => by
      simpa [sourceTermPattern, translatedTermPattern] using
        Derivation.translateFunction
          (vectorTranslationDerivation environment arguments children))
    term

noncomputable def termsTranslationDerivation
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) :
    (terms : List (TptpFofSkolemizationSemantics.Source.Term sourceDepth)) ->
    Derivation
      (translateTermsRequest (environmentPattern environment)
        (sourceTermsPattern terms))
      (translateTermsResult (environmentPattern environment)
        (sourceTermsPattern terms) (translatedTermsPattern environment terms))
  | [] => by
      simpa [sourceTermsPattern, translatedTermsPattern,
        encodeSourcePatternList, encodePatternList] using
        Derivation.translateTermsNil (environmentPattern environment)
  | head :: tail => by
      simpa [sourceTermsPattern, translatedTermsPattern,
        encodeSourcePatternList, encodePatternList] using
        Derivation.translateTermsCons (translationDerivation environment head)
          (termsTranslationDerivation environment tail)

theorem encodeSourcePatternList_exact (patterns : List Pattern) :
    encodeSourcePatternList patterns =
      TptpResolvedFofLanguageDef.encodeTermPatterns patterns := by
  induction patterns with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [encodeSourcePatternList,
        TptpResolvedFofLanguageDef.encodeTermPatterns, inductionHypothesis]

theorem sourceTermPattern_exact {depth : Nat}
    (term : TptpFofSkolemizationSemantics.Source.Term depth) :
    sourceTermPattern term = TptpResolvedFofLanguageDef.encodeTerm term := by
  induction term with
  | bvar index => rfl
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      simp only [sourceTermPattern, TptpResolvedFofLanguageDef.encodeTerm]
      rw [encodeSourcePatternList_exact]
      congr 2
      exact List.ofFn_inj.mpr (funext inductionHypothesis)

theorem translatedTermPattern_exact {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (term : TptpFofSkolemizationSemantics.Source.Term sourceDepth) :
    translatedTermPattern environment term =
      TptpFofSkolemLanguageDef.encodeTerm
        (TptpFofSkolemizationSemantics.translateTerm environment term) := by
  induction term with
  | bvar index => exact targetTermPattern_exact (environment index)
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      simp only [translatedTermPattern,
        TptpFofSkolemizationSemantics.translateTerm,
        TptpFofSkolemLanguageDef.encodeTerm]
      rw [encodePatternList_exact]
      congr 2
      exact List.ofFn_inj.mpr (funext inductionHypothesis)

theorem rewriteAt_translateTerm_exact {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (term : TptpFofSkolemizationSemantics.Source.Term sourceDepth) :
    rewriteAt (engineBasePremises RelationEnv.empty) language
        (translationDerivation environment term).height
        (translateTermRequest (environmentPattern environment)
          (TptpResolvedFofLanguageDef.encodeTerm term)) =
      [translateTermResult (environmentPattern environment)
        (TptpResolvedFofLanguageDef.encodeTerm term)
        (TptpFofSkolemLanguageDef.encodeTerm
          (TptpFofSkolemizationSemantics.translateTerm environment term))] := by
  simpa [sourceTermPattern_exact, translatedTermPattern_exact] using
    (translationDerivation environment term).rewriteAt_exact
      (translationDerivation environment term).height (le_refl _)

theorem rewriteAt_translateTerm_no_invention
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (term : TptpFofSkolemizationSemantics.Source.Term sourceDepth)
    (invented : Pattern)
    (membership : invented ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language
        (translationDerivation environment term).height
        (translateTermRequest (environmentPattern environment)
          (TptpResolvedFofLanguageDef.encodeTerm term))) :
    invented = translateTermResult (environmentPattern environment)
      (TptpResolvedFofLanguageDef.encodeTerm term)
      (TptpFofSkolemLanguageDef.encodeTerm
        (TptpFofSkolemizationSemantics.translateTerm environment term)) := by
  rw [rewriteAt_translateTerm_exact] at membership
  simpa using membership

end Semantic

#print axioms shift_variable_exact
#print axioms translate_terms_cons_exact
#print axioms Derivation.rewriteAt_exact
#print axioms Derivation.no_invention
#print axioms Semantic.rewriteAt_bShift_exact
#print axioms Semantic.rewriteAt_bShift_no_invention
#print axioms Semantic.rewriteAt_environmentShift_exact
#print axioms Semantic.shiftedEnvironmentPattern_semantic_exact
#print axioms Semantic.rewriteAt_variables_exact
#print axioms Semantic.rewriteAt_lookup_exact
#print axioms Semantic.rewriteAt_translateTerm_exact
#print axioms Semantic.rewriteAt_translateTerm_no_invention

end Mettapedia.GSLT.LanguageDef.TptpFofSkolemTermAgreement
