import Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedFormulaExecution

/-!
# Exact agreement for official TPTP FOF elaboration

This module connects the independent official-AST decoder to the authored
GSLT transformation.  The first layer isolates exact row behavior for terms
and ordered argument lists.  These lemmas are the induction steps for the
generic decoder/rewrite agreement theorem; each conclusion is an exact
singleton, preserving order and multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedFormulaLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedLanguageDef

attribute [local simp]
  TptpFofSymbolLanguageDef.a
  TptpFofSymbolLanguageDef.encodeFunctionHead
  TptpFofSymbolLanguageDef.encodePredicateHead

private def plainFunction (lexeme arguments : Pattern) : Pattern :=
  targetFunction
    (targetFunctionHead "tptp-fof-symbol:function-plain" lexeme) arguments

private def definedFunction (lexeme arguments : Pattern) : Pattern :=
  targetFunction
    (targetFunctionHead "tptp-fof-symbol:function-defined" lexeme) arguments

private def systemFunction (lexeme arguments : Pattern) : Pattern :=
  targetFunction
    (targetFunctionHead "tptp-fof-symbol:function-system" lexeme) arguments

private def integerFunction (lexeme : Pattern) : Pattern :=
  targetFunction
    (targetFunctionHead "tptp-fof-symbol:function-integer" lexeme)
    targetTermsNil

private def rationalFunction (lexeme : Pattern) : Pattern :=
  targetFunction
    (targetFunctionHead "tptp-fof-symbol:function-rational" lexeme)
    targetTermsNil

private def realFunction (lexeme : Pattern) : Pattern :=
  targetFunction
    (targetFunctionHead "tptp-fof-symbol:function-real" lexeme)
    targetTermsNil

private def distinctObjectFunction (lexeme : Pattern) : Pattern :=
  targetFunction
    (targetFunctionHead "tptp-fof-symbol:function-distinct-object" lexeme)
    targetTermsNil

private def plainPredicate (lexeme arguments : Pattern) : Pattern :=
  targetPredicate
    (targetPredicateHead "tptp-fof-symbol:predicate-plain" lexeme) arguments

private def definedPredicate (lexeme arguments : Pattern) : Pattern :=
  targetPredicate
    (targetPredicateHead "tptp-fof-symbol:predicate-defined" lexeme) arguments

private def systemPredicate (lexeme arguments : Pattern) : Pattern :=
  targetPredicate
    (targetPredicateHead "tptp-fof-symbol:predicate-system" lexeme) arguments

private theorem termRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:term") =
      termRewrites.take 15 := by
  rfl

private theorem argumentsRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:arguments") =
      termRewrites.drop 15 := by
  rfl

/-- A source request has an exact stable result once contextual fuel reaches a
finite structural threshold.  Stability is required because sibling
congruence premises share one fuel budget. -/
def EventuallyExact (source result : Pattern) : Prop :=
  ∃ requiredFuel, ∀ fuel, requiredFuel ≤ fuel →
    rewriteAt (engineBasePremises RelationEnv.empty) language fuel source =
      [result]

/-- Bounded contextual derivations are monotone in their depth budget.  This
is the generic bridge from stable execution at a sufficiently large fuel to
no-invention at every smaller fuel. -/
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

/-- Any reduct visible at one contextual fuel remains visible at every larger
fuel.  Multiplicity is deliberately not asserted here; exact singleton output
comes from the authored transformation agreement. -/
private theorem mem_rewriteAt_mono_fuel
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {fuel largerFuel : Nat} {source target : Pattern}
    (member : target ∈ rewriteAt base lang fuel source)
    (enough : fuel ≤ largerFuel) :
    target ∈ rewriteAt base lang largerFuel source := by
  apply mem_rewriteAt_iff_stepAt.mpr
  exact stepAt_mono_fuel (mem_rewriteAt_iff_stepAt.mp member) enough

/-- Stable exactness at sufficiently large fuel excludes every alternative
target at every fuel, including fuels below the successful threshold. -/
theorem EventuallyExact.no_invention {source result target : Pattern}
    (exact : EventuallyExact source result) (fuel : Nat)
    (member : target ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel source) :
    target = result := by
  rcases exact with ⟨requiredFuel, exact⟩
  have lifted := mem_rewriteAt_mono_fuel member (Nat.le_max_left fuel requiredFuel)
  rw [exact (max fuel requiredFuel) (Nat.le_max_right fuel requiredFuel)] at lifted
  simpa using lifted

private def officialVariableSource (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-2" [
    a "tptp92-ast:variable:alt-1" [
      sourceToken "tptp92-ast:token:upper-word" lexeme]]

private def officialPlainNullarySource (atomicAlternative tokenLabel : String)
    (lexeme : Pattern) : Pattern :=
  sourcePlainTerm <|
    a "tptp92-ast:fof-plain-term:alt-1" [
      a "tptp92-ast:constant:alt-1" [
        a "tptp92-ast:functor:alt-1" [
          sourceAtomicWord atomicAlternative tokenLabel lexeme]]]

theorem variable_rewriteAt_exact (fuel : Nat) (lexeme : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (translateTerm (officialVariableSource lexeme)) =
      [targetVariable lexeme] := by
  change rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
    (.apply "tptp-fof-elab:term" [officialVariableSource lexeme]) =
      [targetVariable lexeme]
  rw [rewriteAt_eq_root_filter, termRootRules]
  simp [termRewrites, variableRule, plainNullaryRule, plainAppliedRule,
    numberRule, distinctRule, definedNullaryRule, definedAppliedRule,
    systemNullaryRule, systemAppliedRule, officialVariableSource,
    translateTerm, translateArguments, targetVariable, targetName,
    targetFunction, targetTermsNil, sourcePlainTerm,
    sourceDefinedTerm, sourceSystemTerm, sourceDefinedFunctor,
    sourceSystemFunctor, sourceToken, sourceAtomicWord, mkRule, congruence,
    a, v, applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
    premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings]

theorem plain_lower_nullary_rewriteAt_exact (fuel : Nat)
    (lexeme : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (translateTerm <| officialPlainNullarySource
          "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word"
          lexeme) =
      [plainFunction lexeme targetTermsNil] := by
  change rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
    (.apply "tptp-fof-elab:term" [officialPlainNullarySource
      "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word"
      lexeme]) = [plainFunction lexeme targetTermsNil]
  rw [rewriteAt_eq_root_filter, termRootRules]
  simp [termRewrites, variableRule, plainNullaryRule, plainAppliedRule,
    numberRule, distinctRule, definedNullaryRule, definedAppliedRule,
    systemNullaryRule, systemAppliedRule, officialPlainNullarySource,
    translateTerm, translateArguments, targetVariable, targetName,
    targetFunctionHead, targetFunction, plainFunction, targetTermsNil,
    sourcePlainTerm,
    sourceDefinedTerm, sourceSystemTerm, sourceDefinedFunctor,
    sourceSystemFunctor, sourceToken, sourceAtomicWord, mkRule, congruence,
    a, v, applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
    premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings]

theorem arguments_one_rewriteAt_exact (fuel : Nat)
    (term termResult : Pattern)
    (termStep :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
          (translateTerm term) = [termResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (translateArguments <|
          a "tptp92-ast:fof-arguments:alt-1" [term]) =
      [targetTermsCons termResult targetTermsNil] := by
  change rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
    (.apply "tptp-fof-elab:arguments" [
      a "tptp92-ast:fof-arguments:alt-1" [term]]) =
      [targetTermsCons termResult targetTermsNil]
  simp only [translateTerm, a] at termStep
  rw [rewriteAt_eq_root_filter, argumentsRootRules]
  simp [termRewrites, argumentsOneRule, argumentsMoreRule, translateTerm,
    translateArguments, targetTermsNil, targetTermsCons, mkRule, congruence,
    a, v, applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
    premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, termStep]

theorem arguments_more_rewriteAt_exact (fuel : Nat)
    (term arguments termResult argumentsResult : Pattern)
    (termStep :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
          (translateTerm term) = [termResult])
    (argumentsStep :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
          (translateArguments arguments) = [argumentsResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (translateArguments <|
          a "tptp92-ast:fof-arguments:alt-2" [term, arguments]) =
      [targetTermsCons termResult argumentsResult] := by
  change rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
    (.apply "tptp-fof-elab:arguments" [
      a "tptp92-ast:fof-arguments:alt-2" [term, arguments]]) =
      [targetTermsCons termResult argumentsResult]
  simp only [translateTerm, translateArguments, a] at termStep argumentsStep
  rw [rewriteAt_eq_root_filter, argumentsRootRules]
  simp [termRewrites, argumentsOneRule, argumentsMoreRule, translateTerm,
    translateArguments, targetTermsNil, targetTermsCons, mkRule, congruence,
    a, v, applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
    premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, termStep, argumentsStep]

theorem variable_eventuallyExact (lexeme : Pattern) :
    EventuallyExact (translateTerm (officialVariableSource lexeme))
      (targetVariable lexeme) := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ fuel =>
      simpa [Nat.succ_eq_add_one] using variable_rewriteAt_exact fuel lexeme

theorem plain_lower_nullary_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (translateTerm <| officialPlainNullarySource
        "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word"
        lexeme)
      (plainFunction lexeme targetTermsNil) := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ fuel =>
      simpa [Nat.succ_eq_add_one] using
        plain_lower_nullary_rewriteAt_exact fuel lexeme

theorem arguments_one_eventuallyExact
    (term termResult : Pattern)
    (termExact : EventuallyExact (translateTerm term) termResult) :
    EventuallyExact
      (translateArguments <| a "tptp92-ast:fof-arguments:alt-1" [term])
      (targetTermsCons termResult targetTermsNil) := by
  rcases termExact with ⟨requiredFuel, termExact⟩
  refine ⟨requiredFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ fuel =>
      apply arguments_one_rewriteAt_exact
      apply termExact
      omega

theorem arguments_more_eventuallyExact
    (term arguments termResult argumentsResult : Pattern)
    (termExact : EventuallyExact (translateTerm term) termResult)
    (argumentsExact :
      EventuallyExact (translateArguments arguments) argumentsResult) :
    EventuallyExact
      (translateArguments <|
        a "tptp92-ast:fof-arguments:alt-2" [term, arguments])
      (targetTermsCons termResult argumentsResult) := by
  rcases termExact with ⟨termFuel, termExact⟩
  rcases argumentsExact with ⟨argumentsFuel, argumentsExact⟩
  refine ⟨max termFuel argumentsFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ fuel =>
      apply arguments_more_rewriteAt_exact
      · apply termExact
        omega
      · apply argumentsExact
        omega

private theorem encodeTerms_nil :
    TptpNamedFofLanguageDef.encodeTerms [] = targetTermsNil := by
  rfl

private theorem encodeTerms_cons
    (term : TptpFofBinderResolution.NamedTerm)
    (terms : List TptpFofBinderResolution.NamedTerm) :
    TptpNamedFofLanguageDef.encodeTerms (term :: terms) =
      targetTermsCons (TptpNamedFofLanguageDef.encodeTerm term)
        (TptpNamedFofLanguageDef.encodeTerms terms) := by
  rfl

private theorem encodeTerm_variable (name : String) :
    TptpNamedFofLanguageDef.encodeTerm (.variable name) =
      targetVariable (.apply name []) := by
  rfl

private theorem encodeTerm_function
    (head : TptpFofSymbolIdentity.FunctionHead)
    (arguments : List TptpFofBinderResolution.NamedTerm) :
    TptpNamedFofLanguageDef.encodeTerm (.function head arguments) =
      targetFunction (TptpFofSymbolLanguageDef.encodeFunctionHead head)
        (TptpNamedFofLanguageDef.encodeTerms arguments) := by
  rfl

private theorem encodeFormula_predicate
    (head : TptpFofSymbolIdentity.PredicateHead)
    (arguments : List TptpFofBinderResolution.NamedTerm) :
    TptpNamedFofLanguageDef.encodeFormula (.predicate head arguments) =
      targetPredicate (TptpFofSymbolLanguageDef.encodePredicateHead head)
        (TptpNamedFofLanguageDef.encodeTerms arguments) := by
  rfl

private theorem encodeFormula_verum :
    TptpNamedFofLanguageDef.encodeFormula .verum =
      targetNullary "verum" := by
  rfl

private theorem encodeFormula_falsum :
    TptpNamedFofLanguageDef.encodeFormula .falsum =
      targetNullary "falsum" := by
  rfl

private theorem encodeFormula_equal
    (left right : TptpFofBinderResolution.NamedTerm) :
    TptpNamedFofLanguageDef.encodeFormula (.equal left right) =
      targetEqual (TptpNamedFofLanguageDef.encodeTerm left)
        (TptpNamedFofLanguageDef.encodeTerm right) := by
  rfl

private theorem encodeFormula_not
    (body : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.not body) =
      targetUnary "not" (TptpNamedFofLanguageDef.encodeFormula body) := by
  rfl

private theorem encodeFormula_iff (left right : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.iff left right) =
      targetBinary "iff" (TptpNamedFofLanguageDef.encodeFormula left)
        (TptpNamedFofLanguageDef.encodeFormula right) := by rfl

private theorem encodeFormula_implies (left right : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.implies left right) =
      targetBinary "implies" (TptpNamedFofLanguageDef.encodeFormula left)
        (TptpNamedFofLanguageDef.encodeFormula right) := by rfl

private theorem encodeFormula_reverseImplies
    (left right : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.reverseImplies left right) =
      targetBinary "reverse-implies"
        (TptpNamedFofLanguageDef.encodeFormula left)
        (TptpNamedFofLanguageDef.encodeFormula right) := by rfl

private theorem encodeFormula_xor (left right : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.xor left right) =
      targetBinary "xor" (TptpNamedFofLanguageDef.encodeFormula left)
        (TptpNamedFofLanguageDef.encodeFormula right) := by rfl

private theorem encodeFormula_nor (left right : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.nor left right) =
      targetBinary "nor" (TptpNamedFofLanguageDef.encodeFormula left)
        (TptpNamedFofLanguageDef.encodeFormula right) := by rfl

private theorem encodeFormula_nand (left right : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.nand left right) =
      targetBinary "nand" (TptpNamedFofLanguageDef.encodeFormula left)
        (TptpNamedFofLanguageDef.encodeFormula right) := by rfl

private theorem encodeFormula_or (left right : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.or left right) =
      targetBinary "or" (TptpNamedFofLanguageDef.encodeFormula left)
        (TptpNamedFofLanguageDef.encodeFormula right) := by rfl

private theorem encodeFormula_and (left right : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.and left right) =
      targetBinary "and" (TptpNamedFofLanguageDef.encodeFormula left)
        (TptpNamedFofLanguageDef.encodeFormula right) := by rfl

private theorem encodeFormula_all (binder : String)
    (body : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.all binder body) =
      targetBinder "all" (.apply binder [])
        (TptpNamedFofLanguageDef.encodeFormula body) := by rfl

private theorem encodeFormula_ex (binder : String)
    (body : TptpFofBinderResolution.NamedFormula) :
    TptpNamedFofLanguageDef.encodeFormula (.ex binder body) =
      targetBinder "ex" (.apply binder [])
        (TptpNamedFofLanguageDef.encodeFormula body) := by rfl

private def TermAgreement (source : Pattern) : Prop :=
  ∀ result, TptpOfficialFofElaboration.decodeTerm? source = some result →
    EventuallyExact (translateTerm source)
      (TptpNamedFofLanguageDef.encodeTerm result)

private def FunctionTermAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeFunctionTerm? source = some result →
      EventuallyExact
        (translateTerm <| .apply "tptp92-ast:fof-term:alt-1" [source])
        (TptpNamedFofLanguageDef.encodeTerm result)

private def SystemTermAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeSystemTerm? source = some result →
      EventuallyExact (translateTerm (sourceSystemTerm source))
        (TptpNamedFofLanguageDef.encodeTerm result)

private def ArgumentsAgreement (source : Pattern) : Prop :=
  ∀ results,
    TptpOfficialFofElaboration.decodeArguments? source = some results →
      EventuallyExact (translateArguments source)
        (TptpNamedFofLanguageDef.encodeTerms results)

private def DefinedTermAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeDefinedTerm? source = some result →
      EventuallyExact (translateTerm (sourceDefinedTerm source))
        (TptpNamedFofLanguageDef.encodeTerm result)

private def DefinedPlainTermAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeDefinedPlainTerm? source = some result →
      EventuallyExact (translateTerm <| sourceDefinedTerm <|
        .apply "tptp92-ast:fof-defined-term:alt-2" [
          .apply "tptp92-ast:fof-defined-atomic-term:alt-1" [source]])
        (TptpNamedFofLanguageDef.encodeTerm result)

private def PlainTermAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodePlainTerm? source = some result →
      EventuallyExact (translateTerm (sourcePlainTerm source))
        (TptpNamedFofLanguageDef.encodeTerm result)

private theorem eventuallyExact_of_one_step (source result : Pattern)
    (step : ∀ fuel,
      rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        source = [result]) :
    EventuallyExact source result := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using step predecessor

private theorem eventuallyExact_of_one_premise
    (premiseSource premiseResult source result : Pattern)
    (premiseExact : EventuallyExact premiseSource premiseResult)
    (step : ∀ fuel,
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
          premiseSource = [premiseResult] →
        rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
          source = [result]) :
    EventuallyExact source result := by
  rcases premiseExact with ⟨requiredFuel, premiseExact⟩
  refine ⟨requiredFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using
        step predecessor (premiseExact predecessor (by omega))

local macro "close_term_leaf" : tactic =>
  `(tactic|
    exact eventuallyExact_of_one_step _ _ (by
      intro fuel
      simp only [translateTerm, a]
      rw [rewriteAt_eq_root_filter, termRootRules]
      simp [termRewrites, variableRule, plainNullaryRule,
        plainAppliedRule, numberRule, distinctRule, definedNullaryRule,
        definedAppliedRule, systemNullaryRule, systemAppliedRule,
        translateTerm, translateArguments, targetVariable, targetName,
        targetFunctionHead, targetFunction, plainFunction, definedFunction,
        systemFunction, integerFunction, rationalFunction, realFunction,
        distinctObjectFunction, targetTermsNil, targetTermsCons, sourcePlainTerm,
        sourceDefinedTerm, sourceSystemTerm, sourceDefinedFunctor,
        sourceSystemFunctor, sourceToken, sourceAtomicWord,
        officialPlainNullarySource, mkRule,
        congruence, a, v, applyRuleUsing,
        matchPatternForRule_eq_syntactic, premisesUsing,
        premiseStepUsing, matchPattern, matchArgs, mergeBindings,
        applyBindingsForRule, applyBindings]))

local macro "close_applied_term" argumentsExact:term : tactic =>
  `(tactic|
    exact eventuallyExact_of_one_premise _ _ _ _ ($argumentsExact) (by
      intro fuel argumentsStep
      simp only [translateTerm, a]
      simp only [translateArguments, a] at argumentsStep
      rw [rewriteAt_eq_root_filter, termRootRules]
      simp [termRewrites, variableRule, plainNullaryRule,
        plainAppliedRule, numberRule, distinctRule, definedNullaryRule,
        definedAppliedRule, systemNullaryRule, systemAppliedRule,
        translateTerm, translateArguments, targetVariable, targetName,
        targetFunctionHead, targetFunction, plainFunction, definedFunction,
        systemFunction, integerFunction, rationalFunction, realFunction,
        distinctObjectFunction, targetTermsNil, targetTermsCons, sourcePlainTerm,
        sourceDefinedTerm, sourceSystemTerm, sourceDefinedFunctor,
        sourceSystemFunctor, sourceToken, sourceAtomicWord,
        officialPlainNullarySource, mkRule,
        congruence, a, v, applyRuleUsing,
        matchPatternForRule_eq_syntactic, premisesUsing,
        premiseStepUsing, matchPattern, matchArgs, mergeBindings,
        applyBindingsForRule, applyBindings, argumentsStep]))

private theorem plain_quoted_nullary_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (translateTerm <| officialPlainNullarySource
        "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted"
        lexeme)
      (plainFunction lexeme targetTermsNil) := by
  close_term_leaf

private theorem plain_backquoted_nullary_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (translateTerm <| officialPlainNullarySource
        "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted"
        lexeme)
      (plainFunction lexeme targetTermsNil) := by
  close_term_leaf

private theorem plain_lower_applied_eventuallyExact
    (lexeme arguments argumentsResult : Pattern)
    (argumentsExact :
      EventuallyExact (translateArguments arguments) argumentsResult) :
    EventuallyExact
      (translateTerm <| sourcePlainTerm <|
        .apply "tptp92-ast:fof-plain-term:alt-2" [
          .apply "tptp92-ast:functor:alt-1" [
            sourceAtomicWord "tptp92-ast:atomic-word:alt-1"
              "tptp92-ast:token:lower-word" lexeme], arguments])
      (plainFunction lexeme argumentsResult) := by
  close_applied_term argumentsExact

private theorem plain_quoted_applied_eventuallyExact
    (lexeme arguments argumentsResult : Pattern)
    (argumentsExact :
      EventuallyExact (translateArguments arguments) argumentsResult) :
    EventuallyExact
      (translateTerm <| sourcePlainTerm <|
        .apply "tptp92-ast:fof-plain-term:alt-2" [
          .apply "tptp92-ast:functor:alt-1" [
            sourceAtomicWord "tptp92-ast:atomic-word:alt-2"
              "tptp92-ast:token:single-quoted" lexeme], arguments])
      (plainFunction lexeme argumentsResult) := by
  close_applied_term argumentsExact

private theorem plain_backquoted_applied_eventuallyExact
    (lexeme arguments argumentsResult : Pattern)
    (argumentsExact :
      EventuallyExact (translateArguments arguments) argumentsResult) :
    EventuallyExact
      (translateTerm <| sourcePlainTerm <|
        .apply "tptp92-ast:fof-plain-term:alt-2" [
          .apply "tptp92-ast:functor:alt-1" [
            sourceAtomicWord "tptp92-ast:atomic-word:alt-3"
              "tptp92-ast:token:back-quoted" lexeme], arguments])
      (plainFunction lexeme argumentsResult) := by
  close_applied_term argumentsExact

private theorem number_integer_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (translateTerm <| sourceDefinedTerm <|
        .apply "tptp92-ast:fof-defined-term:alt-1" [
          .apply "tptp92-ast:defined-term:alt-1" [
            .apply "tptp92-ast:number:alt-1" [
              sourceToken "tptp92-ast:token:integer" lexeme]]])
      (integerFunction lexeme) := by
  close_term_leaf

private theorem number_rational_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (translateTerm <| sourceDefinedTerm <|
        .apply "tptp92-ast:fof-defined-term:alt-1" [
          .apply "tptp92-ast:defined-term:alt-1" [
            .apply "tptp92-ast:number:alt-2" [
              sourceToken "tptp92-ast:token:rational" lexeme]]])
      (rationalFunction lexeme) := by
  close_term_leaf

private theorem number_real_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (translateTerm <| sourceDefinedTerm <|
        .apply "tptp92-ast:fof-defined-term:alt-1" [
          .apply "tptp92-ast:defined-term:alt-1" [
            .apply "tptp92-ast:number:alt-3" [
              sourceToken "tptp92-ast:token:real" lexeme]]])
      (realFunction lexeme) := by
  close_term_leaf

private theorem distinct_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (translateTerm <| sourceDefinedTerm <|
        .apply "tptp92-ast:fof-defined-term:alt-1" [
          .apply "tptp92-ast:defined-term:alt-2" [
            sourceToken "tptp92-ast:token:distinct-object" lexeme]])
      (distinctObjectFunction lexeme) := by
  close_term_leaf

private theorem defined_nullary_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (translateTerm <| sourceDefinedTerm <|
        .apply "tptp92-ast:fof-defined-term:alt-2" [
          .apply "tptp92-ast:fof-defined-atomic-term:alt-1" [
            .apply "tptp92-ast:fof-defined-plain-term:alt-1" [
              .apply "tptp92-ast:defined-constant:alt-1" [
                sourceDefinedFunctor lexeme]]]])
      (definedFunction lexeme targetTermsNil) := by
  close_term_leaf

private theorem defined_applied_eventuallyExact
    (lexeme arguments argumentsResult : Pattern)
    (argumentsExact :
      EventuallyExact (translateArguments arguments) argumentsResult) :
    EventuallyExact
      (translateTerm <| sourceDefinedTerm <|
        .apply "tptp92-ast:fof-defined-term:alt-2" [
          .apply "tptp92-ast:fof-defined-atomic-term:alt-1" [
            .apply "tptp92-ast:fof-defined-plain-term:alt-2" [
              sourceDefinedFunctor lexeme, arguments]]])
      (definedFunction lexeme argumentsResult) := by
  close_applied_term argumentsExact

private theorem system_nullary_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (translateTerm <| sourceSystemTerm <|
        .apply "tptp92-ast:fof-system-term:alt-1" [
          .apply "tptp92-ast:system-constant:alt-1" [
            sourceSystemFunctor lexeme]])
      (systemFunction lexeme targetTermsNil) := by
  close_term_leaf

private theorem system_applied_eventuallyExact
    (lexeme arguments argumentsResult : Pattern)
    (argumentsExact :
      EventuallyExact (translateArguments arguments) argumentsResult) :
    EventuallyExact
      (translateTerm <| sourceSystemTerm <|
        .apply "tptp92-ast:fof-system-term:alt-2" [
          sourceSystemFunctor lexeme, arguments])
      (systemFunction lexeme argumentsResult) := by
  close_applied_term argumentsExact

/-- Once term elaboration is known, the independent ordered-argument decoder
and the authored argument-list rules agree for every successful source. -/
theorem decodeArguments_eventuallyExact
    (termSound : ∀ source result,
      TptpOfficialFofElaboration.decodeTerm? source = some result →
        EventuallyExact (translateTerm source)
          (TptpNamedFofLanguageDef.encodeTerm result))
    (source : Pattern) (results : List TptpFofBinderResolution.NamedTerm)
    (decoded :
      TptpOfficialFofElaboration.decodeArguments? source = some results) :
    EventuallyExact (translateArguments source)
      (TptpNamedFofLanguageDef.encodeTerms results) := by
  unfold TptpOfficialFofElaboration.decodeArguments? at decoded
  split at decoded
  · rename_i sourceShape sourceTerm
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨result, resultDecoded, resultEquality⟩
    cases resultEquality
    rw [encodeTerms_cons, encodeTerms_nil]
    simpa [translateArguments, a] using
      arguments_one_eventuallyExact sourceTerm
        (TptpNamedFofLanguageDef.encodeTerm result)
        (termSound sourceTerm result resultDecoded)
  · rename_i sourceShape sourceTerm sourceArguments
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨result, resultDecoded, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨argumentResults, argumentResultsDecoded, resultEquality⟩
    cases resultEquality
    rw [encodeTerms_cons]
    simpa [translateArguments, a] using
      arguments_more_eventuallyExact sourceTerm sourceArguments
        (TptpNamedFofLanguageDef.encodeTerm result)
        (TptpNamedFofLanguageDef.encodeTerms argumentResults)
        (termSound sourceTerm result resultDecoded)
        (decodeArguments_eventuallyExact termSound sourceArguments argumentResults
          argumentResultsDecoded)
  · contradiction
termination_by sizeOf source

private theorem decodeArguments_ne_nil (source : Pattern)
    {results : List TptpFofBinderResolution.NamedTerm}
    (decoded :
      TptpOfficialFofElaboration.decodeArguments? source = some results) :
    results ≠ [] := by
  intro empty
  subst results
  unfold TptpOfficialFofElaboration.decodeArguments? at decoded
  split at decoded
  · rcases Option.bind_eq_some_iff.mp decoded with
      ⟨termResult, _, resultEquality⟩
    simp at resultEquality
  · rcases Option.bind_eq_some_iff.mp decoded with
      ⟨termResult, _, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨argumentResults, _, resultEquality⟩
    simp at resultEquality
  · contradiction

/-- The independent term decoder and the authored 17-row term/argument GSLT
agree for every successful official source.  The proof follows the decoder's
mutual structural induction, so recursive argument evaluation is not assumed
as an external oracle. -/
theorem decodeTerm_eventuallyExact (source : Pattern) : TermAgreement source := by
  apply TptpOfficialFofElaboration.decodeTerm?.induct
    (motive_1 := TermAgreement)
    (motive_2 := FunctionTermAgreement)
    (motive_3 := SystemTermAgreement)
    (motive_4 := ArgumentsAgreement)
    (motive_5 := DefinedTermAgreement)
    (motive_6 := DefinedPlainTermAgreement)
    (motive_7 := PlainTermAgreement)
  case case1 =>
    intro term inductionHypothesis result decoded
    apply inductionHypothesis result
    simpa [TptpOfficialFofElaboration.decodeTerm?] using decoded
  case case2 =>
    intro variablePattern result decoded
    fun_cases TptpOfficialFofElaboration.decodeVariableName? variablePattern
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodeTerm?,
        TptpOfficialFofElaboration.decodeVariableName?] at decoded
      subst result
      rw [encodeTerm_variable]
      exact variable_eventuallyExact (.apply lexeme [])
    · simp_all [TptpOfficialFofElaboration.decodeTerm?,
        TptpOfficialFofElaboration.decodeVariableName?]
  case case3 =>
    intro source notFunction notVariable result decoded
    simp_all [TptpOfficialFofElaboration.decodeTerm?]
  case case4 =>
    intro term inductionHypothesis result decoded
    apply inductionHypothesis result
    simpa [TptpOfficialFofElaboration.decodeFunctionTerm?] using decoded
  case case5 =>
    intro term inductionHypothesis result decoded
    apply inductionHypothesis result
    simpa [TptpOfficialFofElaboration.decodeFunctionTerm?] using decoded
  case case6 =>
    intro term inductionHypothesis result decoded
    apply inductionHypothesis result
    simpa [TptpOfficialFofElaboration.decodeFunctionTerm?] using decoded
  case case7 =>
    intro source notPlain notDefined notSystem result decoded
    simp_all [TptpOfficialFofElaboration.decodeFunctionTerm?]
  case case8 =>
    intro functor result decoded
    fun_cases TptpOfficialFofElaboration.decodeSystemFunctorName? functor
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodeSystemTerm?,
        TptpOfficialFofElaboration.decodeSystemFunctorName?] at decoded
      subst result
      rw [encodeTerm_function, encodeTerms_nil]
      exact system_nullary_eventuallyExact (.apply lexeme [])
    · simp_all [TptpOfficialFofElaboration.decodeSystemTerm?,
        TptpOfficialFofElaboration.decodeSystemFunctorName?]
  case case9 =>
    intro functor arguments argumentsInduction result decoded
    fun_cases TptpOfficialFofElaboration.decodeSystemFunctorName? functor
    · rename_i lexeme
      cases argumentsDecoded :
          TptpOfficialFofElaboration.decodeArguments? arguments with
      | none =>
          simp [TptpOfficialFofElaboration.decodeSystemTerm?,
            TptpOfficialFofElaboration.decodeSystemFunctorName?,
            argumentsDecoded] at decoded
      | some argumentResults =>
          simp [TptpOfficialFofElaboration.decodeSystemTerm?,
            TptpOfficialFofElaboration.decodeSystemFunctorName?,
            argumentsDecoded] at decoded
          subst result
          rw [encodeTerm_function]
          exact system_applied_eventuallyExact (.apply lexeme []) arguments
            (TptpNamedFofLanguageDef.encodeTerms argumentResults)
            (argumentsInduction argumentResults argumentsDecoded)
    · simp_all [TptpOfficialFofElaboration.decodeSystemTerm?,
        TptpOfficialFofElaboration.decodeSystemFunctorName?]
  case case10 =>
    intro source notNullary notApplied result decoded
    simp_all [TptpOfficialFofElaboration.decodeSystemTerm?]
  case case11 =>
    intro term termInduction results decoded
    cases termDecoded : TptpOfficialFofElaboration.decodeTerm? term with
    | none =>
        simp [TptpOfficialFofElaboration.decodeArguments?, termDecoded] at decoded
    | some termResult =>
        simp [TptpOfficialFofElaboration.decodeArguments?, termDecoded] at decoded
        subst results
        rw [encodeTerms_cons, encodeTerms_nil]
        exact arguments_one_eventuallyExact term
          (TptpNamedFofLanguageDef.encodeTerm termResult)
          (termInduction termResult termDecoded)
  case case12 =>
    intro term arguments termInduction argumentsInduction results decoded
    cases termDecoded : TptpOfficialFofElaboration.decodeTerm? term with
    | none =>
        simp [TptpOfficialFofElaboration.decodeArguments?, termDecoded] at decoded
    | some termResult =>
        cases argumentsDecoded :
            TptpOfficialFofElaboration.decodeArguments? arguments with
        | none =>
            simp [TptpOfficialFofElaboration.decodeArguments?, termDecoded,
              argumentsDecoded] at decoded
        | some argumentResults =>
            simp [TptpOfficialFofElaboration.decodeArguments?, termDecoded,
              argumentsDecoded] at decoded
            subst results
            rw [encodeTerms_cons]
            exact arguments_more_eventuallyExact term arguments
              (TptpNamedFofLanguageDef.encodeTerm termResult)
              (TptpNamedFofLanguageDef.encodeTerms argumentResults)
              (termInduction termResult termDecoded)
              (argumentsInduction argumentResults argumentsDecoded)
  case case13 =>
    intro source notOne notMore results decoded
    simp_all [TptpOfficialFofElaboration.decodeArguments?]
  case case14 =>
    intro number result decoded
    fun_cases TptpOfficialFofElaboration.decodeNumberHead? number
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodeDefinedTerm?,
        TptpOfficialFofElaboration.decodeNumberHead?] at decoded
      subst result
      rw [encodeTerm_function, encodeTerms_nil]
      exact number_integer_eventuallyExact (.apply lexeme [])
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodeDefinedTerm?,
        TptpOfficialFofElaboration.decodeNumberHead?] at decoded
      subst result
      rw [encodeTerm_function, encodeTerms_nil]
      exact number_rational_eventuallyExact (.apply lexeme [])
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodeDefinedTerm?,
        TptpOfficialFofElaboration.decodeNumberHead?] at decoded
      subst result
      rw [encodeTerm_function, encodeTerms_nil]
      exact number_real_eventuallyExact (.apply lexeme [])
    · simp_all [TptpOfficialFofElaboration.decodeDefinedTerm?,
        TptpOfficialFofElaboration.decodeNumberHead?]
  case case15 =>
    intro lexeme result decoded
    simp [TptpOfficialFofElaboration.decodeDefinedTerm?] at decoded
    subst result
    rw [encodeTerm_function, encodeTerms_nil]
    exact distinct_eventuallyExact (.apply lexeme [])
  case case16 =>
    intro term inductionHypothesis result decoded
    apply inductionHypothesis result
    simpa [TptpOfficialFofElaboration.decodeDefinedTerm?] using decoded
  case case17 =>
    intro source notNumber notDistinct notAtomic result decoded
    simp_all [TptpOfficialFofElaboration.decodeDefinedTerm?]
  case case18 =>
    intro functor result decoded
    fun_cases TptpOfficialFofElaboration.decodeDefinedFunctorName? functor
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodeDefinedPlainTerm?,
        TptpOfficialFofElaboration.decodeDefinedFunctorName?] at decoded
      subst result
      rw [encodeTerm_function, encodeTerms_nil]
      exact defined_nullary_eventuallyExact (.apply lexeme [])
    · simp_all [TptpOfficialFofElaboration.decodeDefinedPlainTerm?,
        TptpOfficialFofElaboration.decodeDefinedFunctorName?]
  case case19 =>
    intro functor arguments argumentsInduction result decoded
    fun_cases TptpOfficialFofElaboration.decodeDefinedFunctorName? functor
    · rename_i lexeme
      cases argumentsDecoded :
          TptpOfficialFofElaboration.decodeArguments? arguments with
      | none =>
          simp [TptpOfficialFofElaboration.decodeDefinedPlainTerm?,
            TptpOfficialFofElaboration.decodeDefinedFunctorName?,
            argumentsDecoded] at decoded
      | some argumentResults =>
          simp [TptpOfficialFofElaboration.decodeDefinedPlainTerm?,
            TptpOfficialFofElaboration.decodeDefinedFunctorName?,
            argumentsDecoded] at decoded
          subst result
          rw [encodeTerm_function]
          exact defined_applied_eventuallyExact (.apply lexeme []) arguments
            (TptpNamedFofLanguageDef.encodeTerms argumentResults)
            (argumentsInduction argumentResults argumentsDecoded)
    · simp_all [TptpOfficialFofElaboration.decodeDefinedPlainTerm?,
        TptpOfficialFofElaboration.decodeDefinedFunctorName?]
  case case20 =>
    intro source notNullary notApplied result decoded
    simp_all [TptpOfficialFofElaboration.decodeDefinedPlainTerm?]
  case case21 =>
    intro functor result decoded
    fun_cases TptpOfficialFofElaboration.decodeFunctorName? functor
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodePlainTerm?,
        TptpOfficialFofElaboration.decodeFunctorName?] at decoded
      subst result
      rw [encodeTerm_function, encodeTerms_nil]
      exact plain_lower_nullary_eventuallyExact (.apply lexeme [])
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodePlainTerm?,
        TptpOfficialFofElaboration.decodeFunctorName?] at decoded
      subst result
      rw [encodeTerm_function, encodeTerms_nil]
      exact plain_quoted_nullary_eventuallyExact (.apply lexeme [])
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodePlainTerm?,
        TptpOfficialFofElaboration.decodeFunctorName?] at decoded
      subst result
      rw [encodeTerm_function, encodeTerms_nil]
      exact plain_backquoted_nullary_eventuallyExact (.apply lexeme [])
    · simp_all [TptpOfficialFofElaboration.decodePlainTerm?,
        TptpOfficialFofElaboration.decodeFunctorName?]
  case case22 =>
    intro functor arguments argumentsInduction result decoded
    fun_cases TptpOfficialFofElaboration.decodeFunctorName? functor
    · rename_i lexeme
      cases argumentsDecoded :
          TptpOfficialFofElaboration.decodeArguments? arguments with
      | none =>
          simp [TptpOfficialFofElaboration.decodePlainTerm?,
            TptpOfficialFofElaboration.decodeFunctorName?,
            argumentsDecoded] at decoded
      | some argumentResults =>
          simp [TptpOfficialFofElaboration.decodePlainTerm?,
            TptpOfficialFofElaboration.decodeFunctorName?,
            argumentsDecoded] at decoded
          subst result
          rw [encodeTerm_function]
          exact plain_lower_applied_eventuallyExact (.apply lexeme [])
            arguments (TptpNamedFofLanguageDef.encodeTerms argumentResults)
            (argumentsInduction argumentResults argumentsDecoded)
    · rename_i lexeme
      cases argumentsDecoded :
          TptpOfficialFofElaboration.decodeArguments? arguments with
      | none =>
          simp [TptpOfficialFofElaboration.decodePlainTerm?,
            TptpOfficialFofElaboration.decodeFunctorName?,
            argumentsDecoded] at decoded
      | some argumentResults =>
          simp [TptpOfficialFofElaboration.decodePlainTerm?,
            TptpOfficialFofElaboration.decodeFunctorName?,
            argumentsDecoded] at decoded
          subst result
          rw [encodeTerm_function]
          exact plain_quoted_applied_eventuallyExact (.apply lexeme [])
            arguments (TptpNamedFofLanguageDef.encodeTerms argumentResults)
            (argumentsInduction argumentResults argumentsDecoded)
    · rename_i lexeme
      cases argumentsDecoded :
          TptpOfficialFofElaboration.decodeArguments? arguments with
      | none =>
          simp [TptpOfficialFofElaboration.decodePlainTerm?,
            TptpOfficialFofElaboration.decodeFunctorName?,
            argumentsDecoded] at decoded
      | some argumentResults =>
          simp [TptpOfficialFofElaboration.decodePlainTerm?,
            TptpOfficialFofElaboration.decodeFunctorName?,
            argumentsDecoded] at decoded
          subst result
          rw [encodeTerm_function]
          exact plain_backquoted_applied_eventuallyExact (.apply lexeme [])
            arguments (TptpNamedFofLanguageDef.encodeTerms argumentResults)
            (argumentsInduction argumentResults argumentsDecoded)
    · simp_all [TptpOfficialFofElaboration.decodePlainTerm?,
        TptpOfficialFofElaboration.decodeFunctorName?]
  case case23 =>
    intro source notNullary notApplied result decoded
    simp_all [TptpOfficialFofElaboration.decodePlainTerm?]

/-- Whenever the independent decoder accepts an official term, every reduct
of the authored elaboration language is exactly that decoded term.  The
statement quantifies over all contextual fuel, including insufficient fuel;
membership makes those empty cases impossible. -/
theorem decodeTerm_no_invention (source : Pattern)
    {result : TptpFofBinderResolution.NamedTerm}
    (decoded : TptpOfficialFofElaboration.decodeTerm? source = some result)
    {fuel : Nat} {target : Pattern}
    (member : target ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (translateTerm source)) :
    target = TptpNamedFofLanguageDef.encodeTerm result := by
  exact (decodeTerm_eventuallyExact source result decoded).no_invention
    fuel member

private theorem formulaRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:formula") =
      delegationFormulaRules := by
  rfl

private theorem logicRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:logic") =
      delegationLogicRules := by
  rfl

private theorem atomicRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:atomic") =
      delegationAtomicRouteRules := by
  rfl

private theorem plainAtomicRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:plain-atomic") =
      plainAtomicLowerNullaryRules ++ plainAtomicQuotedNullaryRules ++
        plainAtomicLowerAppliedRules ++ plainAtomicQuotedAppliedRules := by
  rfl

private theorem definedAtomicRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:defined-atomic") =
      delegationTailRules.take 2 := by
  rfl

private theorem definedPlainRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:defined-plain") =
      definedTruthRules ++ definedPredicateRules := by
  rfl

private theorem definedInfixRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:defined-infix") =
      [equalityRule] := by
  rfl

private theorem systemAtomicRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:system-atomic") =
      systemAtomicRules := by
  rfl

private theorem infixUnaryRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:infix-unary") =
      [inequalityRule] := by
  rfl

private theorem binaryRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:binary") =
      delegationBinaryRouteRules := by
  rfl

private theorem binaryNonassocRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:binary-nonassoc") =
      nonassocRules := by
  rfl

private theorem binaryAssocRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:binary-assoc") =
      delegationAssocRouteRules := by
  rfl

private theorem orRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:or") =
      assocOrRules := by
  rfl

private theorem andRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:and") =
      assocAndRules := by
  rfl

private theorem unaryRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:unary") =
      [delegateRule "tptp-fof-elab:unary-infix" "tptp-fof-elab:unary"
        "tptp92-ast:fof-unary-formula:alt-2" "tptp-fof-elab:infix-unary"
        "Tptp92Ast:fof-infix-unary", unaryNotRule] := by
  rfl

private theorem unitRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:unit") =
      delegationUnitRouteRules.drop 1 := by
  rfl

private theorem unitaryRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:unitary") =
      delegationUnitaryRouteRules := by
  rfl

private theorem quantifiedRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:quantified") =
      quantifierHeadRules := by
  rfl

private theorem bindAllRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:bind-all") =
      bindAllRules := by
  rfl

private theorem bindExRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:bind-ex") =
      bindExRules := by
  rfl

private theorem sequentRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:sequent") =
      [delegateRule "tptp-fof-elab:sequent-parenthesized"
        "tptp-fof-elab:sequent" "tptp92-ast:fof-sequent:alt-2"
        "tptp-fof-elab:sequent" "Tptp92Ast:fof-sequent", sequentRule] := by
  rfl

private theorem tupleConjunctionRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:tuple-conjunction") =
      conjunctionHeadRules := by
  rfl

private theorem commaConjunctionRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:comma-conjunction") =
      conjunctionTailRules := by
  rfl

private theorem tupleDisjunctionRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:tuple-disjunction") =
      disjunctionHeadRules := by
  rfl

private theorem commaDisjunctionRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:comma-disjunction") =
      disjunctionTailRules := by
  rfl

private theorem formula_logic_eventuallyExact (source result : Pattern)
    (innerExact :
      EventuallyExact (request "tptp-fof-elab:logic" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:formula" <|
        .apply "tptp92-ast:fof-formula:alt-1" [source])
      result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, formulaRootRules]
  simp [delegationFormulaRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem formula_sequent_eventuallyExact (source result : Pattern)
    (innerExact :
      EventuallyExact (request "tptp-fof-elab:sequent" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:formula" <|
        .apply "tptp92-ast:fof-formula:alt-2" [source])
      result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, formulaRootRules]
  simp [delegationFormulaRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem logic_binary_eventuallyExact (source result : Pattern)
    (innerExact :
      EventuallyExact (request "tptp-fof-elab:binary" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:logic" <|
        .apply "tptp92-ast:fof-logic-formula:alt-1" [source])
      result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, logicRootRules]
  simp [delegationLogicRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem logic_unary_eventuallyExact (source result : Pattern)
    (innerExact :
      EventuallyExact (request "tptp-fof-elab:unary" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:logic" <|
        .apply "tptp92-ast:fof-logic-formula:alt-2" [source])
      result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, logicRootRules]
  simp [delegationLogicRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem logic_unitary_eventuallyExact (source result : Pattern)
    (innerExact :
      EventuallyExact (request "tptp-fof-elab:unitary" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:logic" <|
        .apply "tptp92-ast:fof-logic-formula:alt-3" [source])
      result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, logicRootRules]
  simp [delegationLogicRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem eventuallyExact_of_two_premises
    (firstSource firstResult secondSource secondResult source result : Pattern)
    (firstExact : EventuallyExact firstSource firstResult)
    (secondExact : EventuallyExact secondSource secondResult)
    (step : ∀ fuel,
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
          firstSource = [firstResult] →
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
          secondSource = [secondResult] →
        rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
          source = [result]) :
    EventuallyExact source result := by
  rcases firstExact with ⟨firstFuel, firstExact⟩
  rcases secondExact with ⟨secondFuel, secondExact⟩
  refine ⟨max firstFuel secondFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using step predecessor
        (firstExact predecessor (by omega))
        (secondExact predecessor (by omega))

private def officialPlainAtomicNullarySource
    (atomicAlternative tokenLabel : String) (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:fof-plain-atomic-formula:alt-1" [
    a "tptp92-ast:fof-plain-term:alt-1" [
      a "tptp92-ast:constant:alt-1" [
        sourceFunctor atomicAlternative tokenLabel lexeme]]]

private def officialPlainAtomicAppliedSource
    (atomicAlternative tokenLabel : String)
    (lexeme arguments : Pattern) : Pattern :=
  a "tptp92-ast:fof-plain-atomic-formula:alt-1" [
    a "tptp92-ast:fof-plain-term:alt-2" [
      sourceFunctor atomicAlternative tokenLabel lexeme, arguments]]

private theorem plain_atomic_lower_nullary_eventuallyExact
    (lexeme : Pattern) :
    EventuallyExact
      (request "tptp-fof-elab:plain-atomic" <|
        officialPlainAtomicNullarySource
          "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word"
          lexeme)
      (plainPredicate lexeme targetTermsNil) := by
  exact eventuallyExact_of_one_step _ _ (by
    intro fuel
    simp only [request, a]
    rw [rewriteAt_eq_root_filter, plainAtomicRootRules]
    simp [plainAtomicLowerNullaryRules, plainAtomicQuotedNullaryRules,
      plainAtomicLowerAppliedRules, plainAtomicQuotedAppliedRules,
      plainAtomicNullaryRule, plainAtomicAppliedRule,
      officialPlainAtomicNullarySource, sourceFunctor, sourceAtomicWord,
      sourceToken, targetPredicateHead, targetPredicate, plainPredicate,
      targetTermsNil,
      mkRule, congruence, request, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings])

local macro "close_plain_atomic_leaf" : tactic =>
  `(tactic|
    exact eventuallyExact_of_one_step _ _ (by
      intro fuel
      simp only [request, a]
      rw [rewriteAt_eq_root_filter, plainAtomicRootRules]
      simp [plainAtomicLowerNullaryRules, plainAtomicQuotedNullaryRules,
        plainAtomicLowerAppliedRules, plainAtomicQuotedAppliedRules,
        plainAtomicNullaryRule, plainAtomicAppliedRule,
        officialPlainAtomicNullarySource, sourceFunctor, sourceAtomicWord,
        sourceToken, targetPredicateHead, targetPredicate, plainPredicate,
        targetTermsNil,
        mkRule, congruence, request, a, v, applyRuleUsing,
        matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
        matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
        applyBindings]))

private theorem plain_atomic_quoted_nullary_eventuallyExact
    (lexeme : Pattern) :
    EventuallyExact
      (request "tptp-fof-elab:plain-atomic" <|
        officialPlainAtomicNullarySource
          "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted"
          lexeme)
      (plainPredicate lexeme targetTermsNil) := by
  close_plain_atomic_leaf

private theorem plain_atomic_backquoted_nullary_eventuallyExact
    (lexeme : Pattern) :
    EventuallyExact
      (request "tptp-fof-elab:plain-atomic" <|
        officialPlainAtomicNullarySource
          "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted"
          lexeme)
      (plainPredicate lexeme targetTermsNil) := by
  close_plain_atomic_leaf

local macro "close_plain_atomic_applied" argumentsExact:term : tactic =>
  `(tactic|
    exact eventuallyExact_of_one_premise _ _ _ _ ($argumentsExact) (by
      intro fuel argumentsStep
      simp only [request, a]
      simp only [translateArguments, a] at argumentsStep
      rw [rewriteAt_eq_root_filter, plainAtomicRootRules]
      simp [plainAtomicLowerNullaryRules, plainAtomicQuotedNullaryRules,
        plainAtomicLowerAppliedRules, plainAtomicQuotedAppliedRules,
        plainAtomicNullaryRule, plainAtomicAppliedRule,
        officialPlainAtomicAppliedSource, sourceFunctor, sourceAtomicWord,
        sourceToken, targetPredicateHead, targetPredicate, plainPredicate,
        targetTermsNil,
        mkRule, congruence, request, translateArguments, a, v,
        applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
        premiseStepUsing, matchPattern, matchArgs, mergeBindings,
        applyBindingsForRule, applyBindings, argumentsStep]))

private theorem plain_atomic_lower_applied_eventuallyExact
    (lexeme arguments argumentsResult : Pattern)
    (argumentsExact :
      EventuallyExact (translateArguments arguments) argumentsResult) :
    EventuallyExact
      (request "tptp-fof-elab:plain-atomic" <|
        officialPlainAtomicAppliedSource
          "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word"
          lexeme arguments)
      (plainPredicate lexeme argumentsResult) := by
  close_plain_atomic_applied argumentsExact

private theorem plain_atomic_quoted_applied_eventuallyExact
    (lexeme arguments argumentsResult : Pattern)
    (argumentsExact :
      EventuallyExact (translateArguments arguments) argumentsResult) :
    EventuallyExact
      (request "tptp-fof-elab:plain-atomic" <|
        officialPlainAtomicAppliedSource
          "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted"
          lexeme arguments)
      (plainPredicate lexeme argumentsResult) := by
  close_plain_atomic_applied argumentsExact

private theorem plain_atomic_backquoted_applied_eventuallyExact
    (lexeme arguments argumentsResult : Pattern)
    (argumentsExact :
      EventuallyExact (translateArguments arguments) argumentsResult) :
    EventuallyExact
      (request "tptp-fof-elab:plain-atomic" <|
        officialPlainAtomicAppliedSource
          "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted"
          lexeme arguments)
      (plainPredicate lexeme argumentsResult) := by
  close_plain_atomic_applied argumentsExact

/-- The authored plain-atomic rows implement every successful result of the
independent official-AST decoder. -/
private theorem decodePlainAtomicFormula_eventuallyExact
    (source : Pattern) {result : TptpFofBinderResolution.NamedFormula}
    (decoded :
      TptpOfficialFofElaboration.decodePlainAtomicFormula? source =
        some result) :
    EventuallyExact (request "tptp-fof-elab:plain-atomic" source)
      (TptpNamedFofLanguageDef.encodeFormula result) := by
  unfold TptpOfficialFofElaboration.decodePlainAtomicFormula? at decoded
  split at decoded
  · rename_i functor
    fun_cases TptpOfficialFofElaboration.decodeFunctorName? functor
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodeFunctorName?] at decoded
      subst result
      rw [encodeFormula_predicate, encodeTerms_nil]
      simpa [
        officialPlainAtomicNullarySource, sourceFunctor,
        sourceAtomicWord, sourceToken, targetPredicateHead, targetPredicate,
        plainPredicate,
        targetTermsNil, a] using
        plain_atomic_lower_nullary_eventuallyExact (.apply lexeme [])
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodeFunctorName?] at decoded
      subst result
      rw [encodeFormula_predicate, encodeTerms_nil]
      simpa [
        officialPlainAtomicNullarySource, sourceFunctor,
        sourceAtomicWord, sourceToken, targetPredicateHead, targetPredicate,
        plainPredicate,
        targetTermsNil, a] using
        plain_atomic_quoted_nullary_eventuallyExact (.apply lexeme [])
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodeFunctorName?] at decoded
      subst result
      rw [encodeFormula_predicate, encodeTerms_nil]
      simpa [
        officialPlainAtomicNullarySource, sourceFunctor,
        sourceAtomicWord, sourceToken, targetPredicateHead, targetPredicate,
        plainPredicate,
        targetTermsNil, a] using
        plain_atomic_backquoted_nullary_eventuallyExact (.apply lexeme [])
    · simp_all [TptpOfficialFofElaboration.decodeFunctorName?]
  · rename_i functor arguments
    fun_cases TptpOfficialFofElaboration.decodeFunctorName? functor
    · rename_i lexeme
      cases argumentsDecoded :
          TptpOfficialFofElaboration.decodeArguments? arguments with
      | none =>
          simp [TptpOfficialFofElaboration.decodeFunctorName?,
            argumentsDecoded] at decoded
      | some argumentResults =>
          simp [TptpOfficialFofElaboration.decodeFunctorName?,
            argumentsDecoded] at decoded
          subst result
          rw [encodeFormula_predicate]
          simpa [
            officialPlainAtomicAppliedSource, sourceFunctor,
            sourceAtomicWord, sourceToken, targetPredicateHead,
            targetPredicate, plainPredicate, a]
            using plain_atomic_lower_applied_eventuallyExact
              (.apply lexeme []) arguments
              (TptpNamedFofLanguageDef.encodeTerms argumentResults)
              (decodeArguments_eventuallyExact
                (fun source result => decodeTerm_eventuallyExact source result)
                arguments argumentResults argumentsDecoded)
    · rename_i lexeme
      cases argumentsDecoded :
          TptpOfficialFofElaboration.decodeArguments? arguments with
      | none =>
          simp [TptpOfficialFofElaboration.decodeFunctorName?,
            argumentsDecoded] at decoded
      | some argumentResults =>
          simp [TptpOfficialFofElaboration.decodeFunctorName?,
            argumentsDecoded] at decoded
          subst result
          rw [encodeFormula_predicate]
          simpa [
            officialPlainAtomicAppliedSource, sourceFunctor,
            sourceAtomicWord, sourceToken, targetPredicateHead,
            targetPredicate, plainPredicate, a]
            using plain_atomic_quoted_applied_eventuallyExact
              (.apply lexeme []) arguments
              (TptpNamedFofLanguageDef.encodeTerms argumentResults)
              (decodeArguments_eventuallyExact
                (fun source result => decodeTerm_eventuallyExact source result)
                arguments argumentResults argumentsDecoded)
    · rename_i lexeme
      cases argumentsDecoded :
          TptpOfficialFofElaboration.decodeArguments? arguments with
      | none =>
          simp [TptpOfficialFofElaboration.decodeFunctorName?,
            argumentsDecoded] at decoded
      | some argumentResults =>
          simp [TptpOfficialFofElaboration.decodeFunctorName?,
            argumentsDecoded] at decoded
          subst result
          rw [encodeFormula_predicate]
          simpa [
            officialPlainAtomicAppliedSource, sourceFunctor,
            sourceAtomicWord, sourceToken, targetPredicateHead,
            targetPredicate, plainPredicate, a]
            using plain_atomic_backquoted_applied_eventuallyExact
              (.apply lexeme []) arguments
              (TptpNamedFofLanguageDef.encodeTerms argumentResults)
              (decodeArguments_eventuallyExact
                (fun source result => decodeTerm_eventuallyExact source result)
                arguments argumentResults argumentsDecoded)
    · simp_all [TptpOfficialFofElaboration.decodeFunctorName?]
  · contradiction

private def officialDefinedPlainNullarySource (lexeme : String) : Pattern :=
  a "tptp92-ast:fof-defined-plain-formula:alt-1" [
    a "tptp92-ast:fof-defined-plain-term:alt-1" [
      a "tptp92-ast:defined-constant:alt-1" [
        sourceDefinedFunctor (a lexeme)]]]

private def officialDefinedPredicateSource
    (lexeme arguments : Pattern) : Pattern :=
  a "tptp92-ast:fof-defined-plain-formula:alt-1" [
    a "tptp92-ast:fof-defined-plain-term:alt-2" [
      sourceDefinedFunctor lexeme, arguments]]

private theorem defined_true_eventuallyExact :
    EventuallyExact
      (request "tptp-fof-elab:defined-plain" <|
        officialDefinedPlainNullarySource "$true")
      (targetNullary "verum") := by
  exact eventuallyExact_of_one_step _ _ (by
    intro fuel
    simp only [request, a]
    rw [rewriteAt_eq_root_filter, definedPlainRootRules]
    simp [definedTruthRules, definedPredicateRules, definedTruthRule,
      definedPredicateRule, officialDefinedPlainNullarySource,
      sourceDefinedFunctor, sourceToken, targetNullary, mkRule,
      congruence, request, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings])

private theorem defined_false_eventuallyExact :
    EventuallyExact
      (request "tptp-fof-elab:defined-plain" <|
        officialDefinedPlainNullarySource "$false")
      (targetNullary "falsum") := by
  exact eventuallyExact_of_one_step _ _ (by
    intro fuel
    simp only [request, a]
    rw [rewriteAt_eq_root_filter, definedPlainRootRules]
    simp [definedTruthRules, definedPredicateRules, definedTruthRule,
      definedPredicateRule, officialDefinedPlainNullarySource,
      sourceDefinedFunctor, sourceToken, targetNullary, mkRule,
      congruence, request, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings])

private theorem defined_predicate_eventuallyExact
    (lexeme arguments argumentsResult : Pattern)
    (argumentsExact :
      EventuallyExact (translateArguments arguments) argumentsResult) :
    EventuallyExact
      (request "tptp-fof-elab:defined-plain" <|
        officialDefinedPredicateSource lexeme arguments)
      (definedPredicate lexeme argumentsResult) := by
  exact eventuallyExact_of_one_premise _ _ _ _ argumentsExact (by
    intro fuel argumentsStep
    simp only [request, a]
    simp only [translateArguments, a] at argumentsStep
    rw [rewriteAt_eq_root_filter, definedPlainRootRules]
    simp [definedTruthRules, definedPredicateRules, definedTruthRule,
      definedPredicateRule, officialDefinedPredicateSource,
      sourceDefinedFunctor, sourceToken, targetNullary, targetPredicateHead,
      targetPredicate, definedPredicate, translateArguments, mkRule,
      congruence, request, a, v,
      applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
      premiseStepUsing, matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings, argumentsStep])

private def officialSystemAtomicNullarySource (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:fof-system-atomic-formula:alt-1" [
    a "tptp92-ast:fof-system-term:alt-1" [
      a "tptp92-ast:system-constant:alt-1" [
        sourceSystemFunctor lexeme]]]

private def officialSystemAtomicAppliedSource
    (lexeme arguments : Pattern) : Pattern :=
  a "tptp92-ast:fof-system-atomic-formula:alt-1" [
    a "tptp92-ast:fof-system-term:alt-2" [
      sourceSystemFunctor lexeme, arguments]]

private theorem system_atomic_nullary_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (request "tptp-fof-elab:system-atomic" <|
        officialSystemAtomicNullarySource lexeme)
      (systemPredicate lexeme targetTermsNil) := by
  exact eventuallyExact_of_one_step _ _ (by
    intro fuel
    simp only [request, a]
    rw [rewriteAt_eq_root_filter, systemAtomicRootRules]
    simp [systemAtomicRules, systemAtomicNullaryRule,
      systemAtomicAppliedRule, officialSystemAtomicNullarySource,
      sourceSystemFunctor, sourceToken, targetPredicateHead, targetPredicate,
      systemPredicate,
      targetTermsNil, translateArguments, mkRule, congruence, request,
      a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing, matchPattern, matchArgs,
      mergeBindings, applyBindingsForRule, applyBindings])

private theorem system_atomic_applied_eventuallyExact
    (lexeme arguments argumentsResult : Pattern)
    (argumentsExact :
      EventuallyExact (translateArguments arguments) argumentsResult) :
    EventuallyExact
      (request "tptp-fof-elab:system-atomic" <|
        officialSystemAtomicAppliedSource lexeme arguments)
      (systemPredicate lexeme argumentsResult) := by
  exact eventuallyExact_of_one_premise _ _ _ _ argumentsExact (by
    intro fuel argumentsStep
    simp only [request, a]
    simp only [translateArguments, a] at argumentsStep
    rw [rewriteAt_eq_root_filter, systemAtomicRootRules]
    simp [systemAtomicRules, systemAtomicNullaryRule,
      systemAtomicAppliedRule, officialSystemAtomicAppliedSource,
      sourceSystemFunctor, sourceToken, targetPredicateHead, targetPredicate,
      systemPredicate,
      translateArguments, mkRule, congruence, request, a, v,
      applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
      premiseStepUsing, matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings, argumentsStep])

private def officialEqualitySource (left right : Pattern) : Pattern :=
  a "tptp92-ast:fof-defined-infix-formula:alt-1" [
    left,
    a "tptp92-ast:defined-infix-pred:alt-1" [
      a "tptp92-ast:infix-equality:alt-1"],
    right]

private theorem equality_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact : EventuallyExact (translateTerm left) leftResult)
    (rightExact : EventuallyExact (translateTerm right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:defined-infix" <|
        officialEqualitySource left right)
      (targetEqual leftResult rightResult) := by
  exact eventuallyExact_of_two_premises _ _ _ _ _ _ leftExact rightExact (by
    intro fuel leftStep rightStep
    simp only [request, translateTerm, a] at leftStep rightStep ⊢
    rw [rewriteAt_eq_root_filter, definedInfixRootRules]
    simp [equalityRule, officialEqualitySource, targetEqual, mkRule,
      congruence, request, translateTerm, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings, leftStep, rightStep])

private theorem decodeSystemAtomicFormula_eventuallyExact
    (source : Pattern) {result : TptpFofBinderResolution.NamedFormula}
    (decoded :
      TptpOfficialFofElaboration.decodeSystemAtomicFormula? source =
        some result) :
    EventuallyExact (request "tptp-fof-elab:system-atomic" source)
      (TptpNamedFofLanguageDef.encodeFormula result) := by
  unfold TptpOfficialFofElaboration.decodeSystemAtomicFormula? at decoded
  split at decoded
  · rename_i functor
    fun_cases TptpOfficialFofElaboration.decodeSystemFunctorName? functor
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodeSystemFunctorName?] at decoded
      subst result
      rw [encodeFormula_predicate, encodeTerms_nil]
      simpa [officialSystemAtomicNullarySource, sourceSystemFunctor,
        sourceToken, targetPredicateHead, targetPredicate, systemPredicate,
        targetTermsNil, a] using
        system_atomic_nullary_eventuallyExact (.apply lexeme [])
    · simp_all [TptpOfficialFofElaboration.decodeSystemFunctorName?]
  · rename_i functor arguments
    fun_cases TptpOfficialFofElaboration.decodeSystemFunctorName? functor
    · rename_i lexeme
      cases argumentsDecoded :
          TptpOfficialFofElaboration.decodeArguments? arguments with
      | none =>
          simp [TptpOfficialFofElaboration.decodeSystemFunctorName?,
            argumentsDecoded] at decoded
      | some argumentResults =>
          simp [TptpOfficialFofElaboration.decodeSystemFunctorName?,
            argumentsDecoded] at decoded
          subst result
          rw [encodeFormula_predicate]
          simpa [officialSystemAtomicAppliedSource, sourceSystemFunctor,
            sourceToken, targetPredicateHead, targetPredicate,
            systemPredicate, a] using
            system_atomic_applied_eventuallyExact (.apply lexeme []) arguments
              (TptpNamedFofLanguageDef.encodeTerms argumentResults)
              (decodeArguments_eventuallyExact
                (fun source result => decodeTerm_eventuallyExact source result)
                arguments argumentResults argumentsDecoded)
    · simp_all [TptpOfficialFofElaboration.decodeSystemFunctorName?]
  · contradiction

private theorem decodeDefinedInfixFormula_eventuallyExact
    (source : Pattern) {result : TptpFofBinderResolution.NamedFormula}
    (decoded :
      TptpOfficialFofElaboration.decodeDefinedInfixFormula? source =
        some result) :
    EventuallyExact (request "tptp-fof-elab:defined-infix" source)
      (TptpNamedFofLanguageDef.encodeFormula result) := by
  unfold TptpOfficialFofElaboration.decodeDefinedInfixFormula? at decoded
  split at decoded
  · rename_i left right
    cases leftDecoded : TptpOfficialFofElaboration.decodeTerm? left with
    | none => simp [leftDecoded] at decoded
    | some leftResult =>
        cases rightDecoded : TptpOfficialFofElaboration.decodeTerm? right with
        | none => simp [leftDecoded, rightDecoded] at decoded
        | some rightResult =>
            simp [leftDecoded, rightDecoded] at decoded
            subst result
            rw [encodeFormula_equal]
            simpa [officialEqualitySource, a] using
              equality_eventuallyExact left right
                (TptpNamedFofLanguageDef.encodeTerm leftResult)
                (TptpNamedFofLanguageDef.encodeTerm rightResult)
                (decodeTerm_eventuallyExact left leftResult leftDecoded)
                (decodeTerm_eventuallyExact right rightResult rightDecoded)
  · contradiction

private theorem decodeDefinedPlainFormula_eventuallyExact
    (source : Pattern) {result : TptpFofBinderResolution.NamedFormula}
    (decoded :
      TptpOfficialFofElaboration.decodeDefinedPlainFormula? source =
        some result) :
    EventuallyExact (request "tptp-fof-elab:defined-plain" source)
      (TptpNamedFofLanguageDef.encodeFormula result) := by
  unfold TptpOfficialFofElaboration.decodeDefinedPlainFormula? at decoded
  split at decoded
  · rename_i term
    unfold TptpOfficialFofElaboration.decodeDefinedPlainTerm? at decoded
    split at decoded
    · rename_i functor
      fun_cases TptpOfficialFofElaboration.decodeDefinedFunctorName? functor
      · rename_i lexeme
        by_cases trueName : lexeme = "$true"
        · subst lexeme
          simp [TptpOfficialFofElaboration.decodeDefinedFunctorName?] at decoded
          subst result
          rw [encodeFormula_verum]
          simpa [officialDefinedPlainNullarySource, sourceDefinedFunctor,
            sourceToken, a] using defined_true_eventuallyExact
        · by_cases falseName : lexeme = "$false"
          · subst lexeme
            simp [TptpOfficialFofElaboration.decodeDefinedFunctorName?] at decoded
            subst result
            rw [encodeFormula_falsum]
            simpa [officialDefinedPlainNullarySource, sourceDefinedFunctor,
              sourceToken, a] using defined_false_eventuallyExact
          · simp [TptpOfficialFofElaboration.decodeDefinedFunctorName?,
              trueName, falseName] at decoded
      · simp_all [TptpOfficialFofElaboration.decodeDefinedFunctorName?]
    · rename_i functor arguments
      fun_cases TptpOfficialFofElaboration.decodeDefinedFunctorName? functor
      · rename_i lexeme
        cases argumentsDecoded :
            TptpOfficialFofElaboration.decodeArguments? arguments with
        | none =>
            simp [TptpOfficialFofElaboration.decodeDefinedFunctorName?,
              argumentsDecoded] at decoded
        | some argumentResults =>
            cases argumentResults with
            | nil =>
                exact False.elim
                  (decodeArguments_ne_nil arguments argumentsDecoded rfl)
            | cons argument argumentResults =>
                simp [TptpOfficialFofElaboration.decodeDefinedFunctorName?,
                  argumentsDecoded] at decoded
                subst result
                rw [encodeFormula_predicate]
                simpa [officialDefinedPredicateSource, sourceDefinedFunctor,
                  sourceToken, targetPredicateHead, targetPredicate,
                  definedPredicate, a] using
                  defined_predicate_eventuallyExact (.apply lexeme []) arguments
                    (TptpNamedFofLanguageDef.encodeTerms
                      (argument :: argumentResults))
                    (decodeArguments_eventuallyExact
                      (fun source result => decodeTerm_eventuallyExact
                        source result)
                      arguments (argument :: argumentResults) argumentsDecoded)
      · simp_all [TptpOfficialFofElaboration.decodeDefinedFunctorName?]
    · contradiction
  · contradiction

private theorem atomic_plain_eventuallyExact (source result : Pattern)
    (innerExact :
      EventuallyExact (request "tptp-fof-elab:plain-atomic" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:atomic" <|
        a "tptp92-ast:fof-atomic-formula:alt-1" [source])
      result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, atomicRootRules]
  simp [delegationAtomicRouteRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem atomic_defined_eventuallyExact (source result : Pattern)
    (innerExact :
      EventuallyExact (request "tptp-fof-elab:defined-atomic" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:atomic" <|
        a "tptp92-ast:fof-atomic-formula:alt-2" [source])
      result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, atomicRootRules]
  simp [delegationAtomicRouteRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem atomic_system_eventuallyExact (source result : Pattern)
    (innerExact :
      EventuallyExact (request "tptp-fof-elab:system-atomic" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:atomic" <|
        a "tptp92-ast:fof-atomic-formula:alt-3" [source])
      result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, atomicRootRules]
  simp [delegationAtomicRouteRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem defined_atomic_plain_eventuallyExact (source result : Pattern)
    (innerExact :
      EventuallyExact (request "tptp-fof-elab:defined-plain" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:defined-atomic" <|
        a "tptp92-ast:fof-defined-atomic-formula:alt-1" [source])
      result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, definedAtomicRootRules]
  simp [delegationTailRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem defined_atomic_infix_eventuallyExact (source result : Pattern)
    (innerExact :
      EventuallyExact (request "tptp-fof-elab:defined-infix" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:defined-atomic" <|
        a "tptp92-ast:fof-defined-atomic-formula:alt-2" [source])
      result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, definedAtomicRootRules]
  simp [delegationTailRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem decodeDefinedAtomicFormula_eventuallyExact
    (source : Pattern) {result : TptpFofBinderResolution.NamedFormula}
    (decoded :
      TptpOfficialFofElaboration.decodeDefinedAtomicFormula? source =
        some result) :
    EventuallyExact (request "tptp-fof-elab:defined-atomic" source)
      (TptpNamedFofLanguageDef.encodeFormula result) := by
  unfold TptpOfficialFofElaboration.decodeDefinedAtomicFormula? at decoded
  split at decoded
  · rename_i inner
    exact defined_atomic_plain_eventuallyExact inner _
      (decodeDefinedPlainFormula_eventuallyExact inner decoded)
  · rename_i inner
    exact defined_atomic_infix_eventuallyExact inner _
      (decodeDefinedInfixFormula_eventuallyExact inner decoded)
  · contradiction

/-- Atomic FOF is now a complete authored vertical: every successful
independent atomic decoder result is produced exactly and stably by the
corresponding GSLT route and leaf rules. -/
theorem decodeAtomicFormula_eventuallyExact
    (source : Pattern) {result : TptpFofBinderResolution.NamedFormula}
    (decoded :
      TptpOfficialFofElaboration.decodeAtomicFormula? source = some result) :
    EventuallyExact (request "tptp-fof-elab:atomic" source)
      (TptpNamedFofLanguageDef.encodeFormula result) := by
  unfold TptpOfficialFofElaboration.decodeAtomicFormula? at decoded
  split at decoded
  · rename_i inner
    exact atomic_plain_eventuallyExact inner _
      (decodePlainAtomicFormula_eventuallyExact inner decoded)
  · rename_i inner
    exact atomic_defined_eventuallyExact inner _
      (decodeDefinedAtomicFormula_eventuallyExact inner decoded)
  · rename_i inner
    exact atomic_system_eventuallyExact inner _
      (decodeSystemAtomicFormula_eventuallyExact inner decoded)
  · contradiction

theorem decodeAtomicFormula_no_invention (source : Pattern)
    {result : TptpFofBinderResolution.NamedFormula}
    (decoded :
      TptpOfficialFofElaboration.decodeAtomicFormula? source = some result)
    {fuel : Nat} {target : Pattern}
    (member : target ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (request "tptp-fof-elab:atomic" source)) :
    target = TptpNamedFofLanguageDef.encodeFormula result := by
  exact (decodeAtomicFormula_eventuallyExact source decoded).no_invention
    fuel member

private def officialNonassocSource
    (connective : String) (left right : Pattern) : Pattern :=
  a "tptp92-ast:fof-binary-nonassoc:alt-1" [left, a connective, right]

local macro "close_nonassoc" leftExact:ident rightExact:ident : tactic =>
  `(tactic|
    exact eventuallyExact_of_two_premises _ _ _ _ _ _
      ($leftExact) ($rightExact) (by
        intro fuel leftStep rightStep
        simp only [request, a] at leftStep rightStep ⊢
        rw [rewriteAt_eq_root_filter, binaryNonassocRootRules]
        simp [nonassocRules, nonassocIffRules, nonassocImplicationRules,
          nonassocXorRules, nonassocNorNandRules, nonassocRule,
          officialNonassocSource, targetBinary, mkRule, congruence,
          request, a, v, applyRuleUsing,
          matchPatternForRule_eq_syntactic, premisesUsing,
          premiseStepUsing, matchPattern, matchArgs, mergeBindings,
          applyBindingsForRule, applyBindings, leftStep, rightStep]))

private theorem nonassoc_iff_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact :
      EventuallyExact (request "tptp-fof-elab:unit" left) leftResult)
    (rightExact :
      EventuallyExact (request "tptp-fof-elab:unit" right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:binary-nonassoc" <|
        officialNonassocSource "tptp92-ast:nonassoc-connective:alt-1"
          left right)
      (targetBinary "iff" leftResult rightResult) := by
  close_nonassoc leftExact rightExact

private theorem nonassoc_implies_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact :
      EventuallyExact (request "tptp-fof-elab:unit" left) leftResult)
    (rightExact :
      EventuallyExact (request "tptp-fof-elab:unit" right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:binary-nonassoc" <|
        officialNonassocSource "tptp92-ast:nonassoc-connective:alt-2"
          left right)
      (targetBinary "implies" leftResult rightResult) := by
  close_nonassoc leftExact rightExact

private theorem nonassoc_reverse_implies_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact :
      EventuallyExact (request "tptp-fof-elab:unit" left) leftResult)
    (rightExact :
      EventuallyExact (request "tptp-fof-elab:unit" right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:binary-nonassoc" <|
        officialNonassocSource "tptp92-ast:nonassoc-connective:alt-3"
          left right)
      (targetBinary "reverse-implies" leftResult rightResult) := by
  close_nonassoc leftExact rightExact

private theorem nonassoc_xor_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact :
      EventuallyExact (request "tptp-fof-elab:unit" left) leftResult)
    (rightExact :
      EventuallyExact (request "tptp-fof-elab:unit" right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:binary-nonassoc" <|
        officialNonassocSource "tptp92-ast:nonassoc-connective:alt-4"
          left right)
      (targetBinary "xor" leftResult rightResult) := by
  close_nonassoc leftExact rightExact

private theorem nonassoc_nor_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact :
      EventuallyExact (request "tptp-fof-elab:unit" left) leftResult)
    (rightExact :
      EventuallyExact (request "tptp-fof-elab:unit" right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:binary-nonassoc" <|
        officialNonassocSource "tptp92-ast:nonassoc-connective:alt-5"
          left right)
      (targetBinary "nor" leftResult rightResult) := by
  close_nonassoc leftExact rightExact

private theorem nonassoc_nand_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact :
      EventuallyExact (request "tptp-fof-elab:unit" left) leftResult)
    (rightExact :
      EventuallyExact (request "tptp-fof-elab:unit" right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:binary-nonassoc" <|
        officialNonassocSource "tptp92-ast:nonassoc-connective:alt-6"
          left right)
      (targetBinary "nand" leftResult rightResult) := by
  close_nonassoc leftExact rightExact

private def officialAssocSource
    (constructor : String) (left right : Pattern) : Pattern :=
  a constructor [left, right]

local macro "close_or_assoc" leftExact:ident rightExact:ident : tactic =>
  `(tactic|
    exact eventuallyExact_of_two_premises _ _ _ _ _ _
      ($leftExact) ($rightExact) (by
        intro fuel leftStep rightStep
        simp only [request, a] at leftStep rightStep ⊢
        rw [rewriteAt_eq_root_filter, orRootRules]
        simp [assocOrRules, assocRule, officialAssocSource, targetBinary,
          mkRule, congruence, request, a, v, applyRuleUsing,
          matchPatternForRule_eq_syntactic, premisesUsing,
          premiseStepUsing, matchPattern, matchArgs, mergeBindings,
          applyBindingsForRule, applyBindings, leftStep, rightStep]))

local macro "close_and_assoc" leftExact:ident rightExact:ident : tactic =>
  `(tactic|
    exact eventuallyExact_of_two_premises _ _ _ _ _ _
      ($leftExact) ($rightExact) (by
        intro fuel leftStep rightStep
        simp only [request, a] at leftStep rightStep ⊢
        rw [rewriteAt_eq_root_filter, andRootRules]
        simp [assocAndRules, assocRule, officialAssocSource, targetBinary,
          mkRule, congruence, request, a, v, applyRuleUsing,
          matchPatternForRule_eq_syntactic, premisesUsing,
          premiseStepUsing, matchPattern, matchArgs, mergeBindings,
          applyBindingsForRule, applyBindings, leftStep, rightStep]))

private theorem or_first_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact : EventuallyExact (request "tptp-fof-elab:unit" left) leftResult)
    (rightExact : EventuallyExact (request "tptp-fof-elab:unit" right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:or" <|
        officialAssocSource "tptp92-ast:fof-or-formula:alt-1" left right)
      (targetBinary "or" leftResult rightResult) := by
  close_or_assoc leftExact rightExact

private theorem or_more_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact : EventuallyExact (request "tptp-fof-elab:or" left) leftResult)
    (rightExact : EventuallyExact (request "tptp-fof-elab:unit" right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:or" <|
        officialAssocSource "tptp92-ast:fof-or-formula:alt-2" left right)
      (targetBinary "or" leftResult rightResult) := by
  close_or_assoc leftExact rightExact

private theorem and_first_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact : EventuallyExact (request "tptp-fof-elab:unit" left) leftResult)
    (rightExact : EventuallyExact (request "tptp-fof-elab:unit" right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:and" <|
        officialAssocSource "tptp92-ast:fof-and-formula:alt-1" left right)
      (targetBinary "and" leftResult rightResult) := by
  close_and_assoc leftExact rightExact

private theorem and_more_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact : EventuallyExact (request "tptp-fof-elab:and" left) leftResult)
    (rightExact : EventuallyExact (request "tptp-fof-elab:unit" right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:and" <|
        officialAssocSource "tptp92-ast:fof-and-formula:alt-2" left right)
      (targetBinary "and" leftResult rightResult) := by
  close_and_assoc leftExact rightExact

private theorem unary_not_eventuallyExact
    (body bodyResult : Pattern)
    (bodyExact : EventuallyExact (request "tptp-fof-elab:unit" body) bodyResult) :
    EventuallyExact
      (request "tptp-fof-elab:unary" <|
        a "tptp92-ast:fof-unary-formula:alt-1" [
          a "tptp92-ast:unary-connective:alt-1", body])
      (targetUnary "not" bodyResult) := by
  exact eventuallyExact_of_one_premise _ _ _ _ bodyExact (by
    intro fuel bodyStep
    simp only [request, a] at bodyStep ⊢
    rw [rewriteAt_eq_root_filter, unaryRootRules]
    simp [delegateRule, unaryNotRule,
      targetUnary, mkRule, congruence, request, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings, bodyStep])

private def officialInequalitySource (left right : Pattern) : Pattern :=
  a "tptp92-ast:fof-infix-unary:alt-1" [
    left, a "tptp92-ast:infix-inequality:alt-1", right]

private theorem inequality_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact : EventuallyExact (translateTerm left) leftResult)
    (rightExact : EventuallyExact (translateTerm right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:infix-unary" <|
        officialInequalitySource left right)
      (targetUnary "not" (targetEqual leftResult rightResult)) := by
  exact eventuallyExact_of_two_premises _ _ _ _ _ _ leftExact rightExact (by
    intro fuel leftStep rightStep
    simp only [request, translateTerm, a] at leftStep rightStep ⊢
    rw [rewriteAt_eq_root_filter, infixUnaryRootRules]
    simp [inequalityRule, officialInequalitySource, targetUnary, targetEqual,
      mkRule, congruence, request, translateTerm, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings, leftStep, rightStep])

private theorem decodeInfixUnary_eventuallyExact
    (source : Pattern) {result : TptpFofBinderResolution.NamedFormula}
    (decoded :
      TptpOfficialFofElaboration.decodeInfixUnary? source = some result) :
    EventuallyExact (request "tptp-fof-elab:infix-unary" source)
      (TptpNamedFofLanguageDef.encodeFormula result) := by
  unfold TptpOfficialFofElaboration.decodeInfixUnary? at decoded
  split at decoded
  · rename_i left right
    cases leftDecoded : TptpOfficialFofElaboration.decodeTerm? left with
    | none => simp [leftDecoded] at decoded
    | some leftResult =>
        cases rightDecoded : TptpOfficialFofElaboration.decodeTerm? right with
        | none => simp [leftDecoded, rightDecoded] at decoded
        | some rightResult =>
            simp [leftDecoded, rightDecoded] at decoded
            subst result
            rw [encodeFormula_not, encodeFormula_equal]
            simpa [officialInequalitySource, a] using
              inequality_eventuallyExact left right
                (TptpNamedFofLanguageDef.encodeTerm leftResult)
                (TptpNamedFofLanguageDef.encodeTerm rightResult)
                (decodeTerm_eventuallyExact left leftResult leftDecoded)
                (decodeTerm_eventuallyExact right rightResult rightDecoded)
  · contradiction

private theorem binary_nonassoc_route_eventuallyExact
    (source result : Pattern)
    (innerExact : EventuallyExact
      (request "tptp-fof-elab:binary-nonassoc" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:binary" <|
        a "tptp92-ast:fof-binary-formula:alt-1" [source]) result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, binaryRootRules]
  simp [delegationBinaryRouteRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem binary_assoc_route_eventuallyExact
    (source result : Pattern)
    (innerExact : EventuallyExact
      (request "tptp-fof-elab:binary-assoc" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:binary" <|
        a "tptp92-ast:fof-binary-formula:alt-2" [source]) result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, binaryRootRules]
  simp [delegationBinaryRouteRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem binary_assoc_or_route_eventuallyExact
    (source result : Pattern)
    (innerExact : EventuallyExact
      (request "tptp-fof-elab:or" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:binary-assoc" <|
        a "tptp92-ast:fof-binary-assoc:alt-1" [source]) result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, binaryAssocRootRules]
  simp [delegationAssocRouteRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem binary_assoc_and_route_eventuallyExact
    (source result : Pattern)
    (innerExact : EventuallyExact
      (request "tptp-fof-elab:and" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:binary-assoc" <|
        a "tptp92-ast:fof-binary-assoc:alt-2" [source]) result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, binaryAssocRootRules]
  simp [delegationAssocRouteRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem unary_infix_route_eventuallyExact
    (source result : Pattern)
    (innerExact : EventuallyExact
      (request "tptp-fof-elab:infix-unary" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:unary" <|
        a "tptp92-ast:fof-unary-formula:alt-2" [source]) result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, unaryRootRules]
  simp [delegateRule, unaryNotRule, mkRule,
    congruence, request, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings, innerStep]

private theorem unit_unitary_route_eventuallyExact
    (source result : Pattern)
    (innerExact : EventuallyExact
      (request "tptp-fof-elab:unitary" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:unit" <|
        a "tptp92-ast:fof-unit-formula:alt-1" [source]) result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, unitRootRules]
  simp [delegationUnitRouteRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem unit_unary_route_eventuallyExact
    (source result : Pattern)
    (innerExact : EventuallyExact
      (request "tptp-fof-elab:unary" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:unit" <|
        a "tptp92-ast:fof-unit-formula:alt-2" [source]) result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, unitRootRules]
  simp [delegationUnitRouteRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem unitary_atomic_route_eventuallyExact
    (source result : Pattern)
    (innerExact : EventuallyExact
      (request "tptp-fof-elab:atomic" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:unitary" <|
        a "tptp92-ast:fof-unitary-formula:alt-2" [source]) result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, unitaryRootRules]
  simp [delegationUnitaryRouteRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem unitary_logic_route_eventuallyExact
    (source result : Pattern)
    (innerExact : EventuallyExact
      (request "tptp-fof-elab:logic" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:unitary" <|
        a "tptp92-ast:fof-unitary-formula:alt-3" [source]) result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, unitaryRootRules]
  simp [delegationUnitaryRouteRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem bind_all_one_eventuallyExact
    (lexeme body : Pattern) :
    EventuallyExact
      (requestWithBody "tptp-fof-elab:bind-all"
        (a "tptp92-ast:fof-variable-list:alt-1" [sourceVariable lexeme]) body)
      (targetBinder "all" lexeme body) := by
  exact eventuallyExact_of_one_step _ _ (by
    intro fuel
    simp only [requestWithBody, a]
    rw [rewriteAt_eq_root_filter, bindAllRootRules]
    simp [bindAllRules, bindOneRule, bindMoreRule, sourceVariable,
      sourceToken, targetBinder, targetName, mkRule, congruence, requestWithBody,
      a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing, matchPattern, matchArgs,
      mergeBindings, applyBindingsForRule, applyBindings])

private theorem bind_all_more_eventuallyExact
    (lexeme rest body restResult : Pattern)
    (restExact : EventuallyExact
      (requestWithBody "tptp-fof-elab:bind-all" rest body) restResult) :
    EventuallyExact
      (requestWithBody "tptp-fof-elab:bind-all"
        (a "tptp92-ast:fof-variable-list:alt-2" [
          sourceVariable lexeme, rest]) body)
      (targetBinder "all" lexeme restResult) := by
  exact eventuallyExact_of_one_premise _ _ _ _ restExact (by
    intro fuel restStep
    simp only [requestWithBody, a] at restStep ⊢
    rw [rewriteAt_eq_root_filter, bindAllRootRules]
    simp [bindAllRules, bindOneRule, bindMoreRule, sourceVariable,
      sourceToken, targetBinder, targetName, mkRule, congruence, requestWithBody,
      a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing, matchPattern, matchArgs,
      mergeBindings, applyBindingsForRule, applyBindings, restStep])

private theorem bind_ex_one_eventuallyExact
    (lexeme body : Pattern) :
    EventuallyExact
      (requestWithBody "tptp-fof-elab:bind-ex"
        (a "tptp92-ast:fof-variable-list:alt-1" [sourceVariable lexeme]) body)
      (targetBinder "ex" lexeme body) := by
  exact eventuallyExact_of_one_step _ _ (by
    intro fuel
    simp only [requestWithBody, a]
    rw [rewriteAt_eq_root_filter, bindExRootRules]
    simp [bindExRules, bindOneRule, bindMoreRule, sourceVariable,
      sourceToken, targetBinder, targetName, mkRule, congruence, requestWithBody,
      a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing, matchPattern, matchArgs,
      mergeBindings, applyBindingsForRule, applyBindings])

private theorem bind_ex_more_eventuallyExact
    (lexeme rest body restResult : Pattern)
    (restExact : EventuallyExact
      (requestWithBody "tptp-fof-elab:bind-ex" rest body) restResult) :
    EventuallyExact
      (requestWithBody "tptp-fof-elab:bind-ex"
        (a "tptp92-ast:fof-variable-list:alt-2" [
          sourceVariable lexeme, rest]) body)
      (targetBinder "ex" lexeme restResult) := by
  exact eventuallyExact_of_one_premise _ _ _ _ restExact (by
    intro fuel restStep
    simp only [requestWithBody, a] at restStep ⊢
    rw [rewriteAt_eq_root_filter, bindExRootRules]
    simp [bindExRules, bindOneRule, bindMoreRule, sourceVariable,
      sourceToken, targetBinder, targetName, mkRule, congruence, requestWithBody,
      a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing, matchPattern, matchArgs,
      mergeBindings, applyBindingsForRule, applyBindings, restStep])

private theorem decodeVariableList_bindAll_eventuallyExact
    (source : Pattern) (names : List String)
    (decoded :
      TptpOfficialFofElaboration.decodeVariableList? source = some names)
    (body : TptpFofBinderResolution.NamedFormula) :
    EventuallyExact
      (requestWithBody "tptp-fof-elab:bind-all" source
        (TptpNamedFofLanguageDef.encodeFormula body))
      (TptpNamedFofLanguageDef.encodeFormula
        (names.foldr TptpFofBinderResolution.NamedFormula.all body)) := by
  unfold TptpOfficialFofElaboration.decodeVariableList? at decoded
  split at decoded
  · rename_i variablePattern
    fun_cases TptpOfficialFofElaboration.decodeVariableName? variablePattern
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodeVariableName?] at decoded
      subst names
      simp only [List.foldr]
      rw [encodeFormula_all]
      simpa [sourceVariable, sourceToken, targetBinder, a] using
        bind_all_one_eventuallyExact (.apply lexeme [])
          (TptpNamedFofLanguageDef.encodeFormula body)
    · simp_all [TptpOfficialFofElaboration.decodeVariableName?]
  · rename_i variablePattern rest
    fun_cases TptpOfficialFofElaboration.decodeVariableName? variablePattern
    · rename_i lexeme
      cases restDecoded :
          TptpOfficialFofElaboration.decodeVariableList? rest with
      | none =>
          simp [TptpOfficialFofElaboration.decodeVariableName?,
            restDecoded] at decoded
      | some restNames =>
          simp [TptpOfficialFofElaboration.decodeVariableName?,
            restDecoded] at decoded
          subst names
          simp only [List.foldr]
          rw [encodeFormula_all]
          simpa [sourceVariable, sourceToken, targetBinder, a] using
            bind_all_more_eventuallyExact (.apply lexeme []) rest
              (TptpNamedFofLanguageDef.encodeFormula body)
              (TptpNamedFofLanguageDef.encodeFormula
                (restNames.foldr TptpFofBinderResolution.NamedFormula.all
                  body))
              (decodeVariableList_bindAll_eventuallyExact rest restNames
                restDecoded body)
    · simp_all [TptpOfficialFofElaboration.decodeVariableName?]
  · contradiction
termination_by sizeOf source

private theorem decodeVariableList_bindEx_eventuallyExact
    (source : Pattern) (names : List String)
    (decoded :
      TptpOfficialFofElaboration.decodeVariableList? source = some names)
    (body : TptpFofBinderResolution.NamedFormula) :
    EventuallyExact
      (requestWithBody "tptp-fof-elab:bind-ex" source
        (TptpNamedFofLanguageDef.encodeFormula body))
      (TptpNamedFofLanguageDef.encodeFormula
        (names.foldr TptpFofBinderResolution.NamedFormula.ex body)) := by
  unfold TptpOfficialFofElaboration.decodeVariableList? at decoded
  split at decoded
  · rename_i variablePattern
    fun_cases TptpOfficialFofElaboration.decodeVariableName? variablePattern
    · rename_i lexeme
      simp [TptpOfficialFofElaboration.decodeVariableName?] at decoded
      subst names
      simp only [List.foldr]
      rw [encodeFormula_ex]
      simpa [sourceVariable, sourceToken, targetBinder, a] using
        bind_ex_one_eventuallyExact (.apply lexeme [])
          (TptpNamedFofLanguageDef.encodeFormula body)
    · simp_all [TptpOfficialFofElaboration.decodeVariableName?]
  · rename_i variablePattern rest
    fun_cases TptpOfficialFofElaboration.decodeVariableName? variablePattern
    · rename_i lexeme
      cases restDecoded :
          TptpOfficialFofElaboration.decodeVariableList? rest with
      | none =>
          simp [TptpOfficialFofElaboration.decodeVariableName?,
            restDecoded] at decoded
      | some restNames =>
          simp [TptpOfficialFofElaboration.decodeVariableName?,
            restDecoded] at decoded
          subst names
          simp only [List.foldr]
          rw [encodeFormula_ex]
          simpa [sourceVariable, sourceToken, targetBinder, a] using
            bind_ex_more_eventuallyExact (.apply lexeme []) rest
              (TptpNamedFofLanguageDef.encodeFormula body)
              (TptpNamedFofLanguageDef.encodeFormula
                (restNames.foldr TptpFofBinderResolution.NamedFormula.ex
                  body))
              (decodeVariableList_bindEx_eventuallyExact rest restNames
                restDecoded body)
    · simp_all [TptpOfficialFofElaboration.decodeVariableName?]
  · contradiction
termination_by sizeOf source

private theorem quantified_all_eventuallyExact
    (binderPatterns body bodyResult result : Pattern)
    (bodyExact : EventuallyExact
      (request "tptp-fof-elab:unit" body) bodyResult)
    (bindersExact : EventuallyExact
      (requestWithBody "tptp-fof-elab:bind-all" binderPatterns bodyResult)
        result) :
    EventuallyExact
      (request "tptp-fof-elab:quantified" <|
        a "tptp92-ast:fof-quantified-formula:alt-1" [
          a "tptp92-ast:fof-quantifier:alt-1", binderPatterns, body])
      result := by
  exact eventuallyExact_of_two_premises _ _ _ _ _ _
    bodyExact bindersExact (by
      intro fuel bodyStep bindersStep
      simp only [request, requestWithBody, a] at bodyStep bindersStep ⊢
      rw [rewriteAt_eq_root_filter, quantifiedRootRules]
      simp [quantifierHeadRules, quantifiedRule, mkRule, congruence,
        request, requestWithBody, a, v, applyRuleUsing,
        matchPatternForRule_eq_syntactic, premisesUsing,
        premiseStepUsing, matchPattern, matchArgs, mergeBindings,
        applyBindingsForRule, applyBindings, bodyStep, bindersStep])

private theorem quantified_ex_eventuallyExact
    (binderPatterns body bodyResult result : Pattern)
    (bodyExact : EventuallyExact
      (request "tptp-fof-elab:unit" body) bodyResult)
    (bindersExact : EventuallyExact
      (requestWithBody "tptp-fof-elab:bind-ex" binderPatterns bodyResult)
        result) :
    EventuallyExact
      (request "tptp-fof-elab:quantified" <|
        a "tptp92-ast:fof-quantified-formula:alt-1" [
          a "tptp92-ast:fof-quantifier:alt-2", binderPatterns, body])
      result := by
  exact eventuallyExact_of_two_premises _ _ _ _ _ _
    bodyExact bindersExact (by
      intro fuel bodyStep bindersStep
      simp only [request, requestWithBody, a] at bodyStep bindersStep ⊢
      rw [rewriteAt_eq_root_filter, quantifiedRootRules]
      simp [quantifierHeadRules, quantifiedRule, mkRule, congruence,
        request, requestWithBody, a, v, applyRuleUsing,
        matchPatternForRule_eq_syntactic, premisesUsing,
        premiseStepUsing, matchPattern, matchArgs, mergeBindings,
        applyBindingsForRule, applyBindings, bodyStep, bindersStep])

private theorem unitary_quantified_route_eventuallyExact
    (source result : Pattern)
    (innerExact : EventuallyExact
      (request "tptp-fof-elab:quantified" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:unitary" <|
        a "tptp92-ast:fof-unitary-formula:alt-1" [source]) result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, unitaryRootRules]
  simp [delegationUnitaryRouteRules, delegateRule, mkRule, congruence,
    request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private theorem decodeQuantifiedFormula_eventuallyExact
    (quantifier binderPatterns body : Pattern)
    (bodySound : ∀ result,
      TptpOfficialFofElaboration.decodeUnitFormula? body = some result →
        EventuallyExact (request "tptp-fof-elab:unit" body)
          (TptpNamedFofLanguageDef.encodeFormula result))
    {result : TptpFofBinderResolution.NamedFormula}
    (decoded :
      TptpOfficialFofElaboration.decodeQuantifiedFormula?
        (a "tptp92-ast:fof-quantified-formula:alt-1" [
          quantifier, binderPatterns, body]) = some result) :
    EventuallyExact
      (request "tptp-fof-elab:quantified" <|
        a "tptp92-ast:fof-quantified-formula:alt-1" [
          quantifier, binderPatterns, body])
      (TptpNamedFofLanguageDef.encodeFormula result) := by
  simp only [a] at decoded
  unfold TptpOfficialFofElaboration.decodeQuantifiedFormula? at decoded
  cases variablesDecoded :
      TptpOfficialFofElaboration.decodeVariableList? binderPatterns with
  | none =>
      simp [variablesDecoded] at decoded
  | some names =>
      cases bodyDecoded :
          TptpOfficialFofElaboration.decodeUnitFormula? body with
      | none =>
          simp [variablesDecoded, bodyDecoded] at decoded
      | some bodyResult =>
          simp [variablesDecoded, bodyDecoded] at decoded
          split at decoded
          · simp at decoded
            subst result
            exact quantified_all_eventuallyExact binderPatterns body
              (TptpNamedFofLanguageDef.encodeFormula bodyResult)
              (TptpNamedFofLanguageDef.encodeFormula
                (names.foldr TptpFofBinderResolution.NamedFormula.all
                  bodyResult))
              (bodySound bodyResult bodyDecoded)
              (decodeVariableList_bindAll_eventuallyExact binderPatterns
                names variablesDecoded bodyResult)
          · simp at decoded
            subst result
            exact quantified_ex_eventuallyExact binderPatterns body
              (TptpNamedFofLanguageDef.encodeFormula bodyResult)
              (TptpNamedFofLanguageDef.encodeFormula
                (names.foldr TptpFofBinderResolution.NamedFormula.ex
                  bodyResult))
              (bodySound bodyResult bodyDecoded)
              (decodeVariableList_bindEx_eventuallyExact binderPatterns
                names variablesDecoded bodyResult)
          · simp_all

private def LogicFormulaAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeLogicFormula? source = some result →
      EventuallyExact (request "tptp-fof-elab:logic" source)
        (TptpNamedFofLanguageDef.encodeFormula result)

private def UnitaryFormulaAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeUnitaryFormula? source = some result →
      EventuallyExact (request "tptp-fof-elab:unitary" source)
        (TptpNamedFofLanguageDef.encodeFormula result)

private def QuantifiedFormulaAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeQuantifiedFormula? source = some result →
      EventuallyExact (request "tptp-fof-elab:quantified" source)
        (TptpNamedFofLanguageDef.encodeFormula result)

private def UnitFormulaAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeUnitFormula? source = some result →
      EventuallyExact (request "tptp-fof-elab:unit" source)
        (TptpNamedFofLanguageDef.encodeFormula result)

private def UnaryFormulaAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeUnaryFormula? source = some result →
      EventuallyExact (request "tptp-fof-elab:unary" source)
        (TptpNamedFofLanguageDef.encodeFormula result)

private def BinaryFormulaAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeBinaryFormula? source = some result →
      EventuallyExact (request "tptp-fof-elab:binary" source)
        (TptpNamedFofLanguageDef.encodeFormula result)

private def BinaryAssocAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeBinaryAssoc? source = some result →
      EventuallyExact (request "tptp-fof-elab:binary-assoc" source)
        (TptpNamedFofLanguageDef.encodeFormula result)

private def AndFormulaAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeAndFormula? source = some result →
      EventuallyExact (request "tptp-fof-elab:and" source)
        (TptpNamedFofLanguageDef.encodeFormula result)

private def OrFormulaAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeOrFormula? source = some result →
      EventuallyExact (request "tptp-fof-elab:or" source)
        (TptpNamedFofLanguageDef.encodeFormula result)

private def BinaryNonassocAgreement (source : Pattern) : Prop :=
  ∀ result,
    TptpOfficialFofElaboration.decodeBinaryNonassoc? source = some result →
      EventuallyExact (request "tptp-fof-elab:binary-nonassoc" source)
        (TptpNamedFofLanguageDef.encodeFormula result)

/-- The independent logical FOF decoder and the authored formula GSLT agree
for every successful logical formula.  The proof follows the decoder's full
mutual recursion across unitary, quantified, unit, unary, binary,
associative, conjunction, disjunction, and non-associative forms. -/
theorem decodeLogicFormula_eventuallyExact (source : Pattern) :
    LogicFormulaAgreement source := by
  apply TptpOfficialFofElaboration.decodeLogicFormula?.induct
    (motive_1 := LogicFormulaAgreement)
    (motive_2 := UnitaryFormulaAgreement)
    (motive_3 := QuantifiedFormulaAgreement)
    (motive_4 := UnitFormulaAgreement)
    (motive_5 := UnaryFormulaAgreement)
    (motive_6 := BinaryFormulaAgreement)
    (motive_7 := BinaryAssocAgreement)
    (motive_8 := AndFormulaAgreement)
    (motive_9 := OrFormulaAgreement)
    (motive_10 := BinaryNonassocAgreement)
  case case1 =>
    intro formula inductionHypothesis result decoded
    exact logic_binary_eventuallyExact formula _
      (inductionHypothesis result (by
        simpa [TptpOfficialFofElaboration.decodeLogicFormula?] using decoded))
  case case2 =>
    intro formula inductionHypothesis result decoded
    exact logic_unary_eventuallyExact formula _
      (inductionHypothesis result (by
        simpa [TptpOfficialFofElaboration.decodeLogicFormula?] using decoded))
  case case3 =>
    intro formula inductionHypothesis result decoded
    exact logic_unitary_eventuallyExact formula _
      (inductionHypothesis result (by
        simpa [TptpOfficialFofElaboration.decodeLogicFormula?] using decoded))
  case case4 =>
    intro term notBinary notUnary notUnitary result decoded
    simp_all [TptpOfficialFofElaboration.decodeLogicFormula?]
  case case5 =>
    intro formula inductionHypothesis result decoded
    exact unitary_quantified_route_eventuallyExact formula _
      (inductionHypothesis result (by
        simpa [TptpOfficialFofElaboration.decodeUnitaryFormula?] using decoded))
  case case6 =>
    intro formula result decoded
    exact unitary_atomic_route_eventuallyExact formula _
      (decodeAtomicFormula_eventuallyExact formula (by
        simpa [TptpOfficialFofElaboration.decodeUnitaryFormula?] using decoded))
  case case7 =>
    intro formula inductionHypothesis result decoded
    exact unitary_logic_route_eventuallyExact formula _
      (inductionHypothesis result (by
        simpa [TptpOfficialFofElaboration.decodeUnitaryFormula?] using decoded))
  case case8 =>
    intro term notQuantified notAtomic notLogic result decoded
    simp_all [TptpOfficialFofElaboration.decodeUnitaryFormula?]
  case case9 =>
    intro quantifier binderPatterns body bodyInduction result decoded
    exact decodeQuantifiedFormula_eventuallyExact quantifier binderPatterns
      body bodyInduction decoded
  case case10 =>
    intro term notQuantified result decoded
    simp_all [TptpOfficialFofElaboration.decodeQuantifiedFormula?]
  case case11 =>
    intro formula inductionHypothesis result decoded
    exact unit_unitary_route_eventuallyExact formula _
      (inductionHypothesis result (by
        simpa [TptpOfficialFofElaboration.decodeUnitFormula?] using decoded))
  case case12 =>
    intro formula inductionHypothesis result decoded
    exact unit_unary_route_eventuallyExact formula _
      (inductionHypothesis result (by
        simpa [TptpOfficialFofElaboration.decodeUnitFormula?] using decoded))
  case case13 =>
    intro term notUnitary notUnary result decoded
    simp_all [TptpOfficialFofElaboration.decodeUnitFormula?]
  case case14 =>
    intro body bodyInduction result decoded
    cases bodyDecoded : TptpOfficialFofElaboration.decodeUnitFormula? body with
    | none =>
        simp [TptpOfficialFofElaboration.decodeUnaryFormula?, bodyDecoded]
          at decoded
    | some bodyResult =>
        simp [TptpOfficialFofElaboration.decodeUnaryFormula?, bodyDecoded]
          at decoded
        subst result
        rw [encodeFormula_not]
        exact unary_not_eventuallyExact body
          (TptpNamedFofLanguageDef.encodeFormula bodyResult)
          (bodyInduction bodyResult bodyDecoded)
  case case15 =>
    intro formula result decoded
    exact unary_infix_route_eventuallyExact formula _
      (decodeInfixUnary_eventuallyExact formula (by
        simpa [TptpOfficialFofElaboration.decodeUnaryFormula?] using decoded))
  case case16 =>
    intro term notNot notInfix result decoded
    simp_all [TptpOfficialFofElaboration.decodeUnaryFormula?]
  case case17 =>
    intro formula inductionHypothesis result decoded
    exact binary_nonassoc_route_eventuallyExact formula _
      (inductionHypothesis result (by
        simpa [TptpOfficialFofElaboration.decodeBinaryFormula?] using decoded))
  case case18 =>
    intro formula inductionHypothesis result decoded
    exact binary_assoc_route_eventuallyExact formula _
      (inductionHypothesis result (by
        simpa [TptpOfficialFofElaboration.decodeBinaryFormula?] using decoded))
  case case19 =>
    intro term notNonassoc notAssoc result decoded
    simp_all [TptpOfficialFofElaboration.decodeBinaryFormula?]
  case case20 =>
    intro formula inductionHypothesis result decoded
    exact binary_assoc_or_route_eventuallyExact formula _
      (inductionHypothesis result (by
        simpa [TptpOfficialFofElaboration.decodeBinaryAssoc?] using decoded))
  case case21 =>
    intro formula inductionHypothesis result decoded
    exact binary_assoc_and_route_eventuallyExact formula _
      (inductionHypothesis result (by
        simpa [TptpOfficialFofElaboration.decodeBinaryAssoc?] using decoded))
  case case22 =>
    intro term notOr notAnd result decoded
    simp_all [TptpOfficialFofElaboration.decodeBinaryAssoc?]
  case case23 =>
    intro left right leftInduction rightInduction result decoded
    cases leftDecoded : TptpOfficialFofElaboration.decodeUnitFormula? left with
    | none =>
        simp [TptpOfficialFofElaboration.decodeAndFormula?, leftDecoded]
          at decoded
    | some leftResult =>
        cases rightDecoded :
            TptpOfficialFofElaboration.decodeUnitFormula? right with
        | none =>
            simp [TptpOfficialFofElaboration.decodeAndFormula?, leftDecoded,
              rightDecoded] at decoded
        | some rightResult =>
            simp [TptpOfficialFofElaboration.decodeAndFormula?, leftDecoded,
              rightDecoded] at decoded
            subst result
            rw [encodeFormula_and]
            exact and_first_eventuallyExact left right
              (TptpNamedFofLanguageDef.encodeFormula leftResult)
              (TptpNamedFofLanguageDef.encodeFormula rightResult)
              (leftInduction leftResult leftDecoded)
              (rightInduction rightResult rightDecoded)
  case case24 =>
    intro left right leftInduction rightInduction result decoded
    cases leftDecoded : TptpOfficialFofElaboration.decodeAndFormula? left with
    | none =>
        simp [TptpOfficialFofElaboration.decodeAndFormula?, leftDecoded]
          at decoded
    | some leftResult =>
        cases rightDecoded :
            TptpOfficialFofElaboration.decodeUnitFormula? right with
        | none =>
            simp [TptpOfficialFofElaboration.decodeAndFormula?, leftDecoded,
              rightDecoded] at decoded
        | some rightResult =>
            simp [TptpOfficialFofElaboration.decodeAndFormula?, leftDecoded,
              rightDecoded] at decoded
            subst result
            rw [encodeFormula_and]
            exact and_more_eventuallyExact left right
              (TptpNamedFofLanguageDef.encodeFormula leftResult)
              (TptpNamedFofLanguageDef.encodeFormula rightResult)
              (leftInduction leftResult leftDecoded)
              (rightInduction rightResult rightDecoded)
  case case25 =>
    intro term notFirst notMore result decoded
    simp_all [TptpOfficialFofElaboration.decodeAndFormula?]
  case case26 =>
    intro left right leftInduction rightInduction result decoded
    cases leftDecoded : TptpOfficialFofElaboration.decodeUnitFormula? left with
    | none =>
        simp [TptpOfficialFofElaboration.decodeOrFormula?, leftDecoded]
          at decoded
    | some leftResult =>
        cases rightDecoded :
            TptpOfficialFofElaboration.decodeUnitFormula? right with
        | none =>
            simp [TptpOfficialFofElaboration.decodeOrFormula?, leftDecoded,
              rightDecoded] at decoded
        | some rightResult =>
            simp [TptpOfficialFofElaboration.decodeOrFormula?, leftDecoded,
              rightDecoded] at decoded
            subst result
            rw [encodeFormula_or]
            exact or_first_eventuallyExact left right
              (TptpNamedFofLanguageDef.encodeFormula leftResult)
              (TptpNamedFofLanguageDef.encodeFormula rightResult)
              (leftInduction leftResult leftDecoded)
              (rightInduction rightResult rightDecoded)
  case case27 =>
    intro left right leftInduction rightInduction result decoded
    cases leftDecoded : TptpOfficialFofElaboration.decodeOrFormula? left with
    | none =>
        simp [TptpOfficialFofElaboration.decodeOrFormula?, leftDecoded]
          at decoded
    | some leftResult =>
        cases rightDecoded :
            TptpOfficialFofElaboration.decodeUnitFormula? right with
        | none =>
            simp [TptpOfficialFofElaboration.decodeOrFormula?, leftDecoded,
              rightDecoded] at decoded
        | some rightResult =>
            simp [TptpOfficialFofElaboration.decodeOrFormula?, leftDecoded,
              rightDecoded] at decoded
            subst result
            rw [encodeFormula_or]
            exact or_more_eventuallyExact left right
              (TptpNamedFofLanguageDef.encodeFormula leftResult)
              (TptpNamedFofLanguageDef.encodeFormula rightResult)
              (leftInduction leftResult leftDecoded)
              (rightInduction rightResult rightDecoded)
  case case28 =>
    intro term notFirst notMore result decoded
    simp_all [TptpOfficialFofElaboration.decodeOrFormula?]
  case case29 =>
    intro left connective right leftInduction rightInduction result decoded
    cases leftDecoded : TptpOfficialFofElaboration.decodeUnitFormula? left with
    | none =>
        simp [TptpOfficialFofElaboration.decodeBinaryNonassoc?, leftDecoded]
          at decoded
    | some leftResult =>
        cases rightDecoded :
            TptpOfficialFofElaboration.decodeUnitFormula? right with
        | none =>
            simp [TptpOfficialFofElaboration.decodeBinaryNonassoc?, leftDecoded,
              rightDecoded] at decoded
        | some rightResult =>
            simp [TptpOfficialFofElaboration.decodeBinaryNonassoc?, leftDecoded,
              rightDecoded] at decoded
            split at decoded
            · simp at decoded
              subst result
              rw [encodeFormula_iff]
              exact nonassoc_iff_eventuallyExact left right
                (TptpNamedFofLanguageDef.encodeFormula leftResult)
                (TptpNamedFofLanguageDef.encodeFormula rightResult)
                (leftInduction leftResult leftDecoded)
                (rightInduction rightResult rightDecoded)
            · simp at decoded
              subst result
              rw [encodeFormula_implies]
              exact nonassoc_implies_eventuallyExact left right
                (TptpNamedFofLanguageDef.encodeFormula leftResult)
                (TptpNamedFofLanguageDef.encodeFormula rightResult)
                (leftInduction leftResult leftDecoded)
                (rightInduction rightResult rightDecoded)
            · simp at decoded
              subst result
              rw [encodeFormula_reverseImplies]
              exact nonassoc_reverse_implies_eventuallyExact left right
                (TptpNamedFofLanguageDef.encodeFormula leftResult)
                (TptpNamedFofLanguageDef.encodeFormula rightResult)
                (leftInduction leftResult leftDecoded)
                (rightInduction rightResult rightDecoded)
            · simp at decoded
              subst result
              rw [encodeFormula_xor]
              exact nonassoc_xor_eventuallyExact left right
                (TptpNamedFofLanguageDef.encodeFormula leftResult)
                (TptpNamedFofLanguageDef.encodeFormula rightResult)
                (leftInduction leftResult leftDecoded)
                (rightInduction rightResult rightDecoded)
            · simp at decoded
              subst result
              rw [encodeFormula_nor]
              exact nonassoc_nor_eventuallyExact left right
                (TptpNamedFofLanguageDef.encodeFormula leftResult)
                (TptpNamedFofLanguageDef.encodeFormula rightResult)
                (leftInduction leftResult leftDecoded)
                (rightInduction rightResult rightDecoded)
            · simp at decoded
              subst result
              rw [encodeFormula_nand]
              exact nonassoc_nand_eventuallyExact left right
                (TptpNamedFofLanguageDef.encodeFormula leftResult)
                (TptpNamedFofLanguageDef.encodeFormula rightResult)
                (leftInduction leftResult leftDecoded)
                (rightInduction rightResult rightDecoded)
            · simp_all
  case case30 =>
    intro term notNonassoc result decoded
    simp_all [TptpOfficialFofElaboration.decodeBinaryNonassoc?]

private theorem comma_conjunction_nil_eventuallyExact (body : Pattern) :
    EventuallyExact
      (requestWithBody "tptp-fof-elab:comma-conjunction"
        (a "tptp92-ast:list:tptp92ast-comma-fof-logic-formula:nil") body)
      body := by
  exact eventuallyExact_of_one_step _ _ (by
    intro fuel
    simp only [requestWithBody, a]
    rw [rewriteAt_eq_root_filter, commaConjunctionRootRules]
    simp [conjunctionTailRules, commaNilRule, commaConsRule, targetBinary,
      mkRule, congruence, request, requestWithBody, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings])

private theorem comma_disjunction_nil_eventuallyExact (body : Pattern) :
    EventuallyExact
      (requestWithBody "tptp-fof-elab:comma-disjunction"
        (a "tptp92-ast:list:tptp92ast-comma-fof-logic-formula:nil") body)
      body := by
  exact eventuallyExact_of_one_step _ _ (by
    intro fuel
    simp only [requestWithBody, a]
    rw [rewriteAt_eq_root_filter, commaDisjunctionRootRules]
    simp [disjunctionTailRules, commaNilRule, commaConsRule, targetBinary,
      mkRule, congruence, request, requestWithBody, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings])

private theorem comma_conjunction_cons_eventuallyExact
    (formula rest body formulaResult result : Pattern)
    (formulaExact : EventuallyExact
      (request "tptp-fof-elab:logic" formula) formulaResult)
    (restExact : EventuallyExact
      (requestWithBody "tptp-fof-elab:comma-conjunction" rest
        (targetBinary "and" body formulaResult)) result) :
    EventuallyExact
      (requestWithBody "tptp-fof-elab:comma-conjunction"
        (a "tptp92-ast:list:tptp92ast-comma-fof-logic-formula:cons" [
          a "tptp92-ast:comma-fof-logic-formula:alt-1" [formula], rest])
        body) result := by
  exact eventuallyExact_of_two_premises _ _ _ _ _ _
    formulaExact restExact (by
      intro fuel formulaStep restStep
      simp only [request, requestWithBody, a] at formulaStep restStep ⊢
      simp only [targetBinary, a] at restStep
      rw [rewriteAt_eq_root_filter, commaConjunctionRootRules]
      simp [conjunctionTailRules, commaNilRule, commaConsRule, targetBinary,
        mkRule, congruence, request, requestWithBody, a, v, applyRuleUsing,
        matchPatternForRule_eq_syntactic, premisesUsing,
        premiseStepUsing, matchPattern, matchArgs, mergeBindings,
        applyBindingsForRule, applyBindings, formulaStep]
      rw [restStep]
      refine ⟨[("result", result), ("formulaResult", formulaResult),
        ("body", body), ("rest", rest), ("formula", formula)], ?_, ?_⟩
      · rfl
      · rfl)

private theorem comma_disjunction_cons_eventuallyExact
    (formula rest body formulaResult result : Pattern)
    (formulaExact : EventuallyExact
      (request "tptp-fof-elab:logic" formula) formulaResult)
    (restExact : EventuallyExact
      (requestWithBody "tptp-fof-elab:comma-disjunction" rest
        (targetBinary "or" body formulaResult)) result) :
    EventuallyExact
      (requestWithBody "tptp-fof-elab:comma-disjunction"
        (a "tptp92-ast:list:tptp92ast-comma-fof-logic-formula:cons" [
          a "tptp92-ast:comma-fof-logic-formula:alt-1" [formula], rest])
        body) result := by
  exact eventuallyExact_of_two_premises _ _ _ _ _ _
    formulaExact restExact (by
      intro fuel formulaStep restStep
      simp only [request, requestWithBody, a] at formulaStep restStep ⊢
      simp only [targetBinary, a] at restStep
      rw [rewriteAt_eq_root_filter, commaDisjunctionRootRules]
      simp [disjunctionTailRules, commaNilRule, commaConsRule, targetBinary,
        mkRule, congruence, request, requestWithBody, a, v, applyRuleUsing,
        matchPatternForRule_eq_syntactic, premisesUsing,
        premiseStepUsing, matchPattern, matchArgs, mergeBindings,
        applyBindingsForRule, applyBindings, formulaStep]
      rw [restStep]
      refine ⟨[("result", result), ("formulaResult", formulaResult),
        ("body", body), ("rest", rest), ("formula", formula)], ?_, ?_⟩
      · rfl
      · rfl)

private theorem tuple_conjunction_empty_eventuallyExact :
    EventuallyExact
      (request "tptp-fof-elab:tuple-conjunction" <|
        a "tptp92-ast:fof-formula-tuple:alt-1")
      (targetNullary "verum") := by
  exact eventuallyExact_of_one_step _ _ (by
    intro fuel
    simp only [request, a]
    rw [rewriteAt_eq_root_filter, tupleConjunctionRootRules]
    simp [conjunctionHeadRules, tupleEmptyRule, tupleNonemptyRule,
      targetNullary, mkRule, congruence, request, requestWithBody,
      a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing, matchPattern, matchArgs,
      mergeBindings, applyBindingsForRule, applyBindings])

private theorem tuple_disjunction_empty_eventuallyExact :
    EventuallyExact
      (request "tptp-fof-elab:tuple-disjunction" <|
        a "tptp92-ast:fof-formula-tuple:alt-1")
      (targetNullary "falsum") := by
  exact eventuallyExact_of_one_step _ _ (by
    intro fuel
    simp only [request, a]
    rw [rewriteAt_eq_root_filter, tupleDisjunctionRootRules]
    simp [disjunctionHeadRules, tupleEmptyRule, tupleNonemptyRule,
      targetNullary, mkRule, congruence, request, requestWithBody,
      a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing, matchPattern, matchArgs,
      mergeBindings, applyBindingsForRule, applyBindings])

private theorem tuple_conjunction_nonempty_eventuallyExact
    (first rest firstResult result : Pattern)
    (firstExact : EventuallyExact
      (request "tptp-fof-elab:logic" first) firstResult)
    (restExact : EventuallyExact
      (requestWithBody "tptp-fof-elab:comma-conjunction" rest firstResult)
        result) :
    EventuallyExact
      (request "tptp-fof-elab:tuple-conjunction" <|
        a "tptp92-ast:fof-formula-tuple:alt-2" [
          a "tptp92-ast:fof-formula-tuple-list:alt-1" [first, rest]])
      result := by
  exact eventuallyExact_of_two_premises _ _ _ _ _ _
    firstExact restExact (by
      intro fuel firstStep restStep
      simp only [request, requestWithBody, a] at firstStep restStep ⊢
      rw [rewriteAt_eq_root_filter, tupleConjunctionRootRules]
      simp [conjunctionHeadRules, tupleEmptyRule, tupleNonemptyRule,
        mkRule, congruence, request, requestWithBody, a, v, applyRuleUsing,
        matchPatternForRule_eq_syntactic, premisesUsing,
        premiseStepUsing, matchPattern, matchArgs, mergeBindings,
        applyBindingsForRule, applyBindings, firstStep, restStep])

private theorem tuple_disjunction_nonempty_eventuallyExact
    (first rest firstResult result : Pattern)
    (firstExact : EventuallyExact
      (request "tptp-fof-elab:logic" first) firstResult)
    (restExact : EventuallyExact
      (requestWithBody "tptp-fof-elab:comma-disjunction" rest firstResult)
        result) :
    EventuallyExact
      (request "tptp-fof-elab:tuple-disjunction" <|
        a "tptp92-ast:fof-formula-tuple:alt-2" [
          a "tptp92-ast:fof-formula-tuple-list:alt-1" [first, rest]])
      result := by
  exact eventuallyExact_of_two_premises _ _ _ _ _ _
    firstExact restExact (by
      intro fuel firstStep restStep
      simp only [request, requestWithBody, a] at firstStep restStep ⊢
      rw [rewriteAt_eq_root_filter, tupleDisjunctionRootRules]
      simp [disjunctionHeadRules, tupleEmptyRule, tupleNonemptyRule,
        mkRule, congruence, request, requestWithBody, a, v, applyRuleUsing,
        matchPatternForRule_eq_syntactic, premisesUsing,
        premiseStepUsing, matchPattern, matchArgs, mergeBindings,
        applyBindingsForRule, applyBindings, firstStep, restStep])

private theorem sequent_main_eventuallyExact
    (left right leftResult rightResult : Pattern)
    (leftExact : EventuallyExact
      (request "tptp-fof-elab:tuple-conjunction" left) leftResult)
    (rightExact : EventuallyExact
      (request "tptp-fof-elab:tuple-disjunction" right) rightResult) :
    EventuallyExact
      (request "tptp-fof-elab:sequent" <|
        a "tptp92-ast:fof-sequent:alt-1" [
          left, a "tptp92-ast:gentzen-arrow:alt-1", right])
      (targetBinary "implies" leftResult rightResult) := by
  exact eventuallyExact_of_two_premises _ _ _ _ _ _
    leftExact rightExact (by
      intro fuel leftStep rightStep
      simp only [request, a] at leftStep rightStep ⊢
      rw [rewriteAt_eq_root_filter, sequentRootRules]
      simp [delegateRule, sequentRule, targetBinary, mkRule, congruence,
        request, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
        premisesUsing, premiseStepUsing, matchPattern, matchArgs,
        mergeBindings, applyBindingsForRule, applyBindings,
        leftStep, rightStep])

private theorem sequent_parenthesized_eventuallyExact
    (source result : Pattern)
    (innerExact : EventuallyExact
      (request "tptp-fof-elab:sequent" source) result) :
    EventuallyExact
      (request "tptp-fof-elab:sequent" <|
        a "tptp92-ast:fof-sequent:alt-2" [source]) result := by
  apply eventuallyExact_of_one_premise _ _ _ _ innerExact
  intro fuel innerStep
  simp only [request, a] at innerStep ⊢
  rw [rewriteAt_eq_root_filter, sequentRootRules]
  simp [delegateRule, sequentRule, mkRule, congruence, request,
    a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, innerStep]

private def conjunctionResult :
    List TptpFofBinderResolution.NamedFormula →
      TptpFofBinderResolution.NamedFormula
  | [] => .verum
  | formula :: formulas =>
      formulas.foldl TptpFofBinderResolution.NamedFormula.and formula

private def disjunctionResult :
    List TptpFofBinderResolution.NamedFormula →
      TptpFofBinderResolution.NamedFormula
  | [] => .falsum
  | formula :: formulas =>
      formulas.foldl TptpFofBinderResolution.NamedFormula.or formula

private theorem decodeCommaConjunction_eventuallyExact
    (source : Pattern)
    (formulas : List TptpFofBinderResolution.NamedFormula)
    (decoded :
      TptpOfficialFofElaboration.decodeCommaFormulaList? source =
        some formulas)
    (body : TptpFofBinderResolution.NamedFormula) :
    EventuallyExact
      (requestWithBody "tptp-fof-elab:comma-conjunction" source
        (TptpNamedFofLanguageDef.encodeFormula body))
      (TptpNamedFofLanguageDef.encodeFormula
        (formulas.foldl TptpFofBinderResolution.NamedFormula.and body)) := by
  unfold TptpOfficialFofElaboration.decodeCommaFormulaList? at decoded
  split at decoded
  · simp at decoded
    subst formulas
    simp only [List.foldl]
    exact comma_conjunction_nil_eventuallyExact
      (TptpNamedFofLanguageDef.encodeFormula body)
  · rename_i formula rest
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨formulaResult, formulaDecoded, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨restResults, restDecoded, resultEquality⟩
    cases resultEquality
    simp only [List.foldl]
    simpa only [encodeFormula_and, a] using
      comma_conjunction_cons_eventuallyExact formula rest
      (TptpNamedFofLanguageDef.encodeFormula body)
      (TptpNamedFofLanguageDef.encodeFormula formulaResult)
      (TptpNamedFofLanguageDef.encodeFormula
        (restResults.foldl TptpFofBinderResolution.NamedFormula.and
          (.and body formulaResult)))
      (decodeLogicFormula_eventuallyExact formula formulaResult formulaDecoded)
      (decodeCommaConjunction_eventuallyExact rest restResults restDecoded
        (.and body formulaResult))
  · contradiction
termination_by sizeOf source

private theorem decodeCommaDisjunction_eventuallyExact
    (source : Pattern)
    (formulas : List TptpFofBinderResolution.NamedFormula)
    (decoded :
      TptpOfficialFofElaboration.decodeCommaFormulaList? source =
        some formulas)
    (body : TptpFofBinderResolution.NamedFormula) :
    EventuallyExact
      (requestWithBody "tptp-fof-elab:comma-disjunction" source
        (TptpNamedFofLanguageDef.encodeFormula body))
      (TptpNamedFofLanguageDef.encodeFormula
        (formulas.foldl TptpFofBinderResolution.NamedFormula.or body)) := by
  unfold TptpOfficialFofElaboration.decodeCommaFormulaList? at decoded
  split at decoded
  · simp at decoded
    subst formulas
    simp only [List.foldl]
    exact comma_disjunction_nil_eventuallyExact
      (TptpNamedFofLanguageDef.encodeFormula body)
  · rename_i formula rest
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨formulaResult, formulaDecoded, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨restResults, restDecoded, resultEquality⟩
    cases resultEquality
    simp only [List.foldl]
    simpa only [encodeFormula_or, a] using
      comma_disjunction_cons_eventuallyExact formula rest
      (TptpNamedFofLanguageDef.encodeFormula body)
      (TptpNamedFofLanguageDef.encodeFormula formulaResult)
      (TptpNamedFofLanguageDef.encodeFormula
        (restResults.foldl TptpFofBinderResolution.NamedFormula.or
          (.or body formulaResult)))
      (decodeLogicFormula_eventuallyExact formula formulaResult formulaDecoded)
      (decodeCommaDisjunction_eventuallyExact rest restResults restDecoded
        (.or body formulaResult))
  · contradiction
termination_by sizeOf source

private theorem decodeFormulaTupleConjunction_eventuallyExact
    (source : Pattern)
    (formulas : List TptpFofBinderResolution.NamedFormula)
    (decoded :
      TptpOfficialFofElaboration.decodeFormulaTuple? source = some formulas) :
    EventuallyExact
      (request "tptp-fof-elab:tuple-conjunction" source)
      (TptpNamedFofLanguageDef.encodeFormula
        (conjunctionResult formulas)) := by
  unfold TptpOfficialFofElaboration.decodeFormulaTuple? at decoded
  split at decoded
  · simp at decoded
    subst formulas
    rw [conjunctionResult, encodeFormula_verum]
    exact tuple_conjunction_empty_eventuallyExact
  · rename_i formulasSource
    unfold TptpOfficialFofElaboration.decodeFormulaTupleList? at decoded
    split at decoded
    · rename_i first rest
      rcases Option.bind_eq_some_iff.mp decoded with
        ⟨firstResult, firstDecoded, remaining⟩
      rcases Option.bind_eq_some_iff.mp remaining with
        ⟨restResults, restDecoded, resultEquality⟩
      cases resultEquality
      rw [conjunctionResult]
      exact tuple_conjunction_nonempty_eventuallyExact first rest
        (TptpNamedFofLanguageDef.encodeFormula firstResult)
        (TptpNamedFofLanguageDef.encodeFormula
          (restResults.foldl TptpFofBinderResolution.NamedFormula.and
            firstResult))
        (decodeLogicFormula_eventuallyExact first firstResult firstDecoded)
        (decodeCommaConjunction_eventuallyExact rest restResults restDecoded
          firstResult)
    · contradiction
  · contradiction

private theorem decodeFormulaTupleDisjunction_eventuallyExact
    (source : Pattern)
    (formulas : List TptpFofBinderResolution.NamedFormula)
    (decoded :
      TptpOfficialFofElaboration.decodeFormulaTuple? source = some formulas) :
    EventuallyExact
      (request "tptp-fof-elab:tuple-disjunction" source)
      (TptpNamedFofLanguageDef.encodeFormula
        (disjunctionResult formulas)) := by
  unfold TptpOfficialFofElaboration.decodeFormulaTuple? at decoded
  split at decoded
  · simp at decoded
    subst formulas
    rw [disjunctionResult, encodeFormula_falsum]
    exact tuple_disjunction_empty_eventuallyExact
  · rename_i formulasSource
    unfold TptpOfficialFofElaboration.decodeFormulaTupleList? at decoded
    split at decoded
    · rename_i first rest
      rcases Option.bind_eq_some_iff.mp decoded with
        ⟨firstResult, firstDecoded, remaining⟩
      rcases Option.bind_eq_some_iff.mp remaining with
        ⟨restResults, restDecoded, resultEquality⟩
      cases resultEquality
      rw [disjunctionResult]
      exact tuple_disjunction_nonempty_eventuallyExact first rest
        (TptpNamedFofLanguageDef.encodeFormula firstResult)
        (TptpNamedFofLanguageDef.encodeFormula
          (restResults.foldl TptpFofBinderResolution.NamedFormula.or
            firstResult))
        (decodeLogicFormula_eventuallyExact first firstResult firstDecoded)
        (decodeCommaDisjunction_eventuallyExact rest restResults restDecoded
          firstResult)
    · contradiction
  · contradiction

private theorem decodeSequent_eventuallyExact
    (source : Pattern) (result : TptpFofBinderResolution.NamedFormula)
    (decoded : TptpOfficialFofElaboration.decodeSequent? source = some result) :
    EventuallyExact (request "tptp-fof-elab:sequent" source)
      (TptpNamedFofLanguageDef.encodeFormula result) := by
  unfold TptpOfficialFofElaboration.decodeSequent? at decoded
  split at decoded
  · rename_i left right
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨leftResults, leftDecoded, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨rightResults, rightDecoded, resultEquality⟩
    cases resultEquality
    rw [encodeFormula_implies]
    exact sequent_main_eventuallyExact left right
      (TptpNamedFofLanguageDef.encodeFormula
        (conjunctionResult leftResults))
      (TptpNamedFofLanguageDef.encodeFormula
        (disjunctionResult rightResults))
      (decodeFormulaTupleConjunction_eventuallyExact left leftResults
        leftDecoded)
      (decodeFormulaTupleDisjunction_eventuallyExact right rightResults
        rightDecoded)
  · rename_i inner
    exact sequent_parenthesized_eventuallyExact inner
      (TptpNamedFofLanguageDef.encodeFormula result)
      (decodeSequent_eventuallyExact inner result decoded)
  · contradiction
termination_by sizeOf source

/-- Every official FOF formula accepted by the independent elaborator is
produced exactly and stably by the authored formula transformation.  The
statement covers both logical formulas and Gentzen sequents. -/
theorem decodeFormula_eventuallyExact
    (source : Pattern) {result : TptpFofBinderResolution.NamedFormula}
    (decoded : TptpOfficialFofElaboration.decodeFormula? source = some result) :
    EventuallyExact (request "tptp-fof-elab:formula" source)
      (TptpNamedFofLanguageDef.encodeFormula result) := by
  unfold TptpOfficialFofElaboration.decodeFormula? at decoded
  split at decoded
  · rename_i inner
    exact formula_logic_eventuallyExact inner _
      (decodeLogicFormula_eventuallyExact inner result decoded)
  · rename_i inner
    exact formula_sequent_eventuallyExact inner _
      (decodeSequent_eventuallyExact inner result decoded)
  · contradiction

/-- For an independently accepted official FOF formula, the authored
transformation cannot produce any result other than the corresponding named
formula, at any contextual fuel. -/
theorem decodeFormula_no_invention
    (source : Pattern) {result : TptpFofBinderResolution.NamedFormula}
    (decoded : TptpOfficialFofElaboration.decodeFormula? source = some result)
    {fuel : Nat} {target : Pattern}
    (member : target ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (request "tptp-fof-elab:formula" source)) :
    target = TptpNamedFofLanguageDef.encodeFormula result := by
  exact (decodeFormula_eventuallyExact source decoded).no_invention fuel member

#print axioms variable_rewriteAt_exact
#print axioms plain_lower_nullary_rewriteAt_exact
#print axioms arguments_one_rewriteAt_exact
#print axioms arguments_more_rewriteAt_exact
#print axioms variable_eventuallyExact
#print axioms plain_lower_nullary_eventuallyExact
#print axioms arguments_one_eventuallyExact
#print axioms arguments_more_eventuallyExact
#print axioms decodeArguments_eventuallyExact
#print axioms decodeTerm_eventuallyExact
#print axioms decodeTerm_no_invention
#print axioms decodeAtomicFormula_eventuallyExact
#print axioms decodeAtomicFormula_no_invention
#print axioms decodeLogicFormula_eventuallyExact
#print axioms decodeFormula_eventuallyExact
#print axioms decodeFormula_no_invention

end Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedFormulaLanguageDef
