import Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationLanguageDef

/-!
# Exact agreement for official CNF serialization

This module connects the independent allocated-CNF serializer to the authored
serialization LanguageDef.  The proof starts with the mutually recursive term
and ordered-term-list fragment.  Every successful reference result has a
finite fuel threshold after which the authored engine has exactly that one
result, preserving order and multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationLanguageDef

abbrev LexicalPlan :=
  Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationPlan.Plan

/-- Decide whether a rule can structurally match an application root. -/
private def rootMatches (label : String) (rule : RewriteRule) : Bool :=
  match rule.left with
  | .apply ruleLabel _ => ruleLabel == label
  | _ => true

private theorem applyRuleUsing_eq_nil_of_root_mismatch
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (recursiveStep : Pattern → List Pattern) (rule : RewriteRule)
    (label : String) (arguments : List Pattern)
    (mismatch : rootMatches label rule = false) :
    applyRuleUsing base lang recursiveStep rule (.apply label arguments) =
      [] := by
  have noMatch : matchPatternForRule lang rule (.apply label arguments) =
      [] := by
    rw [matchPatternForRule_eq_syntactic]
    cases ruleLeft : rule.left with
    | apply ruleLabel ruleArguments =>
        simp only [rootMatches, ruleLeft, beq_eq_false_iff_ne] at mismatch
        simp [matchPattern, mismatch]
    | bvar index => simp [matchPattern]
    | fvar name => simp [rootMatches, ruleLeft] at mismatch
    | lambda binderName body => simp [matchPattern]
    | multiLambda arity binderNames body => simp [matchPattern]
    | subst body replacement => simp [matchPattern]
    | collection collectionType elements rest => simp [matchPattern]
  rw [applyRuleUsing, noMatch]
  rfl

private theorem flatMap_eq_root_filter
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (recursiveStep : Pattern → List Pattern)
    (label : String) (arguments : List Pattern)
    (rules : List RewriteRule) :
    rules.flatMap (fun rule =>
        applyRuleUsing base lang recursiveStep rule (.apply label arguments)) =
      (rules.filter (rootMatches label)).flatMap (fun rule =>
        applyRuleUsing base lang recursiveStep rule
          (.apply label arguments)) := by
  induction rules with
  | nil => rfl
  | cons rule rules inductionHypothesis =>
      simp only [List.flatMap_cons, List.filter_cons]
      cases hRoot : rootMatches label rule with
      | false =>
          rw [applyRuleUsing_eq_nil_of_root_mismatch base lang recursiveStep
            rule label arguments hRoot]
          simp [inductionHypothesis]
      | true => simp [inductionHypothesis]

private theorem rewriteAt_eq_root_filter
    (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat)
    (label : String) (arguments : List Pattern) :
    rewriteAt base lang (fuel + 1) (.apply label arguments) =
      (lang.rewrites.filter (rootMatches label)).flatMap fun rule =>
        applyRuleUsing base lang (rewriteAt base lang fuel) rule
          (.apply label arguments) := by
  rw [rewriteAt]
  exact flatMap_eq_root_filter base lang (rewriteAt base lang fuel)
    label arguments lang.rewrites

private theorem termRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:term") =
      termRewrites := by
  rfl

private theorem termsRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:terms") =
      sequenceRewrites.take 2 := by
  rfl

private theorem argumentsRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:arguments") =
      sequenceRewrites.drop 2 := by
  rfl

private theorem plainTermRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:plain-term") =
      termBuilderRewrites.take 2 := by
  rfl

private theorem definedTermRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:defined-term") =
      (termBuilderRewrites.drop 2).take 2 := by
  rfl

private theorem systemTermRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:system-term") =
      termBuilderRewrites.drop 4 := by
  rfl

private theorem literalRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:literal") =
      literalRewrites := by
  rfl

private theorem atomicRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:atomic") =
      atomicRewrites.take 5 := by
  rfl

private theorem plainAtomicRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:plain-atomic") =
      atomicRewrites.drop 5 := by
  rfl

private theorem clauseRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:clause") =
      clauseRewrites.take 2 := by
  rfl

private theorem clauseTailRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:clause-tail") =
      clauseRewrites.drop 2 := by
  rfl

private theorem entriesRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:entries") =
      batchRewrites.take 3 := by
  rfl

private theorem serializationRootRules :
    language.rewrites.filter
      (rootMatches "tptp-cnf-official-serialization:serialize") =
      batchRewrites.drop 3 := by
  rfl

/-- A request has one stable result once contextual fuel reaches a finite
structural threshold. -/
def EventuallyExact (plan : LexicalPlan) (source result : Pattern) : Prop :=
  ∃ requiredFuel, ∀ fuel, requiredFuel ≤ fuel →
    rewriteAt (engineBasePremises plan.relationEnv) language fuel source =
      [result]

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

/-- Stable exactness excludes invented alternatives at every fuel, including
fuel below the successful threshold. -/
theorem EventuallyExact.no_invention {plan : LexicalPlan}
    {source result target : Pattern}
    (exact : EventuallyExact plan source result) (fuel : Nat)
    (member : target ∈ rewriteAt
      (engineBasePremises plan.relationEnv) language fuel source) :
    target = result := by
  rcases exact with ⟨requiredFuel, exact⟩
  have lifted :=
    mem_rewriteAt_mono_fuel member (Nat.le_max_left fuel requiredFuel)
  rw [exact (max fuel requiredFuel)
    (Nat.le_max_right fuel requiredFuel)] at lifted
  simpa using lifted

def renderTerms : List Pattern → Pattern
  | [] => renderedTermsNil
  | head :: tail => renderedTermsCons head (renderTerms tail)

private theorem eventuallyExact_of_one_step (plan : LexicalPlan)
    (source result : Pattern)
    (step : ∀ fuel,
      rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
        source = [result]) :
    EventuallyExact plan source result := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using step predecessor

private theorem eventuallyExact_of_one_premise (plan : LexicalPlan)
    (premiseSource premiseResult source result : Pattern)
    (premiseExact : EventuallyExact plan premiseSource premiseResult)
    (step : ∀ fuel,
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
          premiseSource = [premiseResult] →
        rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
          source = [result]) :
    EventuallyExact plan source result := by
  rcases premiseExact with ⟨requiredFuel, premiseExact⟩
  refine ⟨requiredFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using
        step predecessor (premiseExact predecessor (by omega))

private theorem eventuallyExact_of_two_premises (plan : LexicalPlan)
    (firstSource firstResult secondSource secondResult source result : Pattern)
    (firstExact : EventuallyExact plan firstSource firstResult)
    (secondExact : EventuallyExact plan secondSource secondResult)
    (step : ∀ fuel,
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
          firstSource = [firstResult] →
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
          secondSource = [secondResult] →
        rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
          source = [result]) :
    EventuallyExact plan source result := by
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

local macro "serialization_root" : tactic =>
  `(tactic|
    simp [rewriteAt, language_rewrites, rewrites, termRewrites,
      sequenceRewrites, termBuilderRewrites, literalRewrites,
      atomicRewrites, clauseRewrites, batchRewrites,
      applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing, mkRule, typed, congruence, relation,
      termVariableRule, originalTermRule, generatedTermRule,
      numericTermRule, distinctObjectTermRule, termsNilRule, termsConsRule,
      argumentsOneRule, argumentsMoreRule, nullaryBuilderRule,
      appliedBuilderRule, plainOriginalTermRule, definedOriginalTermRule,
      systemOriginalTermRule, plainTermNullaryRule, plainTermAppliedRule,
      definedTermNullaryRule, definedTermAppliedRule,
      systemTermNullaryRule, systemTermAppliedRule,
      truthLiteralRule, originalLiteralRule, equalityLiteralRule,
      generatedLiteralRule, atomicRule, atomicNullaryRule,
      plainAtomicNullaryRule, plainAtomicAppliedRule,
      definedAtomicAppliedRule, systemAtomicNullaryRule,
      systemAtomicAppliedRule, plainAtomicBuilderNullaryRule,
      plainAtomicBuilderAppliedRule, verumLiteralRule, falsumLiteralRule,
      originalPositiveLiteralRule, originalNegativeLiteralRule,
      equalLiteralRule, notEqualLiteralRule, definedPositiveLiteralRule,
      definedNegativeLiteralRule,
      emptyClauseRule, clauseStartRule, clauseTailNilRule,
      clauseTailConsRule,
      entriesNilRule, entriesConsRule, entriesPositiveRule,
      entriesNegativeRule, startRule,
      renderedTermsNil, renderedTermsCons, serializeTerm, serializeTerms,
      serializeArguments, plainTermBuilder, definedTermBuilder,
      systemTermBuilder, serializeLiteral, serializeAtomic,
      plainAtomicBuilder, serializeClause, serializeClauseTail,
      serializeEntries, serialize, serializedEntry, serializedEntriesNil,
      serializedEntriesCons, output, quotedAtomicWord, plainFunctor,
      definedFunctorAst, systemFunctorAst,
      plainConstantTerm, plainAppliedTerm, definedConstantTerm,
      definedAppliedTerm, systemConstantTerm, systemAppliedTerm,
      numericTerm, distinctObjectTerm, plainConstantAtomic,
      plainAppliedAtomic, definedAppliedAtomic, systemConstantAtomic,
      systemAppliedAtomic, truthAtomic, equalityAtomic, positiveLiteral,
      negativeLiteral, inequalityLiteral, a, v,
      oneDisjunction, moreDisjunction, cnfFormula,
      formulaRole, annotatedCnf,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

local macro "serialization_root_using_all" : tactic =>
  `(tactic|
    simp only [renderTerms, renderedTermsNil, renderedTermsCons,
      serializeTerm, serializeTerms, serializeArguments, plainTermBuilder,
      definedTermBuilder, systemTermBuilder, serializeLiteral,
      serializeAtomic, plainAtomicBuilder, serializeClause,
      serializeClauseTail, serializeEntries, serialize, serializedEntry,
      serializedEntriesNil, serializedEntriesCons, output, plainFunctor,
      definedFunctorAst, systemFunctorAst, plainConstantTerm,
      plainAppliedTerm, definedConstantTerm, definedAppliedTerm,
      systemConstantTerm, systemAppliedTerm, numericTerm,
      distinctObjectTerm, plainConstantAtomic, plainAppliedAtomic,
      definedAppliedAtomic, systemConstantAtomic, systemAppliedAtomic,
      truthAtomic, equalityAtomic, positiveLiteral, negativeLiteral,
      inequalityLiteral, oneDisjunction, moreDisjunction, cnfFormula,
      formulaRole, annotatedCnf, a] at * <;>
    simp (config := { maxSteps := 1000000 }) [*, rewriteAt,
      language_rewrites, rewrites, termRewrites, sequenceRewrites,
      termBuilderRewrites, literalRewrites, atomicRewrites,
      clauseRewrites, batchRewrites,
      applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing, mkRule, typed, congruence, relation,
      termVariableRule, originalTermRule, generatedTermRule,
      numericTermRule, distinctObjectTermRule, termsNilRule, termsConsRule,
      argumentsOneRule, argumentsMoreRule, nullaryBuilderRule,
      appliedBuilderRule, plainOriginalTermRule, definedOriginalTermRule,
      systemOriginalTermRule, plainTermNullaryRule, plainTermAppliedRule,
      definedTermNullaryRule, definedTermAppliedRule,
      systemTermNullaryRule, systemTermAppliedRule,
      truthLiteralRule, originalLiteralRule, equalityLiteralRule,
      generatedLiteralRule, atomicRule, atomicNullaryRule,
      plainAtomicNullaryRule, plainAtomicAppliedRule,
      definedAtomicAppliedRule, systemAtomicNullaryRule,
      systemAtomicAppliedRule, plainAtomicBuilderNullaryRule,
      plainAtomicBuilderAppliedRule, verumLiteralRule, falsumLiteralRule,
      originalPositiveLiteralRule, originalNegativeLiteralRule,
      equalLiteralRule, notEqualLiteralRule, definedPositiveLiteralRule,
      definedNegativeLiteralRule,
      emptyClauseRule, clauseStartRule, clauseTailNilRule,
      clauseTailConsRule,
      entriesNilRule, entriesConsRule, entriesPositiveRule,
      entriesNegativeRule, startRule,
      renderedTermsNil, renderedTermsCons, serializeTerm, serializeTerms,
      serializeArguments, plainTermBuilder, definedTermBuilder,
      systemTermBuilder, serializeLiteral, serializeAtomic,
      plainAtomicBuilder, serializeClause, serializeClauseTail,
      serializeEntries, serialize, serializedEntry, serializedEntriesNil,
      serializedEntriesCons, output, quotedAtomicWord, plainFunctor,
      definedFunctorAst, systemFunctorAst,
      plainConstantTerm, plainAppliedTerm, definedConstantTerm,
      definedAppliedTerm, systemConstantTerm, systemAppliedTerm,
      numericTerm, distinctObjectTerm, plainConstantAtomic,
      plainAppliedAtomic, definedAppliedAtomic, systemConstantAtomic,
      systemAppliedAtomic, truthAtomic, equalityAtomic, positiveLiteral,
      negativeLiteral, inequalityLiteral, a, v,
      oneDisjunction, moreDisjunction, cnfFormula,
      formulaRole, annotatedCnf,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

theorem terms_nil_rewriteAt_exact (plan : LexicalPlan) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeTerms <| a "tptp-fof-skolem:terms-nil") =
      [renderedTermsNil] := by
  simp only [serializeTerms, a]
  rw [rewriteAt_eq_root_filter, termsRootRules]
  serialization_root

theorem terms_cons_rewriteAt_exact (plan : LexicalPlan)
    (head tail renderedHead renderedTail : Pattern) (fuel : Nat)
    (headExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerm head) = [renderedHead])
    (tailExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerms tail) = [renderedTail]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeTerms <| a "tptp-fof-skolem:terms-cons" [head, tail]) =
      [renderedTermsCons renderedHead renderedTail] := by
  simp only [serializeTerms, a]
  rw [rewriteAt_eq_root_filter, termsRootRules]
  serialization_root_using_all

theorem arguments_one_rewriteAt_exact (plan : LexicalPlan)
    (head : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeArguments <| renderedTermsCons head renderedTermsNil) =
      [a "tptp92-ast:fof-arguments:alt-1" [head]] := by
  simp only [serializeArguments, renderedTermsCons, renderedTermsNil, a]
  rw [rewriteAt_eq_root_filter, argumentsRootRules]
  serialization_root

theorem arguments_more_rewriteAt_exact (plan : LexicalPlan)
    (head tailHead tail renderedTail : Pattern) (fuel : Nat)
    (tailExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeArguments <| renderedTermsCons tailHead tail) =
        [renderedTail]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeArguments <| renderedTermsCons head <|
        renderedTermsCons tailHead tail) =
      [a "tptp92-ast:fof-arguments:alt-2" [head, renderedTail]] := by
  simp only [serializeArguments, renderedTermsCons, a]
  rw [rewriteAt_eq_root_filter, argumentsRootRules]
  serialization_root_using_all

theorem plain_term_nullary_rewriteAt_exact (plan : LexicalPlan)
    (functor : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (plainTermBuilder functor renderedTermsNil) =
      [plainConstantTerm functor] := by
  simp only [plainTermBuilder, renderedTermsNil, a]
  rw [rewriteAt_eq_root_filter, plainTermRootRules]
  serialization_root

theorem plain_term_applied_rewriteAt_exact (plan : LexicalPlan)
    (functor head tail arguments : Pattern) (fuel : Nat)
    (argumentsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeArguments <| renderedTermsCons head tail) = [arguments]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (plainTermBuilder functor <| renderedTermsCons head tail) =
      [plainAppliedTerm functor arguments] := by
  simp only [plainTermBuilder, renderedTermsCons, a]
  rw [rewriteAt_eq_root_filter, plainTermRootRules]
  serialization_root_using_all

theorem defined_term_nullary_rewriteAt_exact (plan : LexicalPlan)
    (functor : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (definedTermBuilder functor renderedTermsNil) =
      [definedConstantTerm functor] := by
  simp only [definedTermBuilder, renderedTermsNil, a]
  rw [rewriteAt_eq_root_filter, definedTermRootRules]
  serialization_root

theorem defined_term_applied_rewriteAt_exact (plan : LexicalPlan)
    (functor head tail arguments : Pattern) (fuel : Nat)
    (argumentsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeArguments <| renderedTermsCons head tail) = [arguments]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (definedTermBuilder functor <| renderedTermsCons head tail) =
      [definedAppliedTerm functor arguments] := by
  simp only [definedTermBuilder, renderedTermsCons, a]
  rw [rewriteAt_eq_root_filter, definedTermRootRules]
  serialization_root_using_all

theorem system_term_nullary_rewriteAt_exact (plan : LexicalPlan)
    (functor : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (systemTermBuilder functor renderedTermsNil) =
      [systemConstantTerm functor] := by
  simp only [systemTermBuilder, renderedTermsNil, a]
  rw [rewriteAt_eq_root_filter, systemTermRootRules]
  serialization_root

theorem system_term_applied_rewriteAt_exact (plan : LexicalPlan)
    (functor head tail arguments : Pattern) (fuel : Nat)
    (argumentsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeArguments <| renderedTermsCons head tail) = [arguments]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (systemTermBuilder functor <| renderedTermsCons head tail) =
      [systemAppliedTerm functor arguments] := by
  simp only [systemTermBuilder, renderedTermsCons, a]
  rw [rewriteAt_eq_root_filter, systemTermRootRules]
  serialization_root_using_all

theorem term_variable_rewriteAt_exact (plan : LexicalPlan)
    (index targetVariable : Pattern)
    (lookup : plan.variableNames.lookup? index = some targetVariable)
    (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeTerm <| a "tptp-fof-skolem:term-variable" [index]) =
      [a "tptp92-ast:fof-term:alt-2" [targetVariable]] := by
  simp only [serializeTerm, a]
  rw [rewriteAt_eq_root_filter, termRootRules]
  have relationRows := plan.variableTuples_of_lookup index
    (.fvar "variable") targetVariable lookup
  have relationRows' :
      plan.relationEnv.tuples
        "tptp-cnf-official-serialization:variable"
        [index, .fvar "variable"] = [[index, targetVariable]] := by
    simpa [TptpFofCnfOfficialSerializationPlan.variableRelation] using
      relationRows
  simp [termRewrites, termVariableRule, originalTermRule,
    generatedTermRule, numericTermRule, distinctObjectTermRule,
    plainOriginalTermRule, definedOriginalTermRule, systemOriginalTermRule,
    mkRule, typed, congruence, relation, serializeTerm, serializeTerms,
    plainTermBuilder, definedTermBuilder, systemTermBuilder,
    quotedAtomicWord, plainFunctor, definedFunctorAst, systemFunctorAst,
    numericTerm, distinctObjectTerm, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings, engineBasePremises, premiseStepWithEnv,
    relationQueryStep, builtinRelationTuples,
    TptpFofCnfOfficialSerializationPlan.variableRelation,
    TptpFofCnfOfficialSerializationPlan.skolemFunctorRelation]
  rw [relationRows']
  simp [matchRelationArgs, matchRelationArgument, Bindings.lookup,
    mergeBindings]

theorem original_plain_term_rewriteAt_exact (plan : LexicalPlan)
    (lexeme sourceTerms renderedTerms target : Pattern) (fuel : Nat)
    (termsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerms sourceTerms) = [renderedTerms])
    (builderExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (plainTermBuilder (plainFunctor lexeme) renderedTerms) = [target]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeTerm <| a "tptp-fof-skolem:term-original" [
        a "tptp-fof-symbol:function-plain" [lexeme], sourceTerms]) =
      [target] := by
  simp only [plainFunctor, quotedAtomicWord, a] at builderExact
  simp only [serializeTerm, a]
  rw [rewriteAt_eq_root_filter, termRootRules]
  serialization_root_using_all

theorem original_defined_term_rewriteAt_exact (plan : LexicalPlan)
    (lexeme sourceTerms renderedTerms target : Pattern) (fuel : Nat)
    (termsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerms sourceTerms) = [renderedTerms])
    (builderExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (definedTermBuilder (definedFunctorAst lexeme) renderedTerms) =
          [target]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeTerm <| a "tptp-fof-skolem:term-original" [
        a "tptp-fof-symbol:function-defined" [lexeme], sourceTerms]) =
      [target] := by
  simp only [serializeTerm, a]
  rw [rewriteAt_eq_root_filter, termRootRules]
  serialization_root_using_all

theorem original_system_term_rewriteAt_exact (plan : LexicalPlan)
    (lexeme sourceTerms renderedTerms target : Pattern) (fuel : Nat)
    (termsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerms sourceTerms) = [renderedTerms])
    (builderExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (systemTermBuilder (systemFunctorAst lexeme) renderedTerms) =
          [target]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeTerm <| a "tptp-fof-skolem:term-original" [
        a "tptp-fof-symbol:function-system" [lexeme], sourceTerms]) =
      [target] := by
  simp only [serializeTerm, a]
  rw [rewriteAt_eq_root_filter, termRootRules]
  serialization_root_using_all

theorem integer_term_rewriteAt_exact (plan : LexicalPlan)
    (lexeme : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeTerm <| a "tptp-fof-skolem:term-original" [
        a "tptp-fof-symbol:function-integer" [lexeme],
        a "tptp-fof-skolem:terms-nil"]) =
      [numericTerm "tptp92-ast:number:alt-1"
        "tptp92-ast:token:integer" lexeme] := by
  simp only [serializeTerm, a]
  rw [rewriteAt_eq_root_filter, termRootRules]
  serialization_root

theorem rational_term_rewriteAt_exact (plan : LexicalPlan)
    (lexeme : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeTerm <| a "tptp-fof-skolem:term-original" [
        a "tptp-fof-symbol:function-rational" [lexeme],
        a "tptp-fof-skolem:terms-nil"]) =
      [numericTerm "tptp92-ast:number:alt-2"
        "tptp92-ast:token:rational" lexeme] := by
  simp only [serializeTerm, a]
  rw [rewriteAt_eq_root_filter, termRootRules]
  serialization_root

theorem real_term_rewriteAt_exact (plan : LexicalPlan)
    (lexeme : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeTerm <| a "tptp-fof-skolem:term-original" [
        a "tptp-fof-symbol:function-real" [lexeme],
        a "tptp-fof-skolem:terms-nil"]) =
      [numericTerm "tptp92-ast:number:alt-3"
        "tptp92-ast:token:real" lexeme] := by
  simp only [serializeTerm, a]
  rw [rewriteAt_eq_root_filter, termRootRules]
  serialization_root

theorem distinct_object_term_rewriteAt_exact (plan : LexicalPlan)
    (lexeme : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeTerm <| a "tptp-fof-skolem:term-original" [
        a "tptp-fof-symbol:function-distinct-object" [lexeme],
        a "tptp-fof-skolem:terms-nil"]) =
      [distinctObjectTerm lexeme] := by
  simp only [serializeTerm, a]
  rw [rewriteAt_eq_root_filter, termRootRules]
  serialization_root

theorem generated_term_rewriteAt_exact (plan : LexicalPlan)
    (identity functor sourceTerms renderedTerms target : Pattern)
    (lookup : plan.skolemFunctors.lookup? identity = some functor)
    (fuel : Nat)
    (termsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerms sourceTerms) = [renderedTerms])
    (builderExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (plainTermBuilder functor renderedTerms) = [target]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeTerm <| a "tptp-fof-skolem:term-generated"
        [identity, sourceTerms]) = [target] := by
  simp only [serializeTerm, a]
  rw [rewriteAt_eq_root_filter, termRootRules]
  simp only [serializeTerms, plainTermBuilder, a] at termsExact builderExact
  have relationRows := plan.skolemFunctorTuples_of_lookup identity
    (.fvar "functor") functor lookup
  have relationRows' :
      plan.relationEnv.tuples
        "tptp-cnf-official-serialization:skolem-functor"
        [identity, .fvar "functor"] = [[identity, functor]] := by
    simpa [TptpFofCnfOfficialSerializationPlan.skolemFunctorRelation] using
      relationRows
  simp (config := { maxSteps := 1000000 }) [*, termRewrites,
    termVariableRule, originalTermRule, generatedTermRule,
    numericTermRule, distinctObjectTermRule, plainOriginalTermRule,
    definedOriginalTermRule, systemOriginalTermRule, mkRule, typed,
    congruence, relation, serializeTerm, serializeTerms, plainTermBuilder,
    definedTermBuilder, systemTermBuilder, quotedAtomicWord, plainFunctor,
    definedFunctorAst, systemFunctorAst, numericTerm, distinctObjectTerm, a, v,
    applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
    premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings, engineBasePremises,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    TptpFofCnfOfficialSerializationPlan.variableRelation,
    TptpFofCnfOfficialSerializationPlan.skolemFunctorRelation]
  simp [matchRelationArgs, mergeBindings,
    matchRelationArgument, Bindings.lookup, termsExact, builderExact]

theorem verum_literal_rewriteAt_exact (plan : LexicalPlan) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeLiteral <| a "tptp-fof-named:ref-verum") =
      [positiveLiteral <| truthAtomic <| a "$true"] := by
  simp only [serializeLiteral, a]
  rw [rewriteAt_eq_root_filter, literalRootRules]
  serialization_root

theorem falsum_literal_rewriteAt_exact (plan : LexicalPlan) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeLiteral <| a "tptp-fof-named:ref-falsum") =
      [positiveLiteral <| truthAtomic <| a "$false"] := by
  simp only [serializeLiteral, a]
  rw [rewriteAt_eq_root_filter, literalRootRules]
  serialization_root

theorem plain_atomic_nullary_rewriteAt_exact (plan : LexicalPlan)
    (lexeme : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeAtomic (a "tptp-fof-symbol:predicate-plain" [lexeme])
        renderedTermsNil) =
      [plainConstantAtomic (plainFunctor lexeme)] := by
  simp only [serializeAtomic, a]
  rw [rewriteAt_eq_root_filter, atomicRootRules]
  serialization_root

theorem plain_atomic_applied_rewriteAt_exact (plan : LexicalPlan)
    (lexeme head tail arguments : Pattern) (fuel : Nat)
    (argumentsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeArguments <| renderedTermsCons head tail) = [arguments]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeAtomic (a "tptp-fof-symbol:predicate-plain" [lexeme])
        (renderedTermsCons head tail)) =
      [plainAppliedAtomic (plainFunctor lexeme) arguments] := by
  simp only [serializeAtomic, a]
  rw [rewriteAt_eq_root_filter, atomicRootRules]
  serialization_root_using_all

theorem defined_atomic_applied_rewriteAt_exact (plan : LexicalPlan)
    (lexeme head tail arguments : Pattern) (fuel : Nat)
    (argumentsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeArguments <| renderedTermsCons head tail) = [arguments]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeAtomic (a "tptp-fof-symbol:predicate-defined" [lexeme])
        (renderedTermsCons head tail)) =
      [definedAppliedAtomic (definedFunctorAst lexeme) arguments] := by
  simp only [serializeAtomic, a]
  rw [rewriteAt_eq_root_filter, atomicRootRules]
  serialization_root_using_all

theorem system_atomic_nullary_rewriteAt_exact (plan : LexicalPlan)
    (lexeme : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeAtomic (a "tptp-fof-symbol:predicate-system" [lexeme])
        renderedTermsNil) =
      [systemConstantAtomic (systemFunctorAst lexeme)] := by
  simp only [serializeAtomic, a]
  rw [rewriteAt_eq_root_filter, atomicRootRules]
  serialization_root

theorem system_atomic_applied_rewriteAt_exact (plan : LexicalPlan)
    (lexeme head tail arguments : Pattern) (fuel : Nat)
    (argumentsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeArguments <| renderedTermsCons head tail) = [arguments]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeAtomic (a "tptp-fof-symbol:predicate-system" [lexeme])
        (renderedTermsCons head tail)) =
      [systemAppliedAtomic (systemFunctorAst lexeme) arguments] := by
  simp only [serializeAtomic, a]
  rw [rewriteAt_eq_root_filter, atomicRootRules]
  serialization_root_using_all

theorem plain_atomic_builder_nullary_rewriteAt_exact (plan : LexicalPlan)
    (functor : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (plainAtomicBuilder functor renderedTermsNil) =
      [plainConstantAtomic functor] := by
  simp only [plainAtomicBuilder, a]
  rw [rewriteAt_eq_root_filter, plainAtomicRootRules]
  serialization_root

theorem plain_atomic_builder_applied_rewriteAt_exact (plan : LexicalPlan)
    (functor head tail arguments : Pattern) (fuel : Nat)
    (argumentsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeArguments <| renderedTermsCons head tail) = [arguments]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (plainAtomicBuilder functor (renderedTermsCons head tail)) =
      [plainAppliedAtomic functor arguments] := by
  simp only [plainAtomicBuilder, a]
  rw [rewriteAt_eq_root_filter, plainAtomicRootRules]
  serialization_root_using_all

theorem original_positive_literal_rewriteAt_exact (plan : LexicalPlan)
    (relationHead sourceTerms renderedTerms atomic : Pattern) (fuel : Nat)
    (termsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerms sourceTerms) = [renderedTerms])
    (atomicExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeAtomic relationHead renderedTerms) = [atomic]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeLiteral <| a "tptp-fof-named:ref-original-positive"
        [relationHead, sourceTerms]) = [positiveLiteral atomic] := by
  simp only [serializeLiteral, a]
  rw [rewriteAt_eq_root_filter, literalRootRules]
  serialization_root_using_all

theorem original_negative_literal_rewriteAt_exact (plan : LexicalPlan)
    (relationHead sourceTerms renderedTerms atomic : Pattern) (fuel : Nat)
    (termsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerms sourceTerms) = [renderedTerms])
    (atomicExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeAtomic relationHead renderedTerms) = [atomic]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeLiteral <| a "tptp-fof-named:ref-original-negative"
        [relationHead, sourceTerms]) = [negativeLiteral atomic] := by
  simp only [serializeLiteral, a]
  rw [rewriteAt_eq_root_filter, literalRootRules]
  serialization_root_using_all

theorem equal_literal_rewriteAt_exact (plan : LexicalPlan)
    (left right renderedLeft renderedRight : Pattern) (fuel : Nat)
    (leftExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerm left) = [renderedLeft])
    (rightExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerm right) = [renderedRight]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeLiteral <| a "tptp-fof-named:ref-equal" [left, right]) =
      [positiveLiteral <| equalityAtomic renderedLeft renderedRight] := by
  simp only [serializeLiteral, a]
  rw [rewriteAt_eq_root_filter, literalRootRules]
  serialization_root_using_all

theorem not_equal_literal_rewriteAt_exact (plan : LexicalPlan)
    (left right renderedLeft renderedRight : Pattern) (fuel : Nat)
    (leftExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerm left) = [renderedLeft])
    (rightExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerm right) = [renderedRight]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeLiteral <| a "tptp-fof-named:ref-not-equal" [left, right]) =
      [inequalityLiteral renderedLeft renderedRight] := by
  simp only [serializeLiteral, a]
  rw [rewriteAt_eq_root_filter, literalRootRules]
  serialization_root_using_all

private theorem generated_literal_rewriteAt_exact (plan : LexicalPlan)
    (sourceHead : String) (wrap : Pattern → Pattern)
    (identity functor sourceTerms renderedTerms atomic : Pattern)
    (lookup : plan.definitionFunctors.lookup? identity = some functor)
    (fuel : Nat)
    (termsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerms sourceTerms) = [renderedTerms])
    (atomicExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (plainAtomicBuilder functor renderedTerms) = [atomic])
    (ruleIdentity :
      (sourceHead = "tptp-fof-named:ref-defined-positive" ∧
        wrap = positiveLiteral) ∨
      (sourceHead = "tptp-fof-named:ref-defined-negative" ∧
        wrap = negativeLiteral)) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeLiteral <| a sourceHead [identity, sourceTerms]) =
      [wrap atomic] := by
  rcases ruleIdentity with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [serializeLiteral, a] <;>
    rw [rewriteAt_eq_root_filter, literalRootRules]
  all_goals
    have relationRows := plan.definitionFunctorTuples_of_lookup identity
      (.fvar "functor") functor lookup
    have relationRows' :
        plan.relationEnv.tuples
          "tptp-cnf-official-serialization:definition-functor"
          [identity, .fvar "functor"] = [[identity, functor]] := by
      simpa [TptpFofCnfOfficialSerializationPlan.definitionFunctorRelation]
        using relationRows
    have termsExact' :
        rewriteAt (engineBasePremises plan.relationEnv) language fuel
          (.apply "tptp-cnf-official-serialization:terms" [sourceTerms]) =
          [renderedTerms] := by
      simpa [serializeTerms, a] using termsExact
    have atomicExact' :
        rewriteAt (engineBasePremises plan.relationEnv) language fuel
          (.apply "tptp-cnf-official-serialization:plain-atomic"
            [functor, renderedTerms]) = [atomic] := by
      simpa [plainAtomicBuilder, a] using atomicExact
    simp (config := { maxSteps := 1000000 }) [*, literalRewrites,
      truthLiteralRule, originalLiteralRule, equalityLiteralRule,
      generatedLiteralRule, verumLiteralRule, falsumLiteralRule,
      originalPositiveLiteralRule, originalNegativeLiteralRule,
      equalLiteralRule, notEqualLiteralRule, definedPositiveLiteralRule,
      definedNegativeLiteralRule, mkRule, typed, congruence, relation,
      serializeLiteral, serializeTerms, plainAtomicBuilder,
      positiveLiteral, negativeLiteral, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings, engineBasePremises, premiseStepWithEnv,
      relationQueryStep, builtinRelationTuples,
      TptpFofCnfOfficialSerializationPlan.definitionFunctorRelation]
    simp [matchRelationArgs, mergeBindings, matchRelationArgument,
      Bindings.lookup, termsExact', atomicExact']

theorem defined_positive_literal_rewriteAt_exact (plan : LexicalPlan)
    (identity functor sourceTerms renderedTerms atomic : Pattern)
    (lookup : plan.definitionFunctors.lookup? identity = some functor)
    (fuel : Nat)
    (termsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerms sourceTerms) = [renderedTerms])
    (atomicExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (plainAtomicBuilder functor renderedTerms) = [atomic]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeLiteral <| a "tptp-fof-named:ref-defined-positive"
        [identity, sourceTerms]) = [positiveLiteral atomic] :=
  generated_literal_rewriteAt_exact plan _ _ identity functor sourceTerms
    renderedTerms atomic lookup fuel termsExact atomicExact (Or.inl ⟨rfl, rfl⟩)

theorem defined_negative_literal_rewriteAt_exact (plan : LexicalPlan)
    (identity functor sourceTerms renderedTerms atomic : Pattern)
    (lookup : plan.definitionFunctors.lookup? identity = some functor)
    (fuel : Nat)
    (termsExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeTerms sourceTerms) = [renderedTerms])
    (atomicExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (plainAtomicBuilder functor renderedTerms) = [atomic]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeLiteral <| a "tptp-fof-named:ref-defined-negative"
        [identity, sourceTerms]) = [negativeLiteral atomic] :=
  generated_literal_rewriteAt_exact plan _ _ identity functor sourceTerms
    renderedTerms atomic lookup fuel termsExact atomicExact (Or.inr ⟨rfl, rfl⟩)

theorem empty_clause_rewriteAt_exact (plan : LexicalPlan) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeClause <| a "tptp-fof-cnf:clause-nil") =
      [cnfFormula <| oneDisjunction <| positiveLiteral <|
        truthAtomic <| a "$false"] := by
  simp only [serializeClause, a]
  rw [rewriteAt_eq_root_filter, clauseRootRules]
  serialization_root

theorem clause_start_rewriteAt_exact (plan : LexicalPlan)
    (head tail literal target : Pattern) (fuel : Nat)
    (literalExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeLiteral head) = [literal])
    (tailExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeClauseTail tail <| oneDisjunction literal) = [target]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeClause <| a "tptp-fof-cnf:clause-cons" [head, tail]) =
      [target] := by
  simp only [serializeClause, a]
  rw [rewriteAt_eq_root_filter, clauseRootRules]
  serialization_root_using_all

theorem clause_tail_nil_rewriteAt_exact (plan : LexicalPlan)
    (accumulator : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeClauseTail (a "tptp-fof-cnf:clause-nil") accumulator) =
      [cnfFormula accumulator] := by
  simp only [serializeClauseTail, a]
  rw [rewriteAt_eq_root_filter, clauseTailRootRules]
  serialization_root

theorem clause_tail_cons_rewriteAt_exact (plan : LexicalPlan)
    (head tail accumulator literal target : Pattern) (fuel : Nat)
    (literalExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeLiteral head) = [literal])
    (tailExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeClauseTail tail <|
          moreDisjunction accumulator literal) = [target]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeClauseTail
        (a "tptp-fof-cnf:clause-cons" [head, tail]) accumulator) =
      [target] := by
  simp only [serializeClauseTail, a]
  rw [rewriteAt_eq_root_filter, clauseTailRootRules]
  serialization_root_using_all

theorem entries_nil_rewriteAt_exact (plan : LexicalPlan)
    (polarity : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeEntries polarity <|
        a "tptp-fof-cnf-allocated:entries-nil") =
      [serializedEntriesNil] := by
  simp only [serializeEntries, a]
  rw [rewriteAt_eq_root_filter, entriesRootRules]
  serialization_root

private theorem entries_cons_rewriteAt_exact (plan : LexicalPlan)
    (polarityConstructor roleLexeme : String)
    (identity nameIndex clause rest name formula renderedRest : Pattern)
    (lookup : plan.clauseNames.lookup? nameIndex = some name)
    (fuel : Nat)
    (clauseExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeClause clause) = [formula])
    (restExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeEntries (a polarityConstructor) rest) = [renderedRest])
    (profile :
      (polarityConstructor = "tptp-fof-batch:positive" ∧
        roleLexeme = "axiom") ∨
      (polarityConstructor = "tptp-fof-batch:negative" ∧
        roleLexeme = "negated_conjecture")) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeEntries (a polarityConstructor) <|
        a "tptp-fof-cnf-allocated:entries-cons" [
          a "tptp-fof-cnf-allocated:clause-entry" [identity,
            a "tptp-fof-cnf-allocated:name" [nameIndex], clause], rest]) =
      [serializedEntriesCons
        (serializedEntry identity name clause <|
          annotatedCnf name (formulaRole <| a roleLexeme) formula)
        renderedRest] := by
  rcases profile with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [serializeEntries, serializeClause, a] at clauseExact restExact ⊢
    rw [rewriteAt_eq_root_filter, entriesRootRules]
  all_goals
    have relationRows := plan.clauseNameTuples_of_lookup nameIndex
      (.fvar "name") name lookup
    have relationRows' :
        plan.relationEnv.tuples
          "tptp-cnf-official-serialization:clause-name"
          [nameIndex, .fvar "name"] = [[nameIndex, name]] := by
      simpa [TptpFofCnfOfficialSerializationPlan.clauseNameRelation] using
        relationRows
    simp (config := { maxSteps := 1000000 }) [*, batchRewrites,
      entriesNilRule, entriesConsRule, entriesPositiveRule,
      entriesNegativeRule, startRule, mkRule, typed, congruence, relation,
      serializeEntries, serializedEntry, serializedEntriesNil,
      serializedEntriesCons, formulaRole, annotatedCnf, a, v,
      applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
      premiseStepUsing, matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings, engineBasePremises,
      premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      TptpFofCnfOfficialSerializationPlan.clauseNameRelation]
    simp (config := { maxSteps := 1000000 }) [matchRelationArgs,
      mergeBindings, matchRelationArgument, serializeClause,
      applyBindings, Bindings.lookup, a,
      clauseExact, restExact]

theorem entries_positive_rewriteAt_exact (plan : LexicalPlan)
    (identity nameIndex clause rest name formula renderedRest : Pattern)
    (lookup : plan.clauseNames.lookup? nameIndex = some name)
    (fuel : Nat)
    (clauseExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeClause clause) = [formula])
    (restExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeEntries (a "tptp-fof-batch:positive") rest) =
          [renderedRest]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeEntries (a "tptp-fof-batch:positive") <|
        a "tptp-fof-cnf-allocated:entries-cons" [
          a "tptp-fof-cnf-allocated:clause-entry" [identity,
            a "tptp-fof-cnf-allocated:name" [nameIndex], clause], rest]) =
      [serializedEntriesCons
        (serializedEntry identity name clause <|
          annotatedCnf name (formulaRole <| a "axiom") formula)
        renderedRest] :=
  entries_cons_rewriteAt_exact plan _ _ identity nameIndex clause rest name
    formula renderedRest lookup fuel clauseExact restExact (Or.inl ⟨rfl, rfl⟩)

theorem entries_negative_rewriteAt_exact (plan : LexicalPlan)
    (identity nameIndex clause rest name formula renderedRest : Pattern)
    (lookup : plan.clauseNames.lookup? nameIndex = some name)
    (fuel : Nat)
    (clauseExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeClause clause) = [formula])
    (restExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeEntries (a "tptp-fof-batch:negative") rest) =
          [renderedRest]) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeEntries (a "tptp-fof-batch:negative") <|
        a "tptp-fof-cnf-allocated:entries-cons" [
          a "tptp-fof-cnf-allocated:clause-entry" [identity,
            a "tptp-fof-cnf-allocated:name" [nameIndex], clause], rest]) =
      [serializedEntriesCons
        (serializedEntry identity name clause <|
          annotatedCnf name (formulaRole <| a "negated_conjecture") formula)
        renderedRest] :=
  entries_cons_rewriteAt_exact plan _ _ identity nameIndex clause rest name
    formula renderedRest lookup fuel clauseExact restExact (Or.inr ⟨rfl, rfl⟩)

theorem serialization_start_rewriteAt_exact (plan : LexicalPlan)
    (occurrence polarity skolem cnf sourceEntries firstName nextName
      allocatedEntries renderedEntries : Pattern)
    (fuel : Nat)
    (entriesExact :
      rewriteAt (engineBasePremises plan.relationEnv) language fuel
        (serializeEntries polarity allocatedEntries) = [renderedEntries]) :
    let source := a "tptp-fof-cnf-allocated:output" [
      a "tptp-fof-batch:output" [occurrence, polarity, skolem, cnf,
        sourceEntries], firstName, nextName, allocatedEntries]
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serialize source) = [output source polarity renderedEntries] := by
  dsimp
  simp only [serialize, a]
  rw [rewriteAt_eq_root_filter, serializationRootRules]
  serialization_root_using_all

def renderArguments (head : Pattern) : List Pattern → Pattern
  | [] => a "tptp92-ast:fof-arguments:alt-1" [head]
  | next :: tail =>
      a "tptp92-ast:fof-arguments:alt-2"
        [head, renderArguments next tail]

theorem semantics_arguments_cons (head : Pattern) (tail : List Pattern) :
    TptpFofCnfOfficialSerializationSemantics.arguments (head :: tail) =
      some (renderArguments head tail) := by
  induction tail generalizing head with
  | nil => rfl
  | cons next tail inductionHypothesis =>
      simp [TptpFofCnfOfficialSerializationSemantics.arguments,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.a,
        renderArguments, inductionHypothesis]

theorem arguments_eventuallyExact (plan : LexicalPlan)
    (head : Pattern) (tail : List Pattern) :
    EventuallyExact plan (serializeArguments <| renderTerms (head :: tail))
      (renderArguments head tail) := by
  induction tail generalizing head with
  | nil =>
      apply eventuallyExact_of_one_step
      intro fuel
      simpa [renderTerms, renderArguments] using
        arguments_one_rewriteAt_exact plan head fuel
  | cons next tail inductionHypothesis =>
      apply eventuallyExact_of_one_premise plan
        (serializeArguments <| renderTerms (next :: tail))
        (renderArguments next tail)
        (serializeArguments <| renderTerms (head :: next :: tail))
        (renderArguments head (next :: tail))
        (inductionHypothesis next)
      intro fuel tailExact
      simpa [renderTerms, renderArguments] using
        arguments_more_rewriteAt_exact plan head next
          (renderTerms tail) (renderArguments next tail) fuel tailExact

theorem plain_builder_eventuallyExact (plan : LexicalPlan)
    (functor : Pattern) (terms : List Pattern) :
    EventuallyExact plan (plainTermBuilder functor (renderTerms terms))
      (TptpFofCnfOfficialSerializationSemantics.plainTerm functor terms) := by
  cases terms with
  | nil =>
      apply eventuallyExact_of_one_step
      intro fuel
      simpa [renderTerms,
        TptpFofCnfOfficialSerializationSemantics.plainTerm,
        TptpFofCnfOfficialSerializationSemantics.arguments,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.plainConstantTerm,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        plain_term_nullary_rewriteAt_exact plan functor fuel
  | cons head tail =>
      apply eventuallyExact_of_one_premise plan
        (serializeArguments <| renderTerms (head :: tail))
        (renderArguments head tail)
        (plainTermBuilder functor <| renderTerms (head :: tail))
        (TptpFofCnfOfficialSerializationSemantics.plainTerm
          functor (head :: tail))
        (arguments_eventuallyExact plan head tail)
      intro fuel argumentsExact
      simpa [renderTerms,
        TptpFofCnfOfficialSerializationSemantics.plainTerm,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.plainAppliedTerm,
        TptpFofCnfOfficialSerializationLanguageDef.a,
        semantics_arguments_cons, renderArguments] using
        plain_term_applied_rewriteAt_exact plan functor head
          (renderTerms tail) (renderArguments head tail) fuel argumentsExact

theorem defined_builder_eventuallyExact (plan : LexicalPlan)
    (functor : Pattern) (terms : List Pattern) :
    EventuallyExact plan (definedTermBuilder functor (renderTerms terms))
      (TptpFofCnfOfficialSerializationSemantics.definedTerm functor terms) := by
  cases terms with
  | nil =>
      apply eventuallyExact_of_one_step
      intro fuel
      simpa [renderTerms,
        TptpFofCnfOfficialSerializationSemantics.definedTerm,
        TptpFofCnfOfficialSerializationSemantics.arguments,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.definedConstantTerm,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        defined_term_nullary_rewriteAt_exact plan functor fuel
  | cons head tail =>
      apply eventuallyExact_of_one_premise plan
        (serializeArguments <| renderTerms (head :: tail))
        (renderArguments head tail)
        (definedTermBuilder functor <| renderTerms (head :: tail))
        (TptpFofCnfOfficialSerializationSemantics.definedTerm
          functor (head :: tail))
        (arguments_eventuallyExact plan head tail)
      intro fuel argumentsExact
      simpa [renderTerms,
        TptpFofCnfOfficialSerializationSemantics.definedTerm,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.definedAppliedTerm,
        TptpFofCnfOfficialSerializationLanguageDef.a,
        semantics_arguments_cons, renderArguments] using
        defined_term_applied_rewriteAt_exact plan functor head
          (renderTerms tail) (renderArguments head tail) fuel argumentsExact

theorem system_builder_eventuallyExact (plan : LexicalPlan)
    (functor : Pattern) (terms : List Pattern) :
    EventuallyExact plan (systemTermBuilder functor (renderTerms terms))
      (TptpFofCnfOfficialSerializationSemantics.systemTerm functor terms) := by
  cases terms with
  | nil =>
      apply eventuallyExact_of_one_step
      intro fuel
      simpa [renderTerms,
        TptpFofCnfOfficialSerializationSemantics.systemTerm,
        TptpFofCnfOfficialSerializationSemantics.arguments,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.systemConstantTerm,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        system_term_nullary_rewriteAt_exact plan functor fuel
  | cons head tail =>
      apply eventuallyExact_of_one_premise plan
        (serializeArguments <| renderTerms (head :: tail))
        (renderArguments head tail)
        (systemTermBuilder functor <| renderTerms (head :: tail))
        (TptpFofCnfOfficialSerializationSemantics.systemTerm
          functor (head :: tail))
        (arguments_eventuallyExact plan head tail)
      intro fuel argumentsExact
      simpa [renderTerms,
        TptpFofCnfOfficialSerializationSemantics.systemTerm,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.systemAppliedTerm,
        TptpFofCnfOfficialSerializationLanguageDef.a,
        semantics_arguments_cons, renderArguments] using
        system_term_applied_rewriteAt_exact plan functor head
          (renderTerms tail) (renderArguments head tail) fuel argumentsExact

theorem plain_atomic_builder_eventuallyExact (plan : LexicalPlan)
    (functor : Pattern) (terms : List Pattern) :
    EventuallyExact plan (plainAtomicBuilder functor (renderTerms terms))
      (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
        functor terms) := by
  cases terms with
  | nil =>
      apply eventuallyExact_of_one_step
      intro fuel
      simpa [renderTerms,
        TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula,
        TptpFofCnfOfficialSerializationSemantics.arguments,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.plainConstantAtomic,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        plain_atomic_builder_nullary_rewriteAt_exact plan functor fuel
  | cons head tail =>
      apply eventuallyExact_of_one_premise plan
        (serializeArguments <| renderTerms (head :: tail))
        (renderArguments head tail)
        (plainAtomicBuilder functor <| renderTerms (head :: tail))
        (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
          functor (head :: tail))
        (arguments_eventuallyExact plan head tail)
      intro fuel argumentsExact
      simpa [renderTerms,
        TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.plainAppliedAtomic,
        TptpFofCnfOfficialSerializationLanguageDef.a,
        semantics_arguments_cons, renderArguments] using
        plain_atomic_builder_applied_rewriteAt_exact plan functor head
          (renderTerms tail) (renderArguments head tail) fuel argumentsExact

theorem plain_atomic_eventuallyExact (plan : LexicalPlan)
    (lexeme : Pattern) (terms : List Pattern) :
    EventuallyExact plan
      (serializeAtomic (a "tptp-fof-symbol:predicate-plain" [lexeme])
        (renderTerms terms))
      (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
        (TptpFofCnfOfficialSerializationSemantics.functorPlain lexeme)
        terms) := by
  cases terms with
  | nil =>
      apply eventuallyExact_of_one_step
      intro fuel
      simpa [renderTerms,
        TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula,
        TptpFofCnfOfficialSerializationSemantics.arguments,
        TptpFofCnfOfficialSerializationSemantics.functorPlain,
        TptpFofCnfOfficialSerializationSemantics.atomicWordPlain,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.plainConstantAtomic,
        TptpFofCnfOfficialSerializationLanguageDef.plainFunctor,
        TptpFofCnfOfficialSerializationLanguageDef.quotedAtomicWord,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        plain_atomic_nullary_rewriteAt_exact plan lexeme fuel
  | cons head tail =>
      apply eventuallyExact_of_one_premise plan
        (serializeArguments <| renderTerms (head :: tail))
        (renderArguments head tail)
        (serializeAtomic (a "tptp-fof-symbol:predicate-plain" [lexeme])
          (renderTerms (head :: tail)))
        (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
          (TptpFofCnfOfficialSerializationSemantics.functorPlain lexeme)
          (head :: tail))
        (arguments_eventuallyExact plan head tail)
      intro fuel argumentsExact
      simpa [renderTerms,
        TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula,
        TptpFofCnfOfficialSerializationSemantics.functorPlain,
        TptpFofCnfOfficialSerializationSemantics.atomicWordPlain,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.plainAppliedAtomic,
        TptpFofCnfOfficialSerializationLanguageDef.plainFunctor,
        TptpFofCnfOfficialSerializationLanguageDef.quotedAtomicWord,
        TptpFofCnfOfficialSerializationLanguageDef.a,
        semantics_arguments_cons, renderArguments] using
        plain_atomic_applied_rewriteAt_exact plan lexeme head
          (renderTerms tail) (renderArguments head tail) fuel argumentsExact

theorem defined_atomic_eventuallyExact (plan : LexicalPlan)
    (lexeme head : Pattern) (tail : List Pattern) :
    EventuallyExact plan
      (serializeAtomic (a "tptp-fof-symbol:predicate-defined" [lexeme])
        (renderTerms (head :: tail)))
      (definedAppliedAtomic
        (TptpFofCnfOfficialSerializationSemantics.definedFunctor lexeme)
        (renderArguments head tail)) := by
  apply eventuallyExact_of_one_premise plan
    (serializeArguments <| renderTerms (head :: tail))
    (renderArguments head tail)
    (serializeAtomic (a "tptp-fof-symbol:predicate-defined" [lexeme])
      (renderTerms (head :: tail)))
    (definedAppliedAtomic
      (TptpFofCnfOfficialSerializationSemantics.definedFunctor lexeme)
      (renderArguments head tail))
    (arguments_eventuallyExact plan head tail)
  intro fuel argumentsExact
  simpa [renderTerms,
    TptpFofCnfOfficialSerializationSemantics.definedFunctor,
    TptpFofCnfOfficialSerializationSemantics.a,
    TptpFofCnfOfficialSerializationLanguageDef.definedFunctorAst,
    TptpFofCnfOfficialSerializationLanguageDef.a] using
    defined_atomic_applied_rewriteAt_exact plan lexeme head
      (renderTerms tail) (renderArguments head tail) fuel argumentsExact

theorem system_atomic_eventuallyExact (plan : LexicalPlan)
    (lexeme : Pattern) (terms : List Pattern) :
    EventuallyExact plan
      (serializeAtomic (a "tptp-fof-symbol:predicate-system" [lexeme])
        (renderTerms terms))
      (TptpFofCnfOfficialSerializationSemantics.systemAtomicFormula
        (TptpFofCnfOfficialSerializationSemantics.systemFunctor lexeme)
        terms) := by
  cases terms with
  | nil =>
      apply eventuallyExact_of_one_step
      intro fuel
      simpa [renderTerms,
        TptpFofCnfOfficialSerializationSemantics.systemAtomicFormula,
        TptpFofCnfOfficialSerializationSemantics.arguments,
        TptpFofCnfOfficialSerializationSemantics.systemFunctor,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.systemConstantAtomic,
        TptpFofCnfOfficialSerializationLanguageDef.systemFunctorAst,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        system_atomic_nullary_rewriteAt_exact plan lexeme fuel
  | cons head tail =>
      apply eventuallyExact_of_one_premise plan
        (serializeArguments <| renderTerms (head :: tail))
        (renderArguments head tail)
        (serializeAtomic (a "tptp-fof-symbol:predicate-system" [lexeme])
          (renderTerms (head :: tail)))
        (TptpFofCnfOfficialSerializationSemantics.systemAtomicFormula
          (TptpFofCnfOfficialSerializationSemantics.systemFunctor lexeme)
          (head :: tail))
        (arguments_eventuallyExact plan head tail)
      intro fuel argumentsExact
      simpa [renderTerms,
        TptpFofCnfOfficialSerializationSemantics.systemAtomicFormula,
        TptpFofCnfOfficialSerializationSemantics.systemFunctor,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.systemAppliedAtomic,
        TptpFofCnfOfficialSerializationLanguageDef.systemFunctorAst,
        TptpFofCnfOfficialSerializationLanguageDef.a,
        semantics_arguments_cons, renderArguments] using
        system_atomic_applied_rewriteAt_exact plan lexeme head
          (renderTerms tail) (renderArguments head tail) fuel argumentsExact

private def TermAgreement (plan : LexicalPlan) (source : Pattern) : Prop :=
  ∀ result,
    TptpFofCnfOfficialSerializationSemantics.serializeTerm? plan source =
      some result →
    EventuallyExact plan (serializeTerm source) result

private def TermsAgreement (plan : LexicalPlan) (source : Pattern) : Prop :=
  ∀ results,
    TptpFofCnfOfficialSerializationSemantics.serializeTerms? plan source =
      some results →
    EventuallyExact plan (serializeTerms source) (renderTerms results) ∧
      (results = [] →
        source = .apply "tptp-fof-skolem:terms-nil" [])

private theorem serialization_mutualAgreement (plan : LexicalPlan) :
    (∀ source, TermAgreement plan source) ∧
      ∀ source, TermsAgreement plan source := by
  apply TptpFofCnfOfficialSerializationSemantics.serializeTerm?.mutual_induct
    (motive_1 := TermAgreement plan)
    (motive_2 := TermsAgreement plan)
  all_goals
    simp_all [TermAgreement, TermsAgreement,
      TptpFofCnfOfficialSerializationSemantics.serializeTerm?,
      TptpFofCnfOfficialSerializationSemantics.serializeTerms?]
  case case1 =>
    intro index result decoded
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨targetVariable, lookup, resultEq⟩
    simp only [Option.some.injEq] at resultEq
    subst result
    apply eventuallyExact_of_one_step
    intro fuel
    simpa [TptpFofCnfOfficialSerializationSemantics.a,
      TptpFofCnfOfficialSerializationLanguageDef.a] using
      term_variable_rewriteAt_exact plan index targetVariable lookup fuel
  case case2 =>
    intro function sourceTerms termsAgreement result decoded
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨terms, termsDecoded, remaining⟩
    split at remaining <;> simp_all
    case h_1 =>
      rename_i _ lexeme
      subst result
      apply eventuallyExact_of_two_premises plan
        (serializeTerms sourceTerms) (renderTerms terms)
        (plainTermBuilder (plainFunctor lexeme) (renderTerms terms))
          (TptpFofCnfOfficialSerializationSemantics.plainTerm
            (TptpFofCnfOfficialSerializationSemantics.functorPlain lexeme)
            terms)
        (serializeTerm <| a "tptp-fof-skolem:term-original" [
          a "tptp-fof-symbol:function-plain" [lexeme], sourceTerms])
          (TptpFofCnfOfficialSerializationSemantics.plainTerm
            (TptpFofCnfOfficialSerializationSemantics.functorPlain lexeme)
            terms)
        termsAgreement.1
        (by simpa [TptpFofCnfOfficialSerializationSemantics.functorPlain,
          TptpFofCnfOfficialSerializationSemantics.atomicWordPlain,
          TptpFofCnfOfficialSerializationSemantics.a,
          TptpFofCnfOfficialSerializationLanguageDef.plainFunctor,
          TptpFofCnfOfficialSerializationLanguageDef.quotedAtomicWord,
          TptpFofCnfOfficialSerializationLanguageDef.a] using
          (plain_builder_eventuallyExact plan (plainFunctor lexeme) terms))
      intro fuel termsExact builderExact
      exact original_plain_term_rewriteAt_exact plan lexeme sourceTerms
        (renderTerms terms)
        (TptpFofCnfOfficialSerializationSemantics.plainTerm
          (TptpFofCnfOfficialSerializationSemantics.functorPlain lexeme)
          terms)
        fuel termsExact builderExact
    case h_2 =>
      rename_i _ lexeme
      subst result
      apply eventuallyExact_of_two_premises plan
        (serializeTerms sourceTerms) (renderTerms terms)
        (definedTermBuilder (definedFunctorAst lexeme) (renderTerms terms))
          (TptpFofCnfOfficialSerializationSemantics.definedTerm
            (TptpFofCnfOfficialSerializationSemantics.definedFunctor lexeme)
            terms)
        (serializeTerm <| a "tptp-fof-skolem:term-original" [
          a "tptp-fof-symbol:function-defined" [lexeme], sourceTerms])
          (TptpFofCnfOfficialSerializationSemantics.definedTerm
            (TptpFofCnfOfficialSerializationSemantics.definedFunctor lexeme)
            terms)
        termsAgreement.1
        (by simpa [TptpFofCnfOfficialSerializationSemantics.definedFunctor,
          TptpFofCnfOfficialSerializationSemantics.a,
          TptpFofCnfOfficialSerializationLanguageDef.definedFunctorAst,
          TptpFofCnfOfficialSerializationLanguageDef.a] using
          (defined_builder_eventuallyExact plan
            (definedFunctorAst lexeme) terms))
      intro fuel termsExact builderExact
      exact original_defined_term_rewriteAt_exact plan lexeme sourceTerms
        (renderTerms terms)
        (TptpFofCnfOfficialSerializationSemantics.definedTerm
          (TptpFofCnfOfficialSerializationSemantics.definedFunctor lexeme)
          terms)
        fuel termsExact builderExact
    case h_3 =>
      rename_i _ lexeme
      subst result
      apply eventuallyExact_of_two_premises plan
        (serializeTerms sourceTerms) (renderTerms terms)
        (systemTermBuilder (systemFunctorAst lexeme) (renderTerms terms))
          (TptpFofCnfOfficialSerializationSemantics.systemTerm
            (TptpFofCnfOfficialSerializationSemantics.systemFunctor lexeme)
            terms)
        (serializeTerm <| a "tptp-fof-skolem:term-original" [
          a "tptp-fof-symbol:function-system" [lexeme], sourceTerms])
          (TptpFofCnfOfficialSerializationSemantics.systemTerm
            (TptpFofCnfOfficialSerializationSemantics.systemFunctor lexeme)
            terms)
        termsAgreement.1
        (by simpa [TptpFofCnfOfficialSerializationSemantics.systemFunctor,
          TptpFofCnfOfficialSerializationSemantics.a,
          TptpFofCnfOfficialSerializationLanguageDef.systemFunctorAst,
          TptpFofCnfOfficialSerializationLanguageDef.a] using
          (system_builder_eventuallyExact plan
            (systemFunctorAst lexeme) terms))
      intro fuel termsExact builderExact
      exact original_system_term_rewriteAt_exact plan lexeme sourceTerms
        (renderTerms terms)
        (TptpFofCnfOfficialSerializationSemantics.systemTerm
          (TptpFofCnfOfficialSerializationSemantics.systemFunctor lexeme)
          terms)
        fuel termsExact builderExact
    case h_4 =>
      rename_i _ lexeme
      rcases remaining with ⟨rfl, resultEq⟩
      subst result
      apply eventuallyExact_of_one_step
      intro fuel
      simpa [TptpFofCnfOfficialSerializationSemantics.numericTerm,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.numericTerm,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        integer_term_rewriteAt_exact plan lexeme fuel
    case h_5 =>
      rename_i _ lexeme
      rcases remaining with ⟨rfl, resultEq⟩
      subst result
      apply eventuallyExact_of_one_step
      intro fuel
      simpa [TptpFofCnfOfficialSerializationSemantics.numericTerm,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.numericTerm,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        rational_term_rewriteAt_exact plan lexeme fuel
    case h_6 =>
      rename_i _ lexeme
      rcases remaining with ⟨rfl, resultEq⟩
      subst result
      apply eventuallyExact_of_one_step
      intro fuel
      simpa [TptpFofCnfOfficialSerializationSemantics.numericTerm,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.numericTerm,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        real_term_rewriteAt_exact plan lexeme fuel
    case h_7 =>
      rename_i _ lexeme
      rcases remaining with ⟨rfl, resultEq⟩
      subst result
      apply eventuallyExact_of_one_step
      intro fuel
      simpa [TptpFofCnfOfficialSerializationSemantics.distinctObjectTerm,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.distinctObjectTerm,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        distinct_object_term_rewriteAt_exact plan lexeme fuel
  case case3 =>
    intro identity sourceTerms termsAgreement result decoded
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨functor, lookup, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨terms, termsDecoded, resultEq⟩
    simp only [Option.some.injEq] at resultEq
    subst result
    apply eventuallyExact_of_two_premises plan
      (serializeTerms sourceTerms) (renderTerms terms)
      (plainTermBuilder functor (renderTerms terms))
        (TptpFofCnfOfficialSerializationSemantics.plainTerm functor terms)
      (serializeTerm <| a "tptp-fof-skolem:term-generated"
        [identity, sourceTerms])
        (TptpFofCnfOfficialSerializationSemantics.plainTerm functor terms)
      (termsAgreement terms termsDecoded).1
      (plain_builder_eventuallyExact plan functor terms)
    intro fuel termsExact builderExact
    exact generated_term_rewriteAt_exact plan identity functor sourceTerms
      (renderTerms terms)
      (TptpFofCnfOfficialSerializationSemantics.plainTerm functor terms)
      lookup fuel termsExact builderExact
  case case5 =>
    apply eventuallyExact_of_one_step
    intro fuel
    simpa [renderTerms,
      TptpFofCnfOfficialSerializationLanguageDef.a] using
      terms_nil_rewriteAt_exact plan fuel
  case case6 =>
    intro head tail headAgreement tailAgreement results decoded
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨renderedHead, headDecoded, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨renderedTail, tailDecoded, resultEq⟩
    simp only [Option.some.injEq] at resultEq
    subst results
    constructor
    · apply eventuallyExact_of_two_premises plan
        (serializeTerm head) renderedHead
        (serializeTerms tail) (renderTerms renderedTail)
        (serializeTerms <| a "tptp-fof-skolem:terms-cons" [head, tail])
        (renderTerms (renderedHead :: renderedTail))
        (headAgreement renderedHead headDecoded)
        (tailAgreement renderedTail tailDecoded).1
      intro fuel headExact tailExact
      simpa [renderTerms] using terms_cons_rewriteAt_exact plan head tail
        renderedHead (renderTerms renderedTail) fuel headExact tailExact
    · simp

theorem serializeTerm_eventuallyExact (plan : LexicalPlan)
    (source result : Pattern)
    (decoded :
      TptpFofCnfOfficialSerializationSemantics.serializeTerm? plan source =
        some result) :
    EventuallyExact plan (serializeTerm source) result :=
  (serialization_mutualAgreement plan).1 source result decoded

theorem serializeTerms_eventuallyExact (plan : LexicalPlan)
    (source : Pattern) (results : List Pattern)
    (decoded :
      TptpFofCnfOfficialSerializationSemantics.serializeTerms? plan source =
        some results) :
    EventuallyExact plan (serializeTerms source) (renderTerms results) :=
  ((serialization_mutualAgreement plan).2 source results decoded).1

theorem serializeTerms_empty_reflects_source (plan : LexicalPlan)
    (source : Pattern)
    (decoded :
      TptpFofCnfOfficialSerializationSemantics.serializeTerms? plan source =
        some []) :
    source = .apply "tptp-fof-skolem:terms-nil" [] :=
  ((serialization_mutualAgreement plan).2 source [] decoded).2 rfl

theorem serializeReference_eventuallyExact (plan : LexicalPlan)
    (source result : Pattern)
    (decoded :
      TptpFofCnfOfficialSerializationSemantics.serializeReference? plan
        source = some result) :
    EventuallyExact plan (serializeLiteral source) result := by
  fun_cases
    TptpFofCnfOfficialSerializationSemantics.serializeReference? plan source <;>
    simp_all [TptpFofCnfOfficialSerializationSemantics.serializeReference?]
  case case1 =>
    subst result
    apply eventuallyExact_of_one_step
    intro fuel
    simpa [TptpFofCnfOfficialSerializationSemantics.positiveLiteral,
      TptpFofCnfOfficialSerializationSemantics.truthAtomicFormula,
      TptpFofCnfOfficialSerializationSemantics.definedFunctor,
      TptpFofCnfOfficialSerializationSemantics.a,
      TptpFofCnfOfficialSerializationLanguageDef.positiveLiteral,
      TptpFofCnfOfficialSerializationLanguageDef.truthAtomic,
      TptpFofCnfOfficialSerializationLanguageDef.definedFunctorAst,
      TptpFofCnfOfficialSerializationLanguageDef.a] using
      verum_literal_rewriteAt_exact plan fuel
  case case2 =>
    subst result
    apply eventuallyExact_of_one_step
    intro fuel
    simpa [TptpFofCnfOfficialSerializationSemantics.positiveLiteral,
      TptpFofCnfOfficialSerializationSemantics.truthAtomicFormula,
      TptpFofCnfOfficialSerializationSemantics.definedFunctor,
      TptpFofCnfOfficialSerializationSemantics.a,
      TptpFofCnfOfficialSerializationLanguageDef.positiveLiteral,
      TptpFofCnfOfficialSerializationLanguageDef.truthAtomic,
      TptpFofCnfOfficialSerializationLanguageDef.definedFunctorAst,
      TptpFofCnfOfficialSerializationLanguageDef.a] using
      falsum_literal_rewriteAt_exact plan fuel
  case case3 =>
    rename_i relationHead sourceTerms
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨terms, termsDecoded, mapped⟩
    rcases Option.map_eq_some_iff.mp mapped with
      ⟨atomic, atomicDecoded, resultEq⟩
    fun_cases
      TptpFofCnfOfficialSerializationSemantics.serializeOriginalAtomic?
        relationHead terms <;>
      simp_all [TptpFofCnfOfficialSerializationSemantics.serializeOriginalAtomic?]
    case case1 =>
      rename_i lexeme
      subst atomic
      subst result
      apply eventuallyExact_of_two_premises plan
        (serializeTerms sourceTerms) (renderTerms terms)
        (serializeAtomic
          (a "tptp-fof-symbol:predicate-plain" [lexeme])
          (renderTerms terms))
          (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
            (TptpFofCnfOfficialSerializationSemantics.functorPlain lexeme)
            terms)
        (serializeLiteral <| a "tptp-fof-named:ref-original-positive" [
          a "tptp-fof-symbol:predicate-plain" [lexeme], sourceTerms])
          (TptpFofCnfOfficialSerializationSemantics.positiveLiteral <|
            TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
              (TptpFofCnfOfficialSerializationSemantics.functorPlain lexeme)
              terms)
        (serializeTerms_eventuallyExact plan sourceTerms terms termsDecoded)
        (plain_atomic_eventuallyExact plan lexeme terms)
      intro fuel termsExact atomicExact
      simpa [TptpFofCnfOfficialSerializationSemantics.positiveLiteral,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.positiveLiteral,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        original_positive_literal_rewriteAt_exact plan
          (a "tptp-fof-symbol:predicate-plain" [lexeme]) sourceTerms
          (renderTerms terms)
          (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
            (TptpFofCnfOfficialSerializationSemantics.functorPlain lexeme)
            terms)
          fuel termsExact atomicExact
    case case2 =>
      rename_i lexeme
      cases terms with
      | nil =>
          simp [TptpFofCnfOfficialSerializationSemantics.definedAtomicFormula?,
            TptpFofCnfOfficialSerializationSemantics.arguments] at atomicDecoded
      | cons head tail =>
          simp [TptpFofCnfOfficialSerializationSemantics.definedAtomicFormula?,
            semantics_arguments_cons] at atomicDecoded
          subst atomic
          subst result
          apply eventuallyExact_of_two_premises plan
            (serializeTerms sourceTerms) (renderTerms (head :: tail))
            (serializeAtomic
              (a "tptp-fof-symbol:predicate-defined" [lexeme])
              (renderTerms (head :: tail)))
              (definedAppliedAtomic
                (TptpFofCnfOfficialSerializationSemantics.definedFunctor lexeme)
                (renderArguments head tail))
            (serializeLiteral <| a "tptp-fof-named:ref-original-positive" [
              a "tptp-fof-symbol:predicate-defined" [lexeme], sourceTerms])
              (TptpFofCnfOfficialSerializationSemantics.positiveLiteral <|
                definedAppliedAtomic
                  (TptpFofCnfOfficialSerializationSemantics.definedFunctor
                    lexeme)
                  (renderArguments head tail))
            (serializeTerms_eventuallyExact plan sourceTerms (head :: tail)
              termsDecoded)
            (defined_atomic_eventuallyExact plan lexeme head tail)
          intro fuel termsExact atomicExact
          simpa [TptpFofCnfOfficialSerializationSemantics.positiveLiteral,
            TptpFofCnfOfficialSerializationSemantics.a,
            TptpFofCnfOfficialSerializationLanguageDef.positiveLiteral,
            TptpFofCnfOfficialSerializationLanguageDef.a] using
            original_positive_literal_rewriteAt_exact plan
              (a "tptp-fof-symbol:predicate-defined" [lexeme]) sourceTerms
              (renderTerms (head :: tail))
              (definedAppliedAtomic
                (TptpFofCnfOfficialSerializationSemantics.definedFunctor lexeme)
                (renderArguments head tail))
              fuel termsExact atomicExact
    case case3 =>
      rename_i lexeme
      subst atomic
      subst result
      apply eventuallyExact_of_two_premises plan
        (serializeTerms sourceTerms) (renderTerms terms)
        (serializeAtomic
          (a "tptp-fof-symbol:predicate-system" [lexeme])
          (renderTerms terms))
          (TptpFofCnfOfficialSerializationSemantics.systemAtomicFormula
            (TptpFofCnfOfficialSerializationSemantics.systemFunctor lexeme)
            terms)
        (serializeLiteral <| a "tptp-fof-named:ref-original-positive" [
          a "tptp-fof-symbol:predicate-system" [lexeme], sourceTerms])
          (TptpFofCnfOfficialSerializationSemantics.positiveLiteral <|
            TptpFofCnfOfficialSerializationSemantics.systemAtomicFormula
              (TptpFofCnfOfficialSerializationSemantics.systemFunctor lexeme)
              terms)
        (serializeTerms_eventuallyExact plan sourceTerms terms termsDecoded)
        (system_atomic_eventuallyExact plan lexeme terms)
      intro fuel termsExact atomicExact
      simpa [TptpFofCnfOfficialSerializationSemantics.positiveLiteral,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.positiveLiteral,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        original_positive_literal_rewriteAt_exact plan
          (a "tptp-fof-symbol:predicate-system" [lexeme]) sourceTerms
          (renderTerms terms)
          (TptpFofCnfOfficialSerializationSemantics.systemAtomicFormula
            (TptpFofCnfOfficialSerializationSemantics.systemFunctor lexeme)
            terms)
          fuel termsExact atomicExact
  case case4 =>
    rename_i relationHead sourceTerms
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨terms, termsDecoded, mapped⟩
    rcases Option.map_eq_some_iff.mp mapped with
      ⟨atomic, atomicDecoded, resultEq⟩
    fun_cases
      TptpFofCnfOfficialSerializationSemantics.serializeOriginalAtomic?
        relationHead terms <;>
      simp_all [TptpFofCnfOfficialSerializationSemantics.serializeOriginalAtomic?]
    case case1 =>
      rename_i lexeme
      subst atomic
      subst result
      apply eventuallyExact_of_two_premises plan
        (serializeTerms sourceTerms) (renderTerms terms)
        (serializeAtomic
          (a "tptp-fof-symbol:predicate-plain" [lexeme])
          (renderTerms terms))
          (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
            (TptpFofCnfOfficialSerializationSemantics.functorPlain lexeme)
            terms)
        (serializeLiteral <| a "tptp-fof-named:ref-original-negative" [
          a "tptp-fof-symbol:predicate-plain" [lexeme], sourceTerms])
          (TptpFofCnfOfficialSerializationSemantics.negativeLiteral <|
            TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
              (TptpFofCnfOfficialSerializationSemantics.functorPlain lexeme)
              terms)
        (serializeTerms_eventuallyExact plan sourceTerms terms termsDecoded)
        (plain_atomic_eventuallyExact plan lexeme terms)
      intro fuel termsExact atomicExact
      simpa [TptpFofCnfOfficialSerializationSemantics.negativeLiteral,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.negativeLiteral,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        original_negative_literal_rewriteAt_exact plan
          (a "tptp-fof-symbol:predicate-plain" [lexeme]) sourceTerms
          (renderTerms terms)
          (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
            (TptpFofCnfOfficialSerializationSemantics.functorPlain lexeme)
            terms)
          fuel termsExact atomicExact
    case case2 =>
      rename_i lexeme
      cases terms with
      | nil =>
          simp [TptpFofCnfOfficialSerializationSemantics.definedAtomicFormula?,
            TptpFofCnfOfficialSerializationSemantics.arguments] at atomicDecoded
      | cons head tail =>
          simp [TptpFofCnfOfficialSerializationSemantics.definedAtomicFormula?,
            semantics_arguments_cons] at atomicDecoded
          subst atomic
          subst result
          apply eventuallyExact_of_two_premises plan
            (serializeTerms sourceTerms) (renderTerms (head :: tail))
            (serializeAtomic
              (a "tptp-fof-symbol:predicate-defined" [lexeme])
              (renderTerms (head :: tail)))
              (definedAppliedAtomic
                (TptpFofCnfOfficialSerializationSemantics.definedFunctor lexeme)
                (renderArguments head tail))
            (serializeLiteral <| a "tptp-fof-named:ref-original-negative" [
              a "tptp-fof-symbol:predicate-defined" [lexeme], sourceTerms])
              (TptpFofCnfOfficialSerializationSemantics.negativeLiteral <|
                definedAppliedAtomic
                  (TptpFofCnfOfficialSerializationSemantics.definedFunctor
                    lexeme)
                  (renderArguments head tail))
            (serializeTerms_eventuallyExact plan sourceTerms (head :: tail)
              termsDecoded)
            (defined_atomic_eventuallyExact plan lexeme head tail)
          intro fuel termsExact atomicExact
          simpa [TptpFofCnfOfficialSerializationSemantics.negativeLiteral,
            TptpFofCnfOfficialSerializationSemantics.a,
            TptpFofCnfOfficialSerializationLanguageDef.negativeLiteral,
            TptpFofCnfOfficialSerializationLanguageDef.a] using
            original_negative_literal_rewriteAt_exact plan
              (a "tptp-fof-symbol:predicate-defined" [lexeme]) sourceTerms
              (renderTerms (head :: tail))
              (definedAppliedAtomic
                (TptpFofCnfOfficialSerializationSemantics.definedFunctor lexeme)
                (renderArguments head tail))
              fuel termsExact atomicExact
    case case3 =>
      rename_i lexeme
      subst atomic
      subst result
      apply eventuallyExact_of_two_premises plan
        (serializeTerms sourceTerms) (renderTerms terms)
        (serializeAtomic
          (a "tptp-fof-symbol:predicate-system" [lexeme])
          (renderTerms terms))
          (TptpFofCnfOfficialSerializationSemantics.systemAtomicFormula
            (TptpFofCnfOfficialSerializationSemantics.systemFunctor lexeme)
            terms)
        (serializeLiteral <| a "tptp-fof-named:ref-original-negative" [
          a "tptp-fof-symbol:predicate-system" [lexeme], sourceTerms])
          (TptpFofCnfOfficialSerializationSemantics.negativeLiteral <|
            TptpFofCnfOfficialSerializationSemantics.systemAtomicFormula
              (TptpFofCnfOfficialSerializationSemantics.systemFunctor lexeme)
              terms)
        (serializeTerms_eventuallyExact plan sourceTerms terms termsDecoded)
        (system_atomic_eventuallyExact plan lexeme terms)
      intro fuel termsExact atomicExact
      simpa [TptpFofCnfOfficialSerializationSemantics.negativeLiteral,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.negativeLiteral,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        original_negative_literal_rewriteAt_exact plan
          (a "tptp-fof-symbol:predicate-system" [lexeme]) sourceTerms
          (renderTerms terms)
          (TptpFofCnfOfficialSerializationSemantics.systemAtomicFormula
            (TptpFofCnfOfficialSerializationSemantics.systemFunctor lexeme)
            terms)
          fuel termsExact atomicExact
  case case5 =>
    rename_i left right
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨renderedLeft, leftDecoded, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨renderedRight, rightDecoded, resultEq⟩
    simp only [Option.some.injEq] at resultEq
    subst result
    apply eventuallyExact_of_two_premises plan
      (serializeTerm left) renderedLeft
      (serializeTerm right) renderedRight
      (serializeLiteral <| a "tptp-fof-named:ref-equal" [left, right])
      (TptpFofCnfOfficialSerializationSemantics.positiveLiteral <|
        TptpFofCnfOfficialSerializationSemantics.equalityAtomicFormula
          renderedLeft renderedRight)
      (serializeTerm_eventuallyExact plan left renderedLeft leftDecoded)
      (serializeTerm_eventuallyExact plan right renderedRight rightDecoded)
    intro fuel leftExact rightExact
    simpa [TptpFofCnfOfficialSerializationSemantics.positiveLiteral,
      TptpFofCnfOfficialSerializationSemantics.equalityAtomicFormula,
      TptpFofCnfOfficialSerializationSemantics.a,
      TptpFofCnfOfficialSerializationLanguageDef.positiveLiteral,
      TptpFofCnfOfficialSerializationLanguageDef.equalityAtomic,
      TptpFofCnfOfficialSerializationLanguageDef.a] using
      equal_literal_rewriteAt_exact plan left right renderedLeft
        renderedRight fuel leftExact rightExact
  case case6 =>
    rename_i left right
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨renderedLeft, leftDecoded, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨renderedRight, rightDecoded, resultEq⟩
    simp only [Option.some.injEq] at resultEq
    subst result
    apply eventuallyExact_of_two_premises plan
      (serializeTerm left) renderedLeft
      (serializeTerm right) renderedRight
      (serializeLiteral <| a "tptp-fof-named:ref-not-equal" [left, right])
      (TptpFofCnfOfficialSerializationSemantics.inequalityLiteral
        renderedLeft renderedRight)
      (serializeTerm_eventuallyExact plan left renderedLeft leftDecoded)
      (serializeTerm_eventuallyExact plan right renderedRight rightDecoded)
    intro fuel leftExact rightExact
    simpa [TptpFofCnfOfficialSerializationSemantics.inequalityLiteral,
      TptpFofCnfOfficialSerializationSemantics.a,
      TptpFofCnfOfficialSerializationLanguageDef.inequalityLiteral,
      TptpFofCnfOfficialSerializationLanguageDef.a] using
      not_equal_literal_rewriteAt_exact plan left right renderedLeft
        renderedRight fuel leftExact rightExact
  case case7 =>
    rename_i identity sourceTerms
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨functor, lookup, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨terms, termsDecoded, resultEq⟩
    simp only [Option.some.injEq] at resultEq
    subst result
    apply eventuallyExact_of_two_premises plan
      (serializeTerms sourceTerms) (renderTerms terms)
      (plainAtomicBuilder functor (renderTerms terms))
        (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
          functor terms)
      (serializeLiteral <| a "tptp-fof-named:ref-defined-positive"
        [identity, sourceTerms])
        (TptpFofCnfOfficialSerializationSemantics.positiveLiteral <|
          TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
            functor terms)
      (serializeTerms_eventuallyExact plan sourceTerms terms termsDecoded)
      (plain_atomic_builder_eventuallyExact plan functor terms)
    intro fuel termsExact atomicExact
    simpa [TptpFofCnfOfficialSerializationSemantics.positiveLiteral,
      TptpFofCnfOfficialSerializationSemantics.a,
      TptpFofCnfOfficialSerializationLanguageDef.positiveLiteral,
      TptpFofCnfOfficialSerializationLanguageDef.a] using
      defined_positive_literal_rewriteAt_exact plan identity functor
        sourceTerms (renderTerms terms)
        (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
          functor terms)
        lookup fuel termsExact atomicExact
  case case8 =>
    rename_i identity sourceTerms
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨functor, lookup, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨terms, termsDecoded, resultEq⟩
    simp only [Option.some.injEq] at resultEq
    subst result
    apply eventuallyExact_of_two_premises plan
      (serializeTerms sourceTerms) (renderTerms terms)
      (plainAtomicBuilder functor (renderTerms terms))
        (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
          functor terms)
      (serializeLiteral <| a "tptp-fof-named:ref-defined-negative"
        [identity, sourceTerms])
        (TptpFofCnfOfficialSerializationSemantics.negativeLiteral <|
          TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
            functor terms)
      (serializeTerms_eventuallyExact plan sourceTerms terms termsDecoded)
      (plain_atomic_builder_eventuallyExact plan functor terms)
    intro fuel termsExact atomicExact
    simpa [TptpFofCnfOfficialSerializationSemantics.negativeLiteral,
      TptpFofCnfOfficialSerializationSemantics.a,
      TptpFofCnfOfficialSerializationLanguageDef.negativeLiteral,
      TptpFofCnfOfficialSerializationLanguageDef.a] using
      defined_negative_literal_rewriteAt_exact plan identity functor
        sourceTerms (renderTerms terms)
        (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
          functor terms)
        lookup fuel termsExact atomicExact

private def ClauseTailAgreement (plan : LexicalPlan)
    (source : Pattern) : Prop :=
  ∀ literals,
    TptpFofCnfOfficialSerializationSemantics.serializeClauseLiterals? plan
      source = some literals →
    ∀ accumulator,
      EventuallyExact plan (serializeClauseTail source accumulator)
        (cnfFormula <| literals.foldl moreDisjunction accumulator)

private theorem clauseTailAgreement (plan : LexicalPlan)
    (source : Pattern) : ClauseTailAgreement plan source := by
  apply TptpFofCnfOfficialSerializationSemantics.serializeClauseLiterals?.induct
    (motive := ClauseTailAgreement plan)
  all_goals
    simp_all [ClauseTailAgreement,
      TptpFofCnfOfficialSerializationSemantics.serializeClauseLiterals?]
  case case1 =>
    intro accumulator
    apply eventuallyExact_of_one_step
    intro fuel
    simpa [TptpFofCnfOfficialSerializationLanguageDef.a] using
      clause_tail_nil_rewriteAt_exact plan accumulator fuel
  case case2 =>
    intro head tail tailAgreement literals decoded accumulator
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨literal, literalDecoded, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨tailLiterals, tailDecoded, resultEq⟩
    simp only [Option.some.injEq] at resultEq
    subst literals
    apply eventuallyExact_of_two_premises plan
      (serializeLiteral head) literal
      (serializeClauseTail tail <| moreDisjunction accumulator literal)
        (cnfFormula <|
          tailLiterals.foldl moreDisjunction
            (moreDisjunction accumulator literal))
      (serializeClauseTail
        (a "tptp-fof-cnf:clause-cons" [head, tail]) accumulator)
        (cnfFormula <|
          (literal :: tailLiterals).foldl moreDisjunction accumulator)
      (serializeReference_eventuallyExact plan head literal literalDecoded)
      (tailAgreement tailLiterals tailDecoded
        (moreDisjunction accumulator literal))
    intro fuel literalExact tailExact
    simpa using clause_tail_cons_rewriteAt_exact plan head tail accumulator
      literal
      (cnfFormula <| tailLiterals.foldl moreDisjunction
        (moreDisjunction accumulator literal))
      fuel literalExact tailExact

theorem serializeClause_eventuallyExact (plan : LexicalPlan)
    (source result : Pattern)
    (decoded :
      TptpFofCnfOfficialSerializationSemantics.serializeClause? plan source =
        some result) :
    EventuallyExact plan (serializeClause source) result := by
  apply
    TptpFofCnfOfficialSerializationSemantics.serializeClauseLiterals?.induct
      (motive := fun source =>
        ∀ result,
          TptpFofCnfOfficialSerializationSemantics.serializeClause? plan
            source = some result →
          EventuallyExact plan (serializeClause source) result)
  all_goals
    simp_all [TptpFofCnfOfficialSerializationSemantics.serializeClause?,
      TptpFofCnfOfficialSerializationSemantics.serializeClauseLiterals?]
  case case1 =>
    apply eventuallyExact_of_one_step
    intro fuel
    simpa [TptpFofCnfOfficialSerializationSemantics.disjunction,
      TptpFofCnfOfficialSerializationSemantics.positiveLiteral,
      TptpFofCnfOfficialSerializationSemantics.truthAtomicFormula,
      TptpFofCnfOfficialSerializationSemantics.definedFunctor,
      TptpFofCnfOfficialSerializationSemantics.a,
      TptpFofCnfOfficialSerializationLanguageDef.cnfFormula,
      TptpFofCnfOfficialSerializationLanguageDef.oneDisjunction,
      TptpFofCnfOfficialSerializationLanguageDef.positiveLiteral,
      TptpFofCnfOfficialSerializationLanguageDef.truthAtomic,
      TptpFofCnfOfficialSerializationLanguageDef.definedFunctorAst,
      TptpFofCnfOfficialSerializationLanguageDef.a] using
      empty_clause_rewriteAt_exact plan fuel
  case case2 =>
    intro head tail _ result decoded
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨literals, literalsDecoded, resultEq⟩
    simp only [Option.some.injEq] at resultEq
    subst result
    rcases Option.bind_eq_some_iff.mp literalsDecoded with
      ⟨literal, literalDecoded, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨tailLiterals, tailDecoded, literalsEq⟩
    simp only [Option.some.injEq] at literalsEq
    subst literals
    apply eventuallyExact_of_two_premises plan
      (serializeLiteral head) literal
      (serializeClauseTail tail <| oneDisjunction literal)
        (cnfFormula <|
          tailLiterals.foldl moreDisjunction (oneDisjunction literal))
      (serializeClause <| a "tptp-fof-cnf:clause-cons" [head, tail])
        (TptpFofCnfOfficialSerializationSemantics.a
          "tptp92-ast:cnf-formula:alt-1" [
            TptpFofCnfOfficialSerializationSemantics.disjunction
              (literal :: tailLiterals)])
      (serializeReference_eventuallyExact plan head literal literalDecoded)
      (clauseTailAgreement plan tail tailLiterals tailDecoded
        (oneDisjunction literal))
    intro fuel literalExact tailExact
    exact clause_start_rewriteAt_exact plan head tail literal
        (cnfFormula <|
          tailLiterals.foldl moreDisjunction (oneDisjunction literal))
        fuel literalExact tailExact

def renderEntry
    (entry :
      TptpFofCnfOfficialSerializationSemantics.SerializedClauseEntry) :
    Pattern :=
  serializedEntry entry.identity entry.name entry.clause entry.annotated

def renderEntries :
    List TptpFofCnfOfficialSerializationSemantics.SerializedClauseEntry →
      Pattern
  | [] => serializedEntriesNil
  | head :: tail => serializedEntriesCons (renderEntry head)
      (renderEntries tail)

private def EntriesAgreement (plan : LexicalPlan) (polarity source : Pattern) :
    Prop :=
  ∀ entries,
    TptpFofCnfOfficialSerializationSemantics.serializeEntries? plan polarity
      source = some entries →
    EventuallyExact plan (serializeEntries polarity source)
      (renderEntries entries)

private theorem entriesAgreement (plan : LexicalPlan) (polarity source : Pattern) :
    EntriesAgreement plan polarity source := by
  apply TptpFofCnfOfficialSerializationSemantics.serializeEntries?.induct
    (motive := EntriesAgreement plan polarity)
  all_goals
    simp_all [EntriesAgreement,
      TptpFofCnfOfficialSerializationSemantics.serializeEntries?]
  case case1 =>
    apply eventuallyExact_of_one_step
    intro fuel
    simpa [renderEntries,
      TptpFofCnfOfficialSerializationLanguageDef.a] using
      entries_nil_rewriteAt_exact plan polarity fuel
  case case2 =>
    intro identity nameIndex clause rest restAgreement entries decoded
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨name, nameLookup, afterName⟩
    rcases Option.bind_eq_some_iff.mp afterName with
      ⟨role, roleDecoded, afterRole⟩
    rcases Option.bind_eq_some_iff.mp afterRole with
      ⟨formula, clauseDecoded, afterClause⟩
    rcases Option.bind_eq_some_iff.mp afterClause with
      ⟨tailEntries, tailDecoded, resultEq⟩
    simp only [Option.some.injEq] at resultEq
    fun_cases TptpFofCnfOfficialSerializationSemantics.role? polarity <;>
      simp_all [TptpFofCnfOfficialSerializationSemantics.role?]
    case case1 =>
      subst role
      subst entries
      apply eventuallyExact_of_two_premises plan
        (serializeClause clause) formula
        (serializeEntries (a "tptp-fof-batch:positive") rest)
          (renderEntries tailEntries)
        (serializeEntries (a "tptp-fof-batch:positive") <|
          a "tptp-fof-cnf-allocated:entries-cons" [
            a "tptp-fof-cnf-allocated:clause-entry" [identity,
              a "tptp-fof-cnf-allocated:name" [nameIndex], clause], rest])
          (renderEntries (⟨identity, name, clause,
            TptpFofCnfOfficialSerializationSemantics.annotatedCnf name
              (formulaRole <| a "axiom") formula⟩ :: tailEntries))
        (serializeClause_eventuallyExact plan clause formula clauseDecoded)
        restAgreement
      intro fuel clauseExact restExact
      simpa [renderEntries, renderEntry,
        TptpFofCnfOfficialSerializationSemantics.annotatedCnf,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.annotatedCnf,
        TptpFofCnfOfficialSerializationLanguageDef.formulaRole,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        entries_positive_rewriteAt_exact plan identity nameIndex clause rest
          name formula (renderEntries tailEntries) nameLookup fuel
          clauseExact restExact
    case case2 =>
      subst role
      subst entries
      apply eventuallyExact_of_two_premises plan
        (serializeClause clause) formula
        (serializeEntries (a "tptp-fof-batch:negative") rest)
          (renderEntries tailEntries)
        (serializeEntries (a "tptp-fof-batch:negative") <|
          a "tptp-fof-cnf-allocated:entries-cons" [
            a "tptp-fof-cnf-allocated:clause-entry" [identity,
              a "tptp-fof-cnf-allocated:name" [nameIndex], clause], rest])
          (renderEntries (⟨identity, name, clause,
            TptpFofCnfOfficialSerializationSemantics.annotatedCnf name
              (formulaRole <| a "negated_conjecture") formula⟩ ::
                tailEntries))
        (serializeClause_eventuallyExact plan clause formula clauseDecoded)
        restAgreement
      intro fuel clauseExact restExact
      simpa [renderEntries, renderEntry,
        TptpFofCnfOfficialSerializationSemantics.annotatedCnf,
        TptpFofCnfOfficialSerializationSemantics.a,
        TptpFofCnfOfficialSerializationLanguageDef.annotatedCnf,
        TptpFofCnfOfficialSerializationLanguageDef.formulaRole,
        TptpFofCnfOfficialSerializationLanguageDef.a] using
        entries_negative_rewriteAt_exact plan identity nameIndex clause rest
          name formula (renderEntries tailEntries) nameLookup fuel
          clauseExact restExact

def renderResult
    (result : TptpFofCnfOfficialSerializationSemantics.Result) : Pattern :=
  output result.source result.polarity (renderEntries result.entries)

theorem serialize_eventuallyExact (plan : LexicalPlan)
    (source : Pattern)
    (result : TptpFofCnfOfficialSerializationSemantics.Result)
    (decoded :
      TptpFofCnfOfficialSerializationSemantics.serialize? plan source =
        some result) :
    EventuallyExact plan (serialize source) (renderResult result) := by
  fun_cases TptpFofCnfOfficialSerializationSemantics.serialize? plan source <;>
    simp_all [TptpFofCnfOfficialSerializationSemantics.serialize?]
  case case2 =>
    rename_i firstName nextName allocatedEntries occurrence polarity skolem
      cnf sourceEntries valid
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨entries, entriesDecoded, resultEq⟩
    simp only [Option.some.injEq] at resultEq
    subst result
    let source := a "tptp-fof-cnf-allocated:output" [
      a "tptp-fof-batch:output" [occurrence, polarity, skolem, cnf,
        sourceEntries], firstName, nextName, allocatedEntries]
    apply eventuallyExact_of_one_premise plan
      (serializeEntries polarity allocatedEntries) (renderEntries entries)
      (serialize source)
      (renderResult {
        source := source
        polarity := polarity
        entries := entries })
      (entriesAgreement plan polarity allocatedEntries entries entriesDecoded)
    intro fuel entriesExact
    simpa [source, renderResult] using
      serialization_start_rewriteAt_exact plan occurrence polarity skolem cnf
        sourceEntries firstName nextName allocatedEntries
        (renderEntries entries) fuel entriesExact

/-! ## Whole-program positive and negative controls -/

namespace Canary

def plan : LexicalPlan :=
  TptpFofCnfOfficialSerializationPlan.Canary.plan

def sourceBatch : Pattern :=
  a "tptp-fof-batch:output" [a "source-occurrence",
    a "tptp-fof-batch:positive", a "skolem-state", a "cnf-state",
    a "source-entries"]

def allocatedSource : Pattern :=
  TptpFofCnfAllocatedBatchLanguageDef.allocatedOutput sourceBatch
    (TptpFofCnfOfficialSerializationPlan.index 7)
    (TptpFofCnfOfficialSerializationPlan.index 8)
    (TptpFofCnfAllocatedBatchLanguageDef.entriesCons
      (TptpFofCnfAllocatedBatchLanguageDef.allocatedClauseEntry
        (a "clause-identity") 7
        (a "tptp-fof-cnf:clause-nil"))
      TptpFofCnfAllocatedBatchLanguageDef.entriesNil)

def renderedFormula : Pattern :=
  a "tptp92-ast:cnf-formula:alt-1" [
    a "tptp92-ast:cnf-disjunction:alt-1" [
      TptpFofCnfOfficialSerializationSemantics.positiveLiteral
        (TptpFofCnfOfficialSerializationSemantics.truthAtomicFormula
          "$false")]]

def expectedResult : TptpFofCnfOfficialSerializationSemantics.Result where
  source := allocatedSource
  polarity := a "tptp-fof-batch:positive"
  entries := [{
    identity := a "clause-identity"
    name := TptpFofCnfOfficialSerializationPlan.quotedName "cetta_cnf_7"
    clause := a "tptp-fof-cnf:clause-nil"
    annotated := TptpFofCnfOfficialSerializationSemantics.annotatedCnf
      (TptpFofCnfOfficialSerializationPlan.quotedName "cetta_cnf_7")
      (formulaRole <| a "axiom") renderedFormula }]

theorem independent_whole_batch_exact :
    TptpFofCnfOfficialSerializationSemantics.serialize? plan
      allocatedSource = some expectedResult := by
  have valid : plan.valid = true :=
    TptpFofCnfOfficialSerializationPlan.Canary.plan_is_valid
  simp only [TptpFofCnfOfficialSerializationSemantics.serialize?]
  rw [valid]
  rfl

theorem authored_whole_batch_eventually_exact :
    EventuallyExact plan (serialize allocatedSource)
      (renderResult expectedResult) :=
  serialize_eventuallyExact plan allocatedSource expectedResult
    independent_whole_batch_exact

def missingVariable : Pattern :=
  a "tptp-fof-skolem:term-variable"
    [TptpFofCnfOfficialSerializationPlan.index 99]

theorem missing_variable_has_no_authored_result (fuel : Nat) :
    rewriteAt (engineBasePremises plan.relationEnv) language (fuel + 1)
      (serializeTerm missingVariable) = [] := by
  simp only [missingVariable, serializeTerm, a]
  rw [rewriteAt_eq_root_filter, termRootRules]
  have missing : plan.variableNames.lookup?
      (TptpFofCnfOfficialSerializationPlan.index 99) = none := by
    rfl
  have relationRows :=
    TptpFofCnfOfficialSerializationPlan.Plan.variableTuples_of_missing
      plan (TptpFofCnfOfficialSerializationPlan.index 99)
        (.fvar "variable") missing
  have relationRows' :
      plan.relationEnv.tuples
        "tptp-cnf-official-serialization:variable"
        [TptpFofCnfOfficialSerializationPlan.index 99,
          .fvar "variable"] = [] := by
    simpa [TptpFofCnfOfficialSerializationPlan.variableRelation] using
      relationRows
  simp [termRewrites, termVariableRule, originalTermRule,
    generatedTermRule, numericTermRule, distinctObjectTermRule,
    plainOriginalTermRule, definedOriginalTermRule, systemOriginalTermRule,
    mkRule, typed, congruence, relation, serializeTerm, serializeTerms,
    plainTermBuilder, definedTermBuilder, systemTermBuilder,
    quotedAtomicWord, plainFunctor, definedFunctorAst, systemFunctorAst,
    numericTerm, distinctObjectTerm, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings, engineBasePremises, premiseStepWithEnv,
    relationQueryStep, builtinRelationTuples,
    TptpFofCnfOfficialSerializationPlan.variableRelation,
    TptpFofCnfOfficialSerializationPlan.skolemFunctorRelation,
    relationRows']

end Canary

#print axioms terms_nil_rewriteAt_exact
#print axioms generated_term_rewriteAt_exact
#print axioms arguments_eventuallyExact
#print axioms serializeTerm_eventuallyExact
#print axioms serializeTerms_eventuallyExact
#print axioms serializeReference_eventuallyExact
#print axioms serializeClause_eventuallyExact
#print axioms serialize_eventuallyExact
#print axioms Canary.independent_whole_batch_exact
#print axioms Canary.authored_whole_batch_eventually_exact
#print axioms Canary.missing_variable_has_no_authored_result

end Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationAgreement
