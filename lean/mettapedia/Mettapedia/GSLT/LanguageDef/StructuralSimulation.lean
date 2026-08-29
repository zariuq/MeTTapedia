import Mettapedia.GSLT.LanguageDef.MapLanguageDef
import Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Simulation of contextual reduction along structural presentation maps

One-step operational reduction of a `LanguageDef` is preserved along
structural presentation morphisms.  The center is a fuel-indexed simultaneous
induction over the relational contextual engine (`StepAt` / `PremisesAt` /
`PremiseAt`): if a base premise evaluator maps source results along a symbol action
with injective constructor part, every bounded contextual derivation maps to
a bounded derivation of the image presentation at the same fuel
(`stepAt_mapLanguageDef`).  Together with monotonicity in the rule set
(`stepAt_of_rewrites_mem`) this yields the headline simulation theorem
`step_map_of_structuralMorphism`: a source step is carried by a
`StructuralMorphism` whose constructor action is injective and whose base
premise evaluators satisfy the stated simulation laws.

At the derived-semantics level, the default evaluator
`engineBasePremises RelationEnv.empty` is proved to map source results
(`engineBasePremises_empty_maps_results`) under one extra naming condition:
the symbol action must fix the builtin relation name `"eq"`.  This condition
is genuinely required — `builtinRelationTuples` recognises the literal name
`"eq"`, so an action that renames it silences the builtin equality relation
in the image (negative canary
`engineBasePremises_empty_mapping_requires_eq_name`).  Freshness
premises map unconditionally because `mapPattern` preserves free
variable names.  The corollary `langReduces_map_of_structuralMorphism`
transports the default reduction relation of the OSLF synthesis layer.

Simulation is one-way: the target may have additional rules, so mapped
patterns can step in the target without any source counterpart
(`simulation_is_one_way`).  Constructor injectivity is load-bearing:
`StructuralRenamingSemantics` states `matchPattern_equivariance` only for
injective actions and contains no counterexample for the non-injective case,
so `matchPattern_equivariance_requires_injectivity` below records one.
-/

namespace Mettapedia.GSLT.LanguageDef.StructuralSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics

/-! ## Mapping results of base premise evaluators -/

/-- A change-of-base square for non-contextual premise evidence along a
symbol action: every result produced by `base` at a source presentation is
produced, in mapped form, by `base'` at the image presentation.  Unlike the
exact equality law of the coproduct module, this is a one-directional
membership law, so the target evaluator may produce additional results. -/
def MapsBasePremiseResults (symbols : PresentationSymbols)
    (base base' : BasePremiseEvaluator) : Prop :=
  ∀ (language : LanguageDef) (bindings : Bindings) (premise : Premise)
    (result : Bindings),
    result ∈ base language bindings premise →
      mapBindings symbols result ∈
        base' (mapLanguageDef symbols language) (mapBindings symbols bindings)
          (mapPremise symbols premise)

/-! ## Mapping bounded contextual reduction -/

/-- Bounded contextual derivations map along a symbol action with injective
constructor part and a base-result mapping law, at the same contextual
fuel.  This is the simultaneous induction over `StepAt`, `PremisesAt`, and
`PremiseAt`: the congruence case recurses through the step relation at the
same fuel index, so the fuel induction carries all three statements. -/
theorem stepAt_mapLanguageDef
    {symbols : PresentationSymbols} {base base' : BasePremiseEvaluator}
    {language : LanguageDef}
    (constructorInjective : Function.Injective symbols.constructor)
    (mapsBaseResults : MapsBasePremiseResults symbols base base')
    {fuel : Nat} {source target : Pattern}
    (evidence : StepAt base language fuel source target) :
    StepAt base' (mapLanguageDef symbols language) fuel
      (mapPattern symbols source) (mapPattern symbols target) := by
  induction fuel generalizing source target with
  | zero => cases evidence
  | succ fuel inductionHypothesis =>
      have premiseMap :
          ∀ {initial final : Bindings} {premise : Premise},
            PremiseAt base language fuel initial premise final →
              PremiseAt base' (mapLanguageDef symbols language) fuel
                (mapBindings symbols initial) (mapPremise symbols premise)
                (mapBindings symbols final) := by
        intro initial final premise premiseEvidence
        cases premiseEvidence with
        | freshness member =>
            exact .freshness (mapsBaseResults _ _ _ _ member)
        | relationQuery member =>
            exact .relationQuery (mapsBaseResults _ _ _ _ member)
        | forAll member =>
            exact .forAll (mapsBaseResults _ _ _ _ member)
        | congruence recursive matched merged =>
            rename_i premiseBindings premiseSource premiseTarget candidate
            refine PremiseAt.congruence
              (premiseBindings := mapBindings symbols premiseBindings)
              (candidate := mapPattern symbols candidate) ?_ ?_ ?_
            · rw [applyBindings_mapPattern]
              exact inductionHypothesis recursive
            · rw [matchPattern_equivariance symbols constructorInjective]
              exact List.mem_map_of_mem matched
            · rw [← mergeBindings_mapBindings symbols constructorInjective,
                merged]
              rfl
      have premisesMap :
          ∀ {initial final : Bindings} {premises : List Premise},
            PremisesAt base language fuel initial premises final →
              PremisesAt base' (mapLanguageDef symbols language) fuel
                (mapBindings symbols initial)
                (premises.map (mapPremise symbols))
                (mapBindings symbols final) := by
        intro initial final premises premisesEvidence
        induction premises generalizing initial final with
        | nil =>
            cases premisesEvidence
            exact .nil _
        | cons premise premises premisesHypothesis =>
            cases premisesEvidence with
            | cons first rest =>
                exact .cons (premiseMap first) (premisesHypothesis rest)
      cases evidence with
      | @rule stepFuel stepSource stepTarget authoredRule initialBindings
          finalBindings ruleMember matched premisesEvidence targetEq =>
          have matchedSyntactic :
              initialBindings ∈ matchPattern authoredRule.left source := by
            simpa using matched
          have targetSyntactic :
              applyBindings finalBindings authoredRule.right = target := by
            simpa using targetEq
          refine StepAt.rule (rule := mapRewriteRule symbols authoredRule)
            (initialBindings := mapBindings symbols initialBindings)
            (finalBindings := mapBindings symbols finalBindings)
            (mem_rewrites_mapLanguageDef symbols ruleMember) ?_ ?_ ?_
          · simp only [matchPatternForRule_eq_syntactic, mapRewriteRule]
            rw [matchPattern_equivariance symbols constructorInjective]
            exact List.mem_map_of_mem matchedSyntactic
          · simpa only [mapRewriteRule] using premisesMap premisesEvidence
          · simp only [applyBindingsForRule_eq_syntactic, mapRewriteRule]
            rw [applyBindings_mapPattern]
            exact congrArg (mapPattern symbols) targetSyntactic

/-- Unbounded form: the least contextual relation maps into the least
contextual relation of the image presentation. -/
theorem step_mapLanguageDef
    {symbols : PresentationSymbols} {base base' : BasePremiseEvaluator}
    {language : LanguageDef}
    (constructorInjective : Function.Injective symbols.constructor)
    (mapsBaseResults : MapsBasePremiseResults symbols base base')
    {source target : Pattern}
    (evidence : Step base language source target) :
    Step base' (mapLanguageDef symbols language)
      (mapPattern symbols source) (mapPattern symbols target) := by
  obtain ⟨fuel, bounded⟩ := evidence
  exact ⟨fuel,
    stepAt_mapLanguageDef constructorInjective mapsBaseResults bounded⟩

/-! ## Monotonicity in the rule set for an arbitrary base evaluator -/

/-- Rule-set inclusion preserves a bounded contextual derivation for any base
evaluator that is itself monotone in the language argument.  Matching and
instantiation are unchanged because `matchPatternForRule` and
`applyBindingsForRule` ignore their language argument in the reflection-free
core.  This generalises `StepAt.mono_rules` from `engineBasePremises` to an
arbitrary base evaluator. -/
theorem stepAt_of_rewrites_mem
    {base : BasePremiseEvaluator} {language language' : LanguageDef}
    (rulesMem : ∀ rule, List.Mem rule language.rewrites →
      List.Mem rule language'.rewrites)
    (baseMono : ∀ bindings premise result,
      result ∈ base language bindings premise →
        result ∈ base language' bindings premise)
    {fuel : Nat} {source target : Pattern}
    (evidence : StepAt base language fuel source target) :
    StepAt base language' fuel source target := by
  induction fuel generalizing source target with
  | zero => cases evidence
  | succ fuel inductionHypothesis =>
      have premiseMono :
          ∀ {initial final : Bindings} {premise : Premise},
            PremiseAt base language fuel initial premise final →
              PremiseAt base language' fuel initial premise final := by
        intro initial final premise premiseEvidence
        cases premiseEvidence with
        | freshness member => exact .freshness (baseMono _ _ _ member)
        | relationQuery member => exact .relationQuery (baseMono _ _ _ member)
        | forAll member => exact .forAll (baseMono _ _ _ member)
        | congruence recursive matched merged =>
            exact .congruence (inductionHypothesis recursive) matched merged
      have premisesMono :
          ∀ {initial final : Bindings} {premises : List Premise},
            PremisesAt base language fuel initial premises final →
              PremisesAt base language' fuel initial premises final := by
        intro initial final premises premisesEvidence
        induction premises generalizing initial final with
        | nil =>
            cases premisesEvidence
            exact .nil _
        | cons premise premises premisesHypothesis =>
            cases premisesEvidence with
            | cons first rest =>
                exact .cons (premiseMono first) (premisesHypothesis rest)
      cases evidence with
      | rule ruleMember matched premisesEvidence targetEq =>
          exact .rule (rulesMem _ ruleMember) (by simpa using matched)
            (premisesMono premisesEvidence) (by simpa using targetEq)

/-! ## Simulation along a structural morphism -/

/-- **Headline.**  One-step contextual reduction is preserved along a
structural presentation morphism: a source step maps to a target step on the
mapped patterns.  The morphism supplies the mapped-rules leg through
`mapsRewrites`; the base evaluators supply result preservation along the symbol
action and monotonicity from the mapped source into the full target. -/
theorem step_map_of_structuralMorphism
    {base base' : BasePremiseEvaluator}
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (constructorInjective : Function.Injective morphism.symbols.constructor)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base')
    (baseMono : ∀ bindings premise result,
      result ∈ base' (mapLanguageDef morphism.symbols source.language)
          bindings premise →
        result ∈ base' target.language bindings premise)
    {p q : Pattern}
    (step : Step base source.language p q) :
    Step base' target.language (mapPattern morphism.symbols p)
      (mapPattern morphism.symbols q) := by
  obtain ⟨fuel, bounded⟩ := step
  refine ⟨fuel, stepAt_of_rewrites_mem ?_ baseMono
    (stepAt_mapLanguageDef constructorInjective mapsBaseResults bounded)⟩
  intro rule membership
  rw [mapLanguageDef_rewrites] at membership
  obtain ⟨sourceRule, sourceMembership, rfl⟩ := List.mem_map.mp membership
  exact morphism.mapsRewrites sourceRule sourceMembership

/-! ## Result preservation for the default base evaluator

`engineBasePremises RelationEnv.empty` is the evaluator underlying
`langReduces`.  Congruence and `forAll` premises produce nothing at this
boundary; freshness is equivariant because `mapPattern` preserves free
variable names; a `relationQuery` premise can only produce results through
the builtin `"eq"` relation, which survives exactly when the symbol action
fixes that name. -/

private theorem lookup_mapBindings (symbols : PresentationSymbols)
    (bindings : Bindings) (name : String) :
    (mapBindings symbols bindings).lookup name =
      (bindings.lookup name).map (mapPattern symbols) := by
  simp only [Bindings.lookup, find?_mapBindings, Option.map_map]
  rfl

private theorem freeVars_mapPattern (symbols : PresentationSymbols)
    (pattern : Pattern) :
    freeVars (mapPattern symbols pattern) = freeVars pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, freeVars, List.flatMap_map]
      exact List.flatMap_congr inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      simp [mapPattern, freeVars, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [mapPattern, freeVars, inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [mapPattern, freeVars, bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, freeVars, List.flatMap_map]
      exact List.flatMap_congr inductionHypothesis

private theorem checkFreshness_mapPattern (symbols : PresentationSymbols)
    (varName : String) (term : Pattern) :
    checkFreshness ⟨varName, mapPattern symbols term⟩ =
      checkFreshness ⟨varName, term⟩ := by
  simp [checkFreshness, isFresh, freeVars_mapPattern]

/-- Local mirror of the freshness-variable resolution used by
`premiseStepWithEnv`: a metavariable bound to a name resolves to that name,
an unbound metavariable resolves to itself, and a non-name binding fails. -/
private def resolveFreshName (bindings : Bindings) (varName : String) :
    Option String :=
  match bindings.lookup varName with
  | some (.fvar boundName) => some boundName
  | some _ => none
  | none => some varName

private theorem premiseStepWithEnv_freshness_eq
    (relEnv : RelationEnv) (language : LanguageDef) (bindings : Bindings)
    (condition : FreshnessCondition) :
    premiseStepWithEnv relEnv language bindings (.freshness condition) =
      match resolveFreshName bindings condition.varName with
      | some resolved =>
          if checkFreshness ⟨resolved, applyBindings bindings condition.term⟩
          then [bindings]
          else []
      | none => [] := rfl

private theorem resolveFreshName_mapBindings (symbols : PresentationSymbols)
    (bindings : Bindings) (varName : String) :
    resolveFreshName (mapBindings symbols bindings) varName =
      resolveFreshName bindings varName := by
  unfold resolveFreshName
  rw [lookup_mapBindings]
  cases found : bindings.lookup varName with
  | none => rfl
  | some value => cases value <;> simp [mapPattern]

private theorem mapPattern_eq_fvar {symbols : PresentationSymbols}
    {pattern : Pattern} {name : String}
    (equal : mapPattern symbols pattern = .fvar name) :
    pattern = .fvar name := by
  cases pattern <;> simp_all [mapPattern]

private theorem matchRelationArgument_not_fvar
    (seed : Bindings) (argument value : Pattern)
    (notFvar : ∀ name, argument ≠ .fvar name) :
    matchRelationArgument seed argument value =
      matchPattern (applyBindings seed argument) value := by
  cases argument <;> first
    | rfl
    | exact absurd rfl (notFvar _)

private theorem matchRelationArgument_equivariance
    (symbols : PresentationSymbols)
    (constructorInjective : Function.Injective symbols.constructor)
    (seed : Bindings) (argument value : Pattern) :
    matchRelationArgument (mapBindings symbols seed)
        (mapPattern symbols argument) (mapPattern symbols value) =
      (matchRelationArgument seed argument value).map
        (mapBindings symbols) := by
  by_cases isFvar : ∃ name, argument = .fvar name
  · obtain ⟨name, rfl⟩ := isFvar
    simp only [mapPattern, matchRelationArgument, lookup_mapBindings]
    cases found : seed.lookup name with
    | none => simp [mapBindings]
    | some existing =>
        by_cases equal : existing = value
        · subst equal
          simp
        · have mappedNotEqual :
              mapPattern symbols existing ≠ mapPattern symbols value :=
            fun mappedEqual => equal
              (mapPattern_injective symbols constructorInjective mappedEqual)
          simp [equal, mappedNotEqual]
  · have notFvar : ∀ name, argument ≠ Pattern.fvar name :=
      fun name equal => isFvar ⟨name, equal⟩
    rw [matchRelationArgument_not_fvar seed argument value notFvar,
      matchRelationArgument_not_fvar (mapBindings symbols seed)
        (mapPattern symbols argument) (mapPattern symbols value)
        (fun name equal => notFvar name (mapPattern_eq_fvar equal)),
      applyBindings_mapPattern,
      matchPattern_equivariance symbols constructorInjective]

private theorem matchRelationArgs_equivariance
    (symbols : PresentationSymbols)
    (constructorInjective : Function.Injective symbols.constructor)
    (arguments : List Pattern) :
    ∀ (seed : Bindings) (values : List Pattern),
      matchRelationArgs (mapBindings symbols seed)
          (arguments.map (mapPattern symbols))
          (values.map (mapPattern symbols)) =
        (matchRelationArgs seed arguments values).map
          (mapBindings symbols) := by
  induction arguments with
  | nil =>
      intro seed values
      cases values with
      | nil => simp [matchRelationArgs]
      | cons value values => simp [matchRelationArgs]
  | cons argument arguments inductionHypothesis =>
      intro seed values
      cases values with
      | nil => simp [matchRelationArgs]
      | cons value values =>
          simp only [List.map_cons, matchRelationArgs]
          rw [matchRelationArgument_equivariance symbols constructorInjective]
          simp only [List.flatMap_map]
          rw [List.map_flatMap]
          apply List.flatMap_congr
          intro headBindings headMembership
          rw [← mergeBindings_mapBindings symbols constructorInjective]
          cases merged : mergeBindings seed headBindings with
          | none => simp
          | some extended =>
              simp only [Option.map_some]
              rw [inductionHypothesis extended values]
              exact filterMap_merge_mapBindings symbols constructorInjective
                headBindings (matchRelationArgs extended arguments values)

private theorem builtinRelationTuples_map
    (symbols : PresentationSymbols)
    (relationFixesEq : symbols.relation "eq" = "eq")
    (sourceLanguage targetLanguage : LanguageDef)
    (relation : String) (argumentPatterns : List Pattern)
    {tuple : List Pattern}
    (member : tuple ∈
      builtinRelationTuples sourceLanguage relation argumentPatterns) :
    tuple.map (mapPattern symbols) ∈
      builtinRelationTuples targetLanguage (symbols.relation relation)
        (argumentPatterns.map (mapPattern symbols)) := by
  unfold builtinRelationTuples at member ⊢
  split at member
  · rw [relationFixesEq]
    simp only [List.map_cons, List.map_nil]
    rcases List.mem_cons.mp member with rfl | member
    · simp +decide
    · rcases List.mem_singleton.mp member with rfl
      simp +decide
  · cases member

private theorem relationQueryStep_empty_map
    (symbols : PresentationSymbols)
    (constructorInjective : Function.Injective symbols.constructor)
    (relationFixesEq : symbols.relation "eq" = "eq")
    (sourceLanguage targetLanguage : LanguageDef)
    (bindings : Bindings) (relation : String) (arguments : List Pattern)
    {result : Bindings}
    (member : result ∈ relationQueryStep RelationEnv.empty sourceLanguage
      bindings relation arguments) :
    mapBindings symbols result ∈
      relationQueryStep RelationEnv.empty targetLanguage
        (mapBindings symbols bindings) (symbols.relation relation)
        (arguments.map (mapPattern symbols)) := by
  simp only [relationQueryStep, RelationEnv.empty, List.append_nil,
    List.mem_flatMap, List.mem_filterMap] at member ⊢
  obtain ⟨tuple, tupleMember, premiseBindings, argsMember, merged⟩ := member
  have argumentPatterns :
      (arguments.map (mapPattern symbols)).map
          (applyBindings (mapBindings symbols bindings)) =
        (arguments.map (applyBindings bindings)).map (mapPattern symbols) := by
    simp only [List.map_map]
    exact List.map_congr_left fun argument _ =>
      applyBindings_mapPattern symbols bindings argument
  refine ⟨tuple.map (mapPattern symbols), ?_,
    mapBindings symbols premiseBindings, ?_, ?_⟩
  · rw [argumentPatterns]
    exact builtinRelationTuples_map symbols relationFixesEq
      sourceLanguage targetLanguage relation _ tupleMember
  · rw [matchRelationArgs_equivariance symbols constructorInjective]
    exact List.mem_map_of_mem argsMember
  · rw [← mergeBindings_mapBindings symbols constructorInjective, merged]
    rfl

/-- The default base evaluator maps results along any symbol action with
injective constructor part that fixes the builtin relation name `"eq"`.  The
naming condition is required: see
`engineBasePremises_empty_mapping_requires_eq_name`. -/
theorem engineBasePremises_empty_maps_results
    (symbols : PresentationSymbols)
    (constructorInjective : Function.Injective symbols.constructor)
    (relationFixesEq : symbols.relation "eq" = "eq") :
    MapsBasePremiseResults symbols (engineBasePremises RelationEnv.empty)
      (engineBasePremises RelationEnv.empty) := by
  intro language bindings premise result member
  cases premise with
  | congruence left right =>
      simp [engineBasePremises] at member
  | forAll collection parameter body =>
      simp [engineBasePremises, premiseStepWithEnv] at member
  | freshness condition =>
      have memberEval : result ∈ premiseStepWithEnv RelationEnv.empty
          language bindings (.freshness condition) := member
      rw [premiseStepWithEnv_freshness_eq] at memberEval
      show mapBindings symbols result ∈
        premiseStepWithEnv RelationEnv.empty (mapLanguageDef symbols language)
          (mapBindings symbols bindings)
          (.freshness ⟨condition.varName, mapPattern symbols condition.term⟩)
      rw [premiseStepWithEnv_freshness_eq]
      cases resolved : resolveFreshName bindings condition.varName with
      | none =>
          simp only [resolved] at memberEval
          cases memberEval
      | some resolvedName =>
          simp only [resolved] at memberEval
          by_cases fresh :
              checkFreshness ⟨resolvedName, applyBindings bindings condition.term⟩
          · rw [if_pos fresh] at memberEval
            have resultEq : result = bindings :=
              List.mem_singleton.mp memberEval
            subst resultEq
            simp only [resolveFreshName_mapBindings, resolved,
              applyBindings_mapPattern, checkFreshness_mapPattern]
            rw [if_pos fresh]
            exact List.mem_singleton.mpr rfl
          · rw [if_neg fresh] at memberEval
            cases memberEval
  | relationQuery relation arguments =>
      have memberEval : result ∈ relationQueryStep RelationEnv.empty
          language bindings relation arguments := member
      exact relationQueryStep_empty_map symbols constructorInjective
        relationFixesEq language (mapLanguageDef symbols language) bindings
        relation arguments memberEval

/-- The default base evaluator never consults the language argument: builtin
relation tuples, freshness checks, and the empty relation environment are all
language-independent. -/
theorem engineBasePremises_language_agnostic
    (relEnv : RelationEnv) (firstLanguage secondLanguage : LanguageDef)
    (bindings : Bindings) (premise : Premise) :
    engineBasePremises relEnv firstLanguage bindings premise =
      engineBasePremises relEnv secondLanguage bindings premise := by
  cases premise <;> rfl

/-- **Corollary at the derived-semantics level.**  The default reduction
relation `langReduces` of the OSLF synthesis layer is preserved along any
structural presentation morphism whose symbol action has an injective
constructor part and fixes the builtin relation name `"eq"`. -/
theorem langReduces_map_of_structuralMorphism
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (constructorInjective : Function.Injective morphism.symbols.constructor)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq")
    {p q : Pattern}
    (reduces : langReduces source.language p q) :
    langReduces target.language (mapPattern morphism.symbols p)
      (mapPattern morphism.symbols q) := by
  have step : Step (engineBasePremises RelationEnv.empty)
      source.language p q := reduces
  exact step_map_of_structuralMorphism morphism constructorInjective
    (engineBasePremises_empty_maps_results morphism.symbols
      constructorInjective relationFixesEq)
    (fun bindings premise result member =>
      engineBasePremises_language_agnostic RelationEnv.empty
          (mapLanguageDef morphism.symbols source.language) target.language
          bindings premise ▸ member)
    step

/-! ## Positive canary

A two-constructor source language with one premise-free rewrite, a genuine
constructor renaming into a validated target that also carries one extra
rule, and a concrete step transported by the headline theorem. -/

private def sourceRuleAB : RewriteRule :=
  { name := "step-a-b"
    typeContext := []
    premises := []
    left := .apply "a" []
    right := .apply "b" [] }

private def simulationSourceLanguage : LanguageDef :=
  { name := "simulation-source"
    types := [TypeDecl.plain "Proc"]
    terms :=
      [ { label := "a", category := "Proc", params := [], syntaxPattern := [] }
      , { label := "b", category := "Proc", params := [], syntaxPattern := [] } ]
    equations := []
    rewrites := [sourceRuleAB] }

private def targetRuleAB : RewriteRule :=
  { name := "step-a-b"
    typeContext := []
    premises := []
    left := .apply "sim:a" []
    right := .apply "sim:b" [] }

private def targetRuleCA : RewriteRule :=
  { name := "step-c-a"
    typeContext := []
    premises := []
    left := .apply "sim:c" []
    right := .apply "sim:a" [] }

private def simulationTargetLanguage : LanguageDef :=
  { name := "simulation-target"
    types := [TypeDecl.plain "Proc"]
    terms :=
      [ { label := "sim:a", category := "Proc", params := [], syntaxPattern := [] }
      , { label := "sim:b", category := "Proc", params := [], syntaxPattern := [] }
      , { label := "sim:c", category := "Proc", params := [], syntaxPattern := [] } ]
    equations := []
    rewrites := [targetRuleAB, targetRuleCA] }

/-- Prefix-tagging symbol action on constructors; every other namespace is
untouched, so the builtin relation name `"eq"` is fixed. -/
private def taggingSymbols : PresentationSymbols where
  sort := _root_.id
  constructor := fun name => "sim:" ++ name
  relation := _root_.id
  equation := _root_.id
  rewrite := _root_.id

private theorem taggingConstructorInjective :
    Function.Injective taggingSymbols.constructor := by
  intro left right equality
  apply String.toList_inj.mp
  have listEquality := congrArg String.toList equality
  simp only [taggingSymbols, String.toList_append] at listEquality
  exact (List.append_right_inj _).mp listEquality

private theorem simulationSourceLanguage_validate :
    simulationSourceLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro rewrite membership
    cases membership with
    | head =>
        simp [LanguageDef.validateRewrite, simulationSourceLanguage,
          sourceRuleAB, LanguageDef.validatePatternConstructors,
          LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
          LanguageDef.patternBinderNames, Pattern.constructorRefs,
          Pattern.constructorRefsList, Pattern.freeFvarNames,
          Pattern.isWellScoped, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]
    | tail _ inner => cases inner

private theorem simulationTargetLanguage_validate :
    simulationTargetLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro rewrite membership
    have targetRuleValid : ∀ authoredRule ∈ [targetRuleAB, targetRuleCA],
        LanguageDef.validateRewrite simulationTargetLanguage authoredRule = [] := by
      intro authoredRule ruleMembership
      rcases List.mem_cons.mp ruleMembership with rfl | inner
      · simp [LanguageDef.validateRewrite, simulationTargetLanguage,
          targetRuleAB, LanguageDef.validatePatternConstructors,
          LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
          LanguageDef.patternBinderNames, Pattern.constructorRefs,
          Pattern.constructorRefsList, Pattern.freeFvarNames,
          Pattern.isWellScoped, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]
      · rcases List.mem_singleton.mp inner with rfl
        simp [LanguageDef.validateRewrite, simulationTargetLanguage,
          targetRuleCA, LanguageDef.validatePatternConstructors,
          LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
          LanguageDef.patternBinderNames, Pattern.constructorRefs,
          Pattern.constructorRefsList, Pattern.freeFvarNames,
          Pattern.isWellScoped, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]
    exact targetRuleValid rewrite membership

private def simulationSource : ValidatedLanguageDef where
  language := simulationSourceLanguage
  valid := simulationSourceLanguage_validate

private def simulationTarget : ValidatedLanguageDef where
  language := simulationTargetLanguage
  valid := simulationTargetLanguage_validate

private theorem mappedRuleAB :
    mapRewriteRule taggingSymbols sourceRuleAB = targetRuleAB := rfl

private def simulationMorphism :
    StructuralMorphism simulationSource simulationTarget where
  symbols := taggingSymbols
  mapsTypes := by
    intro declaration membership
    cases membership with
    | head => exact List.Mem.head _
    | tail _ inner => cases inner
  mapsTerms := by
    intro rule membership
    cases membership with
    | head => exact List.Mem.head _
    | tail _ inner =>
        cases inner with
        | head => exact List.Mem.tail _ (List.Mem.head _)
        | tail _ inner => cases inner
  mapsEquations := by
    intro equation membership
    cases membership
  mapsRewrites := by
    intro rewrite membership
    cases membership with
    | head =>
        rw [mappedRuleAB]
        exact List.Mem.head _
    | tail _ inner => cases inner

/-- Concrete source step: `a ⟶ b` at the root. -/
theorem simulationSource_step :
    langReduces simulationSourceLanguage (.apply "a" []) (.apply "b" []) := by
  refine ⟨1, StepAt.rule (rule := sourceRuleAB) (initialBindings := [])
    (finalBindings := []) ?_ ?_ ?_ ?_⟩
  · simp [simulationSourceLanguage]
  · rw [matchPatternForRule_eq_syntactic]
    simp +decide [sourceRuleAB, matchPattern, matchArgs]
  · exact PremisesAt.nil []
  · rw [applyBindingsForRule_eq_syntactic]
    simp [sourceRuleAB, applyBindings]

/-- The headline theorem transports the concrete source step to the concrete
target step on the tagged patterns. -/
theorem simulation_canary_transports :
    langReduces simulationTargetLanguage
      (.apply "sim:a" []) (.apply "sim:b" []) := by
  have mapped := langReduces_map_of_structuralMorphism simulationMorphism
    taggingConstructorInjective rfl simulationSource_step
  exact mapped

/-! ## Negative canaries -/

/-- Simulation is one-way.  `.apply "sim:c" []` is the image of the source
pattern `.apply "c" []`; the target steps from it through its extra rule,
while the source has no step at all from the preimage. -/
theorem simulation_is_one_way :
    mapPattern taggingSymbols (.apply "c" []) = .apply "sim:c" [] ∧
    langReduces simulationTargetLanguage
      (.apply "sim:c" []) (.apply "sim:a" []) ∧
    ∀ result, ¬ langReduces simulationSourceLanguage
      (.apply "c" []) result := by
  refine ⟨rfl, ?_, ?_⟩
  · refine ⟨1, StepAt.rule (rule := targetRuleCA) (initialBindings := [])
      (finalBindings := []) ?_ ?_ ?_ ?_⟩
    · exact List.Mem.tail _ (List.Mem.head _)
    · rw [matchPatternForRule_eq_syntactic]
      simp +decide [targetRuleCA, matchPattern, matchArgs]
    · exact PremisesAt.nil []
    · rw [applyBindingsForRule_eq_syntactic]
      simp [targetRuleCA, applyBindings]
  · intro result
    apply not_step_of_matchPatternForRule_eq_nil
    intro rule membership
    cases membership with
    | head =>
        rw [matchPatternForRule_eq_syntactic]
        simp +decide [sourceRuleAB, matchPattern]
    | tail _ inner => cases inner

/-- Constructor injectivity is load-bearing for matcher equivariance: a
collapsing action makes distinct constructors match after mapping, so the
mapped match set strictly exceeds the image of the source match set. -/
private def collapseConstructors : PresentationSymbols :=
  { PresentationSymbols.id with constructor := fun _ => "collapsed" }

theorem matchPattern_equivariance_requires_injectivity :
    matchPattern (mapPattern collapseConstructors (.apply "left" []))
        (mapPattern collapseConstructors (.apply "right" [])) ≠
      (matchPattern (.apply "left" []) (.apply "right" [])).map
        (mapBindings collapseConstructors) := by
  simp +decide [mapPattern, mapPatternList, collapseConstructors,
    PresentationSymbols.id, matchPattern, matchArgs]

/-- The `"eq"`-naming condition on `engineBasePremises_empty_maps_results` is
required: an action that renames the builtin relation name silences the
builtin equality tuples in the image, losing a source result. -/
private def renameEqSymbols : PresentationSymbols :=
  { PresentationSymbols.id with
    relation := fun name => if name = "eq" then "builtin-eq" else name }

theorem engineBasePremises_empty_mapping_requires_eq_name :
    ¬ MapsBasePremiseResults renameEqSymbols
        (engineBasePremises RelationEnv.empty)
        (engineBasePremises RelationEnv.empty) := by
  intro mapsResults
  have member : ([] : Bindings) ∈
      engineBasePremises RelationEnv.empty (LanguageDef.empty "eq-canary") []
        (.relationQuery "eq" [.apply "atom" [], .apply "atom" []]) := by
    simp +decide [engineBasePremises, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, RelationEnv.empty, matchRelationArgs,
      matchRelationArgument, matchPattern, matchArgs, applyBindings,
      mergeBindings, List.foldlM_nil]
  have mapped := mapsResults (LanguageDef.empty "eq-canary") [] _ [] member
  exact absurd mapped (by decide)

/-! ## Axiom audit -/

#print axioms stepAt_mapLanguageDef
#print axioms step_mapLanguageDef
#print axioms stepAt_of_rewrites_mem
#print axioms step_map_of_structuralMorphism
#print axioms engineBasePremises_empty_maps_results
#print axioms langReduces_map_of_structuralMorphism
#print axioms simulationSource_step
#print axioms simulation_canary_transports
#print axioms simulation_is_one_way
#print axioms matchPattern_equivariance_requires_injectivity
#print axioms engineBasePremises_empty_mapping_requires_eq_name

end Mettapedia.GSLT.LanguageDef.StructuralSimulation
