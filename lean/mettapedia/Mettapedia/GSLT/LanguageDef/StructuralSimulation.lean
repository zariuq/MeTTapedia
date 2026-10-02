import Mettapedia.GSLT.LanguageDef.SymbolMapSimulation
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Structural simulation and its operational controls

`SymbolMapSimulation` proves bounded transport directly between two
presentations: mapped rules remain authored rules, and mapped premise
results remain evaluator results.  This includes arbitrary constructor
maps and inclusion of declarations, at the same derivation depth.

The injectivity-taking theorem signatures in this module are retained for
existing consumers and specialize that general transport.  Injectivity is
needed for exact matcher-result equality in `StructuralRenamingSemantics`,
but is unnecessary for forward reduction.  The controls separate these
claims: collapsing constructors can create a match, and adding target rules
can introduce a transition with no source counterpart.

The default evaluator requires that the built-in relation name `"eq"`
remain fixed.  Renaming it would discard successful equality queries; the
negative control checks that premise boundary explicitly.
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

/-! ## Existing signatures as instances of general transport -/

/-- Bounded contextual derivations map along an injective symbol action.
The general theorem needs no injectivity. -/
theorem stepAt_mapLanguageDef
    {symbols : LanguageDefSymbolMap} {base base' : BasePremiseEvaluator}
    {language : LanguageDef}
    (constructorInjective : Function.Injective symbols.constructor)
    (mapsBaseResults : MapsBasePremiseResults symbols base base')
    {fuel : Nat} {source target : Pattern}
    (evidence : StepAt base language fuel source target) :
    StepAt base' (mapLanguageDef symbols language) fuel
      (mapPattern symbols source) (mapPattern symbols target) := by
  exact (fun _ : Function.Injective symbols.constructor =>
    SymbolMapSimulation.stepAt_map mapsBaseResults evidence) constructorInjective

/-- The least contextual relation maps into the relation of the image
presentation. -/
theorem step_mapLanguageDef
    {symbols : LanguageDefSymbolMap} {base base' : BasePremiseEvaluator}
    {language : LanguageDef}
    (constructorInjective : Function.Injective symbols.constructor)
    (mapsBaseResults : MapsBasePremiseResults symbols base base')
    {source target : Pattern}
    (evidence : Step base language source target) :
    Step base' (mapLanguageDef symbols language)
      (mapPattern symbols source) (mapPattern symbols target) := by
  obtain ⟨fuel, bounded⟩ := evidence
  exact ⟨fuel, stepAt_mapLanguageDef constructorInjective mapsBaseResults bounded⟩

/-- One-step reduction maps along a structural presentation morphism.
The general theorem needs no injectivity. -/
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
  exact (fun _ : Function.Injective morphism.symbols.constructor =>
    SymbolMapSimulation.step_map_of_structuralMorphism morphism mapsBaseResults baseMono step)
    constructorInjective

/-- The default evaluator maps results along an injective symbol action
that fixes the built-in relation name `"eq"`.  The general theorem needs no
injectivity. -/
theorem engineBasePremises_empty_maps_results
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor)
    (relationFixesEq : symbols.relation "eq" = "eq") :
    MapsBasePremiseResults symbols (engineBasePremises RelationEnv.empty)
      (engineBasePremises RelationEnv.empty) := by
  exact (fun _ : Function.Injective symbols.constructor =>
    SymbolMapSimulation.engineBasePremises_empty_maps_results symbols relationFixesEq)
    constructorInjective

/-- The authored default reduction relation is preserved along the
structural presentation morphism. -/
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
private def taggingSymbols : LanguageDefSymbolMap where
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
    simp [sourceRuleAB, Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings]

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
      simp [targetRuleCA, Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings]
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
private def collapseConstructors : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with constructor := fun _ => "collapsed" }

theorem matchPattern_equivariance_requires_injectivity :
    matchPattern (mapPattern collapseConstructors (.apply "left" []))
        (mapPattern collapseConstructors (.apply "right" [])) ≠
      (matchPattern (.apply "left" []) (.apply "right" [])).map
        (mapBindings collapseConstructors) := by
  simp +decide [mapPattern, mapPatternList, collapseConstructors,
    LanguageDefSymbolMap.id, matchPattern, matchArgs]

/-- The `"eq"`-naming condition on `engineBasePremises_empty_maps_results` is
required: an action that renames the builtin relation name silences the
builtin equality tuples in the image, losing a source result. -/
private def renameEqSymbols : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with
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
