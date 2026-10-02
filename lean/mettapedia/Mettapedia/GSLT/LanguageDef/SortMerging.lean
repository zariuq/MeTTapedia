import Mettapedia.GSLT.LanguageDef.EquationSimulation
import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation

/-!
# Merging the sorts of a presentation

A presentation with several sorts can be read at one sort: keep every
constructor and every rule, and replace every sort by one.  The reading is a
map of symbols that sends every sort name to the chosen one and fixes every
other name.

This module records what that map does and does not change.

* It fixes every pattern, since a pattern mentions constructors and no sort.
* A rule and its image have the same two sides and the same name; only the
  sorts of the metavariables differ.  A premise-free rule that validates
  against a signature therefore validates, in its image, against the image
  signature.
* Two languages whose rules correspond in this way and carry no premise
  generate the same steps on patterns.

The reading at one sort admits more terms than the presentation it reads:
arguments that the several sorts kept apart are now of one sort.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SortMerging

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSimulation

/-- Send every sort to one sort and fix every other name. -/
def mergeSorts (sort : String) : LanguageDefSymbolMap where
  sort := fun _ => sort
  constructor := id
  relation := id
  equation := id
  rewrite := id

/-- Merging sorts fixes every unit a collection algebra declares. -/
theorem mergeSorts_fixesDeclaredUnits (sort : String) (language : LanguageDef) :
    FixesDeclaredUnits (mergeSorts sort) language :=
  fixesDeclaredUnits_of_constructor_id _ _ fun _ => rfl

/-! ## Patterns -/

/-- **A map of symbols that fixes every constructor fixes every pattern.** -/
theorem mapPattern_of_constructor_fixed (symbols : LanguageDefSymbolMap)
    (fixed : ∀ label, symbols.constructor label = label) (pattern : Pattern) :
    mapPattern symbols pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [mapPattern]
  | hfvar name => simp [mapPattern]
  | happly constructor arguments recurse =>
      have same : arguments.map (mapPattern symbols) = arguments :=
        (List.map_congr_left recurse).trans (List.map_id arguments)
      simp only [mapPattern, mapPatternList_eq_map, fixed, same]
  | hlambda binder body recurse => simp only [mapPattern, recurse]
  | hmultiLambda arity binders body recurse => simp only [mapPattern, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      simp only [mapPattern, bodyRecurse, replacementRecurse]
  | hcollection collectionType elements rest recurse =>
      have same : elements.map (mapPattern symbols) = elements :=
        (List.map_congr_left recurse).trans (List.map_id elements)
      simp only [mapPattern, mapPatternList_eq_map, same]

/-- Merging sorts fixes every pattern. -/
@[simp] theorem mapPattern_mergeSorts (sort : String) (pattern : Pattern) :
    mapPattern (mergeSorts sort) pattern = pattern :=
  mapPattern_of_constructor_fixed _ (fun _ => rfl) pattern

/-! ## Rules -/

@[simp] theorem mapRewriteRule_mergeSorts_left (sort : String) (rule : RewriteRule) :
    (mapRewriteRule (mergeSorts sort) rule).left = rule.left :=
  mapPattern_mergeSorts sort rule.left

@[simp] theorem mapRewriteRule_mergeSorts_right (sort : String) (rule : RewriteRule) :
    (mapRewriteRule (mergeSorts sort) rule).right = rule.right :=
  mapPattern_mergeSorts sort rule.right

@[simp] theorem mapRewriteRule_mergeSorts_name (sort : String) (rule : RewriteRule) :
    (mapRewriteRule (mergeSorts sort) rule).name = rule.name := rfl

/-- The image of a premise-free rule is premise-free. -/
theorem mapRewriteRule_premises_eq_nil (symbols : LanguageDefSymbolMap) {rule : RewriteRule}
    (premiseFree : rule.premises = []) : (mapRewriteRule symbols rule).premises = [] := by
  show rule.premises.map (mapPremise symbols) = []
  rw [premiseFree]
  rfl

/-- After merging, every base sort a type mentions is the one sort. -/
theorem baseNames_mapTypeExpr_mergeSorts (sort : String) (type : TypeExpr) :
    ∀ name ∈ (mapTypeExpr (mergeSorts sort) type).baseNames, name = sort := by
  induction type with
  | base original =>
      intro name membership
      simpa [mapTypeExpr, TypeExpr.baseNames, mergeSorts] using membership
  | arrow domain codomain domainRecurse codomainRecurse =>
      intro name membership
      simp only [mapTypeExpr, TypeExpr.baseNames, List.mem_append] at membership
      rcases membership with inDomain | inCodomain
      · exact domainRecurse name inDomain
      · exact codomainRecurse name inCodomain
  | multiBinder body recurse =>
      intro name membership
      exact recurse name (by simpa [mapTypeExpr, TypeExpr.baseNames] using membership)
  | collection collectionType element recurse =>
      intro name membership
      exact recurse name (by simpa [mapTypeExpr, TypeExpr.baseNames] using membership)

/-- A constructor reference is declared in the image of a signature exactly
when it is declared in the signature, for a map that fixes constructors. -/
theorem referenceDeclared_map (symbols : LanguageDefSymbolMap)
    (fixed : ∀ label, symbols.constructor label = label) (rules : List GrammarRule)
    (reference : String × Nat) :
    LanguageDef.referenceDeclared (rules.map (mapGrammarRule symbols)) reference =
      LanguageDef.referenceDeclared rules reference := by
  unfold LanguageDef.referenceDeclared
  have filtered :
      (rules.map (mapGrammarRule symbols)).filter (fun declaration =>
          declaration.label == reference.1) =
        (rules.filter fun declaration => declaration.label == reference.1).map
          (mapGrammarRule symbols) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro declaration _
    simp [mapGrammarRule, fixed]
  rw [filtered]
  cases rules.filter (fun declaration => declaration.label == reference.1) with
  | nil => rfl
  | cons head tail =>
      cases tail with
      | nil => simp [mapGrammarRule]
      | cons second rest => rfl

/-- The labels of a signature are those of its image. -/
theorem labels_map (symbols : LanguageDefSymbolMap)
    (fixed : ∀ label, symbols.constructor label = label) (rules : List GrammarRule) :
    (rules.map (mapGrammarRule symbols)).map (·.label) = rules.map (·.label) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro rule _
  exact fixed rule.label

/-- The checks on the two sides of a rule read the names of its
metavariables and not their sorts. -/
theorem validateRulePatterns_mapTypeContext (symbols : LanguageDefSymbolMap)
    (context : String) (labels : List String) (typeContext : List (String × TypeExpr))
    (premises : List Premise) (left right : Pattern) :
    LanguageDef.validateRulePatterns context labels (mapTypeContext symbols typeContext)
        premises left right =
      LanguageDef.validateRulePatterns context labels typeContext premises left right := by
  unfold LanguageDef.validateRulePatterns mapTypeContext
  simp only [List.filterMap_map]
  rfl

/-- **A premise-free rule that validates against a signature validates, with
its sorts merged, against the signature with its sorts merged.** -/
theorem validateRewrite_mergeSorts {source target : LanguageDef} {sort : String}
    (types : target.typeNames = [sort])
    (terms : target.terms = source.terms.map (mapGrammarRule (mergeSorts sort)))
    {rule : RewriteRule} (premiseFree : rule.premises = [])
    (valid : LanguageDef.validateRewrite source rule = []) :
    LanguageDef.validateRewrite target (mapRewriteRule (mergeSorts sort) rule) = [] := by
  have sourceValid := valid
  unfold LanguageDef.validateRewrite at sourceValid
  simp only [premiseFree, List.flatMap_nil, List.append_nil, List.append_eq_nil_iff,
    List.flatMap_eq_nil_iff] at sourceValid
  obtain ⟨⟨⟨-, leftValid⟩, rightValid⟩, patterns⟩ := sourceValid
  unfold LanguageDef.validateRewrite
  simp only [mapRewriteRule_premises_eq_nil (mergeSorts sort) premiseFree, List.flatMap_nil,
    List.append_nil, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro entry membership
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro name nameMember
    obtain ⟨original, -, rfl⟩ := List.mem_map.mp membership
    rw [types]
    exact List.mem_singleton.mpr
      (baseNames_mapTypeExpr_mergeSorts sort original.2 name nameMember)
  · rw [mapRewriteRule_mergeSorts_left, mapRewriteRule_mergeSorts_name]
    apply (LanguageDef.validatePatternConstructors_eq_nil_iff _ _ _).mpr
    intro reference membership
    rw [terms, referenceDeclared_map _ (fun _ => rfl)]
    exact (LanguageDef.validatePatternConstructors_eq_nil_iff _ _ _).mp leftValid reference
      membership
  · rw [mapRewriteRule_mergeSorts_right, mapRewriteRule_mergeSorts_name]
    apply (LanguageDef.validatePatternConstructors_eq_nil_iff _ _ _).mpr
    intro reference membership
    rw [terms, referenceDeclared_map _ (fun _ => rfl)]
    exact (LanguageDef.validatePatternConstructors_eq_nil_iff _ _ _).mp rightValid reference
      membership
  · rw [mapRewriteRule_mergeSorts_left, mapRewriteRule_mergeSorts_right,
      mapRewriteRule_mergeSorts_name, terms, labels_map _ (fun _ => rfl)]
    show LanguageDef.validateRulePatterns _ _
      (mapTypeContext (mergeSorts sort) rule.typeContext) [] rule.left rule.right = []
    rw [validateRulePatterns_mapTypeContext]
    exact patterns

/-! ## Steps -/

/-- **Rules that correspond by merging sorts and carry no premise generate
the same bounded steps.**  A step reads the two sides of a rule, which the
merging does not change. -/
theorem stepAt_iff_of_mergeSorts {base : BasePremiseEvaluator} {source target : LanguageDef}
    {sort : String}
    (rules : target.rewrites = source.rewrites.map (mapRewriteRule (mergeSorts sort)))
    (premiseFree : ∀ rule ∈ source.rewrites, rule.premises = [])
    {fuel : Nat} {pattern next : Pattern} :
    StepAt base target fuel pattern next ↔ StepAt base source fuel pattern next := by
  constructor
  · intro evidence
    cases evidence with
    | @rule stepFuel _ _ image initial final member matched premises built =>
        rw [rules] at member
        obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp member
        rw [mapRewriteRule_premises_eq_nil _ (premiseFree rule ruleMember)] at premises
        cases premises
        refine StepAt.rule (rule := rule) (initialBindings := initial)
          (finalBindings := initial) ruleMember ?_ ?_ ?_
        · simpa using matched
        · rw [premiseFree rule ruleMember]
          exact .nil _
        · simpa [Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings] using built
  · intro evidence
    cases evidence with
    | @rule stepFuel _ _ rule initial final ruleMember matched premises built =>
        rw [premiseFree rule ruleMember] at premises
        cases premises
        refine StepAt.rule (rule := mapRewriteRule (mergeSorts sort) rule)
          (initialBindings := initial) (finalBindings := initial) ?_ ?_ ?_ ?_
        · rw [rules]
          exact List.mem_map_of_mem ruleMember
        · simpa using matched
        · rw [mapRewriteRule_premises_eq_nil _ (premiseFree rule ruleMember)]
          exact .nil _
        · simpa [Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings] using built

/-- Such rules generate the same steps. -/
theorem step_iff_of_mergeSorts {base : BasePremiseEvaluator} {source target : LanguageDef}
    {sort : String}
    (rules : target.rewrites = source.rewrites.map (mapRewriteRule (mergeSorts sort)))
    (premiseFree : ∀ rule ∈ source.rewrites, rule.premises = [])
    {pattern next : Pattern} :
    Step base target pattern next ↔ Step base source pattern next :=
  ⟨fun ⟨fuel, bounded⟩ => ⟨fuel, (stepAt_iff_of_mergeSorts rules premiseFree).mp bounded⟩,
    fun ⟨fuel, bounded⟩ => ⟨fuel, (stepAt_iff_of_mergeSorts rules premiseFree).mpr bounded⟩⟩

end Mettapedia.GSLT.LanguageDef.SortMerging
