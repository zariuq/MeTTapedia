import Mathlib.CategoryTheory.Category.Basic
import Mettapedia.GSLT.LanguageDef.ReflectionExtension
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Structural maps of reflective language extensions

`StructuralMorphism` maps exactly the five-field language core.  This module
lifts that action to admitted reflection profiles without putting reflective
symbols or preservation laws back into the core category.
-/

namespace Mettapedia.GSLT.LanguageDef.ReflectionExtension

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection

/-- The two namespaces introduced by a reflection profile. -/
@[ext]
structure ReflectionSymbols where
  presentation : String → String
  rule : String → String

namespace ReflectionSymbols

def id : ReflectionSymbols where
  presentation := _root_.id
  rule := _root_.id

def comp (first second : ReflectionSymbols) : ReflectionSymbols where
  presentation := second.presentation ∘ first.presentation
  rule := second.rule ∘ first.rule

end ReflectionSymbols

/-- Symbol action for a five-field language and its reflection fibre. -/
@[ext]
structure ReflectiveSymbols extends LanguageDefSymbolMap where
  reflection : ReflectionSymbols

namespace ReflectiveSymbols

def id : ReflectiveSymbols where
  toLanguageDefSymbolMap := LanguageDefSymbolMap.id
  reflection := ReflectionSymbols.id

def comp (first second : ReflectiveSymbols) : ReflectiveSymbols where
  toLanguageDefSymbolMap := first.toLanguageDefSymbolMap.comp
    second.toLanguageDefSymbolMap
  reflection := first.reflection.comp second.reflection

end ReflectiveSymbols

private theorem mapPattern_freeFvarNames_eq (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
    (mapPattern symbols pattern).freeFvarNames = pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn with
  | hbvar => rfl
  | hfvar => rfl
  | happly constructor arguments ih =>
      simp only [mapPattern, mapPatternList_eq_map, Pattern.freeFvarNames, List.flatMap_map]
      exact List.flatMap_congr ih
  | hlambda => simp_all [mapPattern, Pattern.freeFvarNames]
  | hmultiLambda => simp_all [mapPattern, Pattern.freeFvarNames]
  | hsubst => simp_all [mapPattern, Pattern.freeFvarNames]
  | hcollection collectionType elements rest ih =>
      simp only [mapPattern, mapPatternList_eq_map, Pattern.freeFvarNames, List.flatMap_map]
      rw [List.flatMap_congr ih]

private theorem mapPattern_isWellScopedAt_eq (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
    ∀ depth, (mapPattern symbols pattern).isWellScopedAt depth = pattern.isWellScopedAt depth := by
  induction pattern using Pattern.inductionOn with
  | hbvar => intro _; rfl
  | hfvar => intro _; rfl
  | happly constructor arguments ih =>
      intro depth
      simp only [mapPattern, mapPatternList_eq_map, Pattern.isWellScopedAt]
      induction arguments with
      | nil => rfl
      | cons argument rest restIh =>
          simp only [List.map_cons, Pattern.isWellScopedListAt, ih argument (by simp) depth,
            restIh fun other member => ih other (by simp [member])]
  | hlambda binder body ih => intro depth; simp only [mapPattern, Pattern.isWellScopedAt, ih]
  | hmultiLambda arity binders body ih => intro depth; simp only [mapPattern, Pattern.isWellScopedAt, ih]
  | hsubst body replacement ihBody ihReplacement =>
      intro depth; simp only [mapPattern, Pattern.isWellScopedAt, ihBody, ihReplacement]
  | hcollection collectionType elements rest ih =>
      intro depth
      simp only [mapPattern, mapPatternList_eq_map, Pattern.isWellScopedAt]
      induction elements with
      | nil => rfl
      | cons element others othersIh =>
          simp only [List.map_cons, Pattern.isWellScopedListAt, ih element (by simp) depth,
            othersIh fun other member => ih other (by simp [member])]

/-- A frozen spelling stays a global name under a structural map. -/
def mapFrozenSpelling (symbols : LanguageDefSymbolMap) (frozen : FrozenSpelling) : FrozenSpelling :=
  ⟨mapPattern symbols frozen.spelling, by
    rw [mapPattern_freeFvarNames_eq, mapPattern_isWellScopedAt_eq]; exact frozen.ground⟩

/-- Map a quote scope. A frozen spelling is a pattern and is mapped like one; a
closure context constructor is mapped like a constructor, so that the closure
terms it builds correspond. -/
def mapQuoteScope (symbols : ReflectiveSymbols) : QuoteScope → QuoteScope
  | .closed => .closed
  | .reaching .apply => .reaching .apply
  | .reaching (.freeze frozen) => .reaching (.freeze (mapFrozenSpelling symbols.toLanguageDefSymbolMap frozen))
  | .reaching (.closure context) => .reaching (.closure (symbols.constructor context))

/-- A structural map sends a closure context constructor to its image. -/
@[simp] theorem mapQuoteScope_contextConstructor? (symbols : ReflectiveSymbols) (scope : QuoteScope) :
    (mapQuoteScope symbols scope).contextConstructor? = scope.contextConstructor?.map symbols.constructor := by
  rcases scope with _ | (_ | frozen | context) <;> rfl

@[simp] theorem mapQuoteScope_id (scope : QuoteScope) : mapQuoteScope ReflectiveSymbols.id scope = scope := by
  rcases scope with _ | (_ | frozen | context)
  · rfl
  · rfl
  · simp only [mapQuoteScope, ReflectiveSymbols.id, mapFrozenSpelling, mapPattern_id]
  · rfl

@[simp] theorem mapQuoteScope_comp (first second : ReflectiveSymbols) (scope : QuoteScope) :
    mapQuoteScope (first.comp second) scope = mapQuoteScope second (mapQuoteScope first scope) := by
  rcases scope with _ | (_ | frozen | context)
  · rfl
  · rfl
  · simp only [mapQuoteScope, ReflectiveSymbols.comp, mapFrozenSpelling, mapPattern_comp]
  · rfl

/-- Pattern transport reads only the constructor component of a symbol map. -/
theorem mapPattern_congr_constructor {first second : LanguageDefSymbolMap}
    (same : ∀ constructor, first.constructor constructor = second.constructor constructor)
    (pattern : Pattern) : mapPattern first pattern = mapPattern second pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments ih =>
      simp only [mapPattern, mapPatternList_eq_map, same constructor]
      congr 1
      exact List.map_congr_left fun argument member => ih argument member
  | hlambda binder body ih => simp only [mapPattern, ih]
  | hmultiLambda arity binders body ih => simp only [mapPattern, ih]
  | hsubst body replacement ihBody ihReplacement => simp only [mapPattern, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
      simp only [mapPattern, mapPatternList_eq_map]
      congr 1
      exact List.map_congr_left fun element member => ih element member

/-- Quote-scope transport is natural whenever constructor transport is. -/
theorem mapQuoteScope_natural {first second third fourth : ReflectiveSymbols}
    (same : ∀ constructor, second.constructor (first.constructor constructor) =
      fourth.constructor (third.constructor constructor))
    (scope : QuoteScope) :
    mapQuoteScope second (mapQuoteScope first scope) = mapQuoteScope fourth (mapQuoteScope third scope) := by
  rcases scope with _ | (_ | frozen | context)
  · rfl
  · rfl
  · simp only [mapQuoteScope, mapFrozenSpelling, QuoteScope.reaching.injEq, QuoteView.freeze.injEq]
    have spelled : mapPattern second.toLanguageDefSymbolMap (mapPattern first.toLanguageDefSymbolMap
        frozen.spelling) = mapPattern fourth.toLanguageDefSymbolMap
          (mapPattern third.toLanguageDefSymbolMap frozen.spelling) := by
      rw [← mapPattern_comp, ← mapPattern_comp]
      exact mapPattern_congr_constructor (fun constructor => same constructor) frozen.spelling
    cases frozen
    simp only [FrozenSpelling.mk.injEq]
    exact spelled
  · simp only [mapQuoteScope, same]

/-- Map one reflective presentation and all references it makes into the
five-field core. -/
def mapReflectivePresentation (symbols : ReflectiveSymbols)
    (declaration : ReflectivePresentationDecl) : ReflectivePresentationDecl :=
  { name := symbols.reflection.presentation declaration.name
    processSort := symbols.sort declaration.processSort
    nameSort := symbols.sort declaration.nameSort
    quoteConstructor := symbols.constructor declaration.quoteConstructor
    dropConstructor := symbols.constructor declaration.dropConstructor
    parallelCollection := declaration.parallelCollection
    parallelUnitConstructor :=
      symbols.constructor declaration.parallelUnitConstructor
    quoteDropEquation := symbols.equation declaration.quoteDropEquation
    quoteScope := mapQuoteScope symbols declaration.quoteScope }

/-- Map a rule-local reflective selection while preserving its distinct
matching and substitution roles. -/
def mapReflectiveRule (symbols : ReflectiveSymbols)
    (declaration : ReflectiveRuleDecl) : ReflectiveRuleDecl :=
  { name := symbols.reflection.rule declaration.name
    rewriteRule := symbols.rewrite declaration.rewriteRule
    matchingPresentation :=
      symbols.reflection.presentation declaration.matchingPresentation
    substitutionPresentation :=
      symbols.reflection.presentation declaration.substitutionPresentation }

@[simp] theorem mapReflectivePresentation_id
    (declaration : ReflectivePresentationDecl) :
    mapReflectivePresentation ReflectiveSymbols.id declaration = declaration := by
  cases declaration
  simp only [mapReflectivePresentation, mapQuoteScope_id]
  rfl

@[simp] theorem mapReflectivePresentation_comp
    (first second : ReflectiveSymbols)
    (declaration : ReflectivePresentationDecl) :
    mapReflectivePresentation (first.comp second) declaration =
      mapReflectivePresentation second
        (mapReflectivePresentation first declaration) := by
  cases declaration
  simp only [mapReflectivePresentation, mapQuoteScope_comp]
  rfl

@[simp] theorem mapReflectiveRule_id (declaration : ReflectiveRuleDecl) :
    mapReflectiveRule ReflectiveSymbols.id declaration = declaration := by
  cases declaration
  rfl

@[simp] theorem mapReflectiveRule_comp
    (first second : ReflectiveSymbols) (declaration : ReflectiveRuleDecl) :
    mapReflectiveRule (first.comp second) declaration =
      mapReflectiveRule second (mapReflectiveRule first declaration) := by
  cases declaration
  rfl

/-- Forget reflection admission while retaining the validated five-field
language. -/
def ValidatedReflectiveLanguageDef.toValidatedLanguageDef
    (presentation : ValidatedReflectiveLanguageDef) : ValidatedLanguageDef :=
  presentation.core

/-- A structural map of admitted reflective extensions. -/
structure ReflectiveStructuralMorphism
    (source target : ValidatedReflectiveLanguageDef) where
  symbols : ReflectiveSymbols
  mapsTypes : ∀ declaration,
    List.Mem declaration source.language.types →
      List.Mem (mapTypeDecl symbols.toLanguageDefSymbolMap declaration)
        target.language.types
  mapsTerms : ∀ declaration,
    List.Mem declaration source.language.terms →
      List.Mem (mapGrammarRule symbols.toLanguageDefSymbolMap declaration)
        target.language.terms
  mapsEquations : ∀ declaration,
    List.Mem declaration source.language.equations →
      List.Mem (mapEquation symbols.toLanguageDefSymbolMap declaration)
        target.language.equations
  mapsRewrites : ∀ declaration,
    List.Mem declaration source.language.rewrites →
      List.Mem (mapRewriteRule symbols.toLanguageDefSymbolMap declaration)
        target.language.rewrites
  mapsPresentations : ∀ declaration,
    List.Mem declaration source.language.reflection.presentations →
      List.Mem (mapReflectivePresentation symbols declaration)
        target.language.reflection.presentations
  mapsReflectionRules : ∀ declaration,
    List.Mem declaration source.language.reflection.rules →
      List.Mem (mapReflectiveRule symbols declaration)
        target.language.reflection.rules

namespace ReflectiveStructuralMorphism

def toCore {source target : ValidatedReflectiveLanguageDef}
    (morphism : ReflectiveStructuralMorphism source target) :
    StructuralMorphism source.toValidatedLanguageDef
      target.toValidatedLanguageDef where
  symbols := morphism.symbols.toLanguageDefSymbolMap
  mapsTypes := morphism.mapsTypes
  mapsTerms := morphism.mapsTerms
  mapsEquations := morphism.mapsEquations
  mapsRewrites := morphism.mapsRewrites

@[ext] theorem ext {source target : ValidatedReflectiveLanguageDef}
    {first second : ReflectiveStructuralMorphism source target}
    (symbols : first.symbols = second.symbols) : first = second := by
  cases first
  cases second
  cases symbols
  rfl

def id (language : ValidatedReflectiveLanguageDef) :
    ReflectiveStructuralMorphism language language where
  symbols := ReflectiveSymbols.id
  mapsTypes declaration membership := by
    rw [show ReflectiveSymbols.id.toLanguageDefSymbolMap =
      LanguageDefSymbolMap.id from rfl, mapTypeDecl_id]
    exact membership
  mapsTerms declaration membership := by
    rw [show ReflectiveSymbols.id.toLanguageDefSymbolMap =
      LanguageDefSymbolMap.id from rfl, mapGrammarRule_id]
    exact membership
  mapsEquations declaration membership := by
    rw [show ReflectiveSymbols.id.toLanguageDefSymbolMap =
      LanguageDefSymbolMap.id from rfl, mapEquation_id]
    exact membership
  mapsRewrites declaration membership := by
    rw [show ReflectiveSymbols.id.toLanguageDefSymbolMap =
      LanguageDefSymbolMap.id from rfl, mapRewriteRule_id]
    exact membership
  mapsPresentations declaration membership := by
    simpa using membership
  mapsReflectionRules declaration membership := by
    simpa using membership

def comp {first second third : ValidatedReflectiveLanguageDef}
    (left : ReflectiveStructuralMorphism first second)
    (right : ReflectiveStructuralMorphism second third) :
    ReflectiveStructuralMorphism first third where
  symbols := left.symbols.comp right.symbols
  mapsTypes declaration membership := by
    change List.Mem
      (mapTypeDecl (left.symbols.toLanguageDefSymbolMap.comp
        right.symbols.toLanguageDefSymbolMap) declaration) _
    rw [mapTypeDecl_comp]
    exact right.mapsTypes _ (left.mapsTypes declaration membership)
  mapsTerms declaration membership := by
    change List.Mem
      (mapGrammarRule (left.symbols.toLanguageDefSymbolMap.comp
        right.symbols.toLanguageDefSymbolMap) declaration) _
    rw [mapGrammarRule_comp]
    exact right.mapsTerms _ (left.mapsTerms declaration membership)
  mapsEquations declaration membership := by
    change List.Mem
      (mapEquation (left.symbols.toLanguageDefSymbolMap.comp
        right.symbols.toLanguageDefSymbolMap) declaration) _
    rw [mapEquation_comp]
    exact right.mapsEquations _ (left.mapsEquations declaration membership)
  mapsRewrites declaration membership := by
    change List.Mem
      (mapRewriteRule (left.symbols.toLanguageDefSymbolMap.comp
        right.symbols.toLanguageDefSymbolMap) declaration) _
    rw [mapRewriteRule_comp]
    exact right.mapsRewrites _ (left.mapsRewrites declaration membership)
  mapsPresentations declaration membership := by
    rw [mapReflectivePresentation_comp]
    exact right.mapsPresentations _
      (left.mapsPresentations declaration membership)
  mapsReflectionRules declaration membership := by
    rw [mapReflectiveRule_comp]
    exact right.mapsReflectionRules _
      (left.mapsReflectionRules declaration membership)

@[simp] theorem toCore_id (language : ValidatedReflectiveLanguageDef) :
    (id language).toCore = StructuralMorphism.id
      language.toValidatedLanguageDef := by
  apply StructuralMorphism.ext
  rfl

@[simp] theorem toCore_comp {first second third : ValidatedReflectiveLanguageDef}
    (left : ReflectiveStructuralMorphism first second)
    (right : ReflectiveStructuralMorphism second third) :
    (comp left right).toCore = StructuralMorphism.comp left.toCore right.toCore := by
  apply StructuralMorphism.ext
  rfl

end ReflectiveStructuralMorphism

instance : CategoryTheory.Category ValidatedReflectiveLanguageDef where
  Hom := ReflectiveStructuralMorphism
  id := ReflectiveStructuralMorphism.id
  comp := ReflectiveStructuralMorphism.comp
  id_comp morphism := by
    apply ReflectiveStructuralMorphism.ext
    rfl
  comp_id morphism := by
    apply ReflectiveStructuralMorphism.ext
    rfl
  assoc first second third := by
    apply ReflectiveStructuralMorphism.ext
    rfl

end Mettapedia.GSLT.LanguageDef.ReflectionExtension
