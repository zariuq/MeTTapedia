import Mettapedia.GSLT.LanguageDef.RestAwareMorphism
import Mettapedia.GSLT.LanguageDef.MappedPresentationMorphism
import Mettapedia.GSLT.LanguageDef.RestAwareChecker

/-!
# A mapped authored collection-rest schema

This two-sort presentation makes the transport theorem concrete. Its rewrite
contains a collection rest at the result sort and an element constructor
crossing from the other sort. Renaming both sorts and both constructors
preserves its schema typing. Collapsing the two sorts fails validation.
-/

namespace Mettapedia.GSLT.Examples.RestAwareMorphism

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.RestAwareTyping
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

def collectionLanguage : LanguageDef :=
  { name := "CollectionRestTransport"
    types := [TypeDecl.plain "Atom", TypeDecl.plain "Proc"]
    terms :=
      [{ label := "Embed", category := "Proc",
         params := [.simple "atom" (.base "Atom")],
         syntaxPattern := [.terminal "embed", .nonTerminal "atom"] },
       { label := "Parallel", category := "Proc",
         params := [.simple "procs" (.collection .hashBag (.base "Proc"))],
         syntaxPattern := [.terminal "{", .nonTerminal "procs",
           .terminal "}"] }]
    equations := []
    rewrites :=
      [{ name := "DropEmbedded", premises := [],
         typeContext :=
           [("atom", .base "Atom"),
            ("rest", .collection .hashBag (.base "Proc"))],
         left := .collection .hashBag
           [.apply "Embed" [.fvar "atom"]] (some "rest"),
         right := .collection .hashBag [] (some "rest") }] }

theorem collectionLanguage_validates : collectionLanguage.validate = [] := by
  simp [LanguageDef.validate, collectionLanguage,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateTerm,
    LanguageDef.validateRewrite,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validatePatternConstructors,
    LanguageDef.validateRulePatterns,
    LanguageDef.typeNames, TypeDecl.plain, TypeExpr.baseNames,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

def validatedCollectionLanguage : ValidatedLanguageDef :=
  ⟨collectionLanguage, collectionLanguage_validates⟩

theorem collection_rewrite_checks :
    checkRewriteHasType collectionLanguage collectionLanguage.rewrites[0] =
      true := by
  decide +kernel

theorem collection_rewrite_typed :
    RewriteHasType collectionLanguage collectionLanguage.rewrites[0] :=
  checkRewriteHasType_sound collection_rewrite_checks

theorem collection_rewrites_typed :
    RewritesHaveType validatedCollectionLanguage := by
  intro rewrite membership
  simp [validatedCollectionLanguage, collectionLanguage] at membership
  subst rewrite
  exact collection_rewrite_typed

def renameSymbols : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with
    sort := fun sortName =>
      if sortName = "Atom" then "Seed"
      else if sortName = "Proc" then "Process"
      else sortName
    constructor := fun constructorName => constructorName ++ "Mapped"
    rewrite := fun rewriteName => rewriteName ++ "Mapped" }

theorem renamed_collectionLanguage_validates :
    (mapLanguageDef renameSymbols collectionLanguage).validate = [] := by
  simp [LanguageDef.validate, mapLanguageDef, renameSymbols, collectionLanguage,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateTerm,
    LanguageDef.validateRewrite,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validatePatternConstructors,
    LanguageDef.validateRulePatterns,
    LanguageDef.typeNames, TypeDecl.plain, TypeExpr.baseNames,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, mapTypeDecl, mapGrammarRule,
    mapTypeExpr, mapTermParam, mapTypeContext, mapRewriteRule, mapPattern]

def renamedCollectionLanguage : ValidatedLanguageDef :=
  validatedImage validatedCollectionLanguage renameSymbols
    renamed_collectionLanguage_validates

def renameMorphism :
    StructuralMorphism validatedCollectionLanguage
      renamedCollectionLanguage :=
  structuralMapToValidatedImage validatedCollectionLanguage renameSymbols
    renamed_collectionLanguage_validates

theorem renamed_collection_rewrite_typed :
    RewriteHasType renamedCollectionLanguage.language
      (mapRewriteRule renameSymbols collectionLanguage.rewrites[0]) :=
  collection_rewrite_typed.map renameMorphism

theorem renamed_collection_rewrites_typed :
    RewritesHaveType renamedCollectionLanguage := by
  apply RewritesHaveType.map_of_surjective renameMorphism
    collection_rewrites_typed
  intro rewrite membership
  change rewrite ∈
    (collectionLanguage.rewrites.map (mapRewriteRule renameSymbols)) at membership
  obtain ⟨sourceRewrite, sourceMembership, equality⟩ :=
    List.mem_map.mp membership
  exact ⟨sourceRewrite, sourceMembership, equality⟩

theorem renamed_collection_rewrite_checks :
    checkRewriteHasType renamedCollectionLanguage.language
      (mapRewriteRule renameSymbols collectionLanguage.rewrites[0]) = true := by
  decide +kernel

def collapseSymbols : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with
    sort := fun _ => "One" }

theorem collapsed_sort_image_fails_validation :
    (mapLanguageDef collapseSymbols collectionLanguage).validate ≠ [] := by
  decide +kernel

/-! A validated target may add a rule whose two sides have incompatible
types. This shows why whole-target transport needs the coverage premise. -/

def mismatchedRewrite : RewriteRule :=
  { name := "Mismatch"
    premises := []
    typeContext := [("atom", .base "Atom")]
    left := .apply "Embed" [.fvar "atom"]
    right := .fvar "atom" }

def extendedLanguage : LanguageDef :=
  { collectionLanguage with
    rewrites := collectionLanguage.rewrites ++ [mismatchedRewrite] }

theorem extendedLanguage_validates : extendedLanguage.validate = [] := by
  simp [LanguageDef.validate, extendedLanguage, mismatchedRewrite,
    collectionLanguage, LanguageDef.duplicateErrors,
    LanguageDef.duplicateErrorsAux, LanguageDef.validateTerm,
    LanguageDef.validateRewrite,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validatePatternConstructors,
    LanguageDef.validateRulePatterns,
    LanguageDef.typeNames, TypeDecl.plain, TypeExpr.baseNames,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

def validatedExtendedLanguage : ValidatedLanguageDef :=
  ⟨extendedLanguage, extendedLanguage_validates⟩

def inclusionMorphism :
    StructuralMorphism validatedCollectionLanguage
      validatedExtendedLanguage where
  symbols := LanguageDefSymbolMap.id
  mapsTypes := by
    intro declaration membership
    simpa [validatedCollectionLanguage, validatedExtendedLanguage,
      extendedLanguage] using membership
  mapsTerms := by
    intro rule membership
    simpa [validatedCollectionLanguage, validatedExtendedLanguage,
      extendedLanguage] using membership
  mapsEquations := by
    intro equation membership
    simpa [validatedCollectionLanguage, validatedExtendedLanguage,
      extendedLanguage] using membership
  mapsRewrites := by
    intro rewrite membership
    have sourceMembership : List.Mem rewrite collectionLanguage.rewrites := by
      simpa [validatedCollectionLanguage] using membership
    rw [mapRewriteRule_id]
    change List.Mem rewrite
      (collectionLanguage.rewrites ++ [mismatchedRewrite])
    exact List.mem_append_left _ sourceMembership

theorem mismatch_not_typed :
    ¬ RewriteHasType extendedLanguage mismatchedRewrite := by
  intro typed
  obtain ⟨type, leftTyped, rightTyped⟩ := typed
  have rightType : type = .base "Atom" := by
    cases rightTyped with
    | fvar lookup =>
        simpa [mismatchedRewrite, WellSorted.FreeTypeContext.ofList] using
          lookup.symm
  have leftType : type = .base "Proc" := by
    obtain ⟨rule, membership, label, typeEquation⟩ :=
      WellSorted.declared_constructor_of_hasType_apply leftTyped.forget
    simp [extendedLanguage, collectionLanguage] at membership
    rcases membership with ruleIsEmbed | ruleIsParallel
    · subst rule
      simpa [collectionLanguage] using typeEquation
    · subst rule
      simp at label
  have impossible : (TypeExpr.base "Atom") = .base "Proc" :=
    rightType.symm.trans leftType
  simp at impossible

theorem extended_rewrites_not_all_typed :
    ¬ RewritesHaveType validatedExtendedLanguage := by
  intro allTyped
  apply mismatch_not_typed
  exact allTyped mismatchedRewrite (by
    simp [validatedExtendedLanguage, extendedLanguage])

end Mettapedia.GSLT.Examples.RestAwareMorphism
