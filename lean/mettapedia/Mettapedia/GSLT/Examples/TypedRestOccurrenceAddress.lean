import Mettapedia.GSLT.LanguageDef.RestOccurrenceTyping
import Mettapedia.GSLT.Examples.ScopedRhoBinding
import Mettapedia.GSLT.Examples.TypedOccurrenceSubstitution

/-!
# Authored collection-rest addresses

The rho communication schema has a collection rest on both sides. A second
many-sorted schema places a bag rest below a lambda binder. The general
address theorem extracts their actual typed collection sites and binder
prefixes. Ordinary term holes and absent rests remain distinct controls.
-/

namespace Mettapedia.GSLT.Examples.TypedRestOccurrenceAddress

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open Mettapedia.GSLT.Examples.RestAwareMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress
open Mettapedia.OSLF.MeTTaIL.RestOccurrenceAddress

set_option autoImplicit false

private abbrev atom : TypeExpr := .base "Atom"
private abbrev proc : TypeExpr := .base "Proc"

theorem rhoLeftRestSummary :
    (restSiteAt? scopedCommRewrite.left [2]).map
      (fun site => (site.name, binderCount site.context)) =
        some ("rest", 0) := by
  decide +kernel

theorem rhoRightRestSummary :
    (restSiteAt? scopedCommRewrite.right [1]).map
      (fun site => (site.name, binderCount site.context)) =
        some ("rest", 0) := by
  decide +kernel

theorem rhoLeftRestTyped :
    ∃ site focusBound focusType binderPrefix elementType,
      restSiteAt? scopedCommRewrite.left [2] = some site ∧
      site.name = "rest" ∧
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
        rhoCalcWithScopedSchemas
        (WellSorted.FreeTypeContext.ofList scopedCommRewrite.typeContext)
        focusBound site.focus focusType ∧
      WellSorted.FreeTypeContext.ofList scopedCommRewrite.typeContext
        "rest" = some (.collection site.kind elementType) ∧
      focusBound = binderPrefix ∧ binderPrefix.length = 0 ∧
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceDepthAt?
        scopedCommRewrite.left [2] 0 = some 0 := by
  have membership : scopedCommRewrite ∈ rhoCalcWithScopedSchemas.rewrites := by
    simp [rhoCalcWithScopedSchemas]
  obtain ⟨rootType, leftTyped, _⟩ :=
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType_sound
      (scoped_rho_all_rewrites_check scopedCommRewrite membership)
  obtain ⟨site, focusBound, focusType, binderPrefix, elementType,
      decoded, nameEq, focusTyped, lookup, prefixEq,
      prefixLength, runtimeDepth⟩ :=
    leftTyped.restSiteAt_of_summary rhoLeftRestSummary
  exact ⟨site, focusBound, focusType, binderPrefix, elementType,
    decoded, nameEq, focusTyped, lookup, by simpa using prefixEq,
    prefixLength, runtimeDepth⟩

theorem rhoRightRestTyped :
    ∃ site focusBound focusType binderPrefix elementType,
      restSiteAt? scopedCommRewrite.right [1] = some site ∧
      site.name = "rest" ∧
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
        rhoCalcWithScopedSchemas
        (WellSorted.FreeTypeContext.ofList scopedCommRewrite.typeContext)
        focusBound site.focus focusType ∧
      WellSorted.FreeTypeContext.ofList scopedCommRewrite.typeContext
        "rest" = some (.collection site.kind elementType) ∧
      focusBound = binderPrefix ∧ binderPrefix.length = 0 ∧
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceDepthAt?
        scopedCommRewrite.right [1] 0 = some 0 := by
  have membership : scopedCommRewrite ∈ rhoCalcWithScopedSchemas.rewrites := by
    simp [rhoCalcWithScopedSchemas]
  obtain ⟨rootType, _, rightTyped⟩ :=
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType_sound
      (scoped_rho_all_rewrites_check scopedCommRewrite membership)
  obtain ⟨site, focusBound, focusType, binderPrefix, elementType,
      decoded, nameEq, focusTyped, lookup, prefixEq,
      prefixLength, runtimeDepth⟩ :=
    rightTyped.restSiteAt_of_summary rhoRightRestSummary
  exact ⟨site, focusBound, focusType, binderPrefix, elementType,
    decoded, nameEq, focusTyped, lookup, by simpa using prefixEq,
    prefixLength, runtimeDepth⟩

private def restFree : WellSorted.FreeTypeContext :=
  WellSorted.FreeTypeContext.ofList
    [("rest", .collection .hashBag proc)]

def nestedRestSchema : Pattern :=
  .lambda none
    (.collection .hashBag
      [.apply "Embed" [.bvar 1]] (some "rest"))

theorem nestedRestSchemaTyped :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
      collectionLanguage restFree [atom] nestedRestSchema
      (.arrow proc (.collection .hashBag proc)) :=
  Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound
    (by decide +kernel)

theorem nestedRestSummary :
    (restSiteAt? nestedRestSchema [0, 1]).map
      (fun site => (site.name, binderCount site.context)) =
        some ("rest", 1) := by
  decide +kernel

theorem nestedRestTyped :
    ∃ site focusBound focusType binderPrefix elementType,
      restSiteAt? nestedRestSchema [0, 1] = some site ∧
      site.name = "rest" ∧
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
        collectionLanguage restFree focusBound site.focus focusType ∧
      restFree "rest" = some (.collection site.kind elementType) ∧
      focusBound = binderPrefix ++ [atom] ∧
      binderPrefix.length = 1 ∧
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceDepthAt?
        nestedRestSchema [0, 1] 0 = some 1 :=
  nestedRestSchemaTyped.restSiteAt_of_summary nestedRestSummary

theorem absentRestAndOrdinaryVariableHaveNoRestSite :
    restSiteAt? (.collection .hashBag [] none) [0] = none ∧
    restSiteAt? (.fvar "rest") [] = none := by
  decide +kernel

end Mettapedia.GSLT.Examples.TypedRestOccurrenceAddress
