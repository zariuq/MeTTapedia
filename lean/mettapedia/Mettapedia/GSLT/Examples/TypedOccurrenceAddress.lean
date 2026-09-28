import Mettapedia.GSLT.LanguageDef.TypedOccurrenceAddress
import Mettapedia.GSLT.Examples.TypedOccurrenceSubstitution
import Mettapedia.GSLT.Examples.ScopedRhoBinding

/-!
# Authored binder paths with extracted types

The actual `Wrap` rule with a wrong dependency sort has a typed schema and a
structurally admitted binding declaration. Address decoding recovers its one
binder and the existing typed zipper, making the missing argument-sort check
precise. The rho communication rule exercises both a lambda path and an
explicit-substitution body path through its authored collection schema.
-/

namespace Mettapedia.GSLT.Examples.TypedOccurrenceAddress

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Examples.TypedOccurrenceSubstitution
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress

set_option autoImplicit false

private abbrev proc : TypeExpr := .base "Proc"

def wrongSortContext : OneHoleContext :=
  .apply "Wrap" [] (.lambda none .hole) []

theorem wrongSortAddress_decodes :
    termZipperAt? wrongSortBindingRule.left [0, 0] =
      some ("X", wrongSortContext) := by
  decide +kernel

theorem wrongSortAddress_has_typed_binder :
    ∃ focusBound result binderPrefix,
      TypedAt wrongSortBindingLanguage
        (FreeTypeContext.ofList wrongSortBindingRule.typeContext)
        (.fvar "X") wrongSortContext [] proc focusBound result ∧
      FreeTypeContext.ofList wrongSortBindingRule.typeContext "X" =
        some result ∧
      focusBound = binderPrefix ∧
      binderPrefix.length = 1 ∧
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceDepthAt?
        wrongSortBindingRule.left [0, 0] 0 = some 1 := by
  have rootTyped :
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
        wrongSortBindingLanguage
        (FreeTypeContext.ofList wrongSortBindingRule.typeContext) []
        wrongSortBindingRule.left proc :=
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound
      (by decide +kernel)
  obtain ⟨focusBound, result, binderPrefix, selected, lookup,
      prefixEq, prefixLength, runtimeDepth⟩ :=
    rootTyped.typedAtAddress wrongSortAddress_decodes
  have oneBinder : binderPrefix.length = 1 := by
    simpa [wrongSortContext, binderCount] using prefixLength
  refine ⟨focusBound, result, binderPrefix, selected, lookup, ?_, ?_, ?_⟩
  · simpa using prefixEq
  · exact oneBinder
  · simpa [oneBinder] using runtimeDepth

/-- The two authored occurrences of `p` cross exactly one binder each, but
one is a lambda body and the other an explicit-substitution body. -/
theorem rho_left_address_summary :
    (termZipperAt? scopedCommRewrite.left [0, 1, 0]).map
      (fun entry => (entry.1, binderCount entry.2)) =
        some ("p", 1) := by
  decide +kernel

theorem rho_right_address_summary :
    (termZipperAt? scopedCommRewrite.right [0, 0]).map
      (fun entry => (entry.1, binderCount entry.2)) =
        some ("p", 1) := by
  decide +kernel

theorem rho_left_address_typed :
    ∃ rootType context focusBound result binderPrefix,
      termZipperAt? scopedCommRewrite.left [0, 1, 0] =
        some ("p", context) ∧
      TypedAt rhoCalcWithScopedSchemas
        (FreeTypeContext.ofList scopedCommRewrite.typeContext)
        (.fvar "p") context [] rootType focusBound result ∧
      FreeTypeContext.ofList scopedCommRewrite.typeContext "p" =
        some result ∧
      focusBound = binderPrefix ∧ binderPrefix.length = 1 ∧
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceDepthAt?
        scopedCommRewrite.left [0, 1, 0] 0 = some 1 := by
  have membership : scopedCommRewrite ∈ rhoCalcWithScopedSchemas.rewrites := by
    simp [rhoCalcWithScopedSchemas]
  obtain ⟨rootType, leftTyped, _⟩ :=
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType_sound
      (scoped_rho_all_rewrites_check scopedCommRewrite membership)
  obtain ⟨context, focusBound, result, binderPrefix, decoded, selected,
      lookup, prefixEq, prefixLength, runtimeDepth⟩ :=
    leftTyped.typedAtAddress_of_summary rho_left_address_summary
  exact ⟨rootType, context, focusBound, result, binderPrefix,
    decoded, selected, lookup, by simpa using prefixEq,
    prefixLength, runtimeDepth⟩

theorem rho_right_address_typed :
    ∃ rootType context focusBound result binderPrefix,
      termZipperAt? scopedCommRewrite.right [0, 0] =
        some ("p", context) ∧
      TypedAt rhoCalcWithScopedSchemas
        (FreeTypeContext.ofList scopedCommRewrite.typeContext)
        (.fvar "p") context [] rootType focusBound result ∧
      FreeTypeContext.ofList scopedCommRewrite.typeContext "p" =
        some result ∧
      focusBound = binderPrefix ∧ binderPrefix.length = 1 ∧
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceDepthAt?
        scopedCommRewrite.right [0, 0] 0 = some 1 := by
  have membership : scopedCommRewrite ∈ rhoCalcWithScopedSchemas.rewrites := by
    simp [rhoCalcWithScopedSchemas]
  obtain ⟨rootType, _, rightTyped⟩ :=
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType_sound
      (scoped_rho_all_rewrites_check scopedCommRewrite membership)
  obtain ⟨context, focusBound, result, binderPrefix, decoded, selected,
      lookup, prefixEq, prefixLength, runtimeDepth⟩ :=
    rightTyped.typedAtAddress_of_summary rho_right_address_summary
  exact ⟨rootType, context, focusBound, result, binderPrefix,
    decoded, selected, lookup, by simpa using prefixEq,
    prefixLength, runtimeDepth⟩

/-- A collection-rest address is observed by the executable reader but has
no ordinary term zipper. Its sorted address law is a separate obligation. -/
theorem rest_slot_is_not_a_term_hole :
    Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceAt?
      (.collection .hashBag [] (some "rest")) [0] = some "rest" ∧
    termZipperAt? (.collection .hashBag [] (some "rest")) [0] = none := by
  decide +kernel

end Mettapedia.GSLT.Examples.TypedOccurrenceAddress
