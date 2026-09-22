import Mettapedia.OSLF.Framework.DisplayedRewriteTyping
import Mettapedia.GSLT.LanguageDef.WellSortedOccurrence

/-!
# Coherent fvar typing at displayed rewrite occurrences

This connects exact zipper descent to the existing displayed-typing record.
No second occurrence carrier or rule definition is introduced. The resulting
record is accompanied by a `TypedAt` certificate tying its binder prefix to
the actual selected path, rather than merely typing the focus in an arbitrary
ambient context. The existing object-source restriction remains explicit.
-/

namespace Mettapedia.OSLF.Framework.DisplayedRewriteTyping

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option autoImplicit false

/-- Recover a displayed fvar's scope from the authored left typing, and retain
the corresponding right typing. The source variable's exact authored type is
read at that occurrence. A permission context is not inferred. -/
theorem exists_fvar_coherent {definition : ValidatedLanguageDef}
    (site : DisplayedRewriteSite definition.language)
    (name : String) (focus : site.focus = .fvar name)
    (rewriteType : TypeExpr)
    (leftTyped : HasType definition.language
      (FreeTypeContext.ofList site.rewrite.typeContext) [] site.rewrite.left rewriteType)
    (rightTyped : HasType definition.language
      (FreeTypeContext.ofList site.rewrite.typeContext) [] site.rewrite.right rewriteType)
    (sourceIsObject : isObjectPattern site.rewrite.left = true) :
    ∃ typing : DisplayedRewriteTyping definition,
      typing.site = site ∧ typing.rewriteType = rewriteType ∧
      TypedAt definition.language (FreeTypeContext.ofList site.rewrite.typeContext)
        (.fvar name) site.context [] rewriteType
        typing.focusBoundPrefix typing.focusType ∧
      FreeTypeContext.ofList site.rewrite.typeContext name = some typing.focusType := by
  have selection := site.selects
  rw [focus] at selection
  obtain ⟨focusBound, focusType, selected, lookup⟩ :=
    leftTyped.selected_fvar selection
  refine ⟨{
    site := site
    rewriteType := rewriteType
    focusBoundPrefix := focusBound
    focusType := focusType
    rewriteLeftTyped := leftTyped
    rewriteRightTyped := rightTyped
    sourceIsObject := sourceIsObject
    focusTyped := ?_ }, rfl, rfl, selected, lookup⟩
  rw [focus]
  exact selected.focus_typed

end Mettapedia.OSLF.Framework.DisplayedRewriteTyping
