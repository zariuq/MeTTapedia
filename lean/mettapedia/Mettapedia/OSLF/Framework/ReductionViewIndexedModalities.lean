import Mettapedia.OSLF.Framework.DerivedTyping

/-!
# Modal typing is indexed by an operational reduction view

An authored language determines its sorts and constructor crossings, but it
does not by itself determine which sort carries reduction.  OSLF's derived
modal classification takes that reduction sort as an explicit parameter.

This module packages the parameter as a typed operational view and gives the
generic classification laws.  The view selects the reduction carrier; the
language's sorts and constructor crossings alone do not make that selection.
-/


set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ReductionViewIndexedModalities

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedTyping

/-- A reduction carrier selected from the sorts of one authored language. -/
structure ReductionView
    (language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) where
  carrier : LangSort language

namespace ReductionView

def role {language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (view : ReductionView language) {domain codomain : LangSort language}
    (arrow : SortArrow language domain codomain) : ConstructorRole :=
  classifyArrow language view.carrier.val arrow

/-- A quoting observation forces the arrow's domain to be the selected
reduction carrier. -/
theorem role_eq_quoting_iff
    {language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (view : ReductionView language) {domain codomain : LangSort language}
    (arrow : SortArrow language domain codomain) :
    view.role arrow = .quoting ↔ domain.val = view.carrier.val :=
  classifyArrow_eq_quoting_iff language view.carrier.val arrow

/-- Reflection likewise depends on the selected carrier, with the usual
domain-side exclusion. -/
theorem role_eq_reflecting_iff
    {language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (view : ReductionView language) {domain codomain : LangSort language}
    (arrow : SortArrow language domain codomain) :
    view.role arrow = .reflecting ↔
      domain.val ≠ view.carrier.val ∧ codomain.val = view.carrier.val :=
  classifyArrow_eq_reflecting_iff language view.carrier.val arrow

end ReductionView

#print axioms ReductionView.role_eq_quoting_iff
#print axioms ReductionView.role_eq_reflecting_iff

end Mettapedia.OSLF.Framework.ReductionViewIndexedModalities
