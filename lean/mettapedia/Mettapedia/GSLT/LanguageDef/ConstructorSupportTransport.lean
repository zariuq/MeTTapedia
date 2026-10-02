import Mettapedia.GSLT.LanguageDef.ConstructorSupport

/-!
# Constructor support from the range of a symbol map

A translated pattern uses only constructor labels in the map's range. This
specializes the existing support-transport law without imposing an artificial
restriction on the source alphabet.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

theorem constructorsWithin_unrestricted (pattern : Pattern) :
    ConstructorsWithin (fun _ => True) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ | hfvar _ => trivial
  | happly _ arguments ih =>
      exact ⟨trivial, (constructorListWithin_iff_forall arguments).mpr ih⟩
  | hlambda _ _ ih | hmultiLambda _ _ _ ih => exact ih
  | hsubst _ _ body replacement => exact ⟨body, replacement⟩
  | hcollection _ elements _ ih => exact (constructorListWithin_iff_forall elements).mpr ih

/-- Every translated constructor lies in the declared range, independently
of the source pattern's binding and collection structure. -/
theorem constructorsWithin_mapPattern_of_range (symbols : LanguageDefSymbolMap)
    {allowed : String → Prop} (rangeAllowed : ∀ label, allowed (symbols.constructor label))
    (pattern : Pattern) : ConstructorsWithin allowed (mapPattern symbols pattern) :=
  constructorsWithin_mapPattern symbols (fun label _ => rangeAllowed label)
    (constructorsWithin_unrestricted pattern)

end Mettapedia.GSLT.LanguageDef
