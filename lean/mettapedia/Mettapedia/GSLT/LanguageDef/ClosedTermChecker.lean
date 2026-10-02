import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Closed semantic terms from executable checks

Membership of a raw pattern in the closed carrier of a sort is a conjunction
of five conditions, each of which has an executable test.  This module
packages the tests, so that a concrete term of an authored language can be
placed in its carrier by evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- The executable test for membership in the closed carrier of a sort. -/
def checkClosedTerm (language : LanguageDef) (sort : LangSort language)
    (pattern : Pattern) : Bool :=
  checkHasType language FreeTypeContext.empty [] pattern (.base sort.1) &&
    pattern.isGround && pattern.hasCanonicalBinderMetadata &&
    isObjectPattern pattern && pattern.isWellScopedAt 0

/-- A pattern passing the test is a closed term of the sort. -/
theorem checkClosedTerm_sound {language : LanguageDef} {sort : LangSort language}
    {pattern : Pattern} (checked : checkClosedTerm language sort pattern = true) :
    ClosedTermWellSorted language sort pattern := by
  simp only [checkClosedTerm, Bool.and_eq_true] at checked
  obtain ⟨⟨⟨⟨typed, ground⟩, canonical⟩, object⟩, wellScoped⟩ := checked
  exact ⟨checkHasType_sound typed, ground, canonical, object, wellScoped⟩

/-- The closed term whose membership the test establishes. -/
def ClosedTerm.ofCheck {language : LanguageDef} {sort : LangSort language}
    (pattern : Pattern) (checked : checkClosedTerm language sort pattern = true) :
    ClosedTerm language sort :=
  ⟨pattern, checkClosedTerm_sound checked⟩

@[simp] theorem ClosedTerm.ofCheck_val {language : LanguageDef} {sort : LangSort language}
    (pattern : Pattern) (checked : checkClosedTerm language sort pattern = true) :
    (ClosedTerm.ofCheck pattern checked).1 = pattern := rfl

end Mettapedia.GSLT.LanguageDef.WellSorted
