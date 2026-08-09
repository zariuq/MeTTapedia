import Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Executable checking for reflection-indexed carriers

The core checker remains a checker for the five-field language.  This module
adds the independent quote-sealing check selected by a reflection profile and
proves the combined Boolean exactly characterizes the combined carrier.
-/

namespace Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.Syntax

def checkReflectiveScopeSafeAt (profile : ReflectionProfile) (depth : Nat)
    (pattern : Pattern) : Bool :=
  profile.presentations.all fun presentation =>
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt
      presentation.quoteConstructor depth pattern

@[simp]
theorem checkReflectiveScopeSafeAt_eq_true_iff
    (profile : ReflectionProfile) (depth : Nat) (pattern : Pattern) :
    checkReflectiveScopeSafeAt profile depth pattern = true ↔
      ReflectiveScopeSafeAt profile depth pattern := by
  simp [checkReflectiveScopeSafeAt, ReflectiveScopeSafeAt, List.all_eq_true]

def checkOpenPatternWellSorted (profile : ReflectionProfile)
    (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (pattern : Pattern) : Bool :=
  WellSorted.checkOpenPatternWellSorted language free bound expected pattern &&
    checkReflectiveScopeSafeAt profile bound.length pattern

theorem checkOpenPatternWellSorted_eq_true_iff
    (profile : ReflectionProfile) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr)
    (expected : TypeExpr) (pattern : Pattern) :
    checkOpenPatternWellSorted profile language free bound expected pattern =
        true ↔
      OpenPatternWellSorted profile language free bound expected pattern := by
  simp [checkOpenPatternWellSorted, OpenPatternWellSorted,
    WellSorted.checkOpenPatternWellSorted_eq_true_iff,
    checkReflectiveScopeSafeAt_eq_true_iff]

end Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
