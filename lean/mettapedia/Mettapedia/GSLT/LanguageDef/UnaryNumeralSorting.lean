import Mettapedia.OSLF.MeTTaIL.UnaryNumerals
import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# Unary numerals as sorted terms

A language that declares a nullary constructor and a unary constructor on
one sort has the unary numerals built from them as terms of that sort, in
every typing context.  A numeral is an object pattern: it contains no pending
substitution and no open collection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A numeral is an object pattern. -/
@[simp] theorem isObjectPattern_unary (zero succ : String) (count : Nat) :
    isObjectPattern (Pattern.unary zero succ count) = true := by
  induction count with
  | zero => simp [isObjectPattern, isObjectPatternList]
  | succ count recurse => simp [isObjectPattern, isObjectPatternList, recurse]

/-- **The numerals of a declared zero and successor are terms of their
sort.** -/
theorem hasType_unary {language : LanguageDef} {zeroRule succRule : GrammarRule}
    {parameterName : String}
    (zeroMember : zeroRule ∈ language.terms) (succMember : succRule ∈ language.terms)
    (zeroParams : zeroRule.params = [])
    (succParams : succRule.params = [.simple parameterName (.base zeroRule.category)])
    (category : succRule.category = zeroRule.category)
    (free : FreeTypeContext) (bound : List TypeExpr) (count : Nat) :
    HasType language free bound (Pattern.unary zeroRule.label succRule.label count)
      (.base zeroRule.category) := by
  induction count with
  | zero =>
      exact HasType.constructor zeroMember
        (by rintro ⟨name, kind, element, shape⟩; rw [zeroParams] at shape; cases shape)
        (zeroParams ▸ .nil)
  | succ count recurse =>
      have typed := HasType.constructor (free := free) (bound := bound)
        (arguments := [Pattern.unary zeroRule.label succRule.label count]) succMember
        (by rintro ⟨name, kind, element, shape⟩; rw [succParams] at shape; cases shape)
        (succParams ▸ .cons trivial rfl recurse .nil)
      rw [category] at typed
      exact typed

end Mettapedia.GSLT.LanguageDef.WellSorted
