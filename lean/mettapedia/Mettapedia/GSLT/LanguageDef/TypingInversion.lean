import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# Inversion of typing and of renaming at a constructor application

Two facts read a constructor application back.  A typing of an application
comes from a declared constructor with that label, whose parameters type the
arguments.  A renamed pattern that is an application is the renaming of an
application, argument by argument.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A typed constructor application is typed by a declared constructor with
that label: its result sort is the type, and its parameters type the
arguments. -/
theorem HasType.apply_inv {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {label : String} {arguments : List Pattern} {type : TypeExpr}
    (typed : HasType language free bound (.apply label arguments) type) :
    ∃ rule, rule ∈ language.terms ∧ rule.label = label ∧ type = .base rule.category ∧
      ¬ UsesBareCollection rule ∧
        ArgumentsHaveTypes language free bound arguments rule.params := by
  generalize source : Pattern.apply label arguments = pattern at typed
  cases typed with
  | constructor membership notBare argumentsTyped =>
      simp only [Pattern.apply.injEq] at source
      obtain ⟨rfl, rfl⟩ := source
      exact ⟨_, membership, rfl, rfl, notBare, argumentsTyped⟩
  | bvar _ => cases source
  | fvar _ => cases source
  | lambda _ => cases source
  | multiLambda _ => cases source
  | subst _ _ => cases source
  | collection _ => cases source
  | collectionConstructor _ _ _ => cases source

end Mettapedia.GSLT.LanguageDef.WellSorted

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A renamed pattern that is a constructor application is the renaming of a
constructor application. -/
theorem mapPattern_eq_apply_iff (symbols : LanguageDefSymbolMap) (pattern : Pattern)
    (label : String) (arguments : List Pattern) :
    mapPattern symbols pattern = .apply label arguments ↔
      ∃ original originalArguments, pattern = .apply original originalArguments ∧
        symbols.constructor original = label ∧
          originalArguments.map (mapPattern symbols) = arguments := by
  cases pattern <;> simp [mapPattern]

end Mettapedia.GSLT.LanguageDef
