import Mettapedia.Logic.TierZero.Adequacy.MM0ScopedArgumentAdmission
import Mettapedia.Languages.MM0.Kernel.FreeVariables

/-!
# Restricted contextual argument controls

The controls retain unrelated ambient dependencies, reject dependencies hidden
inside regular-variable declarations, and intersect aliased bound-image
restrictions rather than unioning their allowed ranges. Reordering is accepted
when independently admissible, and repeated regular or compound arguments
remain available.

A bound occurrence removed by binder-sensitive free-variable analysis still
remains an occurrence for theorem substitution. These two judgments are
deliberately exercised separately.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ScopedArgumentControls

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open MM0ContextualSupport
open MM0ScopedArgumentInterfaces
open MM0ScopedArgumentAdmission

def noSymbols : TermSignature := fun _ => none
def formal : Context := [.bound 0, .regular 0 ∅]
def independentTarget : Context := [.bound 0, .bound 0, .regular 0 {1}]
def dependentTarget : Context := [.bound 0, .bound 0, .regular 0 {0}]
def expressions : List Preterm := [.var 0, .var 2]

theorem unrelated_ambient_dependency_is_constructible :
    (construct noSymbols formal independentTarget expressions).isSome = true := by decide +kernel

theorem unrelated_ambient_variable_is_constructible :
    (construct noSymbols formal dependentTarget [.var 0, .var 1]).isSome = true := by decide +kernel

theorem an_indirect_forbidden_dependency_has_no_body :
    recoverEntry dependentTarget (Substitution.entries formal expressions)
      ((.regular 0 ∅, .var 2), 1) = none := by decide +kernel

theorem the_actual_recovered_body_uses_parameter_coordinates :
    recoverEntry independentTarget (Substitution.entries formal expressions)
      ((.regular 0 ∅, .var 2), 1) =
      some (.node (.regular 2) (.cons 0 (.idx 0) .nil)) := by decide +kernel

theorem a_forbidden_dependency_is_not_a_late_boolean_filter :
    construct noSymbols formal dependentTarget expressions = none := by decide +kernel

def aliasFormal : Context := [.bound 0, .bound 0, .regular 0 {0}]
def aliasExpressions : List Preterm := [.var 0, .var 0, .var 2]
def aliasOther : Substitution.Entry := ((.regular 0 {0}, .var 2), 2)

theorem one_alias_is_allowed_but_the_other_is_forbidden :
    sourceAllows ((.bound 0, .var 0), 0) aliasOther 0 = true ∧
      sourceAllows ((.bound 0, .var 0), 1) aliasOther 0 = false := by decide +kernel

theorem the_forbidden_alias_survives_interface_construction :
    Thin.bit (interface dependentTarget.length (Substitution.entries aliasFormal aliasExpressions) aliasOther) 0 = false := by
  decide +kernel

theorem an_allowed_alias_cannot_rescue_the_forbidden_capture :
    recoverEntry dependentTarget (Substitution.entries aliasFormal aliasExpressions) aliasOther = none := by decide +kernel

theorem aliased_theorem_bound_images_are_refused_structurally :
    construct noSymbols aliasFormal dependentTarget aliasExpressions = none := by decide +kernel

theorem reordered_bound_images_can_be_admissible :
    (construct noSymbols aliasFormal independentTarget [.var 1, .var 0, .var 2]).isSome = true := by decide +kernel

theorem repeated_regular_arguments_remain_admissible :
    (construct noSymbols [.regular 0 ∅, .regular 0 ∅] independentTarget [.var 2, .var 2]).isSome = true := by decide +kernel

def unarySymbol : TermSignature
  | 0 => some ⟨[.regular 0 ∅], 0, ∅⟩
  | _ => none

theorem compound_regular_arguments_remain_admissible :
    (construct unarySymbol [.regular 0 ∅] [.bound 0] [.app (.term 0) (.var 0)]).isSome = true := by decide +kernel

theorem sorting_is_still_required : construct noSymbols [.bound 0] [.bound 1] [.var 0] = none := by decide +kernel

theorem missing_arguments_are_still_refused : construct noSymbols formal independentTarget [.var 0] = none := by decide +kernel

def bindingSymbol : TermSignature
  | 0 => some ⟨[.bound 0, .regular 0 {0}], 0, ∅⟩
  | _ => none

def boundExpression : Preterm := .app (.app (.term 0) (.var 0)) (.var 2)

theorem occurrence_and_binder_sensitive_freedom_remain_distinct :
    Preterm.HasVar dependentTarget 0 boundExpression ∧
      ¬Preterm.IsFree bindingSymbol dependentTarget boundExpression 0 := by
  constructor
  · exact .function (.argument (.bound rfl))
  · rintro ⟨freeSet, computed, member⟩
    have result : Preterm.freeVariables? bindingSymbol dependentTarget boundExpression = some ∅ := by decide +kernel
    have same := Option.some.inj (computed.eval.symm.trans result)
    subst freeSet
    simp at member

end Mettapedia.Logic.TierZero.Adequacy.MM0ScopedArgumentControls
