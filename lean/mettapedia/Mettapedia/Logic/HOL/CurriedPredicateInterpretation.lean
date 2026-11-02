import Mettapedia.Logic.HOL.ConstructorGuardInterpretation
import Mettapedia.Logic.HOL.CurriedPredicates

/-!
# Curried field programs under closed-term interpretation

The laws derive complete predicate-program agreement from the images of their
inputs. Ordered fields, binder scopes and result-carrier transports remain
explicit, including for compound and noninjective type interpretations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.CurriedPredicates
open FiniteConstructorEncoding
universe u v u' v'
variable {Base : Type u} {Const : Ty Base → Type v}
  {Target : Type u'} {Symbols : Ty Target → Type v'}
  (interpretation : TermInterpretation Base Const Target Symbols)
  {Γ : Ctx Base}

theorem functionType_interpret (fields : List (Ty Base)) (result : Ty Base) :
    Ty.substitute interpretation.types (FunctionType fields result) =
      FunctionType (fields.map (Ty.substitute interpretation.types))
        (Ty.substitute interpretation.types result) := by
  induction fields with
  | nil => rfl
  | cons first rest previous =>
      simp only [FunctionType, List.foldr_cons, List.map_cons, Ty.substitute_arr] at *
      rw [previous]

theorem applyFields_interpret {result : Ty Base} (fields : List (Ty Base))
    (function : Term Const Γ (FunctionType fields result))
    (targetFunction : Term Symbols (Γ.map (Ty.substitute interpretation.types))
      (FunctionType (fields.map (Ty.substitute interpretation.types))
        (Ty.substitute interpretation.types result)))
    (functionSame : HEq (interpretation.term function) targetFunction)
    (arguments : Arguments Const Γ fields) :
    interpretation.term (applyFields fields function arguments) =
      applyFields (fields.map (Ty.substitute interpretation.types)) targetFunction
        (interpretArguments interpretation fields arguments) := by
  induction fields with
  | nil => exact eq_of_heq functionSame
  | cons first rest previous =>
      apply previous (.app function arguments.1)
        (.app targetFunction (interpretation.term arguments.1)) _ arguments.2
      rw [TermInterpretation.term_app]
      congr 1
      · exact functionType_interpret interpretation rest result

theorem constant_interpret (fields : List (Ty Base)) (formula : Formula Const Γ) :
    HEq (interpretation.term (constant fields formula))
      (constant (fields.map (Ty.substitute interpretation.types)) (interpretation.term formula)) := by
  apply abstractArguments_interpret
  intro Δ rho mapped compatible arguments
  exact TermInterpretation.term_subst interpretation rho mapped compatible formula

theorem conjoin_interpret (fields : List (Ty Base))
    (first second : Term Const Γ (handlerType fields))
    (targetFirst targetSecond : Term Symbols (Γ.map (Ty.substitute interpretation.types))
      (handlerType (fields.map (Ty.substitute interpretation.types))))
    (firstSame : HEq (interpretation.term first) targetFirst)
    (secondSame : HEq (interpretation.term second) targetSecond) :
    HEq (interpretation.term (conjoin fields first second))
      (conjoin (fields.map (Ty.substitute interpretation.types)) targetFirst targetSecond) := by
  apply abstractArguments_interpret
  intro Δ rho mapped compatible arguments
  rw [TermInterpretation.term_and, applyArguments_interpret, applyArguments_interpret]
  apply congrArg₂ Term.and
  · apply congrArg (fun function => applyArguments _ function (interpretArguments interpretation fields arguments))
    exact eq_of_heq ((interpretHandler_heq interpretation _ _).trans
      (TermInterpretation.term_subst_heq interpretation rho mapped compatible
        (handlerType_interpret interpretation fields) first targetFirst firstSame))
  · apply congrArg (fun function => applyArguments _ function (interpretArguments interpretation fields arguments))
    exact eq_of_heq ((interpretHandler_heq interpretation _ _).trans
      (TermInterpretation.term_subst_heq interpretation rho mapped compatible
        (handlerType_interpret interpretation fields) second targetSecond secondSame))

theorem equalTo_interpret {result : Ty Base} (fields : List (Ty Base))
    (function : Term Const Γ (FunctionType fields result)) (expected : Term Const Γ result)
    (targetFunction : Term Symbols (Γ.map (Ty.substitute interpretation.types))
      (FunctionType (fields.map (Ty.substitute interpretation.types))
        (Ty.substitute interpretation.types result)))
    (functionSame : HEq (interpretation.term function) targetFunction) :
    HEq (interpretation.term (equalTo fields function expected))
      (equalTo (fields.map (Ty.substitute interpretation.types)) targetFunction (interpretation.term expected)) := by
  apply abstractArguments_interpret
  intro Δ rho mapped compatible arguments
  rw [TermInterpretation.term_eq]
  apply congrArg₂ Term.eq
  · exact applyFields_interpret interpretation fields _ _
      (TermInterpretation.term_subst_heq interpretation rho mapped compatible
        (functionType_interpret interpretation fields result) function targetFunction functionSame) arguments
  · exact TermInterpretation.term_subst interpretation rho mapped compatible expected

theorem conjoin_interpret_as (fields : List (Ty Base)) (targetFields : List (Ty Target))
    (same : fields.map (Ty.substitute interpretation.types) = targetFields)
    (first second : Term Const Γ (handlerType fields))
    (targetFirst targetSecond : Term Symbols (Γ.map (Ty.substitute interpretation.types)) (handlerType targetFields))
    (firstSame : HEq (interpretation.term first) targetFirst)
    (secondSame : HEq (interpretation.term second) targetSecond) :
    HEq (interpretation.term (conjoin fields first second))
      (conjoin targetFields targetFirst targetSecond) := by
  cases same
  exact conjoin_interpret interpretation fields first second targetFirst targetSecond firstSame secondSame

theorem equalTo_interpret_as {result : Ty Base} (fields : List (Ty Base)) (targetFields : List (Ty Target))
    (same : fields.map (Ty.substitute interpretation.types) = targetFields)
    (function : Term Const Γ (FunctionType fields result)) (expected : Term Const Γ result)
    (targetFunction : Term Symbols (Γ.map (Ty.substitute interpretation.types))
      (FunctionType targetFields (Ty.substitute interpretation.types result)))
    (functionSame : HEq (interpretation.term function) targetFunction) :
    HEq (interpretation.term (equalTo fields function expected))
      (equalTo targetFields targetFunction (interpretation.term expected)) := by
  cases same
  exact equalTo_interpret interpretation fields function expected targetFunction functionSame

theorem choose_interpret (fields : List (Ty Base)) {count : Nat}
    (conditions : Fin count → Term Const Γ (handlerType fields))
    (targetConditions : Fin count → Term Symbols (Γ.map (Ty.substitute interpretation.types))
      (handlerType (fields.map (Ty.substitute interpretation.types))))
    (conditionsSame : ∀ position, HEq (interpretation.term (conditions position)) (targetConditions position)) :
    HEq (interpretation.term (choose fields conditions))
      (choose (fields.map (Ty.substitute interpretation.types)) targetConditions) := by
  apply abstractArguments_interpret
  intro Δ rho mapped compatible arguments
  rw [any_interpret, List.map_ofFn]
  apply congrArg any
  apply congrArg List.ofFn
  funext position
  dsimp only [Function.comp_apply]
  rw [applyArguments_interpret]
  apply congrArg (fun function => applyArguments _ function (interpretArguments interpretation fields arguments))
  exact eq_of_heq ((interpretHandler_heq interpretation _ _).trans
    (TermInterpretation.term_subst_heq interpretation rho mapped compatible
      (handlerType_interpret interpretation fields) _ _ (conditionsSame position)))

#print axioms applyFields_interpret
#print axioms constant_interpret
#print axioms conjoin_interpret
#print axioms equalTo_interpret
#print axioms choose_interpret
end Mettapedia.Logic.HOL.CurriedPredicates
