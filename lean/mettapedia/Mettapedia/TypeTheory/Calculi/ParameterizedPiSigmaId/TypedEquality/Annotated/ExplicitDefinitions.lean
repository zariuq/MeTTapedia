import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LaterArguments

/-!
# Explicit definitions: a constant defined by one equation, without recursion

An explicit definition gives a new constant a body over a telescope of arguments:

    plus-two n ⟶ suc (suc n)

Its declared type is the function type over the telescope (`CTele.pis`), and it computes by
one equation (`explicitEquation`): over the arguments, the constant applied to them
(`CTele.etaBody`) is the body. The body is a term of the package before the definition, so it
does not mention the constant: there is no recursion.

The body abstracted over the arguments is a closed term of the declared type
(`explicitWitness_typed`), and the declared type is a type (`explicitType_formed`), when the
context of the arguments is formed, the result type is a type there and the body has it. The
set model is in `TowerInterpretation/SetExplicitDefinitions.lean`.

Positive example: with no argument the equation is `f ⟶ body` (`explicitEquation_nil`).
Negative example: the equation of a definition with one argument is not the equation of the
definition without arguments and the same body lifted, since its left side applies the
constant (`explicitEquation_one_left`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization
open UniverseLevel (LevelOrder)

variable {Head : Type} {m : Nat}

/-- **The equation of an explicit definition**: over the arguments, the defined constant
applied to them is the body. -/
def explicitEquation (f : DeclName) (Ξ : CTele Head 0 m) (body : CTm Head m) :
    DefiningEquation Head where
  arity := m
  telescope := Ξ.extend .nil
  left := Ξ.etaBody (.const f)
  right := body

section Typing

variable {L : Type} [LevelOrder L] {R : Rules Head} {Q : ChurchRules R}
  {Ξ : CTele Head 0 m} {C body : CTm Head m}

/-- **The declared type of an explicit definition is a type**, when the context of the
arguments is formed and the result type is a type there. -/
theorem explicitType_formed (levels : LevelModel R L) (formed : CCtxFormed Q (Ξ.extend .nil))
    (resultType : CIsType Q (Ξ.extend .nil) C) : CIsType Q .nil (Ξ.pis C) :=
  CTele.pis_formed levels Ξ formed resultType

/-- **The body abstracted over the arguments is a closed term of the declared type.** -/
theorem explicitWitness_typed (levels : LevelModel R L)
    (formed : CCtxFormed Q (Ξ.extend .nil)) (resultType : CIsType Q (Ξ.extend .nil) C)
    (typed : CTyped Q (Ξ.extend .nil) body C) : CTyped Q .nil (Ξ.lams body) (Ξ.pis C) :=
  CTele.lams_typed levels Ξ formed resultType typed

end Typing

/-- Positive example: with no argument the equation is `f ⟶ body`. -/
theorem explicitEquation_nil (f : DeclName) (body : CTm Head 0) :
    explicitEquation f (.nil : CTele Head 0 0) body =
      { arity := 0, telescope := .nil, left := .const f, right := body } :=
  rfl

/-- With one argument the left side is the constant applied to the argument. -/
theorem explicitEquation_one_left (f : DeclName) (A : CTm Head 0) (body : CTm Head 1) :
    (explicitEquation f (.cons A .nil) body).left =
      (.app (.const f) (.var 0) : CTm Head 1) :=
  rfl

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
