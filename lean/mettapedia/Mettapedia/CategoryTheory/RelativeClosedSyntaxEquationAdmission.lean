import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationInterpretation

/-!
# Equation admission from complete independent expression readings

Each independently authored parallel pair is evaluated before its equation
is admitted. Equality of the supplied complete values is equivalent to
equality of the actual quotient-functor readings. Consequently every new
equation is realized exactly when the independently read diagrams agree.
The target values retain their endpoints as well as their arrows.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.EquationExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation

universe k w z

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (signature : Signature (C := C) (symbols := symbols))
variable {Index : Type k} (declarations : Index → Declaration signature)
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : Assignment C symbols D) (realized : Realization signature meanings)

theorem declaration_readout_iff (origin : Index) (left right : ArrowValue D)
    (leftRead : meanings.evaluateArrow (declarations origin).left.code = some left)
    (rightRead : meanings.evaluateArrow (declarations origin).right.code = some right) :
    (Interpretation.functor meanings realized).map (classOf (declarations origin).left) =
      (Interpretation.functor meanings realized).map (classOf (declarations origin).right) ↔ left = right := by
  have leftActual := Interpretation.functor_complete_readout meanings realized (declarations origin).left
  have rightActual := Interpretation.functor_complete_readout meanings realized (declarations origin).right
  have leftSame := Option.some.inj (leftActual.symm.trans leftRead)
  have rightSame := Option.some.inj (rightActual.symm.trans rightRead)
  constructor
  · intro same
    exact leftSame.symm.trans ((congrArg (fun arrow => (⟨_,_,arrow⟩ : ArrowValue D)) same).trans rightSame)
  · intro same
    exact ArrowValue.arrow_injective (leftSame.trans (same.trans rightSame.symm))

theorem satisfaction_iff_readouts (left right : Index → ArrowValue D)
    (leftRead : ∀ origin, meanings.evaluateArrow (declarations origin).left.code = some (left origin))
    (rightRead : ∀ origin, meanings.evaluateArrow (declarations origin).right.code = some (right origin)) :
    Satisfies signature declarations meanings realized ↔ ∀ origin, left origin = right origin := by
  constructor
  · intro satisfied origin
    exact (declaration_readout_iff signature declarations meanings realized origin
      (left origin) (right origin) (leftRead origin) (rightRead origin)).mp (satisfied origin)
  · intro same origin
    exact (declaration_readout_iff signature declarations meanings realized origin
      (left origin) (right origin) (leftRead origin) (rightRead origin)).mpr (same origin)

include realized in
theorem realization_iff_readouts (left right : Index → ArrowValue D)
    (leftRead : ∀ origin, meanings.evaluateArrow (declarations origin).left.code = some (left origin))
    (rightRead : ∀ origin, meanings.evaluateArrow (declarations origin).right.code = some (right origin)) :
    Realization (extend signature declarations) (extendAssignment meanings) ↔
      ∀ origin, left origin = right origin :=
  (realization_iff_satisfaction signature declarations meanings realized).trans
    (satisfaction_iff_readouts signature declarations meanings realized left right leftRead rightRead)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.EquationExtension
