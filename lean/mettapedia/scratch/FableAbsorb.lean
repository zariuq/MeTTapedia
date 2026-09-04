import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalStopAlignment

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The enlarged stop relation: the original, plus matched free variables. -/
def StopWithFvars (stop : Pattern → Pattern → Prop) :
    Pattern → Pattern → Prop :=
  fun left right => stop left right ∨ ∃ name, left = .fvar name ∧ right = .fvar name

mutual
theorem CanonicalStopAligned.absorbFvars
    {declaration : ReflectivePresentationDecl}
    {stop : Pattern → Pattern → Prop} {left right : Pattern}
    (aligned : CanonicalStopAligned declaration stop left right) :
    CanonicalStopAligned declaration (StopWithFvars stop) left right := by
  cases aligned with
  | leaf given => exact .leaf (Or.inl given)
  | bvar index => exact .bvar index
  | fvar name => exact .leaf (Or.inr ⟨name, rfl, rfl⟩)
  | apply ne arguments => exact .apply ne arguments.absorbFvars
  | lambda binder body => exact .lambda binder body.absorbFvars
  | multiLambda arity binders body =>
      exact .multiLambda arity binders body.absorbFvars
  | subst body replacement =>
      exact .subst body.absorbFvars replacement.absorbFvars
  | collection ne elements => exact .collection ne elements.absorbFvars
  | collectionRest collectionType rest elements =>
      exact .collectionRest collectionType rest elements.absorbFvars

theorem CanonicalStopAlignedList.absorbFvars
    {declaration : ReflectivePresentationDecl}
    {stop : Pattern → Pattern → Prop} {left right : List Pattern}
    (aligned : CanonicalStopAlignedList declaration stop left right) :
    CanonicalStopAlignedList declaration (StopWithFvars stop) left right := by
  cases aligned with
  | nil => exact .nil
  | cons head tail => exact .cons head.absorbFvars tail.absorbFvars
end

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
