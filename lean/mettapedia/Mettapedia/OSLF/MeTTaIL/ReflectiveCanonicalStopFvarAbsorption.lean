import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalStopAlignment

/-!
# Absorbing matched free variables into the stop relation

A `CanonicalStopAligned` descent has two ways to relate a pair of matched
free variables: the `fvar` constructor, which relates `.fvar name` to itself
structurally, and the `leaf` constructor, which delegates the pair to the
client's stop relation.

Consumers that recurse over such a descent must supply a callback for *each*
constructor they can meet.  A callback for the `fvar` case is stated ahead of
the descent, so it is quantified over **all** names — including names the
descent never actually carries.  That is strictly stronger than the recursion
needs, and it can be strictly stronger than is true: a consumer whose fvar
callback happens to hold only for the names its own producer emits cannot use
such an interface at all.

`absorbFvars` removes the difficulty at the source.  It re-emits every `fvar`
node as a `leaf` under the enlarged relation `StopWithFvars`, so the
resulting descent contains no `fvar` node whatsoever.  A consumer given such
a descent needs no fvar callback, and the matched-variable pairs arrive
through the stop callback instead, where the client already has whatever
evidence its producer established about them.

The enlargement is the least one that works: `StopWithFvars stop` adds
exactly the matched-variable pairs and nothing else, so a client discharging
the stop callback sees a disjunction whose second arm is fully explicit.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The original stop relation together with the matched free-variable pairs.
The second arm records both endpoints explicitly, so a consumer can recover
the name without inverting the descent. -/
def StopWithFvars (stop : Pattern → Pattern → Prop) :
    Pattern → Pattern → Prop :=
  fun left right =>
    stop left right ∨ ∃ name, left = .fvar name ∧ right = .fvar name

mutual
/-- Every `CanonicalStopAligned` descent is also a descent over
`StopWithFvars`, and the translated descent uses no `fvar` constructor.
Structural in the descent; every other constructor is carried unchanged. -/
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

/-- List companion of `CanonicalStopAligned.absorbFvars`. -/
theorem CanonicalStopAlignedList.absorbFvars
    {declaration : ReflectivePresentationDecl}
    {stop : Pattern → Pattern → Prop} {left right : List Pattern}
    (aligned : CanonicalStopAlignedList declaration stop left right) :
    CanonicalStopAlignedList declaration (StopWithFvars stop) left right := by
  cases aligned with
  | nil => exact .nil
  | cons head tail => exact .cons head.absorbFvars tail.absorbFvars
end

/-- The enlargement is monotone: a client that can discharge the original
stop and the matched-variable pairs can discharge the enlarged relation. -/
theorem StopWithFvars.elim {stop : Pattern → Pattern → Prop}
    {motive : Pattern → Pattern → Prop}
    (onStop : ∀ {left right}, stop left right → motive left right)
    (onFvar : ∀ name, motive (.fvar name) (.fvar name))
    {left right : Pattern} (given : StopWithFvars stop left right) :
    motive left right := by
  rcases given with given | ⟨name, leftEq, rightEq⟩
  · exact onStop given
  · subst leftEq; subst rightEq; exact onFvar name

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
