import Mettapedia.GSLT.Topos.ConstructivePresheafOperations

/-!
# Predicate base change across a presheaf pullback

The square retains an actual unique lift of every matching pair of sections.
Both existential and universal quantification satisfy base change across
such a square. This is base change along natural transformations over a
fixed category. No unrestricted theorem about changing the base category is
asserted.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf

open CategoryTheory
open scoped ConstructivePresheaf

universe u v w
variable {C : Type u} [Category.{v} C]
variable {P Q R S : C ⥤ Type w}

/-- Pointwise pullback data in standard presheaf carriers. -/
structure PullbackSquare (top : NatTrans P Q) (left : NatTrans P R)
    (right : NatTrans Q S) (bottom : NatTrans R S) where
  commutes : ∀ (X : C) (p : P.obj X),
    right.app X (top.app X p) = bottom.app X (left.app X p)
  lift : ∀ (X : C) (r : R.obj X) (q : Q.obj X),
    right.app X q = bottom.app X r →
      {p : P.obj X // left.app X p = r ∧ top.app X p = q}
  unique : ∀ (X : C) (p p' : P.obj X),
    left.app X p = left.app X p' → top.app X p = top.app X p' → p = p'

variable {top : NatTrans P Q} {left : NatTrans P R}
variable {right : NatTrans Q S} {bottom : NatTrans R S}

/-- Existential quantification commutes with the specified pullback. -/
theorem image_baseChange (square : PullbackSquare top left right bottom)
    (predicate : Subfunctor Q) :
    preimage bottom (image right predicate) = image left (preimage top predicate) := by
  apply Subfunctor.ext
  funext X
  funext r
  apply propext
  constructor
  · rintro ⟨q, holds, matched⟩
    let lifted := square.lift X r q matched
    refine ⟨lifted.val, ?_, lifted.property.1⟩
    change top.app X lifted.val ∈ predicate.obj X
    rw [lifted.property.2]
    exact holds
  · rintro ⟨p, holds, matched⟩
    refine ⟨top.app X p, holds, ?_⟩
    exact (square.commutes X p).trans (congrArg (bottom.app X) matched)

/-- Universal quantification includes every future restriction on both sides. -/
theorem forall_baseChange (square : PullbackSquare top left right bottom)
    (predicate : Subfunctor Q) :
    preimage bottom (forallAlong right predicate) =
      forallAlong left (preimage top predicate) := by
  apply Subfunctor.ext
  funext X
  funext r
  apply propext
  constructor
  · intro holds Y restriction p over
    apply holds Y restriction (top.app Y p)
    have naturally := congrArg (fun h : R.obj X ⟶ S.obj Y => h r)
      (bottom.naturality restriction)
    exact (square.commutes Y p).trans
      ((congrArg (bottom.app Y) over).trans naturally)
  · intro holds Y restriction q over
    have naturally := congrArg (fun h : R.obj X ⟶ S.obj Y => h r)
      (bottom.naturality restriction)
    let lifted := square.lift Y (R.map restriction r) q (over.trans naturally.symm)
    have result := holds Y restriction lifted.val lifted.property.1
    change top.app Y lifted.val ∈ predicate.obj Y at result
    rw [lifted.property.2] at result
    exact result

end Mettapedia.GSLT.Topos.ConstructivePresheaf
