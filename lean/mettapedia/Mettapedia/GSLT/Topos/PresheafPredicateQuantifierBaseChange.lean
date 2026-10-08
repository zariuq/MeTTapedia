import Mettapedia.GSLT.Topos.PresheafPredicateUniversalQuantifier
import Mettapedia.GSLT.Topos.ConstructivePresheafBaseChange

/-!
# Native quantifier substitution across actual presheaf pullbacks

Both existential image and the future-sensitive universal quantifier commute
with substitution across an actual pullback square. The universal proof uses
all restrictions and the pointwise lifting consequence of that square. The
separately constructed constructive operations agree on the same presheaf
carriers. These comparisons concern natural maps over a fixed base category.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w
variable {C : Type u} [Category.{v} C]
variable {P Q R S : Cᵒᵖ ⥤ Type w}

/-- Universal quantification commutes with substitution across the actual
pullback, including every future restriction on either side. -/
theorem forallAlong_beckChevalley (top : P ⟶ Q) (left : P ⟶ R)
    (right : Q ⟶ S) (bottom : R ⟶ S)
    (square : IsPullback top left right bottom) (predicate : Subfunctor Q) :
    (forallAlong right predicate).preimage bottom =
      forallAlong left (predicate.preimage top) := by
  ext world value
  constructor
  · intro holds next restriction argument over
    apply holds next restriction (top.app next argument)
    have commutes := ConcreteCategory.congr_hom (NatTrans.congr_app square.w next) argument
    change right.app next (top.app next argument) = bottom.app next (left.app next argument)
      at commutes
    exact commutes.trans
      ((congrArg (bottom.app next) over).trans (bottom.naturality_apply restriction value))
  · intro holds next restriction argument over
    have pointwise : IsPullback (top.app next) (left.app next)
        (right.app next) (bottom.app next) :=
      square.map ((evaluation Cᵒᵖ (Type w)).obj next)
    have matched : right.app next argument = bottom.app next (R.map restriction value) :=
      over.trans (bottom.naturality_apply restriction value).symm
    obtain ⟨lifted, upper, lower⟩ :=
      Types.exists_of_isPullback pointwise (x₂ := argument)
        (x₃ := R.map restriction value) matched
    have selected := holds next restriction lifted lower
    change top.app next lifted ∈ predicate.obj next at selected
    rw [upper] at selected
    exact selected

/-- Existential substitution uses the same actual square and the
independently proved image comparison. -/
theorem image_beckChevalley (top : P ⟶ Q) (left : P ⟶ R)
    (right : Q ⟶ S) (bottom : R ⟶ S)
    (square : IsPullback top left right bottom) (predicate : Subfunctor Q) :
    (predicate.image right).preimage bottom = (predicate.preimage top).image left :=
  beckChevalleyPresheafSubfunctor C left top bottom right square.flip predicate

/-- The independently formed constructive inverse-image predicate has
the same members as ordinary native substitution. -/
theorem constructive_preimage_eq {F G : Cᵒᵖ ⥤ Type w}
    (map : F ⟶ G) (predicate : Subfunctor G) :
    ConstructivePresheaf.preimage map predicate = predicate.preimage map := by
  ext world value
  rfl

/-- Both independently formed existential operations retain exactly the
same witnessing inhabitants on the standard presheaf carriers. -/
theorem constructive_image_eq {F G : Cᵒᵖ ⥤ Type w}
    (map : F ⟶ G) (predicate : Subfunctor F) :
    ConstructivePresheaf.image map predicate = predicate.image map := by
  ext world value
  rfl

/-- Both universal operations quantify the same complete future
arguments; their equality does not assume branching or a chosen witness. -/
theorem constructive_forallAlong_eq {F G : Cᵒᵖ ⥤ Type w}
    (map : F ⟶ G) (predicate : Subfunctor F) :
    ConstructivePresheaf.forallAlong map predicate = forallAlong map predicate := by
  ext world value
  rfl

end Mettapedia.GSLT.Topos
