import Mettapedia.GSLT.Topos.PredicateFibration
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Preorder

/-!
# The actual presheaf predicate projection

Subfunctor preimage defines the contravariant category-valued functor, including
its identity and composition laws. The existing contravariant Grothendieck
construction supplies its total category, projection, and cartesian lifts with
unique factorization. This uses the same concrete fibers and preimages as
`presheafPredicateFib`, rather than the frame-only projection of that record.

The construction is over small categories and presheaves in the same universe.
It establishes the predicate projection, not dependent generated syntax or a
classifying category for the complete native type theory.
-/

namespace Mettapedia.GSLT.Topos

open CategoryTheory CategoryTheory.Functor Opposite

universe u

set_option autoImplicit false

variable {C : Type u} [Category.{u} C]

/-- The actual preimage action on the order category of predicates. -/
def predicateReindex {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    Subfunctor Q ⥤ Subfunctor P where
  obj := fun predicate => predicate.preimage f
  map := fun inclusion => homOfLE (fun object _ member => inclusion.le object member)

theorem predicateReindex_identity (P : Cᵒᵖ ⥤ Type u) :
    predicateReindex (𝟙 P) = 𝟭 (Subfunctor P) := by
  refine CategoryTheory.Functor.ext (fun predicate => Subfunctor.preimage_id predicate) ?_
  intros
  apply Subsingleton.elim

theorem predicateReindex_composition {P Q R : Cᵒᵖ ⥤ Type u}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    predicateReindex (f ≫ g) = predicateReindex g ⋙ predicateReindex f := by
  refine CategoryTheory.Functor.ext
    (fun predicate => Subfunctor.preimage_comp predicate f g) ?_
  intros
  apply Subsingleton.elim

/-- Contravariant predicate categories, with the concrete preimage functor. -/
def presheafPredicateFunctor (C : Type u) [Category.{u} C] :
    (Cᵒᵖ ⥤ Type u)ᵒᵖ ⥤ Cat.{u,u} where
  obj := fun P => Cat.of (Subfunctor (unop P))
  map := fun f => (predicateReindex f.unop).toCatHom
  map_id := by
    intro P
    apply Cat.ext
    exact predicateReindex_identity (unop P)
  map_comp := by
    intro P Q R f g
    apply Cat.ext
    exact predicateReindex_composition g.unop f.unop

/-- Promote the same strict action to the locally discrete source bicategory. -/
abbrev presheafPredicatePseudofunctor (C : Type u) [Category.{u} C] :=
  (presheafPredicateFunctor C).toPseudofunctor'

/-- Total predicate category of the actual contravariant presheaf action. -/
abbrev PresheafPredicateTotal (C : Type u) [Category.{u} C] :=
  Pseudofunctor.CoGrothendieck (presheafPredicatePseudofunctor C)

/-- Projection retaining the underlying presheaf and its actual map. -/
abbrev presheafPredicateProjection (C : Type u) [Category.{u} C] :=
  Pseudofunctor.CoGrothendieck.forget (presheafPredicatePseudofunctor C)

/-- The total morphisms have exactly the source definition's shape: an actual
presheaf map and entailment of its target predicate after substitution. -/
def predicateTotalHomEquiv (a b : PresheafPredicateTotal C) :
    (a ⟶ b) ≃ { f : a.base ⟶ b.base //
      (show Subfunctor a.base from a.fiber) ≤ b.fiber.preimage f } where
  toFun := fun arrow => ⟨arrow.base, by
    have inclusion : (show Subfunctor a.base from a.fiber) ⟶
        b.fiber.preimage arrow.base := arrow.fiber
    exact inclusion.le⟩
  invFun := fun arrow => ⟨arrow.val, by
    change (show Subfunctor a.base from a.fiber) ⟶ b.fiber.preimage arrow.val
    exact homOfLE arrow.property⟩
  left_inv := by
    intro arrow
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
    exact @Subsingleton.elim
      ((show Subfunctor a.base from a.fiber) ⟶ b.fiber.preimage arrow.base)
      inferInstance _ _
  right_inv := by
    intro arrow
    apply Subtype.ext
    rfl

/-- Pulling a predicate back along `f` is the domain of its cartesian lift. -/
abbrev predicateLiftDomain {P Q : Cᵒᵖ ⥤ Type u}
    (predicate : Subfunctor Q) (f : P ⟶ Q) : PresheafPredicateTotal C :=
  Pseudofunctor.CoGrothendieck.domainCartesianLift
    (F := presheafPredicatePseudofunctor C) predicate f

abbrev predicateLift {P Q : Cᵒᵖ ⥤ Type u}
    (predicate : Subfunctor Q) (f : P ⟶ Q) :
    predicateLiftDomain predicate f ⟶
      (⟨Q, predicate⟩ : PresheafPredicateTotal C) :=
  Pseudofunctor.CoGrothendieck.cartesianLift
    (F := presheafPredicatePseudofunctor C) predicate f

theorem predicateLift_domain {P Q : Cᵒᵖ ⥤ Type u}
    (predicate : Subfunctor Q) (f : P ⟶ Q) :
    (predicateLiftDomain predicate f).fiber = predicate.preimage f := rfl

/-- A real cartesian lift: factorization exists and is unique over every
preceding base map, rather than merely over an identity. -/
theorem predicateLift_stronglyCartesian {P Q : Cᵒᵖ ⥤ Type u}
    (predicate : Subfunctor Q) (f : P ⟶ Q) :
    IsStronglyCartesian (presheafPredicateProjection C) f
      (predicateLift predicate f) :=
  Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift
    (F := presheafPredicatePseudofunctor C) predicate f

/-- Every arrow over a composite base map factors uniquely through the
constructed predicate pullback, over the preceding map. -/
theorem predicateLift_factorization {P Q : Cᵒᵖ ⥤ Type u}
    (predicate : Subfunctor Q) (f : P ⟶ Q)
    (a : PresheafPredicateTotal C) (g : a.base ⟶ P)
    (arrow : a ⟶ (⟨Q, predicate⟩ : PresheafPredicateTotal C))
    [IsHomLift (presheafPredicateProjection C) (g ≫ f) arrow] :
    ∃! factor : a ⟶ predicateLiftDomain predicate f,
      IsHomLift (presheafPredicateProjection C) g factor ∧
        factor ≫ predicateLift predicate f = arrow := by
  have := predicateLift_stronglyCartesian predicate f
  exact IsStronglyCartesian.universal_property
    (presheafPredicateProjection C) f (predicateLift predicate f)
    g (g ≫ f) rfl arrow

theorem presheafPredicateProjection_fibered (C : Type u) [Category.{u} C] :
    IsFibered (presheafPredicateProjection C) := inferInstance

/-- The lift uses exactly the concrete reindexing from the original package. -/
theorem predicateLift_original_pullback {P Q : Cᵒᵖ ⥤ Type u}
    (predicate : Subfunctor Q) (f : P ⟶ Q) :
    (predicateLiftDomain predicate f).fiber =
      (presheafPredicateFib C).pullback f predicate := rfl

end Mettapedia.GSLT.Topos
