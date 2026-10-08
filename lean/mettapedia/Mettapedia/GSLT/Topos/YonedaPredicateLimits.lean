import Mettapedia.GSLT.Topos.YonedaPredicateTotal
import Mettapedia.GSLT.Topos.PresheafPredicateLimits
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Limits in the Yoneda-restricted predicate category

An actual base limit lifts by intersecting all predicate inverse images along
its cone. The complete universal map satisfies this predicate because its
components are the supplied admitted cone maps. This constructs finite limits
when the base has them, and earns their preservation by the projection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.YonedaPredicate

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w
variable {C : Type u} [Category.{u} C]
variable {J : Type v} [Category.{w} J] (K : J ⥤ Total C)

/-- Intersection of the actual predicate inverse images at the supplied cone. -/
def limitPredicate (cone : Cone (K ⋙ projection C)) :
    Subfunctor (yoneda.obj cone.pt) :=
  ⨅ j, (predicate (K.obj j)).preimage (yoneda.map (cone.π.app j))

theorem mem_limitPredicate (cone : Cone (K ⋙ projection C))
    (U : Cᵒᵖ) (point : U.unop ⟶ cone.pt) :
    point ∈ (limitPredicate K cone).obj U ↔
      ∀ j, point ≫ cone.π.app j ∈ (predicate (K.obj j)).obj U := by
  simp only [limitPredicate, Subfunctor.iInf_obj, Set.mem_iInter]
  rfl

/-- The cone carries precisely the predicate required by all its admitted components. -/
def liftedCone (cone : Cone (K ⋙ projection C)) : Cone K where
  pt := ofPredicate cone.pt (limitPredicate K cone)
  π :=
    { app := fun j => homOfEntailment (cone.π.app j) (iInf_le _ j)
      naturality := by intro i j f; exact hom_ext _ _ (cone.π.naturality f) }

/-- Full existence, factorization and uniqueness of the lifted limit. -/
def liftedIsLimit (cone : Cone (K ⋙ projection C)) (universal : IsLimit cone) :
    IsLimit (liftedCone K cone) where
  lift other := homOfEntailment (universal.lift ((projection C).mapCone other)) (by
    intro U point held
    apply (mem_limitPredicate K cone U _).mpr
    intro j
    have factor := universal.fac ((projection C).mapCone other) j
    change universal.lift ((projection C).mapCone other) ≫ cone.π.app j =
      (other.π.app j).base at factor
    change (point ≫ universal.lift ((projection C).mapCone other)) ≫ cone.π.app j ∈
      (predicate (K.obj j)).obj U
    have reading : (point ≫ universal.lift ((projection C).mapCone other)) ≫ cone.π.app j =
        point ≫ (other.π.app j).base := by
      exact (Category.assoc _ _ _).trans (congrArg (fun arrow => point ≫ arrow) factor)
    exact reading.symm ▸ hom_entailment (other.π.app j) U held)
  fac other j := hom_ext _ _ (universal.fac ((projection C).mapCone other) j)
  uniq other mapping factors := by
    apply hom_ext
    apply universal.uniq ((projection C).mapCone other) mapping.base
    intro j
    exact congrArg Pseudofunctor.CoGrothendieck.Hom.base (factors j)

noncomputable instance hasLimit [HasLimit (K ⋙ projection C)] : HasLimit K :=
  ⟨⟨liftedCone K (limit.cone _), liftedIsLimit K _ (limit.isLimit _)⟩⟩

noncomputable instance preservesLimit [HasLimit (K ⋙ projection C)] :
    PreservesLimit K (projection C) :=
  preservesLimit_of_preserves_limit_cone (liftedIsLimit K _ (limit.isLimit _))
    (limit.isLimit _)

noncomputable instance hasFiniteLimits [HasFiniteLimits C] : HasFiniteLimits (Total C) where
  out _ := { }

noncomputable instance projectionPreservesFiniteLimits [HasFiniteLimits C] :
    PreservesFiniteLimits (projection C) where
  preservesFiniteLimits _ := { }

end Mettapedia.GSLT.Topos.YonedaPredicate
