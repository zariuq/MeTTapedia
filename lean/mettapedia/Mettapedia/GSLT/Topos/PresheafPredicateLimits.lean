import Mettapedia.GSLT.Topos.PresheafPredicateTotalProducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Completeness and cocompleteness of the total predicate category

Lift a limit of underlying presheaves by intersecting the inverse images of
its predicates. Lift a colimit by taking the union of their direct images.
The universal properties are proved in the existing total predicate category,
using its entailment morphisms and their faithful projection.

The construction works for every diagram whose underlying limit or colimit
exists. In particular, all small limits and colimits exist, and the projection
preserves them. This is Proposition 18 of Williams and Stay's Native Type
Theory (2021), with the diagram sizes explicit in the Lean universes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PredicateLimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w
variable {C : Type u} [Category.{u} C] {J : Type v} [Category.{w} J]
variable (K : J ⥤ PresheafPredicateTotal C)

def limitPredicate (s : Cone (K ⋙ presheafPredicateProjection C)) : Subfunctor s.pt :=
  ⨅ j, (objectPredicate (K.obj j)).preimage (s.π.app j)

theorem mem_limitPredicate (s : Cone (K ⋙ presheafPredicateProjection C))
    (U : Cᵒᵖ) (x : s.pt.obj U) :
    x ∈ (limitPredicate K s).obj U ↔
      ∀ j, (s.π.app j).app U x ∈ (objectPredicate (K.obj j)).obj U := by
  simp only [limitPredicate, Subfunctor.iInf_obj, Set.mem_iInter]
  rfl

def liftedCone (s : Cone (K ⋙ presheafPredicateProjection C)) : Cone K where
  pt := totalOfPredicate s.pt (limitPredicate K s)
  π :=
    { app := fun j => homOfEntailment (s.π.app j) (iInf_le _ j)
      naturality := by intro i j f; exact hom_ext _ _ (s.π.naturality f) }

def liftedIsLimit (s : Cone (K ⋙ presheafPredicateProjection C)) (hs : IsLimit s) :
    IsLimit (liftedCone K s) where
  lift t := homOfEntailment (hs.lift ((presheafPredicateProjection C).mapCone t)) (by
    intro U x member
    apply (mem_limitPredicate K s U _).mpr
    intro j
    have fac := congrArg (fun η => η.app U x)
      (hs.fac ((presheafPredicateProjection C).mapCone t) j)
    change (s.π.app j).app U
      ((hs.lift ((presheafPredicateProjection C).mapCone t)).app U x) =
        (t.π.app j).base.app U x at fac
    exact (congrArg (fun y : (K.obj j).base.obj U =>
      y ∈ (objectPredicate (K.obj j)).obj U) fac).mpr
        (hom_entailment (t.π.app j) U member))
  fac t j := hom_ext _ _ (hs.fac ((presheafPredicateProjection C).mapCone t) j)
  uniq t m h := by
    apply hom_ext
    apply hs.uniq ((presheafPredicateProjection C).mapCone t) m.base
    intro j
    exact congrArg (fun f => f.base) (h j)

def colimitPredicate (s : Cocone (K ⋙ presheafPredicateProjection C)) : Subfunctor s.pt :=
  ⨆ j, (objectPredicate (K.obj j)).image (s.ι.app j)

theorem mem_colimitPredicate (s : Cocone (K ⋙ presheafPredicateProjection C))
    (U : Cᵒᵖ) (x : s.pt.obj U) :
    x ∈ (colimitPredicate K s).obj U ↔
      ∃ j y, y ∈ (objectPredicate (K.obj j)).obj U ∧ (s.ι.app j).app U y = x := by
  simp only [colimitPredicate, Subfunctor.iSup_obj, Set.mem_iUnion]
  rfl

def liftedCocone (s : Cocone (K ⋙ presheafPredicateProjection C)) : Cocone K where
  pt := totalOfPredicate s.pt (colimitPredicate K s)
  ι :=
    { app := fun j => homOfEntailment (s.ι.app j) (by
        intro U x member
        exact (mem_colimitPredicate K s U _).mpr ⟨j, x, member, rfl⟩)
      naturality := by intro i j f; exact hom_ext _ _ (s.ι.naturality f) }

def liftedIsColimit (s : Cocone (K ⋙ presheafPredicateProjection C)) (hs : IsColimit s) :
    IsColimit (liftedCocone K s) where
  desc t := homOfEntailment (hs.desc ((presheafPredicateProjection C).mapCocone t)) (by
    intro U x member
    obtain ⟨j, y, hy, rfl⟩ := (mem_colimitPredicate K s U x).mp member
    have fac := congrArg (fun η => η.app U y)
      (hs.fac ((presheafPredicateProjection C).mapCocone t) j)
    change (hs.desc ((presheafPredicateProjection C).mapCocone t)).app U
      ((s.ι.app j).app U y) = (t.ι.app j).base.app U y at fac
    change (hs.desc ((presheafPredicateProjection C).mapCocone t)).app U
      ((s.ι.app j).app U y) ∈ (objectPredicate t.pt).obj U
    rw [fac]
    exact hom_entailment (t.ι.app j) U hy)
  fac t j := hom_ext _ _ (hs.fac ((presheafPredicateProjection C).mapCocone t) j)
  uniq t m h := by
    apply hom_ext
    apply hs.uniq ((presheafPredicateProjection C).mapCocone t) m.base
    intro j
    exact congrArg (fun f => f.base) (h j)

noncomputable instance hasLimit [HasLimit (K ⋙ presheafPredicateProjection C)] : HasLimit K :=
  ⟨⟨liftedCone K (limit.cone _), liftedIsLimit K _ (limit.isLimit _)⟩⟩

noncomputable instance hasColimit [HasColimit (K ⋙ presheafPredicateProjection C)] : HasColimit K :=
  ⟨⟨liftedCocone K (colimit.cocone _), liftedIsColimit K _ (colimit.isColimit _)⟩⟩

noncomputable instance preservesLimit [HasLimit (K ⋙ presheafPredicateProjection C)] :
    PreservesLimit K (presheafPredicateProjection C) :=
  preservesLimit_of_preserves_limit_cone (liftedIsLimit K _ (limit.isLimit _))
    (limit.isLimit _)

noncomputable instance preservesColimit [HasColimit (K ⋙ presheafPredicateProjection C)] :
    PreservesColimit K (presheafPredicateProjection C) :=
  preservesColimit_of_preserves_colimit_cocone (liftedIsColimit K _ (colimit.isColimit _))
    (colimit.isColimit _)

noncomputable instance hasLimitsOfSize : HasLimitsOfSize.{u, u} (PresheafPredicateTotal C) where
  has_limits_of_shape _ _ := { }

noncomputable instance hasColimitsOfSize : HasColimitsOfSize.{u, u} (PresheafPredicateTotal C) where
  has_colimits_of_shape _ _ := { }

noncomputable instance projectionPreservesLimits :
    PreservesLimitsOfSize.{u, u} (presheafPredicateProjection C) where
  preservesLimitsOfShape := { }

noncomputable instance projectionPreservesColimits :
    PreservesColimitsOfSize.{u, u} (presheafPredicateProjection C) where
  preservesColimitsOfShape := { }

end Mettapedia.GSLT.Topos.PredicateLimits
