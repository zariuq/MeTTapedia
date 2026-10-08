import Mettapedia.CategoryTheory.FibrationTwoCategory
import Mettapedia.CategoryTheory.MonoArrowFunctor

/-!+# Codomain and predicate fibrations in the fibration two-category

The actual arrow and monomorphism projections define objects of the
fibration two-category. Finite-limit-preserving functors act through their
actual arrow and predicate maps, and natural transformations supply the
compatible total/base cells. Full comprehension is a Cartesian-preserving
one-cell over the identity base. No preservation of dependent products or
classifiers is inferred from these finite-limit hypotheses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.FibrationTwoCategory

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoArrowImageAdjunction

universe u v
variable {C D E : Type (max u v)} [Category.{v} C] [Category.{v} D] [Category.{v} E]

def codomain (C : Type (max u v)) [Category.{v} C] [HasPullbacks C] :
    Fibration.{max u v,v} where
  projection := ⟨Cat.of (Arrow C), Cat.of C, Arrow.rightFunc.toCatHom⟩
  fibered := by
    change (Arrow.rightFunc : Arrow C ⥤ C).IsFibered
    exact CodomainComprehension.codomain_fibered

def predicates (C : Type (max u v)) [Category.{v} C] [HasPullbacks C] :
    Fibration.{max u v,v} where
  projection := ⟨Cat.of (Predicate C), Cat.of C, (projection C).toCatHom⟩
  fibered := by
    change (projection C).IsFibered
    exact projection_fibered

variable [HasPullbacks C] [HasPullbacks D] [HasPullbacks E]

attribute [local instance] comp_preservesFiniteLimits

/-- The arrow-category action retains the same supplied base functor. -/
def codomainMap (F : C ⥤ D) [PreservesFiniteLimits F] : codomain C ⟶ codomain D where
  square := {
    left := F.mapArrow.toCatHom
    right := F.toCatHom
    comm := by apply Cat.ext; rfl }
  cartesian := by
    intro first second square supplied
    change Arrow.rightFunc.IsCartesian square.right square at supplied
    have := supplied
    exact arrow_map_preserves_cartesian F square

/-- The monomorphism-category action uses the actual mapped inclusion. -/
def predicateMap (F : C ⥤ D) [PreservesFiniteLimits F] : predicates C ⟶ predicates D where
  square := {
    left := (map F).toCatHom
    right := F.toCatHom
    comm := by apply Cat.ext; exact projection_square F }
  cartesian := by
    intro first second square supplied
    change (projection C).IsCartesian square.hom.right square at supplied
    have := supplied
    exact map_preserves_cartesian F square

/-- Full comprehension is an actual Cartesian-preserving square. -/
def comprehensionMap (C : Type (max u v)) [Category.{v} C] [HasPullbacks C] :
    predicates C ⟶ codomain C where
  square := {
    left := (comprehension C).toCatHom
    right := (𝟭 C).toCatHom
    comm := by apply Cat.ext; rfl }
  cartesian := by
    intro first second square supplied
    exact (comprehension_cartesian_iff square).mp supplied

/-- Natural transformations act on actual mapped arrow displays. -/
def codomainCell {F G : C ⥤ D} [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (change : F ⟶ G) : codomainMap F ⟶ codomainMap G where
  hom := {
    left := ((Functor.mapArrowFunctor C D).map change).toCatHom₂
    right := change.toCatHom₂
    compatible := by
      apply heq_of_eq
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext object
      rfl }

/-- Both sides of a predicate cell retain the supplied component. -/
def predicateCell {F G : C ⥤ D} [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (change : F ⟶ G) : predicateMap F ⟶ predicateMap G where
  hom := {
    left := (map₂ change).toCatHom₂
    right := change.toCatHom₂
    compatible := by
      apply heq_of_eq
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext object
      rfl }

@[simp] theorem codomainCell_total_left {F G : C ⥤ D}
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] (change : F ⟶ G)
    (object : Arrow C) :
    ((codomainCell change).hom.left.toNatTrans.app object).left =
      change.app object.left := rfl

@[simp] theorem codomainCell_total_right {F G : C ⥤ D}
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] (change : F ⟶ G)
    (object : Arrow C) :
    ((codomainCell change).hom.left.toNatTrans.app object).right =
      change.app object.right := rfl

@[simp] theorem predicateCell_total_left {F G : C ⥤ D}
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] (change : F ⟶ G)
    (object : Predicate C) :
    ((predicateCell change).hom.left.toNatTrans.app object).hom.left =
      change.app object.obj.left := rfl

@[simp] theorem predicateCell_total_right {F G : C ⥤ D}
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] (change : F ⟶ G)
    (object : Predicate C) :
    ((predicateCell change).hom.left.toNatTrans.app object).hom.right =
      change.app object.obj.right := rfl

/-- The actual predicate action commutes with full comprehension. -/
theorem comprehension_naturality (F : C ⥤ D) [PreservesFiniteLimits F] :
    predicateMap F ≫ comprehensionMap D = comprehensionMap C ≫ codomainMap F := by
  apply Fibration.Hom.ext
  apply StrictTwoArrow.Hom.ext
  · apply Cat.ext
    exact comprehension_square F
  · apply Cat.ext
    rfl

theorem codomainMap_identity : codomainMap (𝟭 C) = 𝟙 (codomain C) := by
  apply Fibration.Hom.ext
  apply StrictTwoArrow.Hom.ext
  · apply Cat.ext
    change (𝟭 C).mapArrow = 𝟭 (Arrow C)
    refine _root_.CategoryTheory.Functor.ext (fun object => Arrow.mk_eq object) ?_
    intro first second square
    rcases first with ⟨_, _, _⟩
    rcases second with ⟨_, _, _⟩
    apply Arrow.hom_ext <;> simp [Functor.mapArrow]
  · rfl

theorem predicateMap_identity : predicateMap (𝟭 C) = 𝟙 (predicates C) := by
  apply Fibration.Hom.ext
  apply StrictTwoArrow.Hom.ext
  · apply Cat.ext
    exact map_identity
  · rfl

theorem codomainMap_composition (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    codomainMap (F ⋙ G) = codomainMap F ≫ codomainMap G := by
  apply Fibration.Hom.ext
  apply StrictTwoArrow.Hom.ext <;> rfl

theorem predicateMap_composition (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    predicateMap (F ⋙ G) = predicateMap F ≫ predicateMap G := by
  apply Fibration.Hom.ext
  apply StrictTwoArrow.Hom.ext <;> rfl

theorem codomainCell_identity (F : C ⥤ D) [PreservesFiniteLimits F] :
    codomainCell (𝟙 F) = 𝟙 (codomainMap F) := by
  apply Fibration.Cell.ext
  apply StrictTwoArrow.Cell.ext <;> apply Cat.Hom₂.ext
  · exact (Functor.mapArrowFunctor C D).map_id F
  · rfl

theorem predicateCell_identity (F : C ⥤ D) [PreservesFiniteLimits F] :
    predicateCell (𝟙 F) = 𝟙 (predicateMap F) := by
  apply Fibration.Cell.ext
  apply StrictTwoArrow.Cell.ext <;> apply Cat.Hom₂.ext
  · exact map₂_identity F
  · rfl

theorem codomainCell_composition {F G H : C ⥤ D}
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    (first : F ⟶ G) (second : G ⟶ H) :
    codomainCell (first ≫ second) = codomainCell first ≫ codomainCell second := by
  apply Fibration.Cell.ext
  apply StrictTwoArrow.Cell.ext <;> apply Cat.Hom₂.ext
  · exact (Functor.mapArrowFunctor C D).map_comp first second
  · rfl

theorem predicateCell_composition {F G H : C ⥤ D}
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    (first : F ⟶ G) (second : G ⟶ H) :
    predicateCell (first ≫ second) = predicateCell first ≫ predicateCell second := by
  apply Fibration.Cell.ext
  apply StrictTwoArrow.Cell.ext <;> apply Cat.Hom₂.ext
  · exact map₂_composition first second
  · rfl

end Mettapedia.CategoryTheory.FibrationTwoCategory
