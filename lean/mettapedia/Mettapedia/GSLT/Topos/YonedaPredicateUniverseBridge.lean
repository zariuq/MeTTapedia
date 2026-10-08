import Mettapedia.CategoryTheory.AsSmallYoneda
import Mettapedia.GSLT.Topos.YonedaPredicateExponential
import Mettapedia.GSLT.Core.LambdaTheory

/-!
# The Yoneda predicate theory across independent universes

The original total category has predicates on the original representables
and actual base maps satisfying their entailments. Raising the category,
worlds, and generalized elements yields an equivalence with the canonical
common-universe Yoneda predicate total category. Both projections retain
their original base maps. This relates the common-universe closed construction
to the original predicates rather than merely renaming a category.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Topos.YonedaPredicateUniverseBridge

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Mettapedia.CategoryTheory.AsSmallYoneda

universe u v

structure Original (C : Type u) [Category.{v} C] where
  base : C
  predicate : Subfunctor (yoneda.obj base)

namespace Original

variable {C : Type u} [Category.{v} C]

structure Hom (first second : Original C) where
  base : first.base ⟶ second.base
  entails : first.predicate ≤ second.predicate.preimage (yoneda.map base)

@[ext] theorem Hom.ext {first second : Original C} (f g : Hom first second)
    (same : f.base = g.base) : f = g := by
  cases f
  cases g
  cases same
  rfl

def identity (object : Original C) : Hom object object where
  base := 𝟙 object.base
  entails := by
    rw [yoneda.map_id, Subfunctor.preimage_id]

def composition {first second third : Original C} (f : Hom first second)
    (g : Hom second third) : Hom first third where
  base := f.base ≫ g.base
  entails := by
    rw [yoneda.map_comp, Subfunctor.preimage_comp]
    intro world arrow held
    exact g.entails world (f.entails world held)

instance category : Category.{v} (Original C) where
  Hom := Hom
  id := identity
  comp := composition
  id_comp f := Hom.ext _ _ (Category.id_comp f.base)
  comp_id f := Hom.ext _ _ (Category.comp_id f.base)
  assoc f g h := Hom.ext _ _ (Category.assoc f.base g.base h.base)

def projection (C : Type u) [Category.{v} C] : Original C ⥤ C where
  obj := Original.base
  map := Hom.base

instance projectionFaithful : (projection C).Faithful where
  map_injective same := Hom.ext _ _ same

/-- True and false predicates remain different actual arrow constraints. -/
theorem no_identity_top_to_bottom (X : C) :
    ¬ ∃ arrow : (⟨X, ⊤⟩ : Original C) ⟶ ⟨X, ⊥⟩, arrow.base = 𝟙 X := by
  rintro ⟨arrow, _⟩
  exact arrow.entails (op X) (show (𝟙 X) ∈ (⊤ : Subfunctor (yoneda.obj X)).obj (op X)
    from Set.mem_univ _)

end Original

variable {C : Type u} [Category.{v} C]

/-- Transport each supplied predicate and its actual admitted base map. -/
def raiseTotal (C : Type u) [Category.{v} C] : Original C ⥤ YonedaPredicate.Total (Small C) where
  obj object := YonedaPredicate.ofPredicate ((up C).obj object.base)
    (raisePredicate object.predicate)
  map arrow := YonedaPredicate.homOfEntailment ((up C).map arrow.base) (by
    intro world value held
    exact arrow.entails (op ((down C).obj world.unop)) held)
  map_id object := YonedaPredicate.hom_ext _ _ rfl
  map_comp first second := YonedaPredicate.hom_ext _ _ rfl

/-- Lower the worlds, predicate values, and every original base arrow. -/
def lowerTotal (C : Type u) [Category.{v} C] : YonedaPredicate.Total (Small C) ⥤ Original C where
  obj object := ⟨(down C).obj object.base, lowerPredicate (YonedaPredicate.predicate object)⟩
  map arrow := {
    base := (down C).map arrow.base
    entails := by
      intro world value held
      exact YonedaPredicate.hom_entailment arrow (op ((up C).obj world.unop)) held }
  map_id object := Original.Hom.ext _ _ rfl
  map_comp first second := Original.Hom.ext _ _ rfl

theorem lower_raise_object (object : Original C) :
    (lowerTotal C).obj ((raiseTotal C).obj object) = object := by
  cases object
  rfl

theorem raise_lower_object (object : YonedaPredicate.Total (Small C)) :
    (raiseTotal C).obj ((lowerTotal C).obj object) = object := by
  cases object
  rfl

def totalEquivalence (C : Type u) [Category.{v} C] :
    Original C ≌ YonedaPredicate.Total (Small C) where
  functor := raiseTotal C
  inverse := lowerTotal C
  unitIso := NatIso.ofComponents (fun object => eqToIso (lower_raise_object object).symm) (by
    intro first second arrow
    apply Original.Hom.ext
    change arrow.base ≫ 𝟙 _ = 𝟙 _ ≫ arrow.base
    rw [Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents (fun object => eqToIso (raise_lower_object object)) (by
    intro first second arrow
    apply YonedaPredicate.hom_ext
    change arrow.base ≫ 𝟙 _ = 𝟙 _ ≫ arrow.base
    rw [Category.comp_id, Category.id_comp])
  functor_unitIso_comp object := by
    apply YonedaPredicate.hom_ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _

theorem raise_projection :
    raiseTotal C ⋙ YonedaPredicate.projection (Small C) = Original.projection C ⋙ up C := rfl

theorem lower_projection :
    lowerTotal C ⋙ Original.projection C = YonedaPredicate.projection (Small C) ⋙ down C := rfl

theorem original_projection_recovered :
    raiseTotal C ⋙ YonedaPredicate.projection (Small C) ⋙ down C = Original.projection C := rfl

theorem raised_predicate_readout (object : Original C) (world : C)
    (value : world ⟶ object.base) :
    (up C).map value ∈
        (YonedaPredicate.predicate ((raiseTotal C).obj object)).obj (op ((up C).obj world)) ↔
      value ∈ object.predicate.obj (op world) := Iff.rfl

theorem raised_arrow_readout {first second : Original C} (arrow : first ⟶ second) :
    (down C).map ((raiseTotal C).map arrow).base = arrow.base := rfl

instance originalProjectionFinite [HasFiniteLimits C] :
    PreservesFiniteLimits (Original.projection C) := by
  let : (raiseTotal C).IsEquivalence := (totalEquivalence C).isEquivalence_functor
  let : PreservesFiniteLimits (Original.projection C ⋙ up C) := by
    rw [← raise_projection]
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves (Original.projection C) (up C)

instance originalFiniteLimits [HasFiniteLimits C] : HasFiniteLimits (Original C) where
  out J := by
    intro _ _
    let : (raiseTotal C).IsEquivalence := (totalEquivalence C).isEquivalence_functor
    exact Adjunction.hasLimitsOfShape_of_equivalence (J := J) (raiseTotal C)

instance originalCartesian [HasFiniteLimits C] [CartesianMonoidalCategory C] :
    CartesianMonoidalCategory (Original C) := .ofHasFiniteProducts

instance originalClosed [HasFiniteLimits C] [CartesianMonoidalCategory C] [MonoidalClosed C] :
    MonoidalClosed (Original C) := cartesianClosedOfEquiv (totalEquivalence C).symm

/-- A supplied theory with independent object and hom universes gives a
genuine common-universe theory through the earned category equivalence. -/
def normalizedTheory (source : Core.LambdaTheory.{u, v}) :
    Core.LambdaTheory.{max u v, max u v} :=
  Core.LambdaTheory.ofCategory (Small source.Obj)

/-- The canonical restricted predicate category carries its actual finite
limits and its independently proved exponential adjunction. -/
def predicateTheory (source : Core.LambdaTheory.{u, v}) :
    Core.LambdaTheory.{max u v, max u v} :=
  Core.LambdaTheory.ofCategory (YonedaPredicate.Total (Small source.Obj))

def canonicalProjection (source : Core.LambdaTheory.{u, v}) :
    Core.LambdaTheoryMap (predicateTheory source) (normalizedTheory source) where
  functor := YonedaPredicate.projection (Small source.Obj)
  preservesFiniteLimits :=
    YonedaPredicate.projectionPreservesFiniteLimits (C := Small source.Obj)
  preservesExponentials := YonedaPredicate.projectionClosed (C := Small source.Obj)

theorem canonical_projection_recovers_original_arrow (source : Core.LambdaTheory.{u, v})
    {first second : Original source.Obj} (arrow : first ⟶ second) :
    (down source.Obj).map ((canonicalProjection source).functor.map
      ((raiseTotal source.Obj).map arrow)) = arrow.base := rfl

end Mettapedia.GSLT.Topos.YonedaPredicateUniverseBridge
