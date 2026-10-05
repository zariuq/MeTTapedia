import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFamilies
import Mettapedia.TypeTheory.ContextualWitnessCover
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFunctor

/-!
# Singleton and union of full future predicates

Singleton membership follows an actual argument along the retained future
arrow. Union admits a future argument when some predicate admitted at that
future contains the argument at its current point. Both constructions are
stable under every actual future morphism and natural in the context.

The operations act on the constructed small displayed power families.
They do not assert a small-powerclass on arbitrary large objects or indexed
finality for such a powerclass.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerOperations

open CategoryTheory
open FuturePowerFamilies
open FuturePowerFunctor
open PowerClassPresheafBaseChange
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u
variable {D : Type u} [Category.{u} D]

/-- Every future member is the actual transport of the original argument. -/
def singleton (A : D ⥤ Type u) (point : D) (argument : A.obj point) : Predicate A point where
  holds future := A.map future.1.2 argument = future.2
  closed {first second} move same := by
    have triangle : first.1.2 ≫ move.1.1 = second.1.2 := move.1.2
    rw [← triangle]
    exact (congrArg (fun operation => operation argument) (A.map_comp first.1.2 move.1.1)).trans
      ((congrArg (A.map move.1.1) same).trans move.2)

theorem singleton_future (A : D ⥤ Type u) (point : D) (argument : A.obj point)
    (future : Arguments A point) :
    (singleton A point argument).holds future ↔ A.map future.1.2 argument = future.2 := Iff.rfl

theorem singleton_current (A : D ⥤ Type u) (point : D) (first second : A.obj point) :
    (singleton A point first).holds (current A point second) ↔ first = second := by
  change A.map (𝟙 point) first = second ↔ _
  rw [A.map_id point]
  exact Iff.rfl

theorem singleton_injective (A : D ⥤ Type u) (point : D) :
    Function.Injective (singleton A point) := by
  intro first second same
  have truth := (singleton_current A point first first).mpr rfl
  rw [same] at truth
  exact ((singleton_current A point second first).mp truth).symm

theorem singleton_restrict (A : D ⥤ Type u) {first second : D} (step : first ⟶ second)
    (argument : A.obj first) :
    restrict A step (singleton A first argument) = singleton A second (A.map step argument) := by
  apply Predicate.ext
  intro future
  change A.map (step ≫ future.1.2) argument = future.2 ↔
    A.map future.1.2 (A.map step argument) = future.2
  rw [A.map_comp]
  exact Iff.rfl

def unit (A : D ⥤ Type u) : NatTrans A (family A) where
  app point := TypeCat.ofHom (singleton A point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro argument
    exact (singleton_restrict A step argument).symm

theorem unit_value (A : D ⥤ Type u) (point : D) (argument : A.obj point) :
    (unit A).app point argument = singleton A point argument := rfl

/-- The witness is a genuine predicate at the retained future target.
Its current truth is tested on the retained future argument. -/
def flatten (A : D ⥤ Type u) (point : D) (outer : Predicate (family A) point) : Predicate A point where
  holds future := ∃ inner : Predicate A future.1.1,
    outer.holds ⟨⟨future.1.1, future.1.2⟩, inner⟩ ∧
      inner.holds (current A future.1.1 future.2)
  closed {first second} move available := by
    obtain ⟨inner, admitted, truth⟩ := available
    refine ⟨restrict A move.1.1 inner, ?_, ?_⟩
    · exact outer.closed
        (CategoryOfElements.homMk (F := Future.domain (family A) point)
          ⟨⟨first.1.1, first.1.2⟩, inner⟩
          ⟨⟨second.1.1, second.1.2⟩, restrict A move.1.1 inner⟩ move.1 rfl) admitted
    · change inner.holds ⟨⟨second.1.1, move.1.1 ≫ 𝟙 second.1.1⟩, second.2⟩
      rw [Category.comp_id]
      exact inner.closed
        (show current A first.1.1 first.2 ⟶
          (⟨⟨second.1.1, move.1.1⟩, second.2⟩ : Arguments A first.1.1) from
            ⟨⟨move.1.1, Category.id_comp _⟩, move.2⟩) truth

theorem flatten_future (A : D ⥤ Type u) (point : D) (outer : Predicate (family A) point)
    (future : Arguments A point) :
    (flatten A point outer).holds future ↔
      ∃ inner : Predicate A future.1.1,
        outer.holds ⟨⟨future.1.1, future.1.2⟩, inner⟩ ∧
          inner.holds (current A future.1.1 future.2) := Iff.rfl

theorem flatten_restrict (A : D ⥤ Type u) {first second : D} (step : first ⟶ second)
    (outer : Predicate (family A) first) :
    restrict A step (flatten A first outer) = flatten A second (restrict (family A) step outer) := by
  apply Predicate.ext
  intro future
  exact Iff.rfl

def multiplication (A : D ⥤ Type u) : NatTrans (family (family A)) (family A) where
  app point := TypeCat.ofHom (flatten A point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro outer
    exact (flatten_restrict A step outer).symm

theorem multiplication_value (A : D ⥤ Type u) (point : D) (outer : Predicate (family A) point) :
    (multiplication A).app point outer = flatten A point outer := rfl

/-- The union of a singleton recovers all future truth, not only current
membership. -/
theorem flatten_singleton (A : D ⥤ Type u) (point : D) (predicate : Predicate A point) :
    flatten A point (singleton (family A) point predicate) = predicate := by
  apply Predicate.ext
  intro future
  constructor
  · rintro ⟨inner, same, truth⟩
    change restrict A future.1.2 predicate = inner at same
    subst inner
    change predicate.holds ⟨⟨future.1.1, future.1.2 ≫ 𝟙 future.1.1⟩, future.2⟩ at truth
    rw [Category.comp_id] at truth
    rcases future with ⟨⟨_, _⟩, _⟩
    exact truth
  · intro truth
    refine ⟨restrict A future.1.2 predicate, rfl, ?_⟩
    change predicate.holds ⟨⟨future.1.1, future.1.2 ≫ 𝟙 future.1.1⟩, future.2⟩
    rw [Category.comp_id]
    rcases future with ⟨⟨_, _⟩, _⟩
    exact truth

theorem left_unit (A : D ⥤ Type u) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
      (unit (family A)) (multiplication A) =
        Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity (family A) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact flatten_singleton A point

def unitHom (A : D ⥤ Type u) : NaturalHom A (family A) := NaturalHom.ofNatTrans (unit A)

def multiplicationHom (A : D ⥤ Type u) : NaturalHom (family (family A)) (family A) :=
  NaturalHom.ofNatTrans (multiplication A)

theorem flatten_image_singleton (A : D ⥤ Type u) (point : D) (predicate : Predicate A point) :
    flatten A point (image (unitHom A) point predicate) = predicate := by
  apply Predicate.ext
  intro future
  constructor
  · rintro ⟨inner, ⟨argument, same, admitted⟩, truth⟩
    change singleton A future.1.1 argument = inner at same
    have currentTruth : (singleton A future.1.1 argument).holds (current A future.1.1 future.2) := by
      rw [same]
      exact truth
    have argumentEq := (singleton_current A future.1.1 argument future.2).mp currentTruth
    rw [argumentEq] at admitted
    rcases future with ⟨⟨_, _⟩, _⟩
    exact admitted
  · intro truth
    refine ⟨singleton A future.1.1 future.2, ⟨future.2, rfl, ?_⟩, ?_⟩
    · rcases future with ⟨⟨_, _⟩, _⟩
      exact truth
    · exact (singleton_current A future.1.1 future.2 future.2).mpr rfl

theorem right_unit (A : D ⥤ Type u) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
      (imageNatTrans (unitHom A)) (multiplication A) =
        Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity (family A) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact flatten_image_singleton A point

/-- Both groupings of union admit precisely the same nested witnesses at
each complete future index. -/
theorem flatten_associativity (A : D ⥤ Type u) (point : D)
    (outer : Predicate (family (family A)) point) :
    flatten A point (flatten (family A) point outer) =
      flatten A point (image (multiplicationHom A) point outer) := by
  apply Predicate.ext
  intro future
  constructor
  · rintro ⟨inner, ⟨middle, admitted, contains⟩, truth⟩
    refine ⟨flatten A future.1.1 middle, ⟨middle, rfl, admitted⟩, ?_⟩
    exact ⟨inner, contains, truth⟩
  · rintro ⟨inner, ⟨middle, same, admitted⟩, truth⟩
    change flatten A future.1.1 middle = inner at same
    have flattenedTruth : (flatten A future.1.1 middle).holds (current A future.1.1 future.2) := by
      rw [same]
      exact truth
    obtain ⟨last, contains, finalTruth⟩ := flattenedTruth
    exact ⟨last, ⟨middle, admitted, contains⟩, finalTruth⟩

theorem associativity (A : D ⥤ Type u) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
      (multiplication (family A)) (multiplication A) =
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
      (imageNatTrans (multiplicationHom A)) (multiplication A) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact flatten_associativity A point

variable {A B : D ⥤ Type u} (operation : NaturalHom A B)

theorem image_singleton (point : D) (argument : A.obj point) :
    image operation point (singleton A point argument) =
      singleton B point (operation.app point argument) := by
  apply Predicate.ext
  intro future
  constructor
  · rintro ⟨value, mapped, source⟩
    change A.map future.1.2 argument = value at source
    change B.map future.1.2 (operation.app point argument) = future.2
    exact (operation.naturality future.1.2 argument).trans
      ((congrArg (operation.app _) source).trans mapped)
  · intro target
    refine ⟨A.map future.1.2 argument, ?_, rfl⟩
    exact (operation.naturality future.1.2 argument).symm.trans target

theorem unit_argument_naturality :
    (unitHom A).comp (imageHom operation) = operation.comp (unitHom B) := by
  apply NaturalHom.ext
  exact image_singleton operation

theorem image_flatten (point : D) (outer : Predicate (family A) point) :
    image operation point (flatten A point outer) =
      flatten B point (image (imageHom operation) point outer) := by
  apply Predicate.ext
  intro future
  constructor
  · rintro ⟨argument, mapped, inner, admitted, truth⟩
    refine ⟨image operation future.1.1 inner, ⟨inner, rfl, admitted⟩, ?_⟩
    exact ⟨argument, mapped, truth⟩
  · rintro ⟨inner, ⟨original, same, admitted⟩, truth⟩
    change image operation future.1.1 original = inner at same
    have imageTruth : (image operation future.1.1 original).holds (current B future.1.1 future.2) := by
      rw [same]
      exact truth
    obtain ⟨argument, mapped, sourceTruth⟩ := imageTruth
    exact ⟨argument, mapped, original, admitted, sourceTruth⟩

theorem multiplication_argument_naturality :
    (multiplicationHom A).comp (imageHom operation) =
      (imageHom (imageHom operation)).comp (multiplicationHom B) := by
  apply NaturalHom.ext
  exact image_flatten operation

def familyIdentity : FamilyObject D ⥤ FamilyObject D where
  obj object := object
  map operation := operation
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The double power functor has the actual iterated image maps. -/
def doublePower : FamilyObject D ⥤ FamilyObject D where
  obj object := ⟨family (family object.interpretation)⟩
  map operation := imageHom (imageHom operation)
  map_id object := by
    change imageHom (imageHom (identityHom object.interpretation)) =
      identityHom (family (family object.interpretation))
    rw [imageHom_identity, imageHom_identity]
  map_comp first second := by
    change imageHom (imageHom (first.comp second)) =
      (imageHom (imageHom first)).comp (imageHom (imageHom second))
    exact (congrArg imageHom (imageHom_comp first second).symm).trans
      (imageHom_comp (imageHom first) (imageHom second)).symm

def unitTransformation : NatTrans (familyIdentity (D := D)) (futurePower (D := D)) where
  app object := unitHom object.interpretation
  naturality _ _ operation := (unit_argument_naturality operation).symm

def multiplicationTransformation : NatTrans (doublePower (D := D)) (futurePower (D := D)) where
  app object := multiplicationHom object.interpretation
  naturality _ _ operation := (multiplication_argument_naturality operation).symm

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerOperations
