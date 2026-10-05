import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFamilies
import Mettapedia.TypeTheory.ContextualWitnessCover

/-!
# Images and inverse images of full contextual power families

Natural argument maps act on stable predicates by actual existential image
and inverse image at every future arrow. The image and inverse-image maps
are natural, compose exactly, and form an order adjunction. An explicitly
constructed pullback of argument families satisfies the complete-future
Beck--Chevalley equation.

All context objects, arrows and argument fibres inhabit the same small
universe. These operations are on the constructed full power families of
small objects; they do not classify small subobjects of arbitrary large
objects or establish indexed finality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFunctor

open CategoryTheory FuturePowerFamilies
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u
variable {D : Type u} [Category.{u} D]
variable {A B F : D ⥤ Type u}

def identityHom (A : D ⥤ Type u) : NaturalHom A A where
  app _ := id
  naturality _ _ := rfl

/-- Every actual future index is retained while its argument is mapped. -/
def futureArguments (operation : NaturalHom A B) (point : D) :
    Arguments A point ⥤ Arguments B point where
  obj argument := ⟨argument.1, operation.app argument.1.1 argument.2⟩
  map step := ⟨step.1, (operation.naturality step.1.1 _).trans
    (congrArg (operation.app _) step.2)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def inverseImage (operation : NaturalHom A B) (point : D) (predicate : Predicate B point) :
    Predicate A point where
  holds argument := predicate.holds ((futureArguments operation point).obj argument)
  closed step available := predicate.closed ((futureArguments operation point).map step) available

/-- Existence is used only as predicate truth. There is no selected
preimage, and labels retain the entire actual future index. -/
def image (operation : NaturalHom A B) (point : D) (predicate : Predicate A point) :
    Predicate B point where
  holds argument := ∃ value : A.obj argument.1.1,
    operation.app argument.1.1 value = argument.2 ∧ predicate.holds ⟨argument.1, value⟩
  closed {first second} step available := by
    obtain ⟨value, mapped, holds⟩ := available
    refine ⟨A.map step.1.1 value, ?_, ?_⟩
    · exact (operation.naturality step.1.1 value).symm.trans
        ((congrArg (B.map step.1.1) mapped).trans step.2)
    · let firstArgument : Arguments A point := ⟨first.1, value⟩
      let secondArgument : Arguments A point := ⟨second.1, A.map step.1.1 value⟩
      let argumentStep : firstArgument ⟶ secondArgument := ⟨step.1, rfl⟩
      exact predicate.closed argumentStep holds

theorem image_holds (operation : NaturalHom A B) (point : D)
    (predicate : Predicate A point) (argument : Arguments B point) :
    (image operation point predicate).holds argument ↔
      ∃ value : A.obj argument.1.1, operation.app argument.1.1 value = argument.2 ∧
        predicate.holds ⟨argument.1, value⟩ := Iff.rfl

theorem inverseImage_holds (operation : NaturalHom A B) (point : D)
    (predicate : Predicate B point) (argument : Arguments A point) :
    (inverseImage operation point predicate).holds argument ↔
      predicate.holds ⟨argument.1, operation.app argument.1.1 argument.2⟩ := Iff.rfl

theorem image_restrict (operation : NaturalHom A B) {first second : D}
    (step : first ⟶ second) (predicate : Predicate A first) :
    restrict B step (image operation first predicate) =
      image operation second (restrict A step predicate) := by
  apply Predicate.ext
  intro argument
  exact Iff.rfl

theorem inverseImage_restrict (operation : NaturalHom A B) {first second : D}
    (step : first ⟶ second) (predicate : Predicate B first) :
    restrict A step (inverseImage operation first predicate) =
      inverseImage operation second (restrict B step predicate) := by
  apply Predicate.ext
  intro argument
  exact Iff.rfl

def imageHom (operation : NaturalHom A B) : NaturalHom (family A) (family B) where
  app := image operation
  naturality := image_restrict operation

def inverseImageHom (operation : NaturalHom A B) : NaturalHom (family B) (family A) where
  app := inverseImage operation
  naturality := inverseImage_restrict operation

def imageNatTrans (operation : NaturalHom A B) : NatTrans (family A) (family B) :=
  (imageHom operation).toNatTrans

def inverseImageNatTrans (operation : NaturalHom A B) : NatTrans (family B) (family A) :=
  (inverseImageHom operation).toNatTrans

theorem image_identity (point : D) (predicate : Predicate A point) :
    image (identityHom A) point predicate = predicate := by
  apply Predicate.ext
  intro argument
  constructor
  · rintro ⟨value, same, holds⟩
    change value = argument.2 at same
    cases same
    rcases argument with ⟨⟨_, _⟩, _⟩
    exact holds
  · intro holds
    exact ⟨argument.2, rfl, holds⟩

theorem inverseImage_identity (point : D) (predicate : Predicate A point) :
    inverseImage (identityHom A) point predicate = predicate := by
  apply Predicate.ext
  intro argument
  rcases argument with ⟨⟨_, _⟩, _⟩
  exact Iff.rfl

theorem image_comp (first : NaturalHom A B) (second : NaturalHom B F)
    (point : D) (predicate : Predicate A point) :
    image second point (image first point predicate) = image (first.comp second) point predicate := by
  apply Predicate.ext
  intro argument
  constructor
  · rintro ⟨middle, lastEq, firstValue, middleEq, holds⟩
    exact ⟨firstValue, (congrArg (second.app _) middleEq).trans lastEq, holds⟩
  · rintro ⟨firstValue, lastEq, holds⟩
    exact ⟨first.app _ firstValue, lastEq, firstValue, rfl, holds⟩

theorem inverseImage_comp (first : NaturalHom A B) (second : NaturalHom B F)
    (point : D) (predicate : Predicate F point) :
    inverseImage first point (inverseImage second point predicate) =
      inverseImage (first.comp second) point predicate := by
  apply Predicate.ext
  intro argument
  exact Iff.rfl

def Included {point : D} (first second : Predicate A point) : Prop :=
  ∀ argument, first.holds argument → second.holds argument

/-- The existential image is left adjoint to inverse image in the order of
actual stable predicates, at every complete future carrier. -/
theorem image_inverseImage_adjunction (operation : NaturalHom A B) (point : D)
    (first : Predicate A point) (second : Predicate B point) :
    Included (image operation point first) second ↔ Included first (inverseImage operation point second) := by
  constructor
  · intro bound argument holds
    exact bound ((futureArguments operation point).obj argument) ⟨argument.2, rfl, holds⟩
  · intro bound argument available
    obtain ⟨value, same, holds⟩ := available
    have result := bound ⟨argument.1, value⟩ holds
    change second.holds ⟨argument.1, operation.app argument.1.1 value⟩ at result
    rw [same] at result
    rcases argument with ⟨⟨_, _⟩, _⟩
    exact result

theorem inverseImage_image_of_injective (operation : NaturalHom A B)
    (injective : ∀ point, Function.Injective (operation.app point))
    (point : D) (predicate : Predicate A point) :
    inverseImage operation point (image operation point predicate) = predicate := by
  apply Predicate.ext
  intro argument
  constructor
  · rintro ⟨value, same, holds⟩
    have inputEq := injective argument.1.1 same
    cases inputEq
    rcases argument with ⟨⟨_, _⟩, _⟩
    exact holds
  · intro holds
    exact ⟨argument.2, rfl, holds⟩

theorem image_inverseImage_of_surjective (operation : NaturalHom A B)
    (surjective : ∀ point, Function.Surjective (operation.app point))
    (point : D) (predicate : Predicate B point) :
    image operation point (inverseImage operation point predicate) = predicate := by
  apply Predicate.ext
  intro argument
  constructor
  · rintro ⟨value, same, holds⟩
    change predicate.holds ⟨argument.1, operation.app argument.1.1 value⟩ at holds
    rw [same] at holds
    rcases argument with ⟨⟨_, _⟩, _⟩
    exact holds
  · intro holds
    obtain ⟨value, same⟩ := surjective argument.1.1 argument.2
    refine ⟨value, same, ?_⟩
    change predicate.holds ⟨argument.1, operation.app argument.1.1 value⟩
    rw [same]
    rcases argument with ⟨⟨_, _⟩, _⟩
    exact holds

theorem imageHom_identity (A : D ⥤ Type u) :
    imageHom (identityHom A) = identityHom (family A) := by
  apply NaturalHom.ext
  exact image_identity

theorem imageHom_comp (first : NaturalHom A B) (second : NaturalHom B F) :
    (imageHom first).comp (imageHom second) = imageHom (first.comp second) := by
  apply NaturalHom.ext
  exact image_comp first second

/-- An explicit argument-family category avoids inheriting implementation
choices from the general functor-category composition wrappers. -/
structure FamilyObject (D : Type u) [Category.{u} D] where
  interpretation : D ⥤ Type u

instance familyObjectCategory : Category.{u} (FamilyObject D) where
  Hom first second := NaturalHom first.interpretation second.interpretation
  id first := identityHom first.interpretation
  comp first second := first.comp second
  id_comp _ := NaturalHom.ext _ _ (fun _ _ => rfl)
  comp_id _ := NaturalHom.ext _ _ (fun _ _ => rfl)
  assoc _ _ _ := NaturalHom.ext _ _ (fun _ _ => rfl)

/-- The constructed full future-power operation is an actual endofunctor on
the small argument-family category. Larger-object small powerclasses remain
a separate construction. -/
def futurePower : FamilyObject D ⥤ FamilyObject D where
  obj object := ⟨family object.interpretation⟩
  map operation := imageHom operation
  map_id object := imageHom_identity object.interpretation
  map_comp first second := (imageHom_comp first second).symm

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFunctor
