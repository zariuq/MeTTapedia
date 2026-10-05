import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFunctor

/-!
# Constructed images of small-covered future predicates

Natural maps of arbitrarily larger argument families preserve the original
small covers by mapping each receipt. Images retain the complete future
index, are stable, commute with contextual restriction, and satisfy identity
and composition. Singleton predicates have constructed one-receipt covers
at every future, independently of argument size.

These constructions give a genuine endofunctor and natural singleton map
on the larger argument-family category. They do not turn an arbitrary inverse
image into a small-covered predicate or supply uniform inner enumerations
needed for a larger-object union construction. Those are separate small-map
and collection obligations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor

open CategoryTheory CoveredFuturePowerFamilies
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v w t
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w} {F : D ⥤ Type t}

def identityHom (A : D ⥤ Type v) : NaturalHom A A where
  app _ := id
  naturality _ _ := rfl

def futureArguments (operation : NaturalHom A B) (point : D) :
    Arguments A point ⥤ Arguments B point where
  obj argument := ⟨argument.1, operation.app argument.1.1 argument.2⟩
  map step := ⟨step.1, (operation.naturality step.1.1 _).trans
    (congrArg (operation.app _) step.2)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An arbitrary inverse image constructs a stable predicate. It does not
silently assert the existence of a small cover for that predicate. -/
def inverseImage (operation : NaturalHom A B) (point : D) (predicate : Predicate B point) :
    Predicate A point where
  holds argument := predicate.holds ((futureArguments operation point).obj argument)
  closed step available := predicate.closed ((futureArguments operation point).map step) available

def image (operation : NaturalHom A B) (point : D) (predicate : Predicate A point) :
    Predicate B point where
  holds argument := ∃ value : A.obj argument.1.1,
    operation.app argument.1.1 value = argument.2 ∧ predicate.holds ⟨argument.1, value⟩
  closed {first second} step available := by
    obtain ⟨value, mapped, holds⟩ := available
    refine ⟨A.map step.1.1 value, ?_, ?_⟩
    · exact (operation.naturality step.1.1 value).symm.trans
        ((congrArg (B.map step.1.1) mapped).trans step.2)
    · let earlier : Arguments A point := ⟨first.1, value⟩
      let later : Arguments A point := ⟨second.1, A.map step.1.1 value⟩
      let move : earlier ⟶ later := ⟨step.1, rfl⟩
      exact predicate.closed move holds

def imageEnumeration (operation : NaturalHom A B) (point : D)
    {predicate : Predicate A point} (enumeration : Enumeration predicate) :
    Enumeration (image operation point predicate) where
  Carrier := enumeration.Carrier
  value future code := operation.app future.1 (enumeration.value future code)
  covered future argument := by
    constructor
    · rintro ⟨value, same, holds⟩
      obtain ⟨code, decoded⟩ := (enumeration.covered future value).mp holds
      exact ⟨code, (congrArg (operation.app future.1) decoded).trans same⟩
    · rintro ⟨code, same⟩
      exact ⟨enumeration.value future code, same,
        (enumeration.covered future _).mpr ⟨code, rfl⟩⟩

def imagePower (operation : NaturalHom A B) (point : D) (predicate : Power A point) :
    Power B point :=
  ⟨image operation point predicate.val, by
    obtain ⟨enumeration⟩ := predicate.property
    exact ⟨imageEnumeration operation point enumeration⟩⟩

theorem image_restrict (operation : NaturalHom A B) {first second : D}
    (step : first ⟶ second) (predicate : Predicate A first) :
    restrict B step (image operation first predicate) =
      image operation second (restrict A step predicate) := by
  apply Predicate.ext
  intro argument
  exact Iff.rfl

theorem imagePower_restrict (operation : NaturalHom A B) {first second : D}
    (step : first ⟶ second) (predicate : Power A first) :
    restrictPower B step (imagePower operation first predicate) =
      imagePower operation second (restrictPower A step predicate) :=
  Subtype.ext (image_restrict operation step predicate.val)

def imageHom (operation : NaturalHom A B) : NaturalHom (family A) (family B) where
  app := imagePower operation
  naturality := imagePower_restrict operation

def Included {point : D} (first second : Predicate A point) : Prop :=
  ∀ argument, first.holds argument → second.holds argument

/-- The order adjunction holds for full predicates. Small-covered image
closure does not change the domain of this inverse-image statement. -/
theorem image_inverseImage_adjunction (operation : NaturalHom A B) (point : D)
    (first : Predicate A point) (second : Predicate B point) :
    Included (image operation point first) second ↔
      Included first (inverseImage operation point second) := by
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

theorem imagePower_identity (point : D) (predicate : Power A point) :
    imagePower (identityHom A) point predicate = predicate :=
  Subtype.ext (image_identity point predicate.val)

theorem imagePower_comp (first : NaturalHom A B) (second : NaturalHom B F)
    (point : D) (predicate : Power A point) :
    imagePower second point (imagePower first point predicate) =
      imagePower (first.comp second) point predicate :=
  Subtype.ext (image_comp first second point predicate.val)

theorem imageHom_identity (A : D ⥤ Type v) :
    imageHom (identityHom A) = identityHom (family A) := by
  apply NaturalHom.ext
  exact imagePower_identity

theorem imageHom_comp (first : NaturalHom A B) (second : NaturalHom B F) :
    (imageHom first).comp (imageHom second) = imageHom (first.comp second) := by
  apply NaturalHom.ext
  exact imagePower_comp first second

def singleton (A : D ⥤ Type v) (point : D) (argument : A.obj point) : Predicate A point where
  holds future := A.map future.1.2 argument = future.2
  closed {first second} move same := by
    have mapLaw := congrArg (fun operation => operation argument)
      (A.map_comp first.1.2 move.1.1)
    exact (congrArg (fun step => A.map step argument) move.1.2).symm.trans
      (mapLaw.trans ((congrArg (A.map move.1.1) same).trans move.2))

def singletonEnumeration (A : D ⥤ Type v) (point : D) (argument : A.obj point) :
    Enumeration (singleton A point argument) where
  Carrier _ := PUnit.{u + 1}
  value future _ := A.map future.2 argument
  covered _ _ := ⟨fun same => ⟨PUnit.unit, same⟩, fun ⟨_, same⟩ => same⟩

def singletonPower (A : D ⥤ Type v) (point : D) (argument : A.obj point) : Power A point :=
  ⟨singleton A point argument, ⟨singletonEnumeration A point argument⟩⟩

theorem singleton_current (A : D ⥤ Type v) (point : D) (first second : A.obj point) :
    (singletonPower A point first).val.holds (current A point second) ↔ first = second := by
  change A.map (𝟙 point) first = second ↔ _
  rw [A.map_id]
  exact Iff.rfl

theorem singletonPower_injective (A : D ⥤ Type v) (point : D) :
    Function.Injective (singletonPower A point) := by
  intro first second same
  have truth := (singleton_current A point first first).mpr rfl
  rw [same] at truth
  exact ((singleton_current A point second first).mp truth).symm

theorem singleton_restrict (A : D ⥤ Type v) {first second : D} (step : first ⟶ second)
    (argument : A.obj first) :
    restrict A step (singleton A first argument) = singleton A second (A.map step argument) := by
  apply Predicate.ext
  intro future
  change A.map (step ≫ future.1.2) argument = future.2 ↔ _
  rw [A.map_comp]
  exact Iff.rfl

theorem singletonPower_restrict (A : D ⥤ Type v) {first second : D} (step : first ⟶ second)
    (argument : A.obj first) :
    restrictPower A step (singletonPower A first argument) =
      singletonPower A second (A.map step argument) :=
  Subtype.ext (singleton_restrict A step argument)

def unitHom (A : D ⥤ Type v) : NaturalHom A (family A) where
  app := singletonPower A
  naturality := singletonPower_restrict A

theorem image_singleton (operation : NaturalHom A B) (point : D) (argument : A.obj point) :
    image operation point (singleton A point argument) =
      singleton B point (operation.app point argument) := by
  apply Predicate.ext
  intro future
  constructor
  · rintro ⟨value, same, supplied⟩
    change A.map future.1.2 argument = value at supplied
    exact (operation.naturality future.1.2 argument).trans
      ((congrArg (operation.app future.1.1) supplied).trans same)
  · intro target
    exact ⟨A.map future.1.2 argument,
      (operation.naturality future.1.2 argument).symm.trans target, rfl⟩

theorem unit_argument_naturality (operation : NaturalHom A B) :
    (unitHom A).comp (imageHom operation) = operation.comp (unitHom B) := by
  apply NaturalHom.ext
  intro point argument
  exact Subtype.ext (image_singleton operation point argument)

structure FamilyObject (D : Type u) [Category.{u} D] where
  interpretation : D ⥤ Type (max u v)

instance familyObjectCategory : Category.{max u v} (FamilyObject.{u, v} D) where
  Hom first second := NaturalHom first.interpretation second.interpretation
  id first := identityHom first.interpretation
  comp first second := first.comp second
  id_comp _ := NaturalHom.ext _ _ (fun _ _ => rfl)
  comp_id _ := NaturalHom.ext _ _ (fun _ _ => rfl)
  assoc _ _ _ := NaturalHom.ext _ _ (fun _ _ => rfl)

/-- A genuine larger-object endofunctor, with small cover bound unchanged. -/
def futurePower : FamilyObject.{u, v} D ⥤ FamilyObject.{u, v} D where
  obj object := ⟨family object.interpretation⟩
  map operation := imageHom operation
  map_id object := imageHom_identity object.interpretation
  map_comp first second := (imageHom_comp first second).symm

theorem smallEquiv_image {A B : D ⥤ Type u} (operation : NaturalHom A B)
    (point : D) (predicate : Power A point) :
    smallEquiv B point (imagePower operation point predicate) =
      FuturePowerFunctor.image operation point (smallEquiv A point predicate) := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor
