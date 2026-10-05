import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor

/-!
# Covered power families in an actual parameter slice

An element retains its parameter and a small-covered stable predicate of
future arguments. Every admitted argument lies over the transported
parameter at that same actual future arrow. This support condition is a
whole-future law, rather than a condition only on the present subset.

The slice object, projection, direct image under commuting argument maps,
identity/composition and singleton are constructed. The receipt bound does
not grow with the parameter or argument host levels. No uniform enumeration
is selected from propositional existence, and no indexed finality or
universal small-map representation is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPower

open CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v w t s
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w} {F : D ⥤ Type t} {G : D ⥤ Type s}

def Supports (operation : NaturalHom A B) (point : D) (parameter : B.obj point)
    (predicate : Power A point) : Prop :=
  ∀ argument : Arguments A point, predicate.val.holds argument →
    operation.app argument.1.1 argument.2 = B.map argument.1.2 parameter

abbrev Element (operation : NaturalHom A B) (point : D) :=
  {entry : B.obj point × Power A point // Supports operation point entry.1 entry.2}

theorem supports_restrict (operation : NaturalHom A B) {first second : D}
    (step : first ⟶ second) (parameter : B.obj first) (predicate : Power A first)
    (supported : Supports operation first parameter predicate) :
    Supports operation second (B.map step parameter) (restrictPower A step predicate) := by
  intro argument available
  have result := supported ((futurePrecompose A step).obj argument) available
  change operation.app argument.1.1 argument.2 = B.map (step ≫ argument.1.2) parameter at result
  rw [B.map_comp_apply] at result
  exact result

def family (operation : NaturalHom A B) : D ⥤ Type (max w (max u v)) where
  obj point := Element operation point
  map step := TypeCat.ofHom fun entry =>
    ⟨(B.map step entry.val.1, restrictPower A step entry.val.2),
      supports_restrict operation step entry.val.1 entry.val.2 entry.property⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro entry
    apply Subtype.ext
    exact Prod.ext (B.map_id_apply point entry.val.1)
      (restrictPower_identity A point entry.val.2)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro entry
    apply Subtype.ext
    exact Prod.ext (B.map_comp_apply earlier later entry.val.1)
      (restrictPower_comp A earlier later entry.val.2)

def projection (operation : NaturalHom A B) : NaturalHom (family operation) B where
  app _ entry := entry.val.1
  naturality _ _ := rfl

def predicateProjection (operation : NaturalHom A B) :
    NaturalHom (family operation) (CoveredFuturePowerFamilies.family A) where
  app _ entry := entry.val.2
  naturality _ _ := rfl

theorem supports_image (first : NaturalHom A B) (second : NaturalHom F B)
    (operation : NaturalHom A F) (commutes : operation.comp second = first)
    (point : D) (parameter : B.obj point) (predicate : Power A point)
    (supported : Supports first point parameter predicate) :
    Supports second point parameter (imagePower operation point predicate) := by
  intro argument available
  obtain ⟨source, same, admitted⟩ := available
  have square := congrArg (fun map : NaturalHom A B => map.app argument.1.1 source) commutes
  change second.app argument.1.1 (operation.app argument.1.1 source) =
    first.app argument.1.1 source at square
  rw [← same, square]
  exact supported ⟨argument.1, source⟩ admitted

def image (first : NaturalHom A B) (second : NaturalHom F B)
    (operation : NaturalHom A F) (commutes : operation.comp second = first) :
    NaturalHom (family first) (family second) where
  app point entry := ⟨(entry.val.1, imagePower operation point entry.val.2),
    supports_image first second operation commutes point entry.val.1 entry.val.2 entry.property⟩
  naturality step entry := by
    apply Subtype.ext
    exact Prod.ext rfl (imagePower_restrict operation step entry.val.2)

theorem image_projection (first : NaturalHom A B) (second : NaturalHom F B)
    (operation : NaturalHom A F) (commutes : operation.comp second = first) :
    (image first second operation commutes).comp (projection second) = projection first := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem image_identity (operation : NaturalHom A B) :
    image operation operation (identityHom A) rfl =
      identityHom (family operation) := by
  apply NaturalHom.ext
  intro point entry
  apply Subtype.ext
  exact Prod.ext rfl (imagePower_identity point entry.val.2)

theorem image_comp (first : NaturalHom A B) (second : NaturalHom F B)
    (third : NaturalHom G B) (earlier : NaturalHom A F) (later : NaturalHom F G)
    (earlierSquare : earlier.comp second = first) (laterSquare : later.comp third = second)
    (compositeSquare : (earlier.comp later).comp third = first) :
    image first third (earlier.comp later) compositeSquare =
      (image first second earlier earlierSquare).comp (image second third later laterSquare) := by
  apply NaturalHom.ext
  intro point entry
  apply Subtype.ext
  exact Prod.ext rfl (imagePower_comp earlier later point entry.val.2).symm

theorem supports_singleton (operation : NaturalHom A B) (point : D) (argument : A.obj point) :
    Supports operation point (operation.app point argument) (singletonPower A point argument) := by
  intro future available
  change A.map future.1.2 argument = future.2 at available
  rw [← available]
  exact (operation.naturality future.1.2 argument).symm

def singleton (operation : NaturalHom A B) : NaturalHom A (family operation) where
  app point argument := ⟨(operation.app point argument, singletonPower A point argument),
    supports_singleton operation point argument⟩
  naturality step argument := by
    apply Subtype.ext
    exact Prod.ext (operation.naturality step argument) (singletonPower_restrict A step argument)

theorem singleton_projection (operation : NaturalHom A B) :
    (singleton operation).comp (projection operation) = operation := by
  apply NaturalHom.ext
  intro _ _
  rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPower
