import Mettapedia.GSLT.Core.LambdaTheory
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Inverse image of presheaves along a theory map

Precomposition with the opposite of an actual base functor reverses the
direction of theories. Limits and colimits are preserved because their
evaluation at every source object is the evaluation at its mapped object.
No preservation of dependent products or of the classifier is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafTheoryAction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core

universe u₁ u₂ v₁ v₂ w j k

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The actual precomposition functor, with no choice of Kan extension. -/
def inverseImage (F : C ⥤ D) : (Dᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w) :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj F.op

@[simp] theorem inverseImage_obj_obj (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type w) (X : C) :
    ((inverseImage F).obj P).obj (Opposite.op X) = P.obj (Opposite.op (F.obj X)) := rfl

@[simp] theorem inverseImage_obj_map (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type w)
    {X Y : C} (f : X ⟶ Y) :
    ((inverseImage F).obj P).map f.op = P.map (F.map f).op := rfl

@[simp] theorem inverseImage_map_app (F : C ⥤ D) {P Q : Dᵒᵖ ⥤ Type w}
    (map : P ⟶ Q) (X : C) :
    ((inverseImage F).map map).app (Opposite.op X) = map.app (Opposite.op (F.obj X)) := rfl

instance inverseImage_preservesLimitsOfShape (F : C ⥤ D) (J : Type j)
    [Category.{k} J] [HasLimitsOfShape J (Type w)] :
    PreservesLimitsOfShape J (inverseImage F : (Dᵒᵖ ⥤ Type w) ⥤ _) := by
  unfold inverseImage
  infer_instance

instance inverseImage_preservesColimitsOfShape (F : C ⥤ D) (J : Type j)
    [Category.{k} J] [HasColimitsOfShape J (Type w)] :
    PreservesColimitsOfShape J (inverseImage F : (Dᵒᵖ ⥤ Type w) ⥤ _) := by
  unfold inverseImage
  infer_instance

instance inverseImage_preservesLimits (F : C ⥤ D) :
    PreservesLimitsOfSize.{w,w} (inverseImage F : (Dᵒᵖ ⥤ Type w) ⥤ _) := by
  unfold inverseImage
  infer_instance

instance inverseImage_preservesColimits (F : C ⥤ D) :
    PreservesColimitsOfSize.{w,w} (inverseImage F : (Dᵒᵖ ⥤ Type w) ⥤ _) := by
  unfold inverseImage
  infer_instance

instance inverseImage_preservesFiniteLimits (F : C ⥤ D) :
    PreservesFiniteLimits (inverseImage F : (Dᵒᵖ ⥤ Type w) ⥤ _) := by
  unfold inverseImage
  infer_instance

instance inverseImage_preservesFiniteColimits (F : C ⥤ D) :
    PreservesFiniteColimits (inverseImage F : (Dᵒᵖ ⥤ Type w) ⥤ _) := by
  unfold inverseImage
  infer_instance

/-- Every supplied limiting cone is taken to a limiting cone. -/
noncomputable def mapIsLimit (F : C ⥤ D) {J : Type j} [Category.{k} J]
    [HasLimitsOfShape J (Type w)] {diagram : J ⥤ Dᵒᵖ ⥤ Type w}
    {cone : Cone diagram} (limit : IsLimit cone) :
    IsLimit ((inverseImage F).mapCone cone) := isLimitOfPreserves _ limit

/-- Every supplied colimiting cocone is taken to a colimiting cocone. -/
noncomputable def mapIsColimit (F : C ⥤ D) {J : Type j} [Category.{k} J]
    [HasColimitsOfShape J (Type w)] {diagram : J ⥤ Dᵒᵖ ⥤ Type w}
    {cocone : Cocone diagram} (colimit : IsColimit cocone) :
    IsColimit ((inverseImage F).mapCocone cocone) := isColimitOfPreserves _ colimit

/-- Actual pullback squares are preserved, with all four mapped arrows. -/
theorem mapIsPullback (F : C ⥤ D) {P Q R S : Dᵒᵖ ⥤ Type w}
    {top : P ⟶ Q} {left : P ⟶ R} {right : Q ⟶ S} {bottom : R ⟶ S}
    (square : IsPullback top left right bottom) :
    IsPullback ((inverseImage F).map top) ((inverseImage F).map left)
      ((inverseImage F).map right) ((inverseImage F).map bottom) := square.map _

/-- Pushout preservation is earned by the same actual inverse image;
there is no additional pushout-preservation hypothesis. -/
theorem mapIsPushout (F : C ⥤ D) {P Q R S : Dᵒᵖ ⥤ Type w}
    {top : P ⟶ Q} {left : P ⟶ R} {right : Q ⟶ S} {bottom : R ⟶ S}
    (square : IsPushout top left right bottom) :
    IsPushout ((inverseImage F).map top) ((inverseImage F).map left)
      ((inverseImage F).map right) ((inverseImage F).map bottom) := square.map _

/-- The source theory's logical map supplies its actual underlying functor.
The inverse image goes from target presheaves to source presheaves. -/
def theoryInverseImage {source : LambdaTheory.{u₁,v₁}}
    {target : LambdaTheory.{u₂,v₁}} (F : LambdaTheoryMap source target) :
    (target.Objᵒᵖ ⥤ Type w) ⥤ (source.Objᵒᵖ ⥤ Type w) := inverseImage F.functor

instance theoryInverseImage_preservesFiniteLimits {source : LambdaTheory.{u₁,v₁}}
    {target : LambdaTheory.{u₂,v₁}} (F : LambdaTheoryMap source target) :
    PreservesFiniteLimits (theoryInverseImage F : (target.Objᵒᵖ ⥤ Type w) ⥤ _) := by
  unfold theoryInverseImage
  infer_instance

instance theoryInverseImage_preservesFiniteColimits {source : LambdaTheory.{u₁,v₁}}
    {target : LambdaTheory.{u₂,v₁}} (F : LambdaTheoryMap source target) :
    PreservesFiniteColimits (theoryInverseImage F : (target.Objᵒᵖ ⥤ Type w) ⥤ _) := by
  unfold theoryInverseImage
  infer_instance

end Mettapedia.GSLT.Topos.PresheafTheoryAction
