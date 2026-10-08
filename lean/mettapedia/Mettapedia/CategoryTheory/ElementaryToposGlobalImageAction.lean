import Mettapedia.CategoryTheory.ElementaryToposImagePseudofunctor
import Mettapedia.CategoryTheory.ElementaryToposImageMate
import Mettapedia.CategoryTheory.ElementaryToposObjectUniverseAction

/-!
# Global elementary-topos action on image-comprehension adjunctions

Object-universe lifting covers independently sized objects and morphisms.
It retains the original arrows and natural transformations, and composes
with the complete native adjunction action. The actual canonical left
mates are invertible by image preservation; no preservation of dependent
products or classifiers is imposed on geometric maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposImageComprehensionAction

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open FibrationTwoCategory

universe u v

def globalAmbientAction : StrictPseudofunctor ElementaryTopos.{u,v}
    FibrationAdjunctionTwoCategory.{max u v,v} :=
  ElementaryToposObjectUniverseLift.action.comp normalizedAction

@[simp] theorem globalAmbientAction_object (topos : ElementaryTopos.{u,v}) :
    globalAmbientAction.obj topos = object (ElementaryToposObjectUniverseLift.raised topos) :=
  rfl

@[simp] theorem globalAmbientAction_map {source target : ElementaryTopos.{u,v}}
    (route : source ⟶ target) :
    globalAmbientAction.map route = map (ElementaryToposObjectUniverseLift.map route) := rfl

@[simp] theorem globalAmbientAction_map₂ {source target : ElementaryTopos.{u,v}}
    {first second : source ⟶ target} (change : first ⟶ second) :
    globalAmbientAction.map₂ change = map₂ (ElementaryToposObjectUniverseLift.map₂ change) :=
  rfl

theorem globalAmbientAction_strong {source target : ElementaryTopos.{u,v}}
    (route : source ⟶ target) :
    AdjunctionTwoCategory.Strong (globalAmbientAction.map route) :=
  map_strong (ElementaryToposObjectUniverseLift.map route)

/-- The translated base arrow decodes to the independently supplied
original arrow, including nonidentity geometric maps. -/
theorem global_base_arrow {source target : ElementaryTopos.{u,v}}
    (route : source ⟶ target) {first second : source} (arrow : first ⟶ second) :
    (ElementaryToposObjectUniverseLift.down target).map
      ((globalAmbientAction.map route).hom.right.square.right.toFunctor.map
        ((ElementaryToposObjectUniverseLift.up source).map arrow)) =
      route.functor.map arrow := rfl

theorem global_base_cell {source target : ElementaryTopos.{u,v}}
    {first second : source ⟶ target} (change : first ⟶ second) (base : source) :
    (ElementaryToposObjectUniverseLift.down target).map
      ((globalAmbientAction.map₂ change).hom.right.hom.right.toNatTrans.app
        ((ElementaryToposObjectUniverseLift.up source).obj base)) =
      change.app base := rfl

/-- The complete dependent display square retains both original
components; equality of base observations alone is not substituted. -/
theorem global_display_square {source target : ElementaryTopos.{u,v}}
    (route : source ⟶ target) {first second : Arrow source} (square : first ⟶ second) :
    (ElementaryToposObjectUniverseLift.down target).mapArrow.map
      ((globalAmbientAction.map route).hom.right.square.left.toFunctor.map
        ((ElementaryToposObjectUniverseLift.up source).mapArrow.map square)) =
      route.functor.mapArrow.map square := by
  apply Arrow.hom_ext <;> rfl

end Mettapedia.CategoryTheory.ElementaryToposImageComprehensionAction
