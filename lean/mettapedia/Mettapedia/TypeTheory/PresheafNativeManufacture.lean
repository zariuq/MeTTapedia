import Mettapedia.GSLT.Topos.PresheafElementaryToposAction
import Mettapedia.TypeTheory.ElementaryToposNativeLanguageAction

/-!
# Native manufacture on authored closed theories

The geometric presheaf action is composed with the actual internal-language
action into higher-order dependent sum theories. The complete predicate,
type and comprehension maps and their ordinary two-cells share this action.
Object and morphism sizes remain independent; presheaf values use the common
size bound. The readouts below decode original presheaf arrows and full
dependent squares from the actual native endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.PresheafNativeManufacture

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open Mettapedia.CategoryTheory Mettapedia.GSLT.Core
open Mettapedia.GSLT.Topos.PresheafTheoryAction
open Mettapedia.GSLT.Topos.PresheafTheoryPseudofunctor
open ElementaryToposImageComprehensionAction

universe u v

def action : Pseudofunctor Theories.{u,v}
    HigherOrderDependentSigma.TwoCategory.{(max u v)+1,max u v,
      (max u v)+1,(max u v)+1,max u v} :=
  Mettapedia.GSLT.Topos.PresheafElementaryTopos.action.comp
    ElementaryToposNativeLanguageAction.action.toPseudofunctor

theorem map_strong {first last : Theories.{u,v}} (route : first ⟶ last) :
    HigherOrderDependentSigma.Strong (action.map route) :=
  ElementaryToposNativeLanguageAction.map_strong
    (Mettapedia.GSLT.Topos.PresheafElementaryTopos.action.map route)

theorem full_display_square {first last : Theories.{u,v}} (route : first ⟶ last)
    {source target : Arrow (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos first)}
    (square : source ⟶ target) :
    (ElementaryToposObjectUniverseLift.down
        (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos last)).mapArrow.map
      ((action.map route).hom.hom.right.square.left.toFunctor.map
        ((ElementaryToposObjectUniverseLift.up
          (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos first)).mapArrow.map square)) =
      (Mettapedia.GSLT.Topos.PresheafElementaryTopos.map route).functor.mapArrow.map square :=
  global_display_square (Mettapedia.GSLT.Topos.PresheafElementaryTopos.map route) square

theorem original_program_arrow {S T : LambdaTheory.{u,v}} (F : LambdaTheoryMap S T)
    {P Q : T.Objᵒᵖ ⥤ Type (max u v)} (arrow : P ⟶ Q) :
    (ElementaryToposObjectUniverseLift.down
        (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos (theory S))).map
      ((action.map (route F)).hom.hom.right.square.right.toFunctor.map
        ((ElementaryToposObjectUniverseLift.up
          (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos (theory T))).map arrow)) =
      (inverseImage F.functor).map arrow :=
  global_base_arrow (Mettapedia.GSLT.Topos.PresheafElementaryTopos.map (route F)) arrow

theorem original_theory_cell {S T : LambdaTheory.{u,v}}
    {F G : LambdaTheoryMap S T} (change : F.functor ⟶ G.functor)
    (P : T.Objᵒᵖ ⥤ Type (max u v)) :
    (ElementaryToposObjectUniverseLift.down
        (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos (theory S))).map
      ((action.map₂ (Mettapedia.GSLT.Topos.PresheafTheoryPseudofunctor.change change)).hom.hom.right.hom.right.toNatTrans.app
        ((ElementaryToposObjectUniverseLift.up
          (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos (theory T))).obj P)) =
      (cell change).app P :=
  global_base_cell
    (Mettapedia.GSLT.Topos.PresheafElementaryTopos.action.map₂
      (Mettapedia.GSLT.Topos.PresheafTheoryPseudofunctor.change change)) P

end Mettapedia.TypeTheory.PresheafNativeManufacture
