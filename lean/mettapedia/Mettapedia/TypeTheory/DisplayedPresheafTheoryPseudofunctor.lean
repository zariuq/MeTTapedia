import Mettapedia.CategoryTheory.BicategoryTwoOpposite
import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfComposition

/-!
# The complete contextual presheaf action as a pseudofunctor

Restriction reverses theory arrows and natural transformations. Its source
is therefore the one-cell opposite of the two-cell opposite of the actual
bicategory of small categories. Objects are the existing presheaf CwFs;
one-cells are actual restriction morphisms; two-cells retain their corrected
comprehension squares. Canonical identity and composition comparisons are
those already proved for the native action.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryPseudofunctor

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafCwf DisplayedPresheafTheoryCwf
open DisplayedPresheafTheoryCwfTransformation DisplayedPresheafTheoryCwfComposition

universe u

abbrev Theories := (Mettapedia.CategoryTheory.TwoOpposite Cat.{u, u})ᵒᵖ

def theory (C : Type u) [Category.{u} C] : Theories.{u} :=
  Opposite.op (Mettapedia.CategoryTheory.TwoOpposite.co (Cat.of C))

def route {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) : theory D ⟶ theory C :=
  Quiver.Hom.op (Opposite.op F.toCatHom)

def change {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (comparison : F ⟶ G) : route G ⟶ route F :=
  _root_.Bicategory.Opposite.op2 (Quiver.Hom.op comparison.toCatHom₂)

def native (theory : Theories.{u}) :=
  presheafCwfWithTerminal.{u, u, u} theory.unop.unco

def underlying {first last : Theories.{u}} (route : first ⟶ last) :
    last.unop.unco ⥤ first.unop.unco := (Opposite.unop route.unop).toFunctor

theorem underlying_route {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) : underlying (route F) = F := rfl

def homAction (first last : Theories.{u}) :
    (first ⟶ last) ⥤ PseudoCwfMorphism (native first) (native last) where
  obj route := pseudoMorphism (underlying route)
  map change := correctedTransformation change.unop2.unop.toNatTrans
  map_id route := correctedTransformation_identity (underlying route)
  map_comp firstChange lastChange :=
    correctedTransformation_composition lastChange.unop2.unop.toNatTrans
      firstChange.unop2.unop.toNatTrans

set_option backward.isDefEq.respectTransparency false in
def action : Pseudofunctor Theories.{u} CwfWithTerminal.{u + 1, u, u + 1, u} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors native homAction
  mapId theory := identityIso theory.unop.unco
  mapComp first second := compositionIso (underlying second) (underlying first)
  map₂_whisker_left := by
    intro first middle last route f g change
    apply CorrectedTransformationData.ext_of_base_eq
    apply NatTrans.ext
    funext context
    apply NatTrans.ext
    funext world
    apply ConcreteCategory.hom_ext
    intro value
    rfl
  map₂_whisker_right := by
    intro first middle last f g change route
    apply CorrectedTransformationData.ext_of_base_eq
    apply NatTrans.ext
    funext context
    apply NatTrans.ext
    funext world
    apply ConcreteCategory.hom_ext
    intro value
    rfl
  map₂_associator := by
    intro first second third last f g h
    apply CorrectedTransformationData.ext_of_base_eq
    apply NatTrans.ext
    funext context
    apply NatTrans.ext
    funext world
    apply ConcreteCategory.hom_ext
    intro value
    change (context.val.map (𝟙 _)) value = value
    exact context.val.map_id_apply _ value
  map₂_left_unitor := by
    intro first last route
    apply CorrectedTransformationData.ext_of_base_eq
    apply NatTrans.ext
    funext context
    apply NatTrans.ext
    funext world
    apply ConcreteCategory.hom_ext
    intro value
    change (context.val.map (𝟙 _)) value = value
    exact context.val.map_id_apply _ value
  map₂_right_unitor := by
    intro first last route
    apply CorrectedTransformationData.ext_of_base_eq
    apply NatTrans.ext
    funext context
    apply NatTrans.ext
    funext world
    apply ConcreteCategory.hom_ext
    intro value
    change (context.val.map (𝟙 _)) value = value
    exact context.val.map_id_apply _ value

end Mettapedia.TypeTheory.DisplayedPresheafTheoryPseudofunctor
