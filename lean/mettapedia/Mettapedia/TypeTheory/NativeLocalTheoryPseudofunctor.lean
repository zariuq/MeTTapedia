import Mettapedia.TypeTheory.NativeLocalTheoryTransformation
import Mettapedia.TypeTheory.ContextualCorrectedBaseLift
import Mettapedia.TypeTheory.DisplayedPresheafTheoryPseudofunctor

/-!
# The contextual theory action on native family presentations

The object action retains external parameter contexts, their actual families
and names. Theory routes act on all three parts, and theory transformations
retain the supplied decoded evidence. Cartesian factorization supplies the
identity and composition comparisons in the actual corrected hom categories.
The resulting action is a pseudofunctor on the one-cell and two-cell opposite
of small categories. Logical constructor comparisons remain the separately
proved native sum isomorphisms and qualified colax product maps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeLocalTheoryPseudofunctor

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open Mettapedia.GSLT.Core.ContextualLadder
open NativeLocalTheoryTransformation
open DisplayedPresheafTheoryPseudofunctor (Theories underlying)

universe u

def native (theory : Theories.{u}) := nativeLocalModel theory.unop.unco

def homAction (first last : Theories.{u}) :
    (first ⟶ last) ⥤ PseudoCwfMorphism (native first) (native last) where
  obj route := localMorphism (underlying route)
  map change := correctedTransformation change.unop2.unop.toNatTrans
  map_id route := correctedTransformation_identity (underlying route)
  map_comp firstChange lastChange :=
    correctedTransformation_composition lastChange.unop2.unop.toNatTrans
      firstChange.unop2.unop.toNatTrans

/-- The identity comparison is the cartesian lift of the actual identity
restriction comparison on complete context substitutions. -/
def identityIso (C : Type u) [Category.{u} C] :
    localMorphism (𝟭 C) ≅ PseudoCwfMorphism.identity (nativeLocalModel C) :=
  ContextualCorrectedBaseLift.liftIso
    (DisplayedPresheafTheoryCwfComposition.identityBaseIso C)

/-- The direct-to-staged comparison lifts the actual composed restriction
of contexts; no equality of chosen family presentations is assumed. -/
def compositionIso {C D E : Type u}
    [Category.{u} C] [Category.{u} D] [Category.{u} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    localMorphism (F ⋙ G) ≅ (localMorphism G).comp (localMorphism F) :=
  ContextualCorrectedBaseLift.liftIso
    (DisplayedPresheafTheoryCwfComposition.compositionBaseIso F G)

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

end Mettapedia.TypeTheory.NativeLocalTheoryPseudofunctor
