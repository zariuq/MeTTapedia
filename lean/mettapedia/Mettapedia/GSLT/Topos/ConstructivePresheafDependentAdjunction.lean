import Mettapedia.GSLT.Topos.ConstructivePresheafDependentFunctions
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The dependent-section adjunction in hom-set form -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf

universe u
variable {C : Type u} [Category.{u} C]

/-- Standard natural transformations, with explicit constructive category laws. -/
@[instance_reducible]
def functionCategory (D : Type u) [Category.{u} D] : Category.{u} (D ⥤ Type u) where
  Hom := NatTrans
  id := identity
  comp := compose
  id_comp transformation := by
    apply NatTrans.ext
    funext X
    exact Category.id_comp (transformation.app X)
  comp_id transformation := by
    apply NatTrans.ext
    funext X
    exact Category.comp_id (transformation.app X)
  assoc first second third := by
    apply NatTrans.ext
    funext X
    exact Category.assoc (first.app X) (second.app X) (third.app X)

attribute [local instance] functionCategory

def projectionReindex (F : C ⥤ Type u) : (C ⥤ Type u) ⥤ (F.Elements ⥤ Type u) where
  obj H := overElements F H
  map transformation := overMap transformation
  map_id H := by
    apply NatTrans.ext
    funext X
    rfl
  map_comp first second := by
    apply NatTrans.ext
    funext X
    rfl

def dependentProduct (F : C ⥤ Type u) : (F.Elements ⥤ Type u) ⥤ (C ⥤ Type u) where
  obj G := dependentFunctions F G
  map transformation := mapFamily transformation
  map_id G := by
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro value
    apply DependentSection.ext
    intro Y restriction argument
    rfl
  map_comp first second := by
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro value
    apply DependentSection.ext
    intro Y restriction argument
    rfl

def dependentAdjunctionCore (F : C ⥤ Type u) :
    Adjunction.CoreHomEquiv (projectionReindex F) (dependentProduct F) where
  homEquiv H G := dependentHomEquiv F G H
  homEquiv_naturality_left_symm first operation := by
    apply NatTrans.ext
    funext X
    rfl
  homEquiv_naturality_right operation later := by
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro parameter
    apply DependentSection.ext
    intro Y restriction argument
    rfl

#print axioms functionCategory
#print axioms projectionReindex
#print axioms dependentProduct
#print axioms dependentAdjunctionCore

end Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
