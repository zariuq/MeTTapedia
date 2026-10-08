import Mettapedia.GSLT.Topos.PresheafElementaryTopos
import Mettapedia.GSLT.Topos.PresheafTheoryPseudofunctor
import Mettapedia.GSLT.Topos.PresheafTheoryKanAdjunctions

/-!
# The reversed presheaf action into elementary topoi

Precomposition preserves finite limits and has the constructed right Kan
adjoint. It therefore gives an actual geometric inverse-image map. The
ordinary source natural transformations act in the reversed direction.
The identity, composition and horizontal comparisons are the complete
precomposition comparisons, now in the genuine geometric target.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Topos.PresheafElementaryTopos

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Bicategory
open Mettapedia.GSLT.Core PresheafTheoryAction PresheafTheoryPseudofunctor
open Mettapedia.CategoryTheory

universe u₁ u₂ v₁ v₂ w u v

/-- The common carrier includes all four indexing-category sizes. No
equality of the source object and arrow universes is required. -/
def inverseImageMap {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D) :
    ElementaryTopos.GeometricHom
      (object.{u₂,v₂,max u₁ v₁ w} D) (object.{u₁,v₁,max u₂ v₂ w} C) where
  functor := inverseImage F
  finite := inverseImage_preservesFiniteLimits F
  leftAdjoint := ⟨rightKan F, ⟨rightAdjunction F⟩⟩

theorem inverseImageMap_value {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
    (P : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) (X : C) :
    ((inverseImageMap F).functor.obj P).obj (Opposite.op X) =
      P.obj (Opposite.op (F.obj X)) := rfl

def topos (S : Theories.{u,v}) : ElementaryTopos.{(max u v)+1,max u v} :=
  object.{u,v,0} S.unop.unco.Obj

def map {first last : Theories.{u,v}} (F : first ⟶ last) : topos first ⟶ topos last where
  functor := inverseImage (underlying F)
  finite := inverseImage_preservesFiniteLimits (underlying F)
  leftAdjoint := ⟨rightKan (underlying F), ⟨rightAdjunction (underlying F)⟩⟩

def geometricHomAction (first last : Theories.{u,v}) :
    (first ⟶ last) ⥤ (topos first ⟶ topos last) where
  obj := map
  map α := cell α.unop2.unop
  map_id F := cell_id (underlying F)
  map_comp α β := cell_comp β.unop2.unop α.unop2.unop

set_option backward.isDefEq.respectTransparency false in
def action : Pseudofunctor Theories.{u,v}
    ElementaryTopos.{(max u v)+1,max u v} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors topos geometricHomAction
  mapId S := ElementaryTopos.isoOfNatIso (identityIso S.unop.unco.Obj)
  mapComp F G := ElementaryTopos.isoOfNatIso
    (compositionIso (underlying G) (underlying F))
  map₂_whisker_left := by
    intro first middle last F G H α
    apply NatTrans.ext
    funext P
    apply NatTrans.ext
    funext X
    change P.map ((underlying F).map (α.unop2.unop.app X.unop)).op =
      𝟙 _ ≫ P.map ((underlying F).map (α.unop2.unop.app X.unop)).op ≫ 𝟙 _
    simp
  map₂_whisker_right := by
    intro first middle last F G α H
    apply NatTrans.ext
    funext P
    apply NatTrans.ext
    funext X
    change P.map (α.unop2.unop.app ((underlying H).obj X.unop)).op =
      𝟙 _ ≫ P.map (α.unop2.unop.app ((underlying H).obj X.unop)).op ≫ 𝟙 _
    simp
  map₂_associator := by
    intro first middle next last F G H
    apply NatTrans.ext
    funext P
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro value
    change P.map (𝟙 _) value = value
    exact P.map_id_apply _ value
  map₂_left_unitor := by
    intro first last F
    apply NatTrans.ext
    funext P
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro value
    change P.map (𝟙 _) value = value
    exact P.map_id_apply _ value
  map₂_right_unitor := by
    intro first last F
    apply NatTrans.ext
    funext P
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro value
    change P.map (𝟙 _) value = value
    exact P.map_id_apply _ value

@[simp] theorem action_route {S T : LambdaTheory.{u,v}} (F : LambdaTheoryMap S T) :
    ((action : Pseudofunctor Theories.{u,v}
      ElementaryTopos.{(max u v)+1,max u v}).map (route F)).functor =
        (theoryInverseImage F : (T.Objᵒᵖ ⥤ Type (max u v)) ⥤ _) := rfl

@[simp] theorem action_change {S T : LambdaTheory.{u,v}}
    {F G : LambdaTheoryMap S T} (α : F.functor ⟶ G.functor) :
    (action : Pseudofunctor Theories.{u,v}
      ElementaryTopos.{(max u v)+1,max u v}).map₂ (change α) =
        (cell α : inverseImage G.functor ⟶
          (inverseImage F.functor : (T.Objᵒᵖ ⥤ Type (max u v)) ⥤ _)) := rfl

/-- Forgetting the geometric structure recovers the independently
constructed presheaf action on every actual one-cell. -/
theorem forget_map {first last : Theories.{u,v}} (F : first ⟶ last) :
    ElementaryTopos.forget.map ((action : Pseudofunctor Theories.{u,v}
      ElementaryTopos.{(max u v)+1,max u v}).map F) =
        (PresheafTheoryPseudofunctor.action : Pseudofunctor Theories.{u,v}
          Cat.{max u v,(max u v)+1}).map F := rfl

theorem forget_cell {first last : Theories.{u,v}} {F G : first ⟶ last} (α : F ⟶ G) :
    ElementaryTopos.forget.map₂ ((action : Pseudofunctor Theories.{u,v}
      ElementaryTopos.{(max u v)+1,max u v}).map₂ α) =
        (PresheafTheoryPseudofunctor.action : Pseudofunctor Theories.{u,v}
          Cat.{max u v,(max u v)+1}).map₂ α := rfl

theorem forget_identity (S : Theories.{u,v}) :
    ElementaryTopos.forget.map₂ (((action : Pseudofunctor Theories.{u,v}
      ElementaryTopos.{(max u v)+1,max u v}).mapId S).hom) =
        ((PresheafTheoryPseudofunctor.action : Pseudofunctor Theories.{u,v}
          Cat.{max u v,(max u v)+1}).mapId S).hom := rfl

theorem forget_composition {first middle last : Theories.{u,v}}
    (F : first ⟶ middle) (G : middle ⟶ last) :
    ElementaryTopos.forget.map₂ (((action : Pseudofunctor Theories.{u,v}
      ElementaryTopos.{(max u v)+1,max u v}).mapComp F G).hom) =
        ((PresheafTheoryPseudofunctor.action : Pseudofunctor Theories.{u,v}
          Cat.{max u v,(max u v)+1}).mapComp F G).hom := rfl

end Mettapedia.GSLT.Topos.PresheafElementaryTopos
