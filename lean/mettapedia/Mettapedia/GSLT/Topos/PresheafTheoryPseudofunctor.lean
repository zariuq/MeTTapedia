import Mettapedia.GSLT.Topos.PresheafTheoryActionCoherence
import Mettapedia.GSLT.Core.LambdaTheoryBicategory
import Mettapedia.CategoryTheory.BicategoryTwoOpposite

/-!
# Presheaf inverse image as an actual reversed theory action

The source reverses both one-cells and two-cells of the supplied closed
theory bicategory. The target is Cat: this action does not assert an
internal-language or full logical morphism into a dependent type theory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafTheoryPseudofunctor

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open Mettapedia.GSLT.Core PresheafTheoryAction

universe u v w

-- This bundle retains independently supplied object and hom universes.
set_option linter.checkUnivs false in
abbrev Theories := (Mettapedia.CategoryTheory.TwoOpposite LambdaTheory.{u,v})ᵒᵖ

def theory (S : LambdaTheory.{u,v}) : Theories.{u,v} :=
  Opposite.op (Mettapedia.CategoryTheory.TwoOpposite.co S)

def route {S T : LambdaTheory.{u,v}} (F : LambdaTheoryMap S T) :
    theory T ⟶ theory S := Quiver.Hom.op (Opposite.op F)

def change {S T : LambdaTheory.{u,v}} {F G : LambdaTheoryMap S T}
    (α : F.functor ⟶ G.functor) : route G ⟶ route F :=
  _root_.Bicategory.Opposite.op2 (Quiver.Hom.op α)

def underlying {first last : Theories.{u,v}} (F : first ⟶ last) :
    last.unop.unco.Obj ⥤ first.unop.unco.Obj := (Opposite.unop F.unop).functor

def presheaves (S : Theories.{u,v}) : Cat.{max u w, max u v (w+1)} :=
  Cat.of (S.unop.unco.Objᵒᵖ ⥤ Type w)

def homAction (first last : Theories.{u,v}) :
    (first ⟶ last) ⥤ (presheaves first ⟶ presheaves last) where
  obj F := (inverseImage (underlying F)).toCatHom
  map α := (cell α.unop2.unop).toCatHom₂
  map_id F := by
    apply Cat.Hom₂.ext
    exact cell_id (underlying F)
  map_comp α β := by
    apply Cat.Hom₂.ext
    exact cell_comp β.unop2.unop α.unop2.unop

set_option backward.isDefEq.respectTransparency false in
def action : Pseudofunctor Theories.{u,v} Cat.{max u w, max u v (w+1)} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors presheaves homAction
  mapId S := Cat.Hom.isoMk (identityIso S.unop.unco.Obj)
  mapComp F G := Cat.Hom.isoMk (compositionIso (underlying G) (underlying F))
  map₂_whisker_left := by
    intro first middle last F G H α
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext P
    apply NatTrans.ext
    funext X
    change P.map ((underlying F).map (α.unop2.unop.app X.unop)).op =
      𝟙 _ ≫ P.map ((underlying F).map (α.unop2.unop.app X.unop)).op ≫ 𝟙 _
    simp
  map₂_whisker_right := by
    intro first middle last F G α H
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext P
    apply NatTrans.ext
    funext X
    change P.map (α.unop2.unop.app ((underlying H).obj X.unop)).op =
      𝟙 _ ≫ P.map (α.unop2.unop.app ((underlying H).obj X.unop)).op ≫ 𝟙 _
    simp
  map₂_associator := by
    intro first middle next last F G H
    apply Cat.Hom₂.ext
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
    apply Cat.Hom₂.ext
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
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext P
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro value
    change P.map (𝟙 _) value = value
    exact P.map_id_apply _ value

@[simp] theorem action_route {S T : LambdaTheory.{u,v}} (F : LambdaTheoryMap S T) :
    (action : Pseudofunctor Theories.{u,v} Cat.{max u w,max u v (w+1)}).map (route F) =
      (theoryInverseImage F).toCatHom := rfl

@[simp] theorem action_change {S T : LambdaTheory.{u,v}}
    {F G : LambdaTheoryMap S T} (α : F.functor ⟶ G.functor) :
    (action : Pseudofunctor Theories.{u,v} Cat.{max u w,max u v (w+1)}).map₂ (change α) =
      (cell α).toCatHom₂ := rfl

end Mettapedia.GSLT.Topos.PresheafTheoryPseudofunctor
