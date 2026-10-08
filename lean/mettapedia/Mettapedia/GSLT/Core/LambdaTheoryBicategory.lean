import Mettapedia.GSLT.Core.LambdaTheory
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# The strict 2-category of supplied closed lambda theories

Objects retain their supplied finite limits and cartesian closed structure. One-cells preserve finite limits and the
actual canonical exponential comparisons. Two-cells are ordinary natural
transformations, with their real vertical composition and whiskering.
The associators and unitors satisfy every bicategory law and are the
corresponding equality cells, yielding a genuine strict 2-category.
Forgetting to Cat retains the complete functor and natural transformation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.LambdaTheory

open _root_.CategoryTheory

universe u v

instance categoryStruct : CategoryStruct LambdaTheory.{u, v} where
  Hom := LambdaTheoryMap
  id := LambdaTheoryMap.id
  comp first second := LambdaTheoryMap.comp second first

instance homCategory (source target : LambdaTheory.{u, v}) :
    Category (source ⟶ target) where
  Hom first second := first.functor ⟶ second.functor
  id first := 𝟙 first.functor
  comp first second := first ≫ second

def isoOfNatIso {source target : LambdaTheory.{u, v}}
    {first second : source ⟶ target} (comparison : first.functor ≅ second.functor) :
    first ≅ second where
  hom := comparison.hom
  inv := comparison.inv
  hom_inv_id := comparison.hom_inv_id
  inv_hom_id := comparison.inv_hom_id

instance bicategory : Bicategory LambdaTheory.{u, v} where
  toCategoryStruct := categoryStruct
  homCategory := homCategory
  whiskerLeft {_ _ _} first {_ _} change := Functor.whiskerLeft first.functor change
  whiskerRight {_ _ _} {_ _} change last := Functor.whiskerRight change last.functor
  associator {_ _ _ _} first middle last :=
    isoOfNatIso (Functor.associator first.functor middle.functor last.functor)
  leftUnitor {_ _} route := isoOfNatIso (first := 𝟙 _ ≫ route) (second := route)
    (Functor.leftUnitor route.functor)
  rightUnitor {_ _} route := isoOfNatIso (first := route ≫ 𝟙 _) (second := route)
    (Functor.rightUnitor route.functor)
  id_whiskerLeft := by
    intro source target first second change
    apply NatTrans.ext
    funext object
    change change.app object = 𝟙 _ ≫ change.app object ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  comp_whiskerLeft := by
    intro source middle next target first second earlier later change
    apply NatTrans.ext
    funext object
    change change.app _ = 𝟙 _ ≫ change.app _ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  id_whiskerRight := by
    intro source middle target first last
    apply NatTrans.ext
    funext object
    exact last.functor.map_id _
  comp_whiskerRight := by
    intro source middle target first second third earlier later last
    apply NatTrans.ext
    funext object
    exact last.functor.map_comp _ _
  whiskerRight_id := by
    intro source target first second change
    apply NatTrans.ext
    funext object
    change change.app object = 𝟙 _ ≫ change.app object ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  whiskerRight_comp := by
    intro source middle next target first second change earlier later
    apply NatTrans.ext
    funext object
    change later.functor.map (earlier.functor.map (change.app object)) =
      𝟙 _ ≫ later.functor.map (earlier.functor.map (change.app object)) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  whisker_assoc := by
    intro source middle next target first earlier later change last
    apply NatTrans.ext
    funext object
    change last.functor.map (change.app (first.functor.obj object)) =
      𝟙 _ ≫ last.functor.map (change.app (first.functor.obj object)) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  whisker_exchange := by
    intro source middle target first second third fourth firstChange lastChange
    apply NatTrans.ext
    funext object
    exact (lastChange.naturality (firstChange.app object)).symm
  pentagon := by
    intro first second third fourth fifth f g h i
    apply NatTrans.ext
    funext object
    change i.functor.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]
    exact (congrArg (fun arrow => arrow ≫ 𝟙 _) (i.functor.map_id _)).trans
      (Category.id_comp _)
  triangle := by
    intro source middle target first second
    apply NatTrans.ext
    funext object
    change 𝟙 _ ≫ 𝟙 _ = second.functor.map (𝟙 _)
    simp only [Category.id_comp]
    exact (second.functor.map_id _).symm

/-- The actual functor composition is strictly associative and unital;
its coherent natural comparison cells are the corresponding equality cells. -/
instance strict : Bicategory.Strict LambdaTheory.{u, v} where
  id_comp route := LambdaTheoryMap.ext (Functor.id_comp route.functor)
  comp_id route := LambdaTheoryMap.ext (Functor.comp_id route.functor)
  assoc first second third := by
    apply LambdaTheoryMap.ext
    rfl
  leftUnitor_eqToIso route := by
    apply Iso.ext
    apply NatTrans.ext
    funext object
    rfl
  rightUnitor_eqToIso route := by
    apply Iso.ext
    apply NatTrans.ext
    funext object
    rfl
  associator_eqToIso first second third := by
    apply Iso.ext
    apply NatTrans.ext
    funext object
    rfl


/-- Expose the same genuine hom category at the bundled-map type as well. -/
instance mapCategory (source target : LambdaTheory.{u, v}) :
    Category (LambdaTheoryMap source target) := homCategory source target


def toCat (source : LambdaTheory.{u, v}) : Cat.{v, u} := Cat.of source.Obj

def forget : Pseudofunctor LambdaTheory.{u, v} Cat.{v, u} where
  obj := toCat
  map route := route.functor.toCatHom
  map₂ change := change.toCatHom₂
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _
  map₂_whisker_left := by
    intro source middle target first second third change
    apply Cat.Hom₂.ext
    change Functor.whiskerLeft first.functor change = 𝟙 _ ≫
      Functor.whiskerLeft first.functor change ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  map₂_whisker_right := by
    intro source middle target first second change last
    apply Cat.Hom₂.ext
    change Functor.whiskerRight change last.functor = 𝟙 _ ≫
      Functor.whiskerRight change last.functor ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  map₂_left_unitor := by
    intro source target route
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext object
    change 𝟙 _ = 𝟙 _ ≫ route.functor.map (𝟙 _) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact (route.functor.map_id _).symm
  map₂_right_unitor := by
    intro source target route
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext object
    change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]

  map₂_associator := by
    intro source middle next target first second third
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext object
    change 𝟙 _ = 𝟙 _ ≫ third.functor.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]
    exact ((congrArg (fun arrow => arrow ≫ 𝟙 _) (third.functor.map_id _)).trans
      (Category.id_comp _)).symm


end Mettapedia.GSLT.Core.LambdaTheory
