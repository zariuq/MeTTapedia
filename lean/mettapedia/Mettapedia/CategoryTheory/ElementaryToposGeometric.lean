import Mettapedia.CategoryTheory.ElementaryTopos
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# The strict 2-category of elementary topoi and inverse-image maps

One-cells are finite-limit-preserving functors equipped with the existence
of an actual right adjoint. They are directed as inverse-image functors.
Ordinary natural transformations supply the two-cells. Composition uses
the genuine composite adjunction, and every bicategory coherence equation
holds for the underlying functors and natural transformations.

Closed-functor and classifier preservation are not required of one-cells.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryTopos

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u₁ v₁ u₂ v₂ u₃ v₃ w w'

structure GeometricHom (source : ElementaryTopos.{u₁, v₁})
    (target : ElementaryTopos.{u₂, v₂}) where
  functor : source ⥤ target
  finite : PreservesFiniteLimits functor
  leftAdjoint : functor.IsLeftAdjoint

namespace GeometricHom

attribute [instance] finite leftAdjoint

@[ext] theorem ext {source : ElementaryTopos.{u₁, v₁}}
    {target : ElementaryTopos.{u₂, v₂}} {first second : GeometricHom source target}
    (equal : first.functor = second.functor) : first = second := by
  cases first
  cases second
  cases equal
  rfl

def id (source : ElementaryTopos.{u₁, v₁}) : GeometricHom source source where
  functor := 𝟭 source
  finite := inferInstance
  leftAdjoint := ⟨𝟭 source, ⟨Adjunction.id⟩⟩

def comp {source : ElementaryTopos.{u₁, v₁}} {middle : ElementaryTopos.{u₂, v₂}}
    {target : ElementaryTopos.{u₃, v₃}}
    (second : GeometricHom middle target) (first : GeometricHom source middle) :
    GeometricHom source target where
  functor := first.functor ⋙ second.functor
  finite := comp_preservesFiniteLimits _ _
  leftAdjoint := inferInstance

def ofAdjunction {source : ElementaryTopos.{u₁, v₁}}
    {target : ElementaryTopos.{u₂, v₂}} (left : source ⥤ target)
    [PreservesFiniteLimits left] {right : target ⥤ source} (adjunction : left ⊣ right) :
    GeometricHom source target where
  functor := left
  finite := inferInstance
  leftAdjoint := ⟨right, ⟨adjunction⟩⟩

def ofEquivalence {source : ElementaryTopos.{u₁, v₁}}
    {target : ElementaryTopos.{u₂, v₂}} (equivalence : source ≌ target) :
    GeometricHom source target where
  functor := equivalence.functor
  finite := inferInstance
  leftAdjoint := equivalence.isLeftAdjoint_functor

def rightAdjoint {source : ElementaryTopos.{u₁, v₁}}
    {target : ElementaryTopos.{u₂, v₂}} (route : GeometricHom source target) :
    target ⥤ source := route.functor.rightAdjoint

def adjunction {source : ElementaryTopos.{u₁, v₁}}
    {target : ElementaryTopos.{u₂, v₂}} (route : GeometricHom source target) :
    route.functor ⊣ route.rightAdjoint := Adjunction.ofIsLeftAdjoint route.functor

/-- Every available small colimit is preserved by the actual inverse-image map. -/
instance preservesColimits {source : ElementaryTopos.{u₁, v₁}}
    {target : ElementaryTopos.{u₂, v₂}} (route : GeometricHom source target) :
    PreservesColimitsOfSize.{w, w'} route.functor := inferInstance

@[simp] theorem id_functor (source : ElementaryTopos.{u₁, v₁}) :
    (id source).functor = 𝟭 source := rfl

@[simp] theorem comp_functor {source : ElementaryTopos.{u₁, v₁}}
    {middle : ElementaryTopos.{u₂, v₂}} {target : ElementaryTopos.{u₃, v₃}}
    (second : GeometricHom middle target) (first : GeometricHom source middle) :
    (comp second first).functor = first.functor ⋙ second.functor := rfl

end GeometricHom

instance categoryStruct : CategoryStruct ElementaryTopos.{u, v} where
  Hom := GeometricHom
  id := GeometricHom.id
  comp first second := GeometricHom.comp second first

instance homCategory (source target : ElementaryTopos.{u, v}) :
    Category (source ⟶ target) where
  Hom first second := first.functor ⟶ second.functor
  id first := 𝟙 first.functor
  comp first second := first ≫ second

def isoOfNatIso {source target : ElementaryTopos.{u, v}}
    {first second : source ⟶ target} (comparison : first.functor ≅ second.functor) :
    first ≅ second where
  hom := comparison.hom
  inv := comparison.inv
  hom_inv_id := comparison.hom_inv_id
  inv_hom_id := comparison.inv_hom_id

instance bicategory : Bicategory ElementaryTopos.{u, v} where
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

instance strict : Bicategory.Strict ElementaryTopos.{u, v} where
  id_comp route := GeometricHom.ext (Functor.id_comp route.functor)
  comp_id route := GeometricHom.ext (Functor.comp_id route.functor)
  assoc first second third := by
    apply GeometricHom.ext
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

instance mapCategory (source target : ElementaryTopos.{u, v}) :
    Category (GeometricHom source target) := homCategory source target

def toCat (source : ElementaryTopos.{u, v}) : Cat.{v, u} := Cat.of source.Carrier

def forget : Pseudofunctor ElementaryTopos.{u, v} Cat.{v, u} where
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

end Mettapedia.CategoryTheory.ElementaryTopos
