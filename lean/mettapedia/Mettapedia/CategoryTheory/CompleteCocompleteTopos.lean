import Mettapedia.CategoryTheory.LogicalClassifierComparison
import Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Complete and cocomplete elementary topoi with logical morphisms

The diagram-size universe is explicit and independent of the object and
hom universes. A logical morphism preserves finite limits, exponentials,
and the classifier through its canonical characteristic comparison.
Natural transformations supply the two-cells. Closure under composition
uses the actual exponential and classifier comparison theorems.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe w u v

set_option linter.checkUnivs false in
structure CompleteCocompleteTopos where
  Carrier : Type u
  category : Category.{v} Carrier
  complete : HasLimitsOfSize.{w, w} Carrier
  cocomplete : HasColimitsOfSize.{w, w} Carrier
  finite : HasFiniteLimits Carrier
  cartesian : CartesianMonoidalCategory Carrier
  closed : MonoidalClosed Carrier
  classifier : Subobject.Classifier Carrier

namespace CompleteCocompleteTopos

attribute [instance] category complete cocomplete finite cartesian closed

instance : CoeSort CompleteCocompleteTopos.{w, u, v} (Type u) := ⟨Carrier⟩

structure LogicalHom (source target : CompleteCocompleteTopos.{w, u, v}) where
  functor : source ⥤ target
  finite : PreservesFiniteLimits functor
  closed : MonoidalClosedFunctor functor
  classifier : IsIso (LogicalClassifierComparison.comparison
    source.classifier target.classifier functor)

attribute [instance] LogicalHom.finite LogicalHom.closed LogicalHom.classifier

@[ext] theorem LogicalHom.ext {source target : CompleteCocompleteTopos.{w, u, v}}
    {first second : LogicalHom source target} (same : first.functor = second.functor) :
    first = second := by
  cases first
  cases second
  cases same
  rfl

def identity (source : CompleteCocompleteTopos.{w, u, v}) : LogicalHom source source where
  functor := 𝟭 source
  finite := inferInstance
  closed := cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts (𝟭 source) (Adjunction.id)
  classifier := by
    rw [LogicalClassifierComparison.identity]
    exact ⟨⟨𝟙 _, by simp⟩⟩

def composition {source middle target : CompleteCocompleteTopos.{w, u, v}}
    (first : LogicalHom source middle) (second : LogicalHom middle target) :
    LogicalHom source target where
  functor := first.functor ⋙ second.functor
  finite := comp_preservesFiniteLimits _ _
  closed := CartesianClosedFunctorCoherence.closed_composition _ _
  classifier := by
    rw [LogicalClassifierComparison.composition source.classifier middle.classifier]
    infer_instance

instance categoryStruct : CategoryStruct CompleteCocompleteTopos.{w, u, v} where
  Hom := LogicalHom
  id := identity
  comp := composition

instance homCategory (source target : CompleteCocompleteTopos.{w, u, v}) :
    Category (source ⟶ target) where
  Hom first second := first.functor ⟶ second.functor
  id first := 𝟙 first.functor
  comp first second := first ≫ second

def isoOfNatIso {source target : CompleteCocompleteTopos.{w, u, v}}
    {first second : source ⟶ target} (comparison : first.functor ≅ second.functor) :
    first ≅ second where
  hom := comparison.hom
  inv := comparison.inv
  hom_inv_id := comparison.hom_inv_id
  inv_hom_id := comparison.inv_hom_id

instance bicategory : Bicategory CompleteCocompleteTopos.{w, u, v} where
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

def toCat (source : CompleteCocompleteTopos.{w, u, v}) : Cat.{v, u} := Cat.of source

def forget : Pseudofunctor CompleteCocompleteTopos.{w, u, v} Cat.{v, u} where
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
  map₂_associator := by
    intro source middle next target first second third
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext object
    change 𝟙 _ = 𝟙 _ ≫ third.functor.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]
    exact ((congrArg (fun arrow => arrow ≫ 𝟙 _) (third.functor.map_id _)).trans
      (Category.id_comp _)).symm

end CompleteCocompleteTopos
end Mettapedia.CategoryTheory
