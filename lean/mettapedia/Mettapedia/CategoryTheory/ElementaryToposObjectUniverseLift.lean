import Mettapedia.CategoryTheory.ElementaryToposGeometric
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Raising the objects of an elementary topos

Only objects are raised. Every hom type remains the original hom type,
and the up and down functors retain the complete supplied morphism.
Finite limits, cartesian closure and the classifier are transported
along the earned equivalence. No relation between the original object
and morphism universe levels is required.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposObjectUniverseLift

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

/-- Object-only lifting, with the original hom universe. -/
def Carrier (topos : ElementaryTopos.{u,v}) : Type (max u v) := ULift.{v} topos.Carrier

instance category (topos : ElementaryTopos.{u,v}) : Category.{v} (Carrier topos) where
  Hom first second := first.down ⟶ second.down
  id first := 𝟙 first.down
  comp first second := first ≫ second

def up (topos : ElementaryTopos.{u,v}) : topos ⥤ Carrier topos where
  obj object := ⟨object⟩
  map arrow := arrow

def down (topos : ElementaryTopos.{u,v}) : Carrier topos ⥤ topos where
  obj object := object.down
  map arrow := arrow

def equivalence (topos : ElementaryTopos.{u,v}) : topos ≌ Carrier topos where
  functor := up topos
  inverse := down topos
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [up, down])
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro first second arrow
    change arrow ≫ 𝟙 second = 𝟙 first ≫ arrow
    simp only [Category.comp_id, Category.id_comp])
  functor_unitIso_comp object := by
    change 𝟙 ((up topos).obj object) ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _

instance up_isEquivalence (topos : ElementaryTopos.{u,v}) : (up topos).IsEquivalence :=
  (equivalence topos).isEquivalence_functor

instance down_isEquivalence (topos : ElementaryTopos.{u,v}) : (down topos).IsEquivalence :=
  (equivalence topos).isEquivalence_inverse

instance finite (topos : ElementaryTopos.{u,v}) : HasFiniteLimits (Carrier topos) where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (down topos)

instance cartesian (topos : ElementaryTopos.{u,v}) :
    CartesianMonoidalCategory (Carrier topos) := .ofHasFiniteProducts

instance closed (topos : ElementaryTopos.{u,v}) : MonoidalClosed (Carrier topos) :=
  cartesianClosedOfEquiv (equivalence topos)

def classifier (topos : ElementaryTopos.{u,v}) : Subobject.Classifier (Carrier topos) :=
  topos.classifier.ofEquivalence (equivalence topos)

/-- The equivalently presented topos is large enough for the codomain
fibration bundle, without raising its morphisms. -/
def raised (topos : ElementaryTopos.{u,v}) : ElementaryTopos.{max u v,v} :=
  ElementaryTopos.ofCategory (Carrier topos) (classifier topos)

@[simp] theorem up_obj_down (topos : ElementaryTopos.{u,v}) (object : topos) :
    ((up topos).obj object).down = object := rfl

@[simp] theorem down_obj_up (topos : ElementaryTopos.{u,v}) (object : Carrier topos) :
    (up topos).obj ((down topos).obj object) = object := rfl

@[simp] theorem down_up_map (topos : ElementaryTopos.{u,v}) {first second : topos}
    (arrow : first ⟶ second) :
    (down topos).map ((up topos).map arrow) = arrow := rfl

@[simp] theorem up_down_map (topos : ElementaryTopos.{u,v})
    {first second : Carrier topos} (arrow : first ⟶ second) :
    (up topos).map ((down topos).map arrow) = arrow := rfl

@[simp] theorem truth_readout (topos : ElementaryTopos.{u,v}) :
    (down topos).map (classifier topos).truth = topos.classifier.truth := rfl

/-- The actual characteristic arrow retains the original complete
classifier readout, including every nonterminal input. -/
theorem characteristic_readout (topos : ElementaryTopos.{u,v})
    {selected object : Carrier topos} (inclusion : selected ⟶ object) [Mono inclusion] :
    (down topos).map ((classifier topos).χ inclusion) =
      topos.classifier.χ ((down topos).map inclusion) := by
  change 𝟙 _ ≫ topos.classifier.χ ((down topos).map inclusion) = _
  exact Category.id_comp _

theorem truth_domain_readout (topos : ElementaryTopos.{u,v}) (object : Carrier topos) :
    (down topos).map ((classifier topos).χ₀ object) =
      topos.classifier.χ₀ ((down topos).obj object) := by
  change 𝟙 _ ≫ topos.classifier.χ₀ ((down topos).obj object) = _
  exact Category.id_comp _

def upGeometric (topos : ElementaryTopos.{u,v}) :
    ElementaryTopos.GeometricHom topos (raised topos) :=
  ElementaryTopos.GeometricHom.ofEquivalence (equivalence topos)

def downGeometric (topos : ElementaryTopos.{u,v}) :
    ElementaryTopos.GeometricHom (raised topos) topos :=
  ElementaryTopos.GeometricHom.ofEquivalence (equivalence topos).symm

/-- Each original slice is retained, including its complete dependent
objects and arrows, in the raised codomain presentation. -/
def sliceEquivalence (topos : ElementaryTopos.{u,v}) (base : topos) :
    Over base ≌ Over ((up topos).obj base) :=
  Over.postEquiv base (equivalence topos)

@[simp] theorem slice_up_domain (topos : ElementaryTopos.{u,v})
    (base : topos) (object : Over base) :
    ((sliceEquivalence topos base).functor.obj object).left.down = object.left := rfl

@[simp] theorem slice_up_display (topos : ElementaryTopos.{u,v})
    (base : topos) (object : Over base) :
    (down topos).map ((sliceEquivalence topos base).functor.obj object).hom = object.hom := rfl

@[simp] theorem slice_up_arrow (topos : ElementaryTopos.{u,v})
    (base : topos) {first second : Over base} (arrow : first ⟶ second) :
    (down topos).map ((sliceEquivalence topos base).functor.map arrow).left = arrow.left := rfl

@[simp] theorem slice_down_domain (topos : ElementaryTopos.{u,v})
    (base : topos) (object : Over ((up topos).obj base)) :
    ((sliceEquivalence topos base).inverse.obj object).left = object.left.down := rfl

theorem slice_down_display (topos : ElementaryTopos.{u,v})
    (base : topos) (object : Over ((up topos).obj base)) :
    ((sliceEquivalence topos base).inverse.obj object).hom = (down topos).map object.hom := by
  change (down topos).map object.hom ≫ 𝟙 base = _
  exact Category.comp_id _

@[simp] theorem slice_down_arrow (topos : ElementaryTopos.{u,v})
    (base : topos) {first second : Over ((up topos).obj base)} (arrow : first ⟶ second) :
    ((sliceEquivalence topos base).inverse.map arrow).left = (down topos).map arrow.left := rfl

@[simp] theorem slice_unit_readout (topos : ElementaryTopos.{u,v})
    (base : topos) (object : Over base) :
    ((sliceEquivalence topos base).unitIso.hom.app object).left = 𝟙 object.left := rfl

@[simp] theorem slice_counit_readout (topos : ElementaryTopos.{u,v})
    (base : topos) (object : Over ((up topos).obj base)) :
    ((sliceEquivalence topos base).counitIso.hom.app object).left = 𝟙 object.left := rfl

end Mettapedia.CategoryTheory.ElementaryToposObjectUniverseLift
