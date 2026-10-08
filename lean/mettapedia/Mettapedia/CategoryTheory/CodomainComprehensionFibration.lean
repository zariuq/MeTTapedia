import Mettapedia.CategoryTheory.CodomainComprehension
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.FiberedCategory.HasFibers

/-!
# The actual codomain fibration and its slice fibres

Chosen pullback squares provide Cartesian lifts. Arbitrary Cartesian
squares are then characterized by their pullback universal property.
Slice morphisms are precisely the maps of display arrows over an identity
base map; the fibre inclusion keeps their full domain map.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.CodomainComprehension

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C]

def fibreInclusion (base : C) : Over base ⥤ Arrow C where
  obj object := Arrow.mk object.hom
  map arrow := Arrow.homMk arrow.left (𝟙 base) (by simp)

@[simp] theorem fibreInclusion_domain (base : C) (object : Over base) :
    ((fibreInclusion base).obj object).left = object.left := rfl

theorem fibreInclusion_codomain (base : C) :
    fibreInclusion base ⋙ Arrow.rightFunc = (Functor.const (Over base)).obj base := rfl

instance fibreInclusion_faithful (base : C) : (fibreInclusion base).Faithful where
  map_injective same := Over.OverMorphism.ext (congrArg Arrow.Hom.left same)

def fibreMapEquiv {base : C} (first second : Over base) :
    (first ⟶ second) ≃
      {square : (fibreInclusion base).obj first ⟶ (fibreInclusion base).obj second //
        square.right = 𝟙 base} where
  toFun arrow := ⟨(fibreInclusion base).map arrow, rfl⟩
  invFun square := Over.homMk square.val.left (by
    have readout := Arrow.w square.val
    change square.val.left ≫ second.hom = first.hom ≫ square.val.right at readout
    rw [square.property, Category.comp_id] at readout
    exact readout)
  left_inv arrow := by
    apply Over.OverMorphism.ext
    rfl
  right_inv square := by
    apply Subtype.ext
    apply Arrow.hom_ext
    · rfl
    · exact square.property.symm

variable [HasPullbacks C]

def pullbackLift {base : C} (object : Arrow C) (route : base ⟶ object.right) :
    Arrow.mk (pullback.snd object.hom route) ⟶ object :=
  Arrow.homMk (pullback.fst object.hom route) route pullback.condition

instance pullbackLift_stronglyCartesian {base : C} (object : Arrow C)
    (route : base ⟶ object.right) :
    Arrow.rightFunc.IsStronglyCartesian route (pullbackLift object route) :=
  pullback_stronglyCartesian (pullbackLift object route)
    (IsPullback.of_hasPullback object.hom route)

instance codomain_fibered : (Arrow.rightFunc : Arrow C ⥤ C).IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian
    (fun (object : Arrow C) (base : C) (route : base ⟶ object.right) =>
    ⟨Arrow.mk (pullback.snd object.hom route), pullbackLift object route, inferInstance⟩)

theorem cartesian_iff_pullback {first second : Arrow C} (square : first ⟶ second) :
    Arrow.rightFunc.IsCartesian square.right square ↔
      IsPullback square.left first.hom second.hom square.right := by
  constructor
  · intro cartesian
    have := cartesian
    exact stronglyCartesian_pullback square
  · intro cartesian
    have := pullback_stronglyCartesian square cartesian
    infer_instance

theorem comprehension_preserves_cartesian {first second : Arrow C}
    (square : first ⟶ second) [Arrow.rightFunc.IsCartesian square.right square] :
    IsPullback ((comprehension C).map square).left
      ((comprehension C).obj first).hom ((comprehension C).obj second).hom
      ((comprehension C).map square).right :=
  (cartesian_iff_pullback square).mp inferInstance

end Mettapedia.CategoryTheory.CodomainComprehension
