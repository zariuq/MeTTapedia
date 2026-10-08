import Mettapedia.CategoryTheory.CodomainComprehensionFibration

/-!
# Slice categories are the complete fibres of codomain

The slice inclusion is full on precisely the squares over an identity
base map. Every display arrow over the base is covered, including arrows
whose codomain is propositionally rather than definitionally that base.
This gives an actual `HasFibers` presentation of the codomain fibration.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.CodomainComprehension

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C]

def fibreFunctor (base : C) : Over base ⥤ Functor.Fiber (Arrow.rightFunc : Arrow C ⥤ C) base :=
  Functor.Fiber.inducedFunctor (fibreInclusion_codomain base)

instance fibreFunctor_faithful (base : C) : (fibreFunctor base).Faithful where
  map_injective same := by
    apply Over.OverMorphism.ext
    exact congrArg (fun square => square.val.left) same

instance fibreFunctor_full (base : C) : (fibreFunctor base).Full where
  map_surjective {first second} square := by
    have := square.property
    have baseMap : 𝟙 base = square.val.right :=
      IsHomLift.eq_of_isHomLift Arrow.rightFunc (𝟙 base) square.val
    let arrow : first ⟶ second := Over.homMk square.val.left (by
      have readout := Arrow.w square.val
      change square.val.left ≫ second.hom = first.hom ≫ square.val.right at readout
      rw [← baseMap] at readout
      exact readout.trans (Category.comp_id _))
    refine ⟨arrow, ?_⟩
    apply Subtype.ext
    apply Arrow.hom_ext
    · rfl
    · exact baseMap

instance fibreFunctor_essSurj (base : C) : (fibreFunctor base).EssSurj where
  mem_essImage object := by
    rcases object with ⟨object, property⟩
    change object.right = base at property
    subst base
    let selected : Over object.right := Over.mk object.hom
    refine ⟨selected, ⟨eqToIso ?_⟩⟩
    apply Subtype.ext
    exact Arrow.mk_eq object

instance fibreFunctor_isEquivalence (base : C) : (fibreFunctor base).IsEquivalence where

def fibreEquivalence (base : C) : Over base ≌ Functor.Fiber (Arrow.rightFunc : Arrow C ⥤ C) base :=
  (fibreFunctor base).asEquivalence

@[instance_reducible] def sliceFibres : HasFibers (Arrow.rightFunc : Arrow C ⥤ C) where
  Fib := Over
  category _ := inferInstance
  ι := fibreInclusion
  comp_const := fibreInclusion_codomain
  equiv base := by
    change (fibreFunctor base).IsEquivalence
    infer_instance

@[simp] theorem fibreFunctor_full_readout {base : C} {first second : Over base}
    (arrow : first ⟶ second) :
    ((fibreFunctor base).map arrow).val.left = arrow.left := rfl

@[simp] theorem fibreFunctor_base_readout {base : C} {first second : Over base}
    (arrow : first ⟶ second) :
    ((fibreFunctor base).map arrow).val.right = 𝟙 base := rfl

end Mettapedia.CategoryTheory.CodomainComprehension
